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
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instances"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducible"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "implicit"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__3_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0(lean_object* v___x_601_, lean_object* v___x_602_, lean_object* v___x_603_, lean_object* v_ctor_604_, lean_object* v_args_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0));
v___x_614_ = lean_string_dec_lt(v_ctor_604_, v___x_613_);
if (v___x_614_ == 0)
{
uint8_t v___x_615_; 
v___x_615_ = lean_string_dec_eq(v_ctor_604_, v___x_613_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0));
v___x_617_ = lean_string_dec_eq(v_ctor_604_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1));
v___x_619_ = lean_string_dec_eq(v_ctor_604_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_dec_ref(v___x_603_);
lean_dec_ref(v___x_602_);
lean_dec_ref(v___x_601_);
v___x_620_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
return v___x_620_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = l_Lean_Name_mkStr4(v___x_601_, v___x_602_, v___x_603_, v___x_618_);
v___x_622_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_621_);
v___x_623_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_621_, v___x_622_, v_args_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_635_; 
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; 
v_unused_636_ = lean_ctor_get(v___x_623_, 0);
lean_dec(v_unused_636_);
v___x_625_ = v___x_623_;
v_isShared_626_ = v_isSharedCheck_635_;
goto v_resetjp_624_;
}
else
{
lean_dec(v___x_623_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_635_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_627_ = 2;
v___x_628_ = lean_box(0);
v___x_629_ = l_Lean_Expr_const___override(v___x_621_, v___x_628_);
v___x_630_ = lean_box(v___x_627_);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___x_629_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v___x_631_);
v___x_633_ = v___x_625_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec(v___x_621_);
v_a_637_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_623_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_623_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = l_Lean_Name_mkStr4(v___x_601_, v___x_602_, v___x_603_, v___x_616_);
v___x_646_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_645_);
v___x_647_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_645_, v___x_646_, v_args_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_659_; 
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v___x_647_, 0);
lean_dec(v_unused_660_);
v___x_649_ = v___x_647_;
v_isShared_650_ = v_isSharedCheck_659_;
goto v_resetjp_648_;
}
else
{
lean_dec(v___x_647_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_659_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_651_ = 4;
v___x_652_ = lean_box(0);
v___x_653_ = l_Lean_Expr_const___override(v___x_645_, v___x_652_);
v___x_654_ = lean_box(v___x_651_);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v___x_653_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_655_);
v___x_657_ = v___x_649_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec(v___x_645_);
v_a_661_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_647_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_647_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = l_Lean_Name_mkStr4(v___x_601_, v___x_602_, v___x_603_, v___x_613_);
v___x_670_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_669_);
v___x_671_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_669_, v___x_670_, v_args_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_683_; 
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; 
v_unused_684_ = lean_ctor_get(v___x_671_, 0);
lean_dec(v_unused_684_);
v___x_673_ = v___x_671_;
v_isShared_674_ = v_isSharedCheck_683_;
goto v_resetjp_672_;
}
else
{
lean_dec(v___x_671_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_683_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_675_ = 3;
v___x_676_ = lean_box(0);
v___x_677_ = l_Lean_Expr_const___override(v___x_669_, v___x_676_);
v___x_678_ = lean_box(v___x_675_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___x_677_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_679_);
v___x_681_ = v___x_673_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
lean_dec(v___x_669_);
v_a_685_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_671_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_671_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
else
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_694_ = lean_string_dec_eq(v_ctor_604_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2));
v___x_696_ = lean_string_dec_eq(v_ctor_604_, v___x_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__3));
v___x_698_ = lean_string_dec_eq(v_ctor_604_, v___x_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; 
lean_dec_ref(v___x_603_);
lean_dec_ref(v___x_602_);
lean_dec_ref(v___x_601_);
v___x_699_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
return v___x_699_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = l_Lean_Name_mkStr4(v___x_601_, v___x_602_, v___x_603_, v___x_697_);
v___x_701_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_700_);
v___x_702_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_700_, v___x_701_, v_args_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_714_; 
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; 
v_unused_715_ = lean_ctor_get(v___x_702_, 0);
lean_dec(v_unused_715_);
v___x_704_ = v___x_702_;
v_isShared_705_ = v_isSharedCheck_714_;
goto v_resetjp_703_;
}
else
{
lean_dec(v___x_702_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_714_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_706_ = 5;
v___x_707_ = lean_box(0);
v___x_708_ = l_Lean_Expr_const___override(v___x_700_, v___x_707_);
v___x_709_ = lean_box(v___x_706_);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v___x_708_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_710_);
v___x_712_ = v___x_704_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec(v___x_700_);
v_a_716_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_702_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_702_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_724_ = l_Lean_Name_mkStr4(v___x_601_, v___x_602_, v___x_603_, v___x_695_);
v___x_725_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_724_);
v___x_726_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_724_, v___x_725_, v_args_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_738_; 
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; 
v_unused_739_ = lean_ctor_get(v___x_726_, 0);
lean_dec(v_unused_739_);
v___x_728_ = v___x_726_;
v_isShared_729_ = v_isSharedCheck_738_;
goto v_resetjp_727_;
}
else
{
lean_dec(v___x_726_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_738_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
uint8_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_730_ = 1;
v___x_731_ = lean_box(0);
v___x_732_ = l_Lean_Expr_const___override(v___x_724_, v___x_731_);
v___x_733_ = lean_box(v___x_730_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v___x_732_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_734_);
v___x_736_ = v___x_728_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v___x_724_);
v_a_740_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_726_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_726_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = l_Lean_Name_mkStr4(v___x_601_, v___x_602_, v___x_603_, v___x_693_);
v___x_749_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_748_);
v___x_750_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_748_, v___x_749_, v_args_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_762_; 
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v___x_750_, 0);
lean_dec(v_unused_763_);
v___x_752_ = v___x_750_;
v_isShared_753_ = v_isSharedCheck_762_;
goto v_resetjp_751_;
}
else
{
lean_dec(v___x_750_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_762_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
uint8_t v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_754_ = 0;
v___x_755_ = lean_box(0);
v___x_756_ = l_Lean_Expr_const___override(v___x_748_, v___x_755_);
v___x_757_ = lean_box(v___x_754_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v___x_756_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_758_);
v___x_760_ = v___x_752_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec(v___x_748_);
v_a_764_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_750_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_750_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___boxed(lean_object* v___x_772_, lean_object* v___x_773_, lean_object* v___x_774_, lean_object* v_ctor_775_, lean_object* v_args_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0(v___x_772_, v___x_773_, v___x_774_, v_ctor_775_, v_args_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec_ref(v_args_776_);
lean_dec_ref(v_ctor_775_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___f_802_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__1));
v___x_803_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2));
v___x_804_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(v___x_803_, v___f_802_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___boxed(lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
return v_res_813_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = lean_box(0);
v___x_816_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2));
v___x_817_ = l_Lean_Expr_const___override(v___x_816_, v___x_815_);
return v___x_817_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1);
v___x_819_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__0));
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v___x_818_);
return v___x_820_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode(void){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2, &l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0(lean_object* v_ctor_822_, lean_object* v_args_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_853_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0));
v___x_854_ = lean_string_dec_lt(v_ctor_822_, v___x_853_);
if (v___x_854_ == 0)
{
uint8_t v___x_855_; 
v___x_855_ = lean_string_dec_eq(v_ctor_822_, v___x_853_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_856_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0));
v___x_857_ = lean_string_dec_eq(v_ctor_822_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_858_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1));
v___x_859_ = lean_string_dec_eq(v_ctor_822_, v___x_858_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
return v___x_860_;
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_861_ = lean_array_get_size(v_args_823_);
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = lean_nat_dec_eq(v___x_861_, v___x_862_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
v___x_864_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_865_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_864_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
else
{
goto v___jp_829_;
}
}
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_874_ = lean_array_get_size(v_args_823_);
v___x_875_ = lean_unsigned_to_nat(0u);
v___x_876_ = lean_nat_dec_eq(v___x_874_, v___x_875_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v___x_877_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_878_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_877_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
else
{
goto v___jp_833_;
}
}
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_887_ = lean_array_get_size(v_args_823_);
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = lean_nat_dec_eq(v___x_887_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v___x_890_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_891_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_890_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
else
{
goto v___jp_837_;
}
}
}
else
{
lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_900_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_901_ = lean_string_dec_eq(v_ctor_822_, v___x_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_902_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2));
v___x_903_ = lean_string_dec_eq(v_ctor_822_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__3));
v___x_905_ = lean_string_dec_eq(v_ctor_822_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
return v___x_906_;
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_907_ = lean_array_get_size(v_args_823_);
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = lean_nat_dec_eq(v___x_907_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
v___x_910_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_911_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_910_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
else
{
goto v___jp_841_;
}
}
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_920_ = lean_array_get_size(v_args_823_);
v___x_921_ = lean_unsigned_to_nat(0u);
v___x_922_ = lean_nat_dec_eq(v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
v___x_923_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_924_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_923_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
else
{
goto v___jp_845_;
}
}
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_933_ = lean_array_get_size(v_args_823_);
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = lean_nat_dec_eq(v___x_933_, v___x_934_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
v___x_936_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_937_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_936_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
else
{
goto v___jp_849_;
}
}
}
v___jp_829_:
{
uint8_t v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_830_ = 2;
v___x_831_ = lean_box(v___x_830_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
v___jp_833_:
{
uint8_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = 4;
v___x_835_ = lean_box(v___x_834_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
return v___x_836_;
}
v___jp_837_:
{
uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = 3;
v___x_839_ = lean_box(v___x_838_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
v___jp_841_:
{
uint8_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = 5;
v___x_843_ = lean_box(v___x_842_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
return v___x_844_;
}
v___jp_845_:
{
uint8_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = 1;
v___x_847_ = lean_box(v___x_846_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
v___jp_849_:
{
uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_850_ = 0;
v___x_851_ = lean_box(v___x_850_);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0___boxed(lean_object* v_ctor_946_, lean_object* v_args_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0(v_ctor_946_, v_args_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec_ref(v_args_947_);
lean_dec_ref(v_ctor_946_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v___f_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___f_961_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___closed__0));
v___x_962_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2));
v___x_963_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_962_, v___f_961_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___boxed(lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
return v_res_970_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1);
v___x_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1);
v___x_975_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__0));
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v___x_974_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode(void){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2, &l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = lean_box(0);
v___x_984_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__3));
v___x_985_ = l_Lean_mkConst(v___x_984_, v___x_983_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0(lean_object* v___x_987_, lean_object* v___x_988_, lean_object* v___x_989_, lean_object* v_ctor_990_, lean_object* v_args_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_1000_ = lean_string_dec_eq(v_ctor_990_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__0));
v___x_1002_ = lean_string_dec_eq(v_ctor_990_, v___x_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__1));
v___x_1004_ = lean_string_dec_eq(v_ctor_990_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; 
lean_dec_ref(v___x_989_);
lean_dec_ref(v___x_988_);
lean_dec_ref(v___x_987_);
v___x_1005_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
return v___x_1005_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = l_Lean_Name_mkStr4(v___x_987_, v___x_988_, v___x_989_, v___x_1003_);
v___x_1007_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1006_);
v___x_1008_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_1006_, v___x_1007_, v_args_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec_ref_known(v___x_1008_, 1);
v___x_1009_ = lean_box(0);
v___x_1010_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4, &l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4);
v___x_1011_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5));
v___x_1012_ = lean_box(0);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_array_get_borrowed(v___x_1012_, v_args_991_, v___x_1013_);
lean_inc(v___x_1014_);
v___x_1015_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(v___x_1010_, v___x_1011_, v___x_1014_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1035_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1018_ = v___x_1015_;
v_isShared_1019_ = v_isSharedCheck_1035_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1035_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v_fst_1020_; lean_object* v_snd_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1034_; 
v_fst_1020_ = lean_ctor_get(v_a_1016_, 0);
v_snd_1021_ = lean_ctor_get(v_a_1016_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_a_1016_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1023_ = v_a_1016_;
v_isShared_1024_ = v_isSharedCheck_1034_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_snd_1021_);
lean_inc(v_fst_1020_);
lean_dec(v_a_1016_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1034_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1025_, 0, v_fst_1020_);
v___x_1026_ = l_Lean_Expr_const___override(v___x_1006_, v___x_1009_);
v___x_1027_ = l_Lean_Expr_app___override(v___x_1026_, v_snd_1021_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___x_1027_);
lean_ctor_set(v___x_1023_, 0, v___x_1025_);
v___x_1029_ = v___x_1023_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1031_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1029_);
v___x_1031_ = v___x_1018_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec(v___x_1006_);
v_a_1036_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1015_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1015_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec(v___x_1006_);
v_a_1044_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1008_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1008_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = l_Lean_Name_mkStr4(v___x_987_, v___x_988_, v___x_989_, v___x_1001_);
v___x_1053_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1052_);
v___x_1054_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_1052_, v___x_1053_, v_args_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
lean_dec_ref_known(v___x_1054_, 1);
v___x_1055_ = lean_box(0);
v___x_1056_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4, &l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4);
v___x_1057_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5));
v___x_1058_ = lean_box(0);
v___x_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = lean_array_get_borrowed(v___x_1058_, v_args_991_, v___x_1059_);
lean_inc(v___x_1060_);
v___x_1061_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(v___x_1056_, v___x_1057_, v___x_1060_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1081_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1081_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1081_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v_fst_1066_; lean_object* v_snd_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1080_; 
v_fst_1066_ = lean_ctor_get(v_a_1062_, 0);
v_snd_1067_ = lean_ctor_get(v_a_1062_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_a_1062_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1069_ = v_a_1062_;
v_isShared_1070_ = v_isSharedCheck_1080_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_snd_1067_);
lean_inc(v_fst_1066_);
lean_dec(v_a_1062_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1080_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1071_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1071_, 0, v_fst_1066_);
v___x_1072_ = l_Lean_Expr_const___override(v___x_1052_, v___x_1055_);
v___x_1073_ = l_Lean_Expr_app___override(v___x_1072_, v_snd_1067_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 1, v___x_1073_);
lean_ctor_set(v___x_1069_, 0, v___x_1071_);
v___x_1075_ = v___x_1069_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1077_; 
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1075_);
v___x_1077_ = v___x_1064_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v___x_1052_);
v_a_1082_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1061_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1061_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec(v___x_1052_);
v_a_1090_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1054_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1054_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1098_ = l_Lean_Name_mkStr4(v___x_987_, v___x_988_, v___x_989_, v___x_999_);
v___x_1099_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_1098_);
v___x_1100_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_1098_, v___x_1099_, v_args_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1111_; 
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1111_ == 0)
{
lean_object* v_unused_1112_; 
v_unused_1112_ = lean_ctor_get(v___x_1100_, 0);
lean_dec(v_unused_1112_);
v___x_1102_ = v___x_1100_;
v_isShared_1103_ = v_isSharedCheck_1111_;
goto v_resetjp_1101_;
}
else
{
lean_dec(v___x_1100_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1111_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1104_ = lean_box(0);
v___x_1105_ = lean_box(0);
v___x_1106_ = l_Lean_Expr_const___override(v___x_1098_, v___x_1105_);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1104_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v___x_1107_);
v___x_1109_ = v___x_1102_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v___x_1098_);
v_a_1113_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1100_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1100_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___boxed(lean_object* v___x_1121_, lean_object* v___x_1122_, lean_object* v___x_1123_, lean_object* v_ctor_1124_, lean_object* v_args_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0(v___x_1121_, v___x_1122_, v___x_1123_, v_ctor_1124_, v_args_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec_ref(v_args_1125_);
lean_dec_ref(v_ctor_1124_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v___f_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___f_1151_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__1));
v___x_1152_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2));
v___x_1153_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(v___x_1152_, v___f_1151_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___boxed(lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
return v_res_1162_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = lean_box(0);
v___x_1165_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2));
v___x_1166_ = l_Lean_Expr_const___override(v___x_1165_, v___x_1164_);
return v___x_1166_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1);
v___x_1168_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__0));
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v___x_1167_);
return v___x_1169_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences(void){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2, &l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = l_Lean_Elab_ConfigEval_EvalExpr_instNat;
v___x_1172_ = l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg(v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0(lean_object* v_ctor_1173_, lean_object* v_args_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1231_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_1232_ = lean_string_dec_eq(v_ctor_1173_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__0));
v___x_1234_ = lean_string_dec_eq(v_ctor_1173_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__1));
v___x_1236_ = lean_string_dec_eq(v_ctor_1173_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
return v___x_1237_;
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1238_ = lean_array_get_size(v_args_1174_);
v___x_1239_ = lean_unsigned_to_nat(1u);
v___x_1240_ = lean_nat_dec_eq(v___x_1238_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
v___x_1241_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_1242_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1241_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
else
{
goto v___jp_1180_;
}
}
}
else
{
lean_object* v___x_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1251_ = lean_array_get_size(v_args_1174_);
v___x_1252_ = lean_unsigned_to_nat(1u);
v___x_1253_ = lean_nat_dec_eq(v___x_1251_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
v___x_1254_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_1255_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1254_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1255_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1255_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
else
{
goto v___jp_1204_;
}
}
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1264_ = lean_array_get_size(v_args_1174_);
v___x_1265_ = lean_unsigned_to_nat(0u);
v___x_1266_ = lean_nat_dec_eq(v___x_1264_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
v___x_1267_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_1268_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1267_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
else
{
goto v___jp_1228_;
}
}
v___jp_1180_:
{
lean_object* v___x_1181_; lean_object* v_evalExpr_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1181_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0, &l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0_once, _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0);
v_evalExpr_1182_ = lean_ctor_get(v___x_1181_, 0);
v___x_1183_ = l_Lean_instInhabitedExpr;
v___x_1184_ = lean_unsigned_to_nat(0u);
v___x_1185_ = lean_array_get_borrowed(v___x_1183_, v_args_1174_, v___x_1184_);
lean_inc_ref(v_evalExpr_1182_);
lean_inc(v___y_1178_);
lean_inc_ref(v___y_1177_);
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
lean_inc(v___x_1185_);
v___x_1186_ = lean_apply_6(v_evalExpr_1182_, v___x_1185_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, lean_box(0));
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1195_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1195_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1195_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_a_1187_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1191_);
v___x_1193_ = v___x_1189_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
v_a_1196_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1186_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1186_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
v___jp_1204_:
{
lean_object* v___x_1205_; lean_object* v_evalExpr_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1205_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0, &l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0_once, _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0);
v_evalExpr_1206_ = lean_ctor_get(v___x_1205_, 0);
v___x_1207_ = l_Lean_instInhabitedExpr;
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = lean_array_get_borrowed(v___x_1207_, v_args_1174_, v___x_1208_);
lean_inc_ref(v_evalExpr_1206_);
lean_inc(v___y_1178_);
lean_inc_ref(v___y_1177_);
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
lean_inc(v___x_1209_);
v___x_1210_ = lean_apply_6(v_evalExpr_1206_, v___x_1209_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, lean_box(0));
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1219_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1215_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1215_, 0, v_a_1211_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1215_);
v___x_1217_ = v___x_1213_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
v_a_1220_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1210_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1210_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
v___jp_1228_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = lean_box(0);
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
return v___x_1230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___boxed(lean_object* v_ctor_1277_, lean_object* v_args_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0(v_ctor_1277_, v_args_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec_ref(v_args_1278_);
lean_dec_ref(v_ctor_1277_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v___f_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___f_1292_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0));
v___x_1293_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2));
v___x_1294_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_1293_, v___f_1292_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___boxed(lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
return v_res_1301_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1);
v___x_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
return v___x_1304_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1);
v___x_1306_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__0));
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
lean_ctor_set(v___x_1307_, 1, v___x_1305_);
return v___x_1307_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences(void){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2, &l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2);
return v___x_1308_;
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
