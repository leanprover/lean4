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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
extern lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instNat;
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__1;
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
return v___x_18_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_11_ = stack[1].m_obj;
lean_object* v___y_12_ = stack[2].m_obj;
lean_object* v___y_13_ = stack[3].m_obj;
lean_object* v___y_14_ = stack[4].m_obj;
lean_object* v___y_15_ = stack[5].m_obj;
lean_object* v___y_16_ = stack[6].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0(lean_box(0), v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___boxed(lean_object* v_00_u03b1_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0(v_00_u03b1_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_28_;
}
}
lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0(lean_object* v___x_32_, lean_object* v___x_33_, lean_object* v___x_34_, lean_object* v_ctor_35_, lean_object* v_args_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_44_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_45_ = lean_string_dec_eq(v_ctor_35_, v___x_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_46_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__1));
v___x_47_ = lean_string_dec_eq(v_ctor_35_, v___x_46_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_48_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__2));
v___x_49_ = lean_string_dec_eq(v_ctor_35_, v___x_48_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; 
lean_dec_ref(v___x_34_);
lean_dec_ref(v___x_33_);
lean_dec_ref(v___x_32_);
v___x_50_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
return v___x_50_;
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = l_Lean_Name_mkStr4(v___x_32_, v___x_33_, v___x_34_, v___x_48_);
v___x_52_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_51_);
v___x_53_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_51_, v___x_52_, v_args_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_65_; 
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_65_ == 0)
{
lean_object* v_unused_66_; 
v_unused_66_ = lean_ctor_get(v___x_53_, 0);
lean_dec(v_unused_66_);
v___x_55_ = v___x_53_;
v_isShared_56_ = v_isSharedCheck_65_;
goto v_resetjp_54_;
}
else
{
lean_dec(v___x_53_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_65_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_63_; 
v___x_57_ = 1;
v___x_58_ = lean_box(0);
v___x_59_ = l_Lean_Expr_const___override(v___x_51_, v___x_58_);
v___x_60_ = lean_box(v___x_57_);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___x_59_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 0, v___x_61_);
v___x_63_ = v___x_55_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
lean_dec(v___x_51_);
v_a_67_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_53_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_53_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = l_Lean_Name_mkStr4(v___x_32_, v___x_33_, v___x_34_, v___x_46_);
v___x_76_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_75_);
v___x_77_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_75_, v___x_76_, v_args_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_89_; 
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v___x_77_, 0);
lean_dec(v_unused_90_);
v___x_79_ = v___x_77_;
v_isShared_80_ = v_isSharedCheck_89_;
goto v_resetjp_78_;
}
else
{
lean_dec(v___x_77_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_89_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_81_ = 0;
v___x_82_ = lean_box(0);
v___x_83_ = l_Lean_Expr_const___override(v___x_75_, v___x_82_);
v___x_84_ = lean_box(v___x_81_);
v___x_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___x_83_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_85_);
v___x_87_ = v___x_79_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
else
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
lean_dec(v___x_75_);
v_a_91_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v___x_77_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_77_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = l_Lean_Name_mkStr4(v___x_32_, v___x_33_, v___x_34_, v___x_44_);
v___x_100_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_99_);
v___x_101_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_99_, v___x_100_, v_args_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_113_; 
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; 
v_unused_114_ = lean_ctor_get(v___x_101_, 0);
lean_dec(v_unused_114_);
v___x_103_ = v___x_101_;
v_isShared_104_ = v_isSharedCheck_113_;
goto v_resetjp_102_;
}
else
{
lean_dec(v___x_101_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_113_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
uint8_t v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_105_ = 2;
v___x_106_ = lean_box(0);
v___x_107_ = l_Lean_Expr_const___override(v___x_99_, v___x_106_);
v___x_108_ = lean_box(v___x_105_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_107_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v___x_109_);
v___x_111_ = v___x_103_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
else
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
lean_dec(v___x_99_);
v_a_115_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_101_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_101_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_32_ = stack[0].m_obj;
lean_object* v___x_33_ = stack[1].m_obj;
lean_object* v___x_34_ = stack[2].m_obj;
lean_object* v_ctor_35_ = stack[3].m_obj;
lean_object* v_args_36_ = stack[4].m_obj;
lean_object* v___y_37_ = stack[5].m_obj;
lean_object* v___y_38_ = stack[6].m_obj;
lean_object* v___y_39_ = stack[7].m_obj;
lean_object* v___y_40_ = stack[8].m_obj;
lean_object* v___y_41_ = stack[9].m_obj;
lean_object* v___y_42_ = stack[10].m_obj;
lean_object* v_res_123_;
v_res_123_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0(v___x_32_, v___x_33_, v___x_34_, v_ctor_35_, v_args_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
stack->m_obj
 = v_res_123_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___boxed(lean_object* v___x_124_, lean_object* v___x_125_, lean_object* v___x_126_, lean_object* v_ctor_127_, lean_object* v_args_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0(v___x_124_, v___x_125_, v___x_126_, v_ctor_127_, v_args_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec_ref(v_args_128_);
lean_dec_ref(v_ctor_127_);
return v_res_136_;
}
}
lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v___f_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___f_156_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__3));
v___x_157_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4));
v___x_158_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(v___x_157_, v___f_156_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
return v___x_158_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_148_ = stack[0].m_obj;
lean_object* v_a_149_ = stack[1].m_obj;
lean_object* v_a_150_ = stack[2].m_obj;
lean_object* v_a_151_ = stack[3].m_obj;
lean_object* v_a_152_ = stack[4].m_obj;
lean_object* v_a_153_ = stack[5].m_obj;
lean_object* v_a_154_ = stack[6].m_obj;
lean_object* v_res_159_;
v_res_159_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
stack->m_obj
 = v_res_159_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___boxed(lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
return v_res_168_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_box(0);
v___x_171_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4));
v___x_172_ = l_Lean_Expr_const___override(v___x_171_, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1);
v___x_174_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__0));
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals(void){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2, &l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_box(0);
v___x_178_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___x_177_);
return v___x_179_;
}
}
lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0);
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_183_;
v_res_183_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
stack->m_obj
 = v_res_183_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___boxed(lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
return v_res_185_;
}
}
lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0(lean_object* v_00_u03b1_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
return v___x_192_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_187_ = stack[1].m_obj;
lean_object* v___y_188_ = stack[2].m_obj;
lean_object* v___y_189_ = stack[3].m_obj;
lean_object* v___y_190_ = stack[4].m_obj;
lean_object* v_res_193_;
v_res_193_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0(lean_box(0), v___y_187_, v___y_188_, v___y_189_, v___y_190_);
stack->m_obj
 = v_res_193_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0(v_00_u03b1_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
return v_res_200_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1(lean_object* v_msgData_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; lean_object* v_env_208_; uint8_t v___x_209_; lean_object* v_env_210_; lean_object* v___x_211_; lean_object* v_toCold_212_; lean_object* v_mctx_213_; lean_object* v_lctx_214_; lean_object* v_options_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_207_ = lean_st_ref_get(v___y_205_);
v_env_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc_ref(v_env_208_);
lean_dec(v___x_207_);
v___x_209_ = 0;
v_env_210_ = l_Lean_Environment_setRecordingDeps(v_env_208_, v___x_209_);
v___x_211_ = lean_st_ref_get(v___y_203_);
v_toCold_212_ = lean_ctor_get(v___y_204_, 0);
v_mctx_213_ = lean_ctor_get(v___x_211_, 0);
lean_inc_ref(v_mctx_213_);
lean_dec(v___x_211_);
v_lctx_214_ = lean_ctor_get(v___y_202_, 2);
v_options_215_ = lean_ctor_get(v_toCold_212_, 2);
lean_inc_ref(v_options_215_);
lean_inc_ref(v_lctx_214_);
v___x_216_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_216_, 0, v_env_210_);
lean_ctor_set(v___x_216_, 1, v_mctx_213_);
lean_ctor_set(v___x_216_, 2, v_lctx_214_);
lean_ctor_set(v___x_216_, 3, v_options_215_);
v___x_217_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v_msgData_201_);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_201_ = stack[0].m_obj;
lean_object* v___y_202_ = stack[1].m_obj;
lean_object* v___y_203_ = stack[2].m_obj;
lean_object* v___y_204_ = stack[3].m_obj;
lean_object* v___y_205_ = stack[4].m_obj;
lean_object* v_res_219_;
v_res_219_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1(v_msgData_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1___boxed(lean_object* v_msgData_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1(v_msgData_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
return v_res_226_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(lean_object* v_msg_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_ref_233_; lean_object* v___x_234_; lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_243_; 
v_ref_233_ = lean_ctor_get(v___y_230_, 2);
v___x_234_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1(v_msg_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_243_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
lean_inc(v_ref_233_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v_ref_233_);
lean_ctor_set(v___x_239_, 1, v_a_235_);
if (v_isShared_238_ == 0)
{
lean_ctor_set_tag(v___x_237_, 1);
lean_ctor_set(v___x_237_, 0, v___x_239_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_227_ = stack[0].m_obj;
lean_object* v___y_228_ = stack[1].m_obj;
lean_object* v___y_229_ = stack[2].m_obj;
lean_object* v___y_230_ = stack[3].m_obj;
lean_object* v___y_231_ = stack[4].m_obj;
lean_object* v_res_244_;
v_res_244_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v_msg_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
stack->m_obj
 = v_res_244_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v_msg_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
return v_res_251_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__0));
v___x_254_ = l_Lean_stringToMessageData(v___x_253_);
return v___x_254_;
}
}
lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0(lean_object* v_ctor_255_, lean_object* v_args_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_275_ = lean_string_dec_eq(v_ctor_255_, v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_276_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__1));
v___x_277_ = lean_string_dec_eq(v_ctor_255_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__2));
v___x_279_ = lean_string_dec_eq(v_ctor_255_, v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
return v___x_280_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_281_ = lean_array_get_size(v_args_256_);
v___x_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = lean_nat_dec_eq(v___x_281_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v___x_284_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_285_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_284_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
else
{
goto v___jp_262_;
}
}
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_294_ = lean_array_get_size(v_args_256_);
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = lean_nat_dec_eq(v___x_294_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
v___x_297_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_298_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_297_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
else
{
goto v___jp_266_;
}
}
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_307_ = lean_array_get_size(v_args_256_);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_nat_dec_eq(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
v___x_310_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_311_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_310_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
else
{
goto v___jp_270_;
}
}
v___jp_262_:
{
uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = 1;
v___x_264_ = lean_box(v___x_263_);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
v___jp_266_:
{
uint8_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = 0;
v___x_268_ = lean_box(v___x_267_);
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
return v___x_269_;
}
v___jp_270_:
{
uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = 2;
v___x_272_ = lean_box(v___x_271_);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctor_255_ = stack[0].m_obj;
lean_object* v_args_256_ = stack[1].m_obj;
lean_object* v___y_257_ = stack[2].m_obj;
lean_object* v___y_258_ = stack[3].m_obj;
lean_object* v___y_259_ = stack[4].m_obj;
lean_object* v___y_260_ = stack[5].m_obj;
lean_object* v_res_320_;
v_res_320_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0(v_ctor_255_, v_args_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
stack->m_obj
 = v_res_320_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___boxed(lean_object* v_ctor_321_, lean_object* v_args_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0(v_ctor_321_, v_args_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec_ref(v_args_322_);
lean_dec_ref(v_ctor_321_);
return v_res_328_;
}
}
lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v___f_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___f_336_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___closed__0));
v___x_337_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4));
v___x_338_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_337_, v___f_336_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
return v___x_338_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_330_ = stack[0].m_obj;
lean_object* v_a_331_ = stack[1].m_obj;
lean_object* v_a_332_ = stack[2].m_obj;
lean_object* v_a_333_ = stack[3].m_obj;
lean_object* v_a_334_ = stack[4].m_obj;
lean_object* v_res_339_;
v_res_339_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___boxed(lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
return v_res_346_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1(lean_object* v_00_u03b1_347_, lean_object* v_msg_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v_msg_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
return v___x_354_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_348_ = stack[1].m_obj;
lean_object* v___y_349_ = stack[2].m_obj;
lean_object* v___y_350_ = stack[3].m_obj;
lean_object* v___y_351_ = stack[4].m_obj;
lean_object* v___y_352_ = stack[5].m_obj;
lean_object* v_res_355_;
v_res_355_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1(lean_box(0), v_msg_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
stack->m_obj
 = v_res_355_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_356_, lean_object* v_msg_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1(v_00_u03b1_356_, v_msg_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_363_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1);
v___x_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1);
v___x_368_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__0));
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v___x_367_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals(void){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2);
return v___x_370_;
}
}
lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0(lean_object* v___x_373_, lean_object* v___x_374_, lean_object* v___x_375_, lean_object* v_ctor_376_, lean_object* v_args_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_386_ = lean_string_dec_eq(v_ctor_376_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0));
v___x_388_ = lean_string_dec_eq(v_ctor_376_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__1));
v___x_390_ = lean_string_dec_eq(v_ctor_376_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
lean_dec_ref(v___x_375_);
lean_dec_ref(v___x_374_);
lean_dec_ref(v___x_373_);
v___x_391_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
return v___x_391_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = l_Lean_Name_mkStr4(v___x_373_, v___x_374_, v___x_375_, v___x_389_);
v___x_393_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_392_);
v___x_394_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_392_, v___x_393_, v_args_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_406_; 
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v___x_394_, 0);
lean_dec(v_unused_407_);
v___x_396_ = v___x_394_;
v_isShared_397_ = v_isSharedCheck_406_;
goto v_resetjp_395_;
}
else
{
lean_dec(v___x_394_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_406_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
uint8_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_398_ = 1;
v___x_399_ = lean_box(0);
v___x_400_ = l_Lean_Expr_const___override(v___x_392_, v___x_399_);
v___x_401_ = lean_box(v___x_398_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_400_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_402_);
v___x_404_ = v___x_396_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec(v___x_392_);
v_a_408_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_394_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_394_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = l_Lean_Name_mkStr4(v___x_373_, v___x_374_, v___x_375_, v___x_387_);
v___x_417_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_416_);
v___x_418_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_416_, v___x_417_, v_args_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_430_; 
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v___x_418_, 0);
lean_dec(v_unused_431_);
v___x_420_ = v___x_418_;
v_isShared_421_ = v_isSharedCheck_430_;
goto v_resetjp_419_;
}
else
{
lean_dec(v___x_418_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_430_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_422_ = 2;
v___x_423_ = lean_box(0);
v___x_424_ = l_Lean_Expr_const___override(v___x_416_, v___x_423_);
v___x_425_ = lean_box(v___x_422_);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v___x_424_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_426_);
v___x_428_ = v___x_420_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec(v___x_416_);
v_a_432_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_418_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_418_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = l_Lean_Name_mkStr4(v___x_373_, v___x_374_, v___x_375_, v___x_385_);
v___x_441_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_440_);
v___x_442_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_440_, v___x_441_, v_args_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_454_; 
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_454_ == 0)
{
lean_object* v_unused_455_; 
v_unused_455_ = lean_ctor_get(v___x_442_, 0);
lean_dec(v_unused_455_);
v___x_444_ = v___x_442_;
v_isShared_445_ = v_isSharedCheck_454_;
goto v_resetjp_443_;
}
else
{
lean_dec(v___x_442_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_454_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
uint8_t v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_446_ = 0;
v___x_447_ = lean_box(0);
v___x_448_ = l_Lean_Expr_const___override(v___x_440_, v___x_447_);
v___x_449_ = lean_box(v___x_446_);
v___x_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v___x_448_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_450_);
v___x_452_ = v___x_444_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_dec(v___x_440_);
v_a_456_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_442_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_442_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_373_ = stack[0].m_obj;
lean_object* v___x_374_ = stack[1].m_obj;
lean_object* v___x_375_ = stack[2].m_obj;
lean_object* v_ctor_376_ = stack[3].m_obj;
lean_object* v_args_377_ = stack[4].m_obj;
lean_object* v___y_378_ = stack[5].m_obj;
lean_object* v___y_379_ = stack[6].m_obj;
lean_object* v___y_380_ = stack[7].m_obj;
lean_object* v___y_381_ = stack[8].m_obj;
lean_object* v___y_382_ = stack[9].m_obj;
lean_object* v___y_383_ = stack[10].m_obj;
lean_object* v_res_464_;
v_res_464_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0(v___x_373_, v___x_374_, v___x_375_, v_ctor_376_, v_args_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
stack->m_obj
 = v_res_464_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___boxed(lean_object* v___x_465_, lean_object* v___x_466_, lean_object* v___x_467_, lean_object* v_ctor_468_, lean_object* v_args_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0(v___x_465_, v___x_466_, v___x_467_, v_ctor_468_, v_args_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec_ref(v_args_469_);
lean_dec_ref(v_ctor_468_);
return v_res_477_;
}
}
lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm(lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___f_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___f_495_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__1));
v___x_496_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2));
v___x_497_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(v___x_496_, v___f_495_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
return v___x_497_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_487_ = stack[0].m_obj;
lean_object* v_a_488_ = stack[1].m_obj;
lean_object* v_a_489_ = stack[2].m_obj;
lean_object* v_a_490_ = stack[3].m_obj;
lean_object* v_a_491_ = stack[4].m_obj;
lean_object* v_a_492_ = stack[5].m_obj;
lean_object* v_a_493_ = stack[6].m_obj;
lean_object* v_res_498_;
v_res_498_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm(v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
stack->m_obj
 = v_res_498_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___boxed(lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm(v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
return v_res_507_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = lean_box(0);
v___x_510_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2));
v___x_511_ = l_Lean_Expr_const___override(v___x_510_, v___x_509_);
return v___x_511_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1);
v___x_513_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__0));
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set(v___x_514_, 1, v___x_512_);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode(void){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2, &l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2);
return v___x_515_;
}
}
lean_object* l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0(lean_object* v_ctor_516_, lean_object* v_args_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_536_ = lean_string_dec_eq(v_ctor_516_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_537_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0));
v___x_538_ = lean_string_dec_eq(v_ctor_516_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__1));
v___x_540_ = lean_string_dec_eq(v_ctor_516_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
return v___x_541_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = lean_array_get_size(v_args_517_);
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = lean_nat_dec_eq(v___x_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v___x_545_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_546_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_545_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
else
{
goto v___jp_523_;
}
}
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = lean_array_get_size(v_args_517_);
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = lean_nat_dec_eq(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
v___x_558_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_559_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_558_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
v_a_560_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_559_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
else
{
goto v___jp_527_;
}
}
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_568_ = lean_array_get_size(v_args_517_);
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = lean_nat_dec_eq(v___x_568_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v___x_571_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_572_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_571_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
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
goto v___jp_531_;
}
}
v___jp_523_:
{
uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = 1;
v___x_525_ = lean_box(v___x_524_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
v___jp_527_:
{
uint8_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = 2;
v___x_529_ = lean_box(v___x_528_);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
v___jp_531_:
{
uint8_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = 0;
v___x_533_ = lean_box(v___x_532_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctor_516_ = stack[0].m_obj;
lean_object* v_args_517_ = stack[1].m_obj;
lean_object* v___y_518_ = stack[2].m_obj;
lean_object* v___y_519_ = stack[3].m_obj;
lean_object* v___y_520_ = stack[4].m_obj;
lean_object* v___y_521_ = stack[5].m_obj;
lean_object* v_res_581_;
v_res_581_ = l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0(v_ctor_516_, v_args_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
stack->m_obj
 = v_res_581_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0___boxed(lean_object* v_ctor_582_, lean_object* v_args_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0(v_ctor_582_, v_args_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec_ref(v_args_583_);
lean_dec_ref(v_ctor_582_);
return v_res_589_;
}
}
lean_object* l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr(lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v___f_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___f_597_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___closed__0));
v___x_598_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2));
v___x_599_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_598_, v___f_597_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
return v___x_599_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_591_ = stack[0].m_obj;
lean_object* v_a_592_ = stack[1].m_obj;
lean_object* v_a_593_ = stack[2].m_obj;
lean_object* v_a_594_ = stack[3].m_obj;
lean_object* v_a_595_ = stack[4].m_obj;
lean_object* v_res_600_;
v_res_600_ = l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr(v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
stack->m_obj
 = v_res_600_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___boxed(lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr(v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
return v_res_607_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1);
v___x_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1);
v___x_612_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__0));
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___x_611_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode(void){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2, &l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2);
return v___x_614_;
}
}
lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0(lean_object* v___x_619_, lean_object* v___x_620_, lean_object* v___x_621_, lean_object* v_ctor_622_, lean_object* v_args_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0));
v___x_632_ = lean_string_dec_lt(v_ctor_622_, v___x_631_);
if (v___x_632_ == 0)
{
uint8_t v___x_633_; 
v___x_633_ = lean_string_dec_eq(v_ctor_622_, v___x_631_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0));
v___x_635_ = lean_string_dec_eq(v_ctor_622_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_636_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1));
v___x_637_ = lean_string_dec_eq(v_ctor_622_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
lean_dec_ref(v___x_621_);
lean_dec_ref(v___x_620_);
lean_dec_ref(v___x_619_);
v___x_638_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
return v___x_638_;
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = l_Lean_Name_mkStr4(v___x_619_, v___x_620_, v___x_621_, v___x_636_);
v___x_640_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_639_);
v___x_641_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_639_, v___x_640_, v_args_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_653_; 
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; 
v_unused_654_ = lean_ctor_get(v___x_641_, 0);
lean_dec(v_unused_654_);
v___x_643_ = v___x_641_;
v_isShared_644_ = v_isSharedCheck_653_;
goto v_resetjp_642_;
}
else
{
lean_dec(v___x_641_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_653_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
uint8_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_645_ = 2;
v___x_646_ = lean_box(0);
v___x_647_ = l_Lean_Expr_const___override(v___x_639_, v___x_646_);
v___x_648_ = lean_box(v___x_645_);
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v___x_647_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_649_);
v___x_651_ = v___x_643_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec(v___x_639_);
v_a_655_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_641_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_641_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = l_Lean_Name_mkStr4(v___x_619_, v___x_620_, v___x_621_, v___x_634_);
v___x_664_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_663_);
v___x_665_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_663_, v___x_664_, v_args_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_677_; 
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; 
v_unused_678_ = lean_ctor_get(v___x_665_, 0);
lean_dec(v_unused_678_);
v___x_667_ = v___x_665_;
v_isShared_668_ = v_isSharedCheck_677_;
goto v_resetjp_666_;
}
else
{
lean_dec(v___x_665_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_677_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_669_ = 4;
v___x_670_ = lean_box(0);
v___x_671_ = l_Lean_Expr_const___override(v___x_663_, v___x_670_);
v___x_672_ = lean_box(v___x_669_);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v___x_671_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_673_);
v___x_675_ = v___x_667_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec(v___x_663_);
v_a_679_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_665_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_665_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = l_Lean_Name_mkStr4(v___x_619_, v___x_620_, v___x_621_, v___x_631_);
v___x_688_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_687_);
v___x_689_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_687_, v___x_688_, v_args_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_701_; 
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; 
v_unused_702_ = lean_ctor_get(v___x_689_, 0);
lean_dec(v_unused_702_);
v___x_691_ = v___x_689_;
v_isShared_692_ = v_isSharedCheck_701_;
goto v_resetjp_690_;
}
else
{
lean_dec(v___x_689_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_701_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_693_ = 3;
v___x_694_ = lean_box(0);
v___x_695_ = l_Lean_Expr_const___override(v___x_687_, v___x_694_);
v___x_696_ = lean_box(v___x_693_);
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v___x_695_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_697_);
v___x_699_ = v___x_691_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec(v___x_687_);
v_a_703_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_689_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_689_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
else
{
lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_711_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_712_ = lean_string_dec_eq(v_ctor_622_, v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_713_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2));
v___x_714_ = lean_string_dec_eq(v_ctor_622_, v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_715_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__3));
v___x_716_ = lean_string_dec_eq(v_ctor_622_, v___x_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
lean_dec_ref(v___x_621_);
lean_dec_ref(v___x_620_);
lean_dec_ref(v___x_619_);
v___x_717_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
return v___x_717_;
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = l_Lean_Name_mkStr4(v___x_619_, v___x_620_, v___x_621_, v___x_715_);
v___x_719_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_718_);
v___x_720_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_718_, v___x_719_, v_args_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_732_; 
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v___x_720_, 0);
lean_dec(v_unused_733_);
v___x_722_ = v___x_720_;
v_isShared_723_ = v_isSharedCheck_732_;
goto v_resetjp_721_;
}
else
{
lean_dec(v___x_720_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_732_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
uint8_t v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_724_ = 5;
v___x_725_ = lean_box(0);
v___x_726_ = l_Lean_Expr_const___override(v___x_718_, v___x_725_);
v___x_727_ = lean_box(v___x_724_);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v___x_726_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_728_);
v___x_730_ = v___x_722_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v___x_718_);
v_a_734_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_720_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_720_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_742_ = l_Lean_Name_mkStr4(v___x_619_, v___x_620_, v___x_621_, v___x_713_);
v___x_743_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_742_);
v___x_744_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_742_, v___x_743_, v_args_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_756_; 
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v___x_744_, 0);
lean_dec(v_unused_757_);
v___x_746_ = v___x_744_;
v_isShared_747_ = v_isSharedCheck_756_;
goto v_resetjp_745_;
}
else
{
lean_dec(v___x_744_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_756_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
uint8_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_748_ = 1;
v___x_749_ = lean_box(0);
v___x_750_ = l_Lean_Expr_const___override(v___x_742_, v___x_749_);
v___x_751_ = lean_box(v___x_748_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v___x_750_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_752_);
v___x_754_ = v___x_746_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v___x_742_);
v_a_758_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_744_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_744_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = l_Lean_Name_mkStr4(v___x_619_, v___x_620_, v___x_621_, v___x_711_);
v___x_767_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_766_);
v___x_768_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_766_, v___x_767_, v_args_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_780_; 
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v___x_768_, 0);
lean_dec(v_unused_781_);
v___x_770_ = v___x_768_;
v_isShared_771_ = v_isSharedCheck_780_;
goto v_resetjp_769_;
}
else
{
lean_dec(v___x_768_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_780_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_772_ = 0;
v___x_773_ = lean_box(0);
v___x_774_ = l_Lean_Expr_const___override(v___x_766_, v___x_773_);
v___x_775_ = lean_box(v___x_772_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v___x_774_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_776_);
v___x_778_ = v___x_770_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec(v___x_766_);
v_a_782_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_768_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_768_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_619_ = stack[0].m_obj;
lean_object* v___x_620_ = stack[1].m_obj;
lean_object* v___x_621_ = stack[2].m_obj;
lean_object* v_ctor_622_ = stack[3].m_obj;
lean_object* v_args_623_ = stack[4].m_obj;
lean_object* v___y_624_ = stack[5].m_obj;
lean_object* v___y_625_ = stack[6].m_obj;
lean_object* v___y_626_ = stack[7].m_obj;
lean_object* v___y_627_ = stack[8].m_obj;
lean_object* v___y_628_ = stack[9].m_obj;
lean_object* v___y_629_ = stack[10].m_obj;
lean_object* v_res_790_;
v_res_790_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0(v___x_619_, v___x_620_, v___x_621_, v_ctor_622_, v_args_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
stack->m_obj
 = v_res_790_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___boxed(lean_object* v___x_791_, lean_object* v___x_792_, lean_object* v___x_793_, lean_object* v_ctor_794_, lean_object* v_args_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0(v___x_791_, v___x_792_, v___x_793_, v_ctor_794_, v_args_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec_ref(v_args_795_);
lean_dec_ref(v_ctor_794_);
return v_res_803_;
}
}
lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v___f_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___f_821_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__1));
v___x_822_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2));
v___x_823_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(v___x_822_, v___f_821_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
return v___x_823_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_813_ = stack[0].m_obj;
lean_object* v_a_814_ = stack[1].m_obj;
lean_object* v_a_815_ = stack[2].m_obj;
lean_object* v_a_816_ = stack[3].m_obj;
lean_object* v_a_817_ = stack[4].m_obj;
lean_object* v_a_818_ = stack[5].m_obj;
lean_object* v_a_819_ = stack[6].m_obj;
lean_object* v_res_824_;
v_res_824_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
stack->m_obj
 = v_res_824_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___boxed(lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
return v_res_833_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_835_ = lean_box(0);
v___x_836_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2));
v___x_837_ = l_Lean_Expr_const___override(v___x_836_, v___x_835_);
return v___x_837_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1);
v___x_839_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__0));
v___x_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
lean_ctor_set(v___x_840_, 1, v___x_838_);
return v___x_840_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode(void){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2, &l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2);
return v___x_841_;
}
}
lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0(lean_object* v_ctor_842_, lean_object* v_args_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_873_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0));
v___x_874_ = lean_string_dec_lt(v_ctor_842_, v___x_873_);
if (v___x_874_ == 0)
{
uint8_t v___x_875_; 
v___x_875_ = lean_string_dec_eq(v_ctor_842_, v___x_873_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_876_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0));
v___x_877_ = lean_string_dec_eq(v_ctor_842_, v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_878_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1));
v___x_879_ = lean_string_dec_eq(v_ctor_842_, v___x_878_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
return v___x_880_;
}
else
{
lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_881_ = lean_array_get_size(v_args_843_);
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = lean_nat_dec_eq(v___x_881_, v___x_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
v___x_884_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_885_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_884_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
else
{
goto v___jp_849_;
}
}
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_894_ = lean_array_get_size(v_args_843_);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = lean_nat_dec_eq(v___x_894_, v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
v___x_897_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_898_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_897_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
v_a_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
else
{
goto v___jp_853_;
}
}
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_907_ = lean_array_get_size(v_args_843_);
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = lean_nat_dec_eq(v___x_907_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
v___x_910_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_911_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_910_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
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
goto v___jp_857_;
}
}
}
else
{
lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_920_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_921_ = lean_string_dec_eq(v_ctor_842_, v___x_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_922_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2));
v___x_923_ = lean_string_dec_eq(v_ctor_842_, v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_924_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__3));
v___x_925_ = lean_string_dec_eq(v_ctor_842_, v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
return v___x_926_;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_927_ = lean_array_get_size(v_args_843_);
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = lean_nat_dec_eq(v___x_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
v___x_930_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_931_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_930_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
v_a_932_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_931_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_931_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
else
{
goto v___jp_861_;
}
}
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_940_ = lean_array_get_size(v_args_843_);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_nat_dec_eq(v___x_940_, v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
v___x_943_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_944_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_943_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
else
{
goto v___jp_865_;
}
}
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_953_ = lean_array_get_size(v_args_843_);
v___x_954_ = lean_unsigned_to_nat(0u);
v___x_955_ = lean_nat_dec_eq(v___x_953_, v___x_954_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
v___x_956_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_957_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_956_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
else
{
goto v___jp_869_;
}
}
}
v___jp_849_:
{
uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_850_ = 2;
v___x_851_ = lean_box(v___x_850_);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
v___jp_853_:
{
uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = 4;
v___x_855_ = lean_box(v___x_854_);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
v___jp_857_:
{
uint8_t v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_858_ = 3;
v___x_859_ = lean_box(v___x_858_);
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
return v___x_860_;
}
v___jp_861_:
{
uint8_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = 5;
v___x_863_ = lean_box(v___x_862_);
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
return v___x_864_;
}
v___jp_865_:
{
uint8_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_866_ = 1;
v___x_867_ = lean_box(v___x_866_);
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
return v___x_868_;
}
v___jp_869_:
{
uint8_t v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_870_ = 0;
v___x_871_ = lean_box(v___x_870_);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctor_842_ = stack[0].m_obj;
lean_object* v_args_843_ = stack[1].m_obj;
lean_object* v___y_844_ = stack[2].m_obj;
lean_object* v___y_845_ = stack[3].m_obj;
lean_object* v___y_846_ = stack[4].m_obj;
lean_object* v___y_847_ = stack[5].m_obj;
lean_object* v_res_966_;
v_res_966_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0(v_ctor_842_, v_args_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
stack->m_obj
 = v_res_966_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0___boxed(lean_object* v_ctor_967_, lean_object* v_args_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0(v_ctor_967_, v_args_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec_ref(v_args_968_);
lean_dec_ref(v_ctor_967_);
return v_res_974_;
}
}
lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v___f_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___f_982_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___closed__0));
v___x_983_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2));
v___x_984_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_983_, v___f_982_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
return v___x_984_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_976_ = stack[0].m_obj;
lean_object* v_a_977_ = stack[1].m_obj;
lean_object* v_a_978_ = stack[2].m_obj;
lean_object* v_a_979_ = stack[3].m_obj;
lean_object* v_a_980_ = stack[4].m_obj;
lean_object* v_res_985_;
v_res_985_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
stack->m_obj
 = v_res_985_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___boxed(lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
return v_res_992_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1);
v___x_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1);
v___x_997_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__0));
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v___x_996_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode(void){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2, &l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = lean_box(0);
v___x_1006_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__3));
v___x_1007_ = l_Lean_mkConst(v___x_1006_, v___x_1005_);
return v___x_1007_;
}
}
lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0(lean_object* v___x_1009_, lean_object* v___x_1010_, lean_object* v___x_1011_, lean_object* v_ctor_1012_, lean_object* v_args_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_1022_ = lean_string_dec_eq(v_ctor_1012_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__0));
v___x_1024_ = lean_string_dec_eq(v_ctor_1012_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__1));
v___x_1026_ = lean_string_dec_eq(v_ctor_1012_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; 
lean_dec_ref(v___x_1011_);
lean_dec_ref(v___x_1010_);
lean_dec_ref(v___x_1009_);
v___x_1027_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
return v___x_1027_;
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = l_Lean_Name_mkStr4(v___x_1009_, v___x_1010_, v___x_1011_, v___x_1025_);
v___x_1029_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1028_);
v___x_1030_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_1028_, v___x_1029_, v_args_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
lean_dec_ref_known(v___x_1030_, 1);
v___x_1031_ = lean_box(0);
v___x_1032_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4, &l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4);
v___x_1033_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5));
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_unsigned_to_nat(0u);
v___x_1036_ = lean_array_get_borrowed(v___x_1034_, v_args_1013_, v___x_1035_);
lean_inc(v___x_1036_);
v___x_1037_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(v___x_1032_, v___x_1033_, v___x_1036_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1057_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1057_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1057_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v_fst_1042_; lean_object* v_snd_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1056_; 
v_fst_1042_ = lean_ctor_get(v_a_1038_, 0);
v_snd_1043_ = lean_ctor_get(v_a_1038_, 1);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_a_1038_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1045_ = v_a_1038_;
v_isShared_1046_ = v_isSharedCheck_1056_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_snd_1043_);
lean_inc(v_fst_1042_);
lean_dec(v_a_1038_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1056_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1047_, 0, v_fst_1042_);
v___x_1048_ = l_Lean_Expr_const___override(v___x_1028_, v___x_1031_);
v___x_1049_ = l_Lean_Expr_app___override(v___x_1048_, v_snd_1043_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 1, v___x_1049_);
lean_ctor_set(v___x_1045_, 0, v___x_1047_);
v___x_1051_ = v___x_1045_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1053_; 
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1051_);
v___x_1053_ = v___x_1040_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec(v___x_1028_);
v_a_1058_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1037_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1037_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec(v___x_1028_);
v_a_1066_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1030_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1030_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = l_Lean_Name_mkStr4(v___x_1009_, v___x_1010_, v___x_1011_, v___x_1023_);
v___x_1075_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1074_);
v___x_1076_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_1074_, v___x_1075_, v_args_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec_ref_known(v___x_1076_, 1);
v___x_1077_ = lean_box(0);
v___x_1078_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4, &l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4);
v___x_1079_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5));
v___x_1080_ = lean_box(0);
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = lean_array_get_borrowed(v___x_1080_, v_args_1013_, v___x_1081_);
lean_inc(v___x_1082_);
v___x_1083_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(v___x_1078_, v___x_1079_, v___x_1082_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1103_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1103_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1103_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v_fst_1088_; lean_object* v_snd_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1102_; 
v_fst_1088_ = lean_ctor_get(v_a_1084_, 0);
v_snd_1089_ = lean_ctor_get(v_a_1084_, 1);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_a_1084_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1091_ = v_a_1084_;
v_isShared_1092_ = v_isSharedCheck_1102_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_snd_1089_);
lean_inc(v_fst_1088_);
lean_dec(v_a_1084_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1102_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1093_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1093_, 0, v_fst_1088_);
v___x_1094_ = l_Lean_Expr_const___override(v___x_1074_, v___x_1077_);
v___x_1095_ = l_Lean_Expr_app___override(v___x_1094_, v_snd_1089_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 1, v___x_1095_);
lean_ctor_set(v___x_1091_, 0, v___x_1093_);
v___x_1097_ = v___x_1091_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1099_; 
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1097_);
v___x_1099_ = v___x_1086_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec(v___x_1074_);
v_a_1104_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1083_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1083_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec(v___x_1074_);
v_a_1112_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1076_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1076_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = l_Lean_Name_mkStr4(v___x_1009_, v___x_1010_, v___x_1011_, v___x_1021_);
v___x_1121_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_1120_);
v___x_1122_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_1120_, v___x_1121_, v_args_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1133_; 
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; 
v_unused_1134_ = lean_ctor_get(v___x_1122_, 0);
lean_dec(v_unused_1134_);
v___x_1124_ = v___x_1122_;
v_isShared_1125_ = v_isSharedCheck_1133_;
goto v_resetjp_1123_;
}
else
{
lean_dec(v___x_1122_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1133_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1126_ = lean_box(0);
v___x_1127_ = lean_box(0);
v___x_1128_ = l_Lean_Expr_const___override(v___x_1120_, v___x_1127_);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1126_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1129_);
v___x_1131_ = v___x_1124_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v___x_1120_);
v_a_1135_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1122_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1122_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1009_ = stack[0].m_obj;
lean_object* v___x_1010_ = stack[1].m_obj;
lean_object* v___x_1011_ = stack[2].m_obj;
lean_object* v_ctor_1012_ = stack[3].m_obj;
lean_object* v_args_1013_ = stack[4].m_obj;
lean_object* v___y_1014_ = stack[5].m_obj;
lean_object* v___y_1015_ = stack[6].m_obj;
lean_object* v___y_1016_ = stack[7].m_obj;
lean_object* v___y_1017_ = stack[8].m_obj;
lean_object* v___y_1018_ = stack[9].m_obj;
lean_object* v___y_1019_ = stack[10].m_obj;
lean_object* v_res_1143_;
v_res_1143_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0(v___x_1009_, v___x_1010_, v___x_1011_, v_ctor_1012_, v_args_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
stack->m_obj
 = v_res_1143_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___boxed(lean_object* v___x_1144_, lean_object* v___x_1145_, lean_object* v___x_1146_, lean_object* v_ctor_1147_, lean_object* v_args_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0(v___x_1144_, v___x_1145_, v___x_1146_, v_ctor_1147_, v_args_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec_ref(v_args_1148_);
lean_dec_ref(v_ctor_1147_);
return v_res_1156_;
}
}
lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___f_1174_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__1));
v___x_1175_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2));
v___x_1176_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(v___x_1175_, v___f_1174_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
return v___x_1176_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1166_ = stack[0].m_obj;
lean_object* v_a_1167_ = stack[1].m_obj;
lean_object* v_a_1168_ = stack[2].m_obj;
lean_object* v_a_1169_ = stack[3].m_obj;
lean_object* v_a_1170_ = stack[4].m_obj;
lean_object* v_a_1171_ = stack[5].m_obj;
lean_object* v_a_1172_ = stack[6].m_obj;
lean_object* v_res_1177_;
v_res_1177_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
stack->m_obj
 = v_res_1177_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___boxed(lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
return v_res_1186_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = lean_box(0);
v___x_1189_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2));
v___x_1190_ = l_Lean_Expr_const___override(v___x_1189_, v___x_1188_);
return v___x_1190_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1);
v___x_1192_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__0));
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v___x_1191_);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences(void){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2, &l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2);
return v___x_1194_;
}
}
lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0(lean_object* v___x_1195_, lean_object* v___x_1196_, lean_object* v_ctor_1197_, lean_object* v_args_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_1252_ = lean_string_dec_eq(v_ctor_1197_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__0));
v___x_1254_ = lean_string_dec_eq(v_ctor_1197_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__1));
v___x_1256_ = lean_string_dec_eq(v_ctor_1197_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
lean_dec_ref(v___x_1195_);
v___x_1257_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
return v___x_1257_;
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1258_ = lean_array_get_size(v_args_1198_);
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = lean_nat_dec_eq(v___x_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec_ref(v___x_1195_);
v___x_1261_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_1262_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1261_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
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
lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1271_ = lean_array_get_size(v_args_1198_);
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = lean_nat_dec_eq(v___x_1271_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref(v___x_1195_);
v___x_1274_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_1275_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1274_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
else
{
goto v___jp_1226_;
}
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
lean_dec_ref(v___x_1195_);
v___x_1284_ = lean_array_get_size(v_args_1198_);
v___x_1285_ = lean_unsigned_to_nat(0u);
v___x_1286_ = lean_nat_dec_eq(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
v___x_1287_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_1288_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1287_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1288_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1288_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
else
{
goto v___jp_1248_;
}
}
v___jp_1204_:
{
lean_object* v_evalExpr_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v_evalExpr_1205_ = lean_ctor_get(v___x_1195_, 0);
lean_inc_ref(v_evalExpr_1205_);
lean_dec_ref(v___x_1195_);
v___x_1206_ = lean_unsigned_to_nat(0u);
v___x_1207_ = lean_array_get_borrowed(v___x_1196_, v_args_1198_, v___x_1206_);
lean_inc(v___y_1202_);
lean_inc_ref(v___y_1201_);
lean_inc(v___y_1200_);
lean_inc_ref(v___y_1199_);
lean_inc(v___x_1207_);
v___x_1208_ = lean_apply_6(v_evalExpr_1205_, v___x_1207_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, lean_box(0));
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1217_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1211_ = v___x_1208_;
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_a_1209_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v___x_1213_);
v___x_1215_ = v___x_1211_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
v_a_1218_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1208_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1208_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
v___jp_1226_:
{
lean_object* v_evalExpr_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_evalExpr_1227_ = lean_ctor_get(v___x_1195_, 0);
lean_inc_ref(v_evalExpr_1227_);
lean_dec_ref(v___x_1195_);
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = lean_array_get_borrowed(v___x_1196_, v_args_1198_, v___x_1228_);
lean_inc(v___y_1202_);
lean_inc_ref(v___y_1201_);
lean_inc(v___y_1200_);
lean_inc_ref(v___y_1199_);
lean_inc(v___x_1229_);
v___x_1230_ = lean_apply_6(v_evalExpr_1227_, v___x_1229_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, lean_box(0));
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1239_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1239_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1239_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1235_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1235_, 0, v_a_1231_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1235_);
v___x_1237_ = v___x_1233_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
v_a_1240_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1230_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1230_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
v___jp_1248_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_box(0);
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1195_ = stack[0].m_obj;
lean_object* v___x_1196_ = stack[1].m_obj;
lean_object* v_ctor_1197_ = stack[2].m_obj;
lean_object* v_args_1198_ = stack[3].m_obj;
lean_object* v___y_1199_ = stack[4].m_obj;
lean_object* v___y_1200_ = stack[5].m_obj;
lean_object* v___y_1201_ = stack[6].m_obj;
lean_object* v___y_1202_ = stack[7].m_obj;
lean_object* v_res_1297_;
v_res_1297_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0(v___x_1195_, v___x_1196_, v_ctor_1197_, v_args_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
stack->m_obj
 = v_res_1297_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___boxed(lean_object* v___x_1298_, lean_object* v___x_1299_, lean_object* v_ctor_1300_, lean_object* v_args_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0(v___x_1298_, v___x_1299_, v_ctor_1300_, v_args_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec_ref(v_args_1301_);
lean_dec_ref(v_ctor_1300_);
lean_dec_ref(v___x_1299_);
return v_res_1307_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = l_Lean_Elab_ConfigEval_EvalExpr_instNat;
v___x_1309_ = l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg(v___x_1308_);
return v___x_1309_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__1(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___f_1312_; 
v___x_1310_ = l_Lean_instInhabitedExpr;
v___x_1311_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0, &l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0_once, _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0);
v___f_1312_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1312_, 0, v___x_1311_);
lean_closure_set(v___f_1312_, 1, v___x_1310_);
return v___f_1312_;
}
}
lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v___f_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___f_1319_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__1);
v___x_1320_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2));
v___x_1321_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_1320_, v___f_1319_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
return v___x_1321_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1313_ = stack[0].m_obj;
lean_object* v_a_1314_ = stack[1].m_obj;
lean_object* v_a_1315_ = stack[2].m_obj;
lean_object* v_a_1316_ = stack[3].m_obj;
lean_object* v_a_1317_ = stack[4].m_obj;
lean_object* v_res_1322_;
v_res_1322_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
stack->m_obj
 = v_res_1322_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___boxed(lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
return v_res_1329_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1);
v___x_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
return v___x_1332_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1);
v___x_1334_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__0));
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v___x_1333_);
return v___x_1335_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences(void){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2, &l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2);
return v___x_1336_;
}
}
lean_object* runtime_initialize_Lean_Elab_ConfigEval_Commands(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval_Instances(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ConfigEval_MetaInstances(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
