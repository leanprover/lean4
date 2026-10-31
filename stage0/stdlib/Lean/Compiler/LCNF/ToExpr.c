// Lean compiler output
// Module: Lean.Compiler.LCNF.ToExpr
// Imports: public import Lean.Compiler.LCNF.Basic import Init.Omega
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
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(uint8_t, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_Arg_toExpr___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExprM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExprM___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_abstractM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_abstractM___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__5_value;
static const lean_closure_object l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__1_value)}};
static const lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__7_value),((lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__3_value),((lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__4_value),((lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__5_value)}};
static const lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__8_value),((lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__6_value)}};
static const lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__9_value;
static const lean_closure_object l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 93, 203, 178, 149, 199, 118, 190)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toExprM___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__2;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "lcUnreachable"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 152, 7, 242, 102, 125, 47, 175)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toExprM___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__5;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "oset"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__6_value),LEAN_SCALAR_PTR_LITERAL(204, 56, 52, 158, 165, 233, 45, 89)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__7_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toExprM___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__8;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dummy"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__9_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__9_value),LEAN_SCALAR_PTR_LITERAL(209, 220, 178, 109, 127, 136, 95, 49)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__10_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__11_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__11_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__12_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__13;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "uset"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__14_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__14_value),LEAN_SCALAR_PTR_LITERAL(124, 160, 46, 241, 188, 4, 130, 152)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__15_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toExprM___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__16;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "sset"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__17 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__17_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__17_value),LEAN_SCALAR_PTR_LITERAL(46, 244, 58, 215, 190, 158, 72, 225)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__18 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__18_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toExprM___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__19;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "setTag"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__20 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__20_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__20_value),LEAN_SCALAR_PTR_LITERAL(249, 157, 207, 131, 172, 199, 30, 80)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__21 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__21_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toExprM___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__22;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inc"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__23 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__23_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__23_value),LEAN_SCALAR_PTR_LITERAL(79, 144, 50, 52, 33, 141, 134, 44)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__24 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__24_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toExprM___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__25;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__27 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__27_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__26 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__26_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__26_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__28_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__27_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__28 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__28_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__29;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__30 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__30_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__26_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__31_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__30_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__31 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__31_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__32;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dec"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__33 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__33_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__33_value),LEAN_SCALAR_PTR_LITERAL(133, 11, 154, 178, 201, 214, 183, 192)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__34 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__34_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toExprM___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__35;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__36 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__36_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__36_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__37 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__37_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toExprM___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__38;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__42 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__42_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__40 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__40_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__39 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__39_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__39_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__41_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__40_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__41 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__41_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toExprM___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__43;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toExprM___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__44;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__45 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__45_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__39_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__46_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__45_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__46 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__46_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toExprM___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__47;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "del"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__48 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__48_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__48_value),LEAN_SCALAR_PTR_LITERAL(59, 0, 194, 149, 61, 187, 104, 96)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__49 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__49_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toExprM___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__50;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExprM(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExprM(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExprM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExprM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExpr(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExpr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0___redArg(lean_object* v_t_1_, lean_object* v_k_2_){
_start:
{
if (lean_obj_tag(v_t_1_) == 0)
{
lean_object* v_k_3_; lean_object* v_v_4_; lean_object* v_l_5_; lean_object* v_r_6_; uint8_t v___x_7_; 
v_k_3_ = lean_ctor_get(v_t_1_, 1);
v_v_4_ = lean_ctor_get(v_t_1_, 2);
v_l_5_ = lean_ctor_get(v_t_1_, 3);
v_r_6_ = lean_ctor_get(v_t_1_, 4);
v___x_7_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2_, v_k_3_);
switch(v___x_7_)
{
case 0:
{
v_t_1_ = v_l_5_;
goto _start;
}
case 1:
{
lean_object* v___x_9_; 
lean_inc(v_v_4_);
v___x_9_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_9_, 0, v_v_4_);
return v___x_9_;
}
default: 
{
v_t_1_ = v_r_6_;
goto _start;
}
}
}
else
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0___redArg___boxed(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0___redArg(v_t_12_, v_k_13_);
lean_dec(v_k_13_);
lean_dec(v_t_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(lean_object* v_offset_15_, lean_object* v_m_16_, lean_object* v_fvarId_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0___redArg(v_m_16_, v_fvarId_17_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Expr_fvar___override(v_fvarId_17_);
return v___x_19_;
}
else
{
lean_object* v_val_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
lean_dec(v_fvarId_17_);
v_val_20_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_val_20_);
lean_dec_ref_known(v___x_18_, 1);
v___x_21_ = lean_nat_sub(v_offset_15_, v_val_20_);
lean_dec(v_val_20_);
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = lean_nat_sub(v___x_21_, v___x_22_);
lean_dec(v___x_21_);
v___x_24_ = l_Lean_Expr_bvar___override(v___x_23_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr___boxed(lean_object* v_offset_25_, lean_object* v_m_26_, lean_object* v_fvarId_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_offset_25_, v_m_26_, v_fvarId_27_);
lean_dec(v_m_26_);
lean_dec(v_offset_25_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0(lean_object* v_00_u03b4_29_, lean_object* v_t_30_, lean_object* v_k_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0___redArg(v_t_30_, v_k_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0___boxed(lean_object* v_00_u03b4_33_, lean_object* v_t_34_, lean_object* v_k_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0(v_00_u03b4_33_, v_t_34_, v_k_35_);
lean_dec(v_k_35_);
lean_dec(v_t_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(lean_object* v_m_37_, lean_object* v_o_38_, lean_object* v_e_39_){
_start:
{
switch(lean_obj_tag(v_e_39_))
{
case 1:
{
lean_object* v_fvarId_40_; lean_object* v___x_41_; 
v_fvarId_40_ = lean_ctor_get(v_e_39_, 0);
lean_inc(v_fvarId_40_);
lean_dec_ref_known(v_e_39_, 1);
v___x_41_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_o_38_, v_m_37_, v_fvarId_40_);
return v___x_41_;
}
case 5:
{
lean_object* v_fn_42_; lean_object* v_arg_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v_fn_42_ = lean_ctor_get(v_e_39_, 0);
lean_inc_ref(v_fn_42_);
v_arg_43_ = lean_ctor_get(v_e_39_, 1);
lean_inc_ref(v_arg_43_);
lean_dec_ref_known(v_e_39_, 2);
v___x_44_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_m_37_, v_o_38_, v_fn_42_);
v___x_45_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_m_37_, v_o_38_, v_arg_43_);
v___x_46_ = l_Lean_Expr_app___override(v___x_44_, v___x_45_);
return v___x_46_;
}
case 6:
{
lean_object* v_binderName_47_; lean_object* v_binderType_48_; lean_object* v_body_49_; uint8_t v_binderInfo_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_binderName_47_ = lean_ctor_get(v_e_39_, 0);
lean_inc(v_binderName_47_);
v_binderType_48_ = lean_ctor_get(v_e_39_, 1);
lean_inc_ref(v_binderType_48_);
v_body_49_ = lean_ctor_get(v_e_39_, 2);
lean_inc_ref(v_body_49_);
v_binderInfo_50_ = lean_ctor_get_uint8(v_e_39_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_39_, 3);
v___x_51_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_m_37_, v_o_38_, v_binderType_48_);
v___x_52_ = lean_unsigned_to_nat(1u);
v___x_53_ = lean_nat_add(v_o_38_, v___x_52_);
v___x_54_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_m_37_, v___x_53_, v_body_49_);
lean_dec(v___x_53_);
v___x_55_ = l_Lean_Expr_lam___override(v_binderName_47_, v___x_51_, v___x_54_, v_binderInfo_50_);
return v___x_55_;
}
case 7:
{
lean_object* v_binderName_56_; lean_object* v_binderType_57_; lean_object* v_body_58_; uint8_t v_binderInfo_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v_binderName_56_ = lean_ctor_get(v_e_39_, 0);
lean_inc(v_binderName_56_);
v_binderType_57_ = lean_ctor_get(v_e_39_, 1);
lean_inc_ref(v_binderType_57_);
v_body_58_ = lean_ctor_get(v_e_39_, 2);
lean_inc_ref(v_body_58_);
v_binderInfo_59_ = lean_ctor_get_uint8(v_e_39_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_39_, 3);
v___x_60_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_m_37_, v_o_38_, v_binderType_57_);
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_add(v_o_38_, v___x_61_);
v___x_63_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_m_37_, v___x_62_, v_body_58_);
lean_dec(v___x_62_);
v___x_64_ = l_Lean_Expr_forallE___override(v_binderName_56_, v___x_60_, v___x_63_, v_binderInfo_59_);
return v___x_64_;
}
case 8:
{
lean_object* v_declName_65_; lean_object* v_type_66_; lean_object* v_value_67_; lean_object* v_body_68_; uint8_t v_nondep_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_declName_65_ = lean_ctor_get(v_e_39_, 0);
lean_inc(v_declName_65_);
v_type_66_ = lean_ctor_get(v_e_39_, 1);
lean_inc_ref(v_type_66_);
v_value_67_ = lean_ctor_get(v_e_39_, 2);
lean_inc_ref(v_value_67_);
v_body_68_ = lean_ctor_get(v_e_39_, 3);
lean_inc_ref(v_body_68_);
v_nondep_69_ = lean_ctor_get_uint8(v_e_39_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_39_, 4);
v___x_70_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_m_37_, v_o_38_, v_type_66_);
v___x_71_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_m_37_, v_o_38_, v_value_67_);
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_add(v_o_38_, v___x_72_);
v___x_74_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_m_37_, v___x_73_, v_body_68_);
lean_dec(v___x_73_);
v___x_75_ = l_Lean_Expr_letE___override(v_declName_65_, v___x_70_, v___x_71_, v___x_74_, v_nondep_69_);
return v___x_75_;
}
case 10:
{
lean_object* v_data_76_; lean_object* v_expr_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_data_76_ = lean_ctor_get(v_e_39_, 0);
lean_inc(v_data_76_);
v_expr_77_ = lean_ctor_get(v_e_39_, 1);
lean_inc_ref(v_expr_77_);
lean_dec_ref_known(v_e_39_, 2);
v___x_78_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_m_37_, v_o_38_, v_expr_77_);
v___x_79_ = l_Lean_Expr_mdata___override(v_data_76_, v___x_78_);
return v___x_79_;
}
case 11:
{
lean_object* v_typeName_80_; lean_object* v_idx_81_; lean_object* v_struct_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_typeName_80_ = lean_ctor_get(v_e_39_, 0);
lean_inc(v_typeName_80_);
v_idx_81_ = lean_ctor_get(v_e_39_, 1);
lean_inc(v_idx_81_);
v_struct_82_ = lean_ctor_get(v_e_39_, 2);
lean_inc_ref(v_struct_82_);
lean_dec_ref_known(v_e_39_, 3);
v___x_83_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_m_37_, v_o_38_, v_struct_82_);
v___x_84_ = l_Lean_Expr_proj___override(v_typeName_80_, v_idx_81_, v___x_83_);
return v___x_84_;
}
default: 
{
return v_e_39_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go___boxed(lean_object* v_m_85_, lean_object* v_o_86_, lean_object* v_e_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_m_85_, v_o_86_, v_e_87_);
lean_dec(v_o_86_);
lean_dec(v_m_85_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27(lean_object* v_offset_89_, lean_object* v_m_90_, lean_object* v_e_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_m_90_, v_offset_89_, v_e_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27___boxed(lean_object* v_offset_93_, lean_object* v_m_94_, lean_object* v_e_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27(v_offset_93_, v_m_94_, v_e_95_);
lean_dec(v_m_94_);
lean_dec(v_offset_93_);
return v_res_96_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg(lean_object* v_params_98_, lean_object* v_offset_99_, lean_object* v_m_100_, lean_object* v_i_101_, lean_object* v_e_102_){
_start:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = lean_nat_dec_lt(v___x_103_, v_i_101_);
if (v___x_104_ == 0)
{
lean_dec(v_i_101_);
lean_dec(v_offset_99_);
return v_e_102_;
}
else
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v_param_108_; lean_object* v_binderName_109_; lean_object* v_type_110_; lean_object* v___x_111_; lean_object* v_domain_112_; uint8_t v___x_113_; lean_object* v___x_114_; 
v___x_105_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg___closed__0, &l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg___closed__0);
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_nat_sub(v_i_101_, v___x_106_);
lean_dec(v_i_101_);
v_param_108_ = lean_array_get_borrowed(v___x_105_, v_params_98_, v___x_107_);
v_binderName_109_ = lean_ctor_get(v_param_108_, 1);
v_type_110_ = lean_ctor_get(v_param_108_, 2);
v___x_111_ = lean_nat_sub(v_offset_99_, v___x_106_);
lean_dec(v_offset_99_);
lean_inc_ref(v_type_110_);
v_domain_112_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_m_100_, v___x_111_, v_type_110_);
v___x_113_ = 0;
lean_inc(v_binderName_109_);
v___x_114_ = l_Lean_Expr_lam___override(v_binderName_109_, v_domain_112_, v_e_102_, v___x_113_);
v_offset_99_ = v___x_111_;
v_i_101_ = v___x_107_;
v_e_102_ = v___x_114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg___boxed(lean_object* v_params_116_, lean_object* v_offset_117_, lean_object* v_m_118_, lean_object* v_i_119_, lean_object* v_e_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg(v_params_116_, v_offset_117_, v_m_118_, v_i_119_, v_e_120_);
lean_dec(v_m_118_);
lean_dec_ref(v_params_116_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(uint8_t v_pu_122_, lean_object* v_params_123_, lean_object* v_offset_124_, lean_object* v_m_125_, lean_object* v_i_126_, lean_object* v_e_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg(v_params_123_, v_offset_124_, v_m_125_, v_i_126_, v_e_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___boxed(lean_object* v_pu_129_, lean_object* v_params_130_, lean_object* v_offset_131_, lean_object* v_m_132_, lean_object* v_i_133_, lean_object* v_e_134_){
_start:
{
uint8_t v_pu_boxed_135_; lean_object* v_res_136_; 
v_pu_boxed_135_ = lean_unbox(v_pu_129_);
v_res_136_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(v_pu_boxed_135_, v_params_130_, v_offset_131_, v_m_132_, v_i_133_, v_e_134_);
lean_dec(v_m_132_);
lean_dec_ref(v_params_130_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM___redArg(lean_object* v_params_137_, lean_object* v_e_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_141_ = lean_array_get_size(v_params_137_);
lean_inc(v_a_139_);
v___x_142_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg(v_params_137_, v_a_139_, v_a_140_, v___x_141_, v_e_138_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v_a_140_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM___redArg___boxed(lean_object* v_params_144_, lean_object* v_e_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Compiler_LCNF_ToExpr_mkLambdaM___redArg(v_params_144_, v_e_145_, v_a_146_, v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_params_144_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM(uint8_t v_pu_149_, lean_object* v_params_150_, lean_object* v_e_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_array_get_size(v_params_150_);
lean_inc(v_a_152_);
v___x_155_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg(v_params_150_, v_a_152_, v_a_153_, v___x_154_, v_e_151_);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v_a_153_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM___boxed(lean_object* v_pu_157_, lean_object* v_params_158_, lean_object* v_e_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
uint8_t v_pu_boxed_162_; lean_object* v_res_163_; 
v_pu_boxed_162_ = lean_unbox(v_pu_157_);
v_res_163_ = l_Lean_Compiler_LCNF_ToExpr_mkLambdaM(v_pu_boxed_162_, v_params_158_, v_e_159_, v_a_160_, v_a_161_);
lean_dec(v_a_160_);
lean_dec_ref(v_params_158_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExprM(lean_object* v_fvarId_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_165_, v_a_166_, v_fvarId_164_);
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v_a_166_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExprM___boxed(lean_object* v_fvarId_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExprM(v_fvarId_169_, v_a_170_, v_a_171_);
lean_dec(v_a_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_abstractM(lean_object* v_e_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_175_, v_a_174_, v_e_173_);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v_a_175_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_abstractM___boxed(lean_object* v_e_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_Compiler_LCNF_ToExpr_abstractM(v_e_178_, v_a_179_, v_a_180_);
lean_dec(v_a_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar___redArg(lean_object* v_fvarId_182_, lean_object* v_k_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
lean_inc(v_a_184_);
v___x_186_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_182_, v_a_184_, v_a_185_);
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_add(v_a_184_, v___x_187_);
v___x_189_ = lean_apply_2(v_k_183_, v___x_188_, v___x_186_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar___redArg___boxed(lean_object* v_fvarId_190_, lean_object* v_k_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Compiler_LCNF_ToExpr_withFVar___redArg(v_fvarId_190_, v_k_191_, v_a_192_, v_a_193_);
lean_dec(v_a_192_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar(lean_object* v_00_u03b1_195_, lean_object* v_fvarId_196_, lean_object* v_k_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
lean_inc(v_a_198_);
v___x_200_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_196_, v_a_198_, v_a_199_);
v___x_201_ = lean_unsigned_to_nat(1u);
v___x_202_ = lean_nat_add(v_a_198_, v___x_201_);
v___x_203_ = lean_apply_2(v_k_197_, v___x_202_, v___x_200_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar___boxed(lean_object* v_00_u03b1_204_, lean_object* v_fvarId_205_, lean_object* v_k_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Compiler_LCNF_ToExpr_withFVar(v_00_u03b1_204_, v_fvarId_205_, v_k_206_, v_a_207_, v_a_208_);
lean_dec(v_a_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(lean_object* v_params_210_, lean_object* v_k_211_, lean_object* v_i_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = lean_array_get_size(v_params_210_);
v___x_216_ = lean_nat_dec_lt(v_i_212_, v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; 
lean_dec(v_i_212_);
v___x_217_ = lean_apply_2(v_k_211_, v_a_213_, v_a_214_);
return v___x_217_;
}
else
{
lean_object* v___x_218_; lean_object* v_fvarId_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_218_ = lean_array_fget_borrowed(v_params_210_, v_i_212_);
v_fvarId_219_ = lean_ctor_get(v___x_218_, 0);
v___x_220_ = lean_unsigned_to_nat(1u);
v___x_221_ = lean_nat_add(v_i_212_, v___x_220_);
lean_dec(v_i_212_);
lean_inc(v_a_213_);
lean_inc(v_fvarId_219_);
v___x_222_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_219_, v_a_213_, v_a_214_);
v___x_223_ = lean_nat_add(v_a_213_, v___x_220_);
lean_dec(v_a_213_);
v_i_212_ = v___x_221_;
v_a_213_ = v___x_223_;
v_a_214_ = v___x_222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg___boxed(lean_object* v_params_225_, lean_object* v_k_226_, lean_object* v_i_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(v_params_225_, v_k_226_, v_i_227_, v_a_228_, v_a_229_);
lean_dec_ref(v_params_225_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go(uint8_t v_pu_231_, lean_object* v_00_u03b1_232_, lean_object* v_params_233_, lean_object* v_k_234_, lean_object* v_i_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v___x_238_; 
lean_inc(v_a_236_);
v___x_238_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(v_params_233_, v_k_234_, v_i_235_, v_a_236_, v_a_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___boxed(lean_object* v_pu_239_, lean_object* v_00_u03b1_240_, lean_object* v_params_241_, lean_object* v_k_242_, lean_object* v_i_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
uint8_t v_pu_boxed_246_; lean_object* v_res_247_; 
v_pu_boxed_246_ = lean_unbox(v_pu_239_);
v_res_247_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go(v_pu_boxed_246_, v_00_u03b1_240_, v_params_241_, v_k_242_, v_i_243_, v_a_244_, v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_params_241_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams___redArg(lean_object* v_params_248_, lean_object* v_k_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_250_);
v___x_253_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(v_params_248_, v_k_249_, v___x_252_, v_a_250_, v_a_251_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams___redArg___boxed(lean_object* v_params_254_, lean_object* v_k_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Compiler_LCNF_ToExpr_withParams___redArg(v_params_254_, v_k_255_, v_a_256_, v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_params_254_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams(uint8_t v_pu_259_, lean_object* v_00_u03b1_260_, lean_object* v_params_261_, lean_object* v_k_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_263_);
v___x_266_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(v_params_261_, v_k_262_, v___x_265_, v_a_263_, v_a_264_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams___boxed(lean_object* v_pu_267_, lean_object* v_00_u03b1_268_, lean_object* v_params_269_, lean_object* v_k_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
uint8_t v_pu_boxed_273_; lean_object* v_res_274_; 
v_pu_boxed_273_ = lean_unbox(v_pu_267_);
v_res_274_ = l_Lean_Compiler_LCNF_ToExpr_withParams(v_pu_boxed_273_, v_00_u03b1_268_, v_params_269_, v_k_270_, v_a_271_, v_a_272_);
lean_dec(v_a_271_);
lean_dec_ref(v_params_269_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run___redArg(lean_object* v_x_275_, lean_object* v_offset_276_, lean_object* v_levelMap_277_){
_start:
{
lean_object* v___x_278_; lean_object* v_fst_279_; 
v___x_278_ = lean_apply_2(v_x_275_, v_offset_276_, v_levelMap_277_);
v_fst_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_fst_279_);
lean_dec_ref(v___x_278_);
return v_fst_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run(lean_object* v_00_u03b1_280_, lean_object* v_x_281_, lean_object* v_offset_282_, lean_object* v_levelMap_283_){
_start:
{
lean_object* v___x_284_; lean_object* v_fst_285_; 
v___x_284_ = lean_apply_2(v_x_281_, v_offset_282_, v_levelMap_283_);
v_fst_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_fst_285_);
lean_dec_ref(v___x_284_);
return v_fst_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___lam__0(lean_object* v_x1_286_, lean_object* v_x2_287_){
_start:
{
if (lean_obj_tag(v_x1_286_) == 0)
{
lean_object* v_size_288_; lean_object* v___x_289_; 
v_size_288_ = lean_ctor_get(v_x1_286_, 0);
lean_inc(v_size_288_);
v___x_289_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_x2_287_, v_size_288_, v_x1_286_);
return v___x_289_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_x2_287_, v___x_290_, v_x1_286_);
return v___x_291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg(lean_object* v_x_312_, lean_object* v_xs_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___y_318_; lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_314_ = lean_box(1);
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = lean_array_get_size(v_xs_313_);
v___x_321_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__9));
v___x_322_ = lean_nat_dec_lt(v___x_315_, v___x_316_);
if (v___x_322_ == 0)
{
lean_dec_ref(v_xs_313_);
v___y_318_ = v___x_314_;
goto v___jp_317_;
}
else
{
lean_object* v___f_323_; size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; 
v___f_323_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10));
v___x_324_ = ((size_t)0ULL);
v___x_325_ = lean_usize_of_nat(v___x_316_);
v___x_326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_321_, v___f_323_, v_xs_313_, v___x_324_, v___x_325_, v___x_314_);
v___y_318_ = v___x_326_;
goto v___jp_317_;
}
v___jp_317_:
{
lean_object* v___x_319_; lean_object* v_fst_320_; 
v___x_319_ = lean_apply_2(v_x_312_, v___x_316_, v___y_318_);
v_fst_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_fst_320_);
lean_dec_ref(v___x_319_);
return v_fst_320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27(lean_object* v_00_u03b1_327_, lean_object* v_x_328_, lean_object* v_xs_329_){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___y_334_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_330_ = lean_box(1);
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = lean_array_get_size(v_xs_329_);
v___x_337_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__9));
v___x_338_ = lean_nat_dec_lt(v___x_331_, v___x_332_);
if (v___x_338_ == 0)
{
lean_dec_ref(v_xs_329_);
v___y_334_ = v___x_330_;
goto v___jp_333_;
}
else
{
lean_object* v___f_339_; size_t v___x_340_; size_t v___x_341_; lean_object* v___x_342_; 
v___f_339_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10));
v___x_340_ = ((size_t)0ULL);
v___x_341_ = lean_usize_of_nat(v___x_332_);
v___x_342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_337_, v___f_339_, v_xs_329_, v___x_340_, v___x_341_, v___x_330_);
v___y_334_ = v___x_342_;
goto v___jp_333_;
}
v___jp_333_:
{
lean_object* v___x_335_; lean_object* v_fst_336_; 
v___x_335_ = lean_apply_2(v_x_328_, v___x_332_, v___y_334_);
v_fst_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_fst_336_);
lean_dec_ref(v___x_335_);
return v_fst_336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(lean_object* v_arg_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = l_Lean_Compiler_LCNF_Arg_toExpr___redArg(v_arg_343_);
v___x_347_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_345_, v_a_344_, v___x_346_);
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v_a_345_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg___boxed(lean_object* v_arg_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_arg_349_, v_a_350_, v_a_351_);
lean_dec(v_a_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM(uint8_t v_pu_353_, lean_object* v_arg_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_arg_354_, v_a_355_, v_a_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___boxed(lean_object* v_pu_358_, lean_object* v_arg_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
uint8_t v_pu_boxed_362_; lean_object* v_res_363_; 
v_pu_boxed_362_ = lean_unbox(v_pu_358_);
v_res_363_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM(v_pu_boxed_362_, v_arg_359_, v_a_360_, v_a_361_);
lean_dec(v_a_360_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(size_t v_sz_364_, size_t v_i_365_, lean_object* v_bs_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
uint8_t v___x_369_; 
v___x_369_ = lean_usize_dec_lt(v_i_365_, v_sz_364_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v_bs_366_);
lean_ctor_set(v___x_370_, 1, v___y_368_);
return v___x_370_;
}
else
{
lean_object* v_v_371_; lean_object* v___x_372_; lean_object* v_fst_373_; lean_object* v_snd_374_; lean_object* v___x_375_; lean_object* v_bs_x27_376_; size_t v___x_377_; size_t v___x_378_; lean_object* v___x_379_; 
v_v_371_ = lean_array_uget_borrowed(v_bs_366_, v_i_365_);
lean_inc(v_v_371_);
v___x_372_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_v_371_, v___y_367_, v___y_368_);
v_fst_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_fst_373_);
v_snd_374_ = lean_ctor_get(v___x_372_, 1);
lean_inc(v_snd_374_);
lean_dec_ref(v___x_372_);
v___x_375_ = lean_unsigned_to_nat(0u);
v_bs_x27_376_ = lean_array_uset(v_bs_366_, v_i_365_, v___x_375_);
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_add(v_i_365_, v___x_377_);
v___x_379_ = lean_array_uset(v_bs_x27_376_, v_i_365_, v_fst_373_);
v_i_365_ = v___x_378_;
v_bs_366_ = v___x_379_;
v___y_368_ = v_snd_374_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg___boxed(lean_object* v_sz_381_, lean_object* v_i_382_, lean_object* v_bs_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
size_t v_sz_boxed_386_; size_t v_i_boxed_387_; lean_object* v_res_388_; 
v_sz_boxed_386_ = lean_unbox_usize(v_sz_381_);
lean_dec(v_sz_381_);
v_i_boxed_387_ = lean_unbox_usize(v_i_382_);
lean_dec(v_i_382_);
v_res_388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_boxed_386_, v_i_boxed_387_, v_bs_383_, v___y_384_, v___y_385_);
lean_dec(v___y_384_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(uint8_t v_pu_389_, size_t v_sz_390_, size_t v_i_391_, lean_object* v_bs_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
uint8_t v___x_395_; 
v___x_395_ = lean_usize_dec_lt(v_i_391_, v_sz_390_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; 
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v_bs_392_);
lean_ctor_set(v___x_396_, 1, v___y_394_);
return v___x_396_;
}
else
{
lean_object* v_v_397_; lean_object* v___x_398_; lean_object* v_bs_x27_399_; lean_object* v_fst_401_; lean_object* v_snd_402_; 
v_v_397_ = lean_array_uget(v_bs_392_, v_i_391_);
v___x_398_ = lean_unsigned_to_nat(0u);
v_bs_x27_399_ = lean_array_uset(v_bs_392_, v_i_391_, v___x_398_);
switch(lean_obj_tag(v_v_397_))
{
case 0:
{
lean_object* v_ctorName_407_; lean_object* v_params_408_; lean_object* v_code_409_; lean_object* v___x_410_; lean_object* v_fst_411_; lean_object* v_snd_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_ctorName_407_ = lean_ctor_get(v_v_397_, 0);
lean_inc(v_ctorName_407_);
v_params_408_ = lean_ctor_get(v_v_397_, 1);
lean_inc_ref(v_params_408_);
v_code_409_ = lean_ctor_get(v_v_397_, 2);
lean_inc_ref(v_code_409_);
lean_dec_ref_known(v_v_397_, 3);
lean_inc(v___y_393_);
v___x_410_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_389_, v_code_409_, v_params_408_, v_params_408_, v___x_398_, v___y_393_, v___y_394_);
lean_dec_ref(v_params_408_);
v_fst_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_fst_411_);
v_snd_412_ = lean_ctor_get(v___x_410_, 1);
lean_inc(v_snd_412_);
lean_dec_ref(v___x_410_);
v___x_413_ = lean_box(0);
v___x_414_ = l_Lean_mkConst(v_ctorName_407_, v___x_413_);
v___x_415_ = l_Lean_Expr_app___override(v___x_414_, v_fst_411_);
v_fst_401_ = v___x_415_;
v_snd_402_ = v_snd_412_;
goto v___jp_400_;
}
case 1:
{
lean_object* v_info_416_; lean_object* v_code_417_; lean_object* v___x_418_; lean_object* v_fst_419_; lean_object* v_snd_420_; lean_object* v_name_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_info_416_ = lean_ctor_get(v_v_397_, 0);
lean_inc_ref(v_info_416_);
v_code_417_ = lean_ctor_get(v_v_397_, 1);
lean_inc_ref(v_code_417_);
lean_dec_ref_known(v_v_397_, 2);
v___x_418_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_389_, v_code_417_, v___y_393_, v___y_394_);
v_fst_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_fst_419_);
v_snd_420_ = lean_ctor_get(v___x_418_, 1);
lean_inc(v_snd_420_);
lean_dec_ref(v___x_418_);
v_name_421_ = lean_ctor_get(v_info_416_, 0);
lean_inc(v_name_421_);
lean_dec_ref(v_info_416_);
v___x_422_ = lean_box(0);
v___x_423_ = l_Lean_mkConst(v_name_421_, v___x_422_);
v___x_424_ = l_Lean_Expr_app___override(v___x_423_, v_fst_419_);
v_fst_401_ = v___x_424_;
v_snd_402_ = v_snd_420_;
goto v___jp_400_;
}
default: 
{
lean_object* v_code_425_; lean_object* v___x_426_; lean_object* v_fst_427_; lean_object* v_snd_428_; 
v_code_425_ = lean_ctor_get(v_v_397_, 0);
lean_inc_ref(v_code_425_);
lean_dec_ref_known(v_v_397_, 1);
v___x_426_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_389_, v_code_425_, v___y_393_, v___y_394_);
v_fst_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_fst_427_);
v_snd_428_ = lean_ctor_get(v___x_426_, 1);
lean_inc(v_snd_428_);
lean_dec_ref(v___x_426_);
v_fst_401_ = v_fst_427_;
v_snd_402_ = v_snd_428_;
goto v___jp_400_;
}
}
v___jp_400_:
{
size_t v___x_403_; size_t v___x_404_; lean_object* v___x_405_; 
v___x_403_ = ((size_t)1ULL);
v___x_404_ = lean_usize_add(v_i_391_, v___x_403_);
v___x_405_ = lean_array_uset(v_bs_x27_399_, v_i_391_, v_fst_401_);
v_i_391_ = v___x_404_;
v_bs_392_ = v___x_405_;
v___y_394_ = v_snd_402_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__2(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = lean_box(0);
v___x_433_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__1));
v___x_434_ = l_Lean_mkConst(v___x_433_, v___x_432_);
return v___x_434_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__5(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_box(0);
v___x_439_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__4));
v___x_440_ = l_Lean_mkConst(v___x_439_, v___x_438_);
return v___x_440_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__8(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_box(0);
v___x_445_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__7));
v___x_446_ = l_Lean_mkConst(v___x_445_, v___x_444_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = lean_box(0);
v___x_454_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__12));
v___x_455_ = l_Lean_mkConst(v___x_454_, v___x_453_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__16(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_box(0);
v___x_460_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__15));
v___x_461_ = l_Lean_mkConst(v___x_460_, v___x_459_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__19(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_box(0);
v___x_466_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__18));
v___x_467_ = l_Lean_mkConst(v___x_466_, v___x_465_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__22(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_box(0);
v___x_472_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__21));
v___x_473_ = l_Lean_mkConst(v___x_472_, v___x_471_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__25(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = lean_box(0);
v___x_478_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__24));
v___x_479_ = l_Lean_mkConst(v___x_478_, v___x_477_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = lean_box(0);
v___x_486_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__28));
v___x_487_ = l_Lean_mkConst(v___x_486_, v___x_485_);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_box(0);
v___x_493_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__31));
v___x_494_ = l_Lean_mkConst(v___x_493_, v___x_492_);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__35(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = lean_box(0);
v___x_499_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__34));
v___x_500_ = l_Lean_mkConst(v___x_499_, v___x_498_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_504_ = lean_box(0);
v___x_505_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__37));
v___x_506_ = l_Lean_mkConst(v___x_505_, v___x_504_);
return v___x_506_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__43(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__42));
v___x_516_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__41));
v___x_517_ = l_Lean_mkConst(v___x_516_, v___x_515_);
return v___x_517_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__44(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_518_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__38, &l_Lean_Compiler_LCNF_Code_toExprM___closed__38_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38);
v___x_519_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__43, &l_Lean_Compiler_LCNF_Code_toExprM___closed__43_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__43);
v___x_520_ = l_Lean_Expr_app___override(v___x_519_, v___x_518_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__47(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__42));
v___x_526_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__46));
v___x_527_ = l_Lean_mkConst(v___x_526_, v___x_525_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__50(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = lean_box(0);
v___x_532_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__49));
v___x_533_ = l_Lean_mkConst(v___x_532_, v___x_531_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExprM(uint8_t v_pu_534_, lean_object* v_code_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
switch(lean_obj_tag(v_code_535_))
{
case 0:
{
lean_object* v_decl_538_; lean_object* v_k_539_; lean_object* v_fvarId_540_; lean_object* v_binderName_541_; lean_object* v_type_542_; lean_object* v_value_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v_fst_551_; lean_object* v_snd_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_561_; 
v_decl_538_ = lean_ctor_get(v_code_535_, 0);
lean_inc_ref(v_decl_538_);
v_k_539_ = lean_ctor_get(v_code_535_, 1);
lean_inc_ref(v_k_539_);
lean_dec_ref_known(v_code_535_, 2);
v_fvarId_540_ = lean_ctor_get(v_decl_538_, 0);
lean_inc(v_fvarId_540_);
v_binderName_541_ = lean_ctor_get(v_decl_538_, 1);
lean_inc(v_binderName_541_);
v_type_542_ = lean_ctor_get(v_decl_538_, 2);
lean_inc_ref(v_type_542_);
v_value_543_ = lean_ctor_get(v_decl_538_, 3);
lean_inc(v_value_543_);
lean_dec_ref(v_decl_538_);
v___x_544_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_537_, v_a_536_, v_type_542_);
v___x_545_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v_pu_534_, v_value_543_);
v___x_546_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_537_, v_a_536_, v___x_545_);
lean_inc(v_a_536_);
v___x_547_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_540_, v_a_536_, v_a_537_);
v___x_548_ = lean_unsigned_to_nat(1u);
v___x_549_ = lean_nat_add(v_a_536_, v___x_548_);
v___x_550_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_534_, v_k_539_, v___x_549_, v___x_547_);
lean_dec(v___x_549_);
v_fst_551_ = lean_ctor_get(v___x_550_, 0);
v_snd_552_ = lean_ctor_get(v___x_550_, 1);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_561_ == 0)
{
v___x_554_ = v___x_550_;
v_isShared_555_ = v_isSharedCheck_561_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_snd_552_);
lean_inc(v_fst_551_);
lean_dec(v___x_550_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_561_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_556_ = 1;
v___x_557_ = l_Lean_Expr_letE___override(v_binderName_541_, v___x_544_, v___x_546_, v_fst_551_, v___x_556_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_557_);
v___x_559_ = v___x_554_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_snd_552_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
case 3:
{
lean_object* v_fvarId_562_; lean_object* v_args_563_; lean_object* v___x_564_; size_t v_sz_565_; size_t v___x_566_; lean_object* v___x_567_; lean_object* v_fst_568_; lean_object* v_snd_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_577_; 
v_fvarId_562_ = lean_ctor_get(v_code_535_, 0);
lean_inc(v_fvarId_562_);
v_args_563_ = lean_ctor_get(v_code_535_, 1);
lean_inc_ref(v_args_563_);
lean_dec_ref_known(v_code_535_, 2);
v___x_564_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_536_, v_a_537_, v_fvarId_562_);
v_sz_565_ = lean_array_size(v_args_563_);
v___x_566_ = ((size_t)0ULL);
v___x_567_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_565_, v___x_566_, v_args_563_, v_a_536_, v_a_537_);
v_fst_568_ = lean_ctor_get(v___x_567_, 0);
v_snd_569_ = lean_ctor_get(v___x_567_, 1);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_577_ == 0)
{
v___x_571_ = v___x_567_;
v_isShared_572_ = v_isSharedCheck_577_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_snd_569_);
lean_inc(v_fst_568_);
lean_dec(v___x_567_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_577_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_573_ = l_Lean_mkAppN(v___x_564_, v_fst_568_);
lean_dec(v_fst_568_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_573_);
v___x_575_ = v___x_571_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_snd_569_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
case 4:
{
lean_object* v_cases_578_; lean_object* v_discr_579_; lean_object* v_alts_580_; size_t v_sz_581_; size_t v___x_582_; lean_object* v___x_583_; lean_object* v_fst_584_; lean_object* v_snd_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_599_; 
v_cases_578_ = lean_ctor_get(v_code_535_, 0);
lean_inc_ref(v_cases_578_);
lean_dec_ref_known(v_code_535_, 1);
v_discr_579_ = lean_ctor_get(v_cases_578_, 2);
lean_inc(v_discr_579_);
v_alts_580_ = lean_ctor_get(v_cases_578_, 3);
lean_inc_ref(v_alts_580_);
lean_dec_ref(v_cases_578_);
v_sz_581_ = lean_array_size(v_alts_580_);
v___x_582_ = ((size_t)0ULL);
v___x_583_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(v_pu_534_, v_sz_581_, v___x_582_, v_alts_580_, v_a_536_, v_a_537_);
v_fst_584_ = lean_ctor_get(v___x_583_, 0);
v_snd_585_ = lean_ctor_get(v___x_583_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_599_ == 0)
{
v___x_587_ = v___x_583_;
v_isShared_588_ = v_isSharedCheck_599_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_snd_585_);
lean_inc(v_fst_584_);
lean_dec(v___x_583_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_599_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_589_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_536_, v_snd_585_, v_discr_579_);
v___x_590_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__2, &l_Lean_Compiler_LCNF_Code_toExprM___closed__2_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__2);
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = lean_mk_empty_array_with_capacity(v___x_591_);
v___x_593_ = lean_array_push(v___x_592_, v___x_589_);
v___x_594_ = l_Array_append___redArg(v___x_593_, v_fst_584_);
lean_dec(v_fst_584_);
v___x_595_ = l_Lean_mkAppN(v___x_590_, v___x_594_);
lean_dec_ref(v___x_594_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_595_);
v___x_597_ = v___x_587_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_snd_585_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
case 5:
{
lean_object* v_fvarId_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_fvarId_600_ = lean_ctor_get(v_code_535_, 0);
lean_inc(v_fvarId_600_);
lean_dec_ref_known(v_code_535_, 1);
v___x_601_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_536_, v_a_537_, v_fvarId_600_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v_a_537_);
return v___x_602_;
}
case 6:
{
lean_object* v_type_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_type_603_ = lean_ctor_get(v_code_535_, 0);
lean_inc_ref(v_type_603_);
lean_dec_ref_known(v_code_535_, 1);
v___x_604_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_537_, v_a_536_, v_type_603_);
v___x_605_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__5, &l_Lean_Compiler_LCNF_Code_toExprM___closed__5_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__5);
v___x_606_ = l_Lean_Expr_app___override(v___x_605_, v___x_604_);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v_a_537_);
return v___x_607_;
}
case 7:
{
lean_object* v_fvarId_608_; lean_object* v_i_609_; lean_object* v_y_610_; lean_object* v_k_611_; lean_object* v___x_612_; lean_object* v_fst_613_; lean_object* v_snd_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v_fst_620_; lean_object* v_snd_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_635_; 
v_fvarId_608_ = lean_ctor_get(v_code_535_, 0);
lean_inc_n(v_fvarId_608_, 2);
v_i_609_ = lean_ctor_get(v_code_535_, 1);
lean_inc(v_i_609_);
v_y_610_ = lean_ctor_get(v_code_535_, 2);
lean_inc(v_y_610_);
v_k_611_ = lean_ctor_get(v_code_535_, 3);
lean_inc_ref(v_k_611_);
lean_dec_ref_known(v_code_535_, 4);
v___x_612_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_y_610_, v_a_536_, v_a_537_);
v_fst_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_fst_613_);
v_snd_614_ = lean_ctor_get(v___x_612_, 1);
lean_inc(v_snd_614_);
lean_dec_ref(v___x_612_);
v___x_615_ = l_Lean_Expr_fvar___override(v_fvarId_608_);
lean_inc(v_a_536_);
v___x_616_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_608_, v_a_536_, v_snd_614_);
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = lean_nat_add(v_a_536_, v___x_617_);
v___x_619_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_534_, v_k_611_, v___x_618_, v___x_616_);
lean_dec(v___x_618_);
v_fst_620_ = lean_ctor_get(v___x_619_, 0);
v_snd_621_ = lean_ctor_get(v___x_619_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_635_ == 0)
{
v___x_623_ = v___x_619_;
v_isShared_624_ = v_isSharedCheck_635_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_snd_621_);
lean_inc(v_fst_620_);
lean_dec(v___x_619_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_635_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_625_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__8, &l_Lean_Compiler_LCNF_Code_toExprM___closed__8_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__8);
v___x_626_ = l_Lean_mkNatLit(v_i_609_);
v___x_627_ = l_Lean_mkApp3(v___x_625_, v___x_615_, v___x_626_, v_fst_613_);
v___x_628_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_629_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_630_ = 1;
v___x_631_ = l_Lean_Expr_letE___override(v___x_628_, v___x_629_, v___x_627_, v_fst_620_, v___x_630_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_631_);
v___x_633_ = v___x_623_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_snd_621_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
case 8:
{
lean_object* v_fvarId_636_; lean_object* v_i_637_; lean_object* v_y_638_; lean_object* v_k_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v_fst_645_; lean_object* v_snd_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_661_; 
v_fvarId_636_ = lean_ctor_get(v_code_535_, 0);
lean_inc_n(v_fvarId_636_, 2);
v_i_637_ = lean_ctor_get(v_code_535_, 1);
lean_inc(v_i_637_);
v_y_638_ = lean_ctor_get(v_code_535_, 2);
lean_inc(v_y_638_);
v_k_639_ = lean_ctor_get(v_code_535_, 3);
lean_inc_ref(v_k_639_);
lean_dec_ref_known(v_code_535_, 4);
v___x_640_ = l_Lean_Expr_fvar___override(v_fvarId_636_);
lean_inc(v_a_536_);
v___x_641_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_636_, v_a_536_, v_a_537_);
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = lean_nat_add(v_a_536_, v___x_642_);
v___x_644_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_534_, v_k_639_, v___x_643_, v___x_641_);
lean_dec(v___x_643_);
v_fst_645_ = lean_ctor_get(v___x_644_, 0);
v_snd_646_ = lean_ctor_get(v___x_644_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_661_ == 0)
{
v___x_648_ = v___x_644_;
v_isShared_649_ = v_isSharedCheck_661_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_snd_646_);
lean_inc(v_fst_645_);
lean_dec(v___x_644_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_661_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v_value_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_650_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__16, &l_Lean_Compiler_LCNF_Code_toExprM___closed__16_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__16);
v___x_651_ = l_Lean_mkNatLit(v_i_637_);
v___x_652_ = l_Lean_Expr_fvar___override(v_y_638_);
v_value_653_ = l_Lean_mkApp3(v___x_650_, v___x_640_, v___x_651_, v___x_652_);
v___x_654_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_655_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_656_ = 1;
v___x_657_ = l_Lean_Expr_letE___override(v___x_654_, v___x_655_, v_value_653_, v_fst_645_, v___x_656_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_657_);
v___x_659_ = v___x_648_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_snd_646_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
case 9:
{
lean_object* v_fvarId_662_; lean_object* v_i_663_; lean_object* v_offset_664_; lean_object* v_y_665_; lean_object* v_ty_666_; lean_object* v_k_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v_fst_673_; lean_object* v_snd_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_690_; 
v_fvarId_662_ = lean_ctor_get(v_code_535_, 0);
lean_inc_n(v_fvarId_662_, 2);
v_i_663_ = lean_ctor_get(v_code_535_, 1);
lean_inc(v_i_663_);
v_offset_664_ = lean_ctor_get(v_code_535_, 2);
lean_inc(v_offset_664_);
v_y_665_ = lean_ctor_get(v_code_535_, 3);
lean_inc(v_y_665_);
v_ty_666_ = lean_ctor_get(v_code_535_, 4);
lean_inc_ref(v_ty_666_);
v_k_667_ = lean_ctor_get(v_code_535_, 5);
lean_inc_ref(v_k_667_);
lean_dec_ref_known(v_code_535_, 6);
v___x_668_ = l_Lean_Expr_fvar___override(v_fvarId_662_);
lean_inc(v_a_536_);
v___x_669_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_662_, v_a_536_, v_a_537_);
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_nat_add(v_a_536_, v___x_670_);
v___x_672_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_534_, v_k_667_, v___x_671_, v___x_669_);
lean_dec(v___x_671_);
v_fst_673_ = lean_ctor_get(v___x_672_, 0);
v_snd_674_ = lean_ctor_get(v___x_672_, 1);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_690_ == 0)
{
v___x_676_ = v___x_672_;
v_isShared_677_ = v_isSharedCheck_690_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_snd_674_);
lean_inc(v_fst_673_);
lean_dec(v___x_672_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_690_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v_value_682_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_678_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__19, &l_Lean_Compiler_LCNF_Code_toExprM___closed__19_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__19);
v___x_679_ = l_Lean_mkNatLit(v_i_663_);
v___x_680_ = l_Lean_mkNatLit(v_offset_664_);
v___x_681_ = l_Lean_Expr_fvar___override(v_y_665_);
v_value_682_ = l_Lean_mkApp5(v___x_678_, v___x_668_, v___x_679_, v___x_680_, v___x_681_, v_ty_666_);
v___x_683_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_684_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_685_ = 1;
v___x_686_ = l_Lean_Expr_letE___override(v___x_683_, v___x_684_, v_value_682_, v_fst_673_, v___x_685_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_686_);
v___x_688_ = v___x_676_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_snd_674_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
case 10:
{
lean_object* v_fvarId_691_; lean_object* v_cidx_692_; lean_object* v_k_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v_fst_698_; lean_object* v_snd_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_714_; 
v_fvarId_691_ = lean_ctor_get(v_code_535_, 0);
lean_inc_n(v_fvarId_691_, 2);
v_cidx_692_ = lean_ctor_get(v_code_535_, 1);
lean_inc(v_cidx_692_);
v_k_693_ = lean_ctor_get(v_code_535_, 2);
lean_inc_ref(v_k_693_);
lean_dec_ref_known(v_code_535_, 3);
lean_inc(v_a_536_);
v___x_694_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_691_, v_a_536_, v_a_537_);
v___x_695_ = lean_unsigned_to_nat(1u);
v___x_696_ = lean_nat_add(v_a_536_, v___x_695_);
v___x_697_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_534_, v_k_693_, v___x_696_, v___x_694_);
lean_dec(v___x_696_);
v_fst_698_ = lean_ctor_get(v___x_697_, 0);
v_snd_699_ = lean_ctor_get(v___x_697_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_714_ == 0)
{
v___x_701_ = v___x_697_;
v_isShared_702_ = v_isSharedCheck_714_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_snd_699_);
lean_inc(v_fst_698_);
lean_dec(v___x_697_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_714_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_703_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__22, &l_Lean_Compiler_LCNF_Code_toExprM___closed__22_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__22);
v___x_704_ = l_Lean_Expr_fvar___override(v_fvarId_691_);
v___x_705_ = l_Lean_mkNatLit(v_cidx_692_);
v___x_706_ = l_Lean_mkAppB(v___x_703_, v___x_704_, v___x_705_);
v___x_707_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_708_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_709_ = 1;
v___x_710_ = l_Lean_Expr_letE___override(v___x_707_, v___x_708_, v___x_706_, v_fst_698_, v___x_709_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_710_);
v___x_712_ = v___x_701_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_snd_699_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
case 11:
{
lean_object* v_fvarId_715_; lean_object* v_n_716_; uint8_t v_check_717_; uint8_t v_persistent_718_; lean_object* v_k_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_745_; 
v_fvarId_715_ = lean_ctor_get(v_code_535_, 0);
lean_inc_n(v_fvarId_715_, 2);
v_n_716_ = lean_ctor_get(v_code_535_, 1);
lean_inc(v_n_716_);
v_check_717_ = lean_ctor_get_uint8(v_code_535_, sizeof(void*)*3);
v_persistent_718_ = lean_ctor_get_uint8(v_code_535_, sizeof(void*)*3 + 1);
v_k_719_ = lean_ctor_get(v_code_535_, 2);
lean_inc_ref(v_k_719_);
lean_dec_ref_known(v_code_535_, 3);
v___x_720_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__25, &l_Lean_Compiler_LCNF_Code_toExprM___closed__25_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__25);
v___x_721_ = l_Lean_Expr_fvar___override(v_fvarId_715_);
v___x_722_ = l_Lean_mkNatLit(v_n_716_);
if (v_check_717_ == 0)
{
lean_object* v___x_748_; 
v___x_748_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_745_ = v___x_748_;
goto v___jp_744_;
}
else
{
lean_object* v___x_749_; 
v___x_749_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_745_ = v___x_749_;
goto v___jp_744_;
}
v___jp_723_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v_fst_730_; lean_object* v_snd_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_743_; 
lean_inc(v_a_536_);
v___x_726_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_715_, v_a_536_, v_a_537_);
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_nat_add(v_a_536_, v___x_727_);
v___x_729_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_534_, v_k_719_, v___x_728_, v___x_726_);
lean_dec(v___x_728_);
v_fst_730_ = lean_ctor_get(v___x_729_, 0);
v_snd_731_ = lean_ctor_get(v___x_729_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_743_ == 0)
{
v___x_733_ = v___x_729_;
v_isShared_734_ = v_isSharedCheck_743_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_snd_731_);
lean_inc(v_fst_730_);
lean_dec(v___x_729_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_743_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v_value_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
lean_inc_ref(v___y_725_);
lean_inc_ref(v___y_724_);
v_value_735_ = l_Lean_mkApp4(v___x_720_, v___x_721_, v___x_722_, v___y_724_, v___y_725_);
v___x_736_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_737_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_738_ = 1;
v___x_739_ = l_Lean_Expr_letE___override(v___x_736_, v___x_737_, v_value_735_, v_fst_730_, v___x_738_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_739_);
v___x_741_ = v___x_733_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_snd_731_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
v___jp_744_:
{
if (v_persistent_718_ == 0)
{
lean_object* v___x_746_; 
v___x_746_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_724_ = v___y_745_;
v___y_725_ = v___x_746_;
goto v___jp_723_;
}
else
{
lean_object* v___x_747_; 
v___x_747_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_724_ = v___y_745_;
v___y_725_ = v___x_747_;
goto v___jp_723_;
}
}
}
case 12:
{
lean_object* v_fvarId_750_; lean_object* v_n_751_; uint8_t v_check_752_; uint8_t v_persistent_753_; lean_object* v_objs_x3f_754_; lean_object* v_k_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v_fst_760_; lean_object* v_snd_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_795_; 
v_fvarId_750_ = lean_ctor_get(v_code_535_, 0);
lean_inc_n(v_fvarId_750_, 2);
v_n_751_ = lean_ctor_get(v_code_535_, 1);
lean_inc(v_n_751_);
v_check_752_ = lean_ctor_get_uint8(v_code_535_, sizeof(void*)*4);
v_persistent_753_ = lean_ctor_get_uint8(v_code_535_, sizeof(void*)*4 + 1);
v_objs_x3f_754_ = lean_ctor_get(v_code_535_, 2);
lean_inc(v_objs_x3f_754_);
v_k_755_ = lean_ctor_get(v_code_535_, 3);
lean_inc_ref(v_k_755_);
lean_dec_ref_known(v_code_535_, 4);
lean_inc(v_a_536_);
v___x_756_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_750_, v_a_536_, v_a_537_);
v___x_757_ = lean_unsigned_to_nat(1u);
v___x_758_ = lean_nat_add(v_a_536_, v___x_757_);
v___x_759_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_534_, v_k_755_, v___x_758_, v___x_756_);
lean_dec(v___x_758_);
v_fst_760_ = lean_ctor_get(v___x_759_, 0);
v_snd_761_ = lean_ctor_get(v___x_759_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_795_ == 0)
{
v___x_763_ = v___x_759_;
v_isShared_764_ = v_isSharedCheck_795_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_snd_761_);
lean_inc(v_fst_760_);
lean_dec(v___x_759_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_795_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_790_; 
v___x_765_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__35, &l_Lean_Compiler_LCNF_Code_toExprM___closed__35_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__35);
v___x_766_ = l_Lean_Expr_fvar___override(v_fvarId_750_);
v___x_767_ = l_Lean_mkNatLit(v_n_751_);
if (v_check_752_ == 0)
{
lean_object* v___x_793_; 
v___x_793_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_790_ = v___x_793_;
goto v___jp_789_;
}
else
{
lean_object* v___x_794_; 
v___x_794_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_790_ = v___x_794_;
goto v___jp_789_;
}
v___jp_768_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
lean_inc_ref(v___y_769_);
lean_inc_ref(v___y_770_);
v___x_772_ = l_Lean_mkApp5(v___x_765_, v___x_766_, v___x_767_, v___y_770_, v___y_769_, v___y_771_);
v___x_773_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_774_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_775_ = 1;
v___x_776_ = l_Lean_Expr_letE___override(v___x_773_, v___x_774_, v___x_772_, v_fst_760_, v___x_775_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_776_);
v___x_778_ = v___x_763_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_snd_761_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
v___jp_780_:
{
lean_object* v___x_783_; 
v___x_783_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__38, &l_Lean_Compiler_LCNF_Code_toExprM___closed__38_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38);
if (lean_obj_tag(v_objs_x3f_754_) == 0)
{
lean_object* v___x_784_; 
v___x_784_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__44, &l_Lean_Compiler_LCNF_Code_toExprM___closed__44_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__44);
v___y_769_ = v___y_782_;
v___y_770_ = v___y_781_;
v___y_771_ = v___x_784_;
goto v___jp_768_;
}
else
{
lean_object* v_val_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_val_785_ = lean_ctor_get(v_objs_x3f_754_, 0);
lean_inc(v_val_785_);
lean_dec_ref_known(v_objs_x3f_754_, 1);
v___x_786_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__47, &l_Lean_Compiler_LCNF_Code_toExprM___closed__47_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__47);
v___x_787_ = l_Lean_mkNatLit(v_val_785_);
v___x_788_ = l_Lean_mkAppB(v___x_786_, v___x_783_, v___x_787_);
v___y_769_ = v___y_782_;
v___y_770_ = v___y_781_;
v___y_771_ = v___x_788_;
goto v___jp_768_;
}
}
v___jp_789_:
{
if (v_persistent_753_ == 0)
{
lean_object* v___x_791_; 
v___x_791_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_781_ = v___y_790_;
v___y_782_ = v___x_791_;
goto v___jp_780_;
}
else
{
lean_object* v___x_792_; 
v___x_792_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_781_ = v___y_790_;
v___y_782_ = v___x_792_;
goto v___jp_780_;
}
}
}
}
case 13:
{
lean_object* v_fvarId_796_; lean_object* v_k_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v_fst_802_; lean_object* v_snd_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_817_; 
v_fvarId_796_ = lean_ctor_get(v_code_535_, 0);
lean_inc_n(v_fvarId_796_, 2);
v_k_797_ = lean_ctor_get(v_code_535_, 1);
lean_inc_ref(v_k_797_);
lean_dec_ref_known(v_code_535_, 2);
lean_inc(v_a_536_);
v___x_798_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_796_, v_a_536_, v_a_537_);
v___x_799_ = lean_unsigned_to_nat(1u);
v___x_800_ = lean_nat_add(v_a_536_, v___x_799_);
v___x_801_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_534_, v_k_797_, v___x_800_, v___x_798_);
lean_dec(v___x_800_);
v_fst_802_ = lean_ctor_get(v___x_801_, 0);
v_snd_803_ = lean_ctor_get(v___x_801_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_817_ == 0)
{
v___x_805_ = v___x_801_;
v_isShared_806_ = v_isSharedCheck_817_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_snd_803_);
lean_inc(v_fst_802_);
lean_dec(v___x_801_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_817_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_807_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__50, &l_Lean_Compiler_LCNF_Code_toExprM___closed__50_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__50);
v___x_808_ = l_Lean_Expr_fvar___override(v_fvarId_796_);
v___x_809_ = l_Lean_Expr_app___override(v___x_807_, v___x_808_);
v___x_810_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_811_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_812_ = 1;
v___x_813_ = l_Lean_Expr_letE___override(v___x_810_, v___x_811_, v___x_809_, v_fst_802_, v___x_812_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_813_);
v___x_815_ = v___x_805_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_snd_803_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
default: 
{
lean_object* v_decl_818_; lean_object* v_k_819_; lean_object* v_fvarId_820_; lean_object* v_binderName_821_; lean_object* v_type_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_fst_825_; lean_object* v_snd_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v_fst_831_; lean_object* v_snd_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_841_; 
v_decl_818_ = lean_ctor_get(v_code_535_, 0);
lean_inc_ref(v_decl_818_);
v_k_819_ = lean_ctor_get(v_code_535_, 1);
lean_inc_ref(v_k_819_);
lean_dec_ref(v_code_535_);
v_fvarId_820_ = lean_ctor_get(v_decl_818_, 0);
lean_inc(v_fvarId_820_);
v_binderName_821_ = lean_ctor_get(v_decl_818_, 1);
lean_inc(v_binderName_821_);
v_type_822_ = lean_ctor_get(v_decl_818_, 3);
lean_inc_ref(v_type_822_);
v___x_823_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_537_, v_a_536_, v_type_822_);
v___x_824_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_534_, v_decl_818_, v_a_536_, v_a_537_);
v_fst_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_fst_825_);
v_snd_826_ = lean_ctor_get(v___x_824_, 1);
lean_inc(v_snd_826_);
lean_dec_ref(v___x_824_);
lean_inc(v_a_536_);
v___x_827_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_820_, v_a_536_, v_snd_826_);
v___x_828_ = lean_unsigned_to_nat(1u);
v___x_829_ = lean_nat_add(v_a_536_, v___x_828_);
v___x_830_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_534_, v_k_819_, v___x_829_, v___x_827_);
lean_dec(v___x_829_);
v_fst_831_ = lean_ctor_get(v___x_830_, 0);
v_snd_832_ = lean_ctor_get(v___x_830_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_841_ == 0)
{
v___x_834_ = v___x_830_;
v_isShared_835_ = v_isSharedCheck_841_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_snd_832_);
lean_inc(v_fst_831_);
lean_dec(v___x_830_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_841_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
uint8_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_836_ = 1;
v___x_837_ = l_Lean_Expr_letE___override(v_binderName_821_, v___x_823_, v_fst_825_, v_fst_831_, v___x_836_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_837_);
v___x_839_ = v___x_834_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_snd_832_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(uint8_t v_pu_842_, lean_object* v_value_843_, lean_object* v_params_844_, lean_object* v_params_845_, lean_object* v_i_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_849_ = lean_array_get_size(v_params_845_);
v___x_850_ = lean_nat_dec_lt(v_i_846_, v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; lean_object* v_fst_852_; lean_object* v_snd_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_862_; 
lean_dec(v_i_846_);
v___x_851_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_842_, v_value_843_, v_a_847_, v_a_848_);
v_fst_852_ = lean_ctor_get(v___x_851_, 0);
v_snd_853_ = lean_ctor_get(v___x_851_, 1);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_862_ == 0)
{
v___x_855_ = v___x_851_;
v_isShared_856_ = v_isSharedCheck_862_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_snd_853_);
lean_inc(v_fst_852_);
lean_dec(v___x_851_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_862_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_857_ = lean_array_get_size(v_params_844_);
v___x_858_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg(v_params_844_, v_a_847_, v_snd_853_, v___x_857_, v_fst_852_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_858_);
v___x_860_ = v___x_855_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_snd_853_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
else
{
lean_object* v___x_863_; lean_object* v_fvarId_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_863_ = lean_array_fget_borrowed(v_params_845_, v_i_846_);
v_fvarId_864_ = lean_ctor_get(v___x_863_, 0);
v___x_865_ = lean_unsigned_to_nat(1u);
v___x_866_ = lean_nat_add(v_i_846_, v___x_865_);
lean_dec(v_i_846_);
lean_inc(v_a_847_);
lean_inc(v_fvarId_864_);
v___x_867_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_864_, v_a_847_, v_a_848_);
v___x_868_ = lean_nat_add(v_a_847_, v___x_865_);
lean_dec(v_a_847_);
v_i_846_ = v___x_866_;
v_a_847_ = v___x_868_;
v_a_848_ = v___x_867_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExprM(uint8_t v_pu_870_, lean_object* v_decl_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
lean_object* v_params_874_; lean_object* v_value_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_params_874_ = lean_ctor_get(v_decl_871_, 2);
lean_inc_ref(v_params_874_);
v_value_875_ = lean_ctor_get(v_decl_871_, 4);
lean_inc_ref(v_value_875_);
lean_dec_ref(v_decl_871_);
v___x_876_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_872_);
v___x_877_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_870_, v_value_875_, v_params_874_, v_params_874_, v___x_876_, v_a_872_, v_a_873_);
lean_dec_ref(v_params_874_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExprM___boxed(lean_object* v_pu_878_, lean_object* v_decl_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
uint8_t v_pu_boxed_882_; lean_object* v_res_883_; 
v_pu_boxed_882_ = lean_unbox(v_pu_878_);
v_res_883_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_boxed_882_, v_decl_879_, v_a_880_, v_a_881_);
lean_dec(v_a_880_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg___boxed(lean_object* v_pu_884_, lean_object* v_value_885_, lean_object* v_params_886_, lean_object* v_params_887_, lean_object* v_i_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
uint8_t v_pu_boxed_891_; lean_object* v_res_892_; 
v_pu_boxed_891_ = lean_unbox(v_pu_884_);
v_res_892_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_boxed_891_, v_value_885_, v_params_886_, v_params_887_, v_i_888_, v_a_889_, v_a_890_);
lean_dec_ref(v_params_887_);
lean_dec_ref(v_params_886_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3___boxed(lean_object* v_pu_893_, lean_object* v_sz_894_, lean_object* v_i_895_, lean_object* v_bs_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
uint8_t v_pu_boxed_899_; size_t v_sz_boxed_900_; size_t v_i_boxed_901_; lean_object* v_res_902_; 
v_pu_boxed_899_ = lean_unbox(v_pu_893_);
v_sz_boxed_900_ = lean_unbox_usize(v_sz_894_);
lean_dec(v_sz_894_);
v_i_boxed_901_ = lean_unbox_usize(v_i_895_);
lean_dec(v_i_895_);
v_res_902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(v_pu_boxed_899_, v_sz_boxed_900_, v_i_boxed_901_, v_bs_896_, v___y_897_, v___y_898_);
lean_dec(v___y_897_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExprM___boxed(lean_object* v_pu_903_, lean_object* v_code_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
uint8_t v_pu_boxed_907_; lean_object* v_res_908_; 
v_pu_boxed_907_ = lean_unbox(v_pu_903_);
v_res_908_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_boxed_907_, v_code_904_, v_a_905_, v_a_906_);
lean_dec(v_a_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0(uint8_t v_pu_909_, lean_object* v_value_910_, lean_object* v_params_911_, uint8_t v_pu_912_, lean_object* v_params_913_, lean_object* v_i_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v___x_917_; 
lean_inc(v_a_915_);
v___x_917_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_909_, v_value_910_, v_params_911_, v_params_913_, v_i_914_, v_a_915_, v_a_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___boxed(lean_object* v_pu_918_, lean_object* v_value_919_, lean_object* v_params_920_, lean_object* v_pu_921_, lean_object* v_params_922_, lean_object* v_i_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
uint8_t v_pu_boxed_926_; uint8_t v_pu_boxed_927_; lean_object* v_res_928_; 
v_pu_boxed_926_ = lean_unbox(v_pu_918_);
v_pu_boxed_927_ = lean_unbox(v_pu_921_);
v_res_928_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0(v_pu_boxed_926_, v_value_919_, v_params_920_, v_pu_boxed_927_, v_params_922_, v_i_923_, v_a_924_, v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_params_922_);
lean_dec_ref(v_params_920_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2(uint8_t v_pu_929_, size_t v_sz_930_, size_t v_i_931_, lean_object* v_bs_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_930_, v_i_931_, v_bs_932_, v___y_933_, v___y_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___boxed(lean_object* v_pu_936_, lean_object* v_sz_937_, lean_object* v_i_938_, lean_object* v_bs_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
uint8_t v_pu_boxed_942_; size_t v_sz_boxed_943_; size_t v_i_boxed_944_; lean_object* v_res_945_; 
v_pu_boxed_942_ = lean_unbox(v_pu_936_);
v_sz_boxed_943_ = lean_unbox_usize(v_sz_937_);
lean_dec(v_sz_937_);
v_i_boxed_944_ = lean_unbox_usize(v_i_938_);
lean_dec(v_i_938_);
v_res_945_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2(v_pu_boxed_942_, v_sz_boxed_943_, v_i_boxed_944_, v_bs_939_, v___y_940_, v___y_941_);
lean_dec(v___y_940_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(lean_object* v_as_946_, size_t v_i_947_, size_t v_stop_948_, lean_object* v_b_949_){
_start:
{
lean_object* v___y_951_; uint8_t v___x_955_; 
v___x_955_ = lean_usize_dec_eq(v_i_947_, v_stop_948_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
v___x_956_ = lean_array_uget_borrowed(v_as_946_, v_i_947_);
if (lean_obj_tag(v_b_949_) == 0)
{
lean_object* v_size_957_; lean_object* v___x_958_; 
v_size_957_ = lean_ctor_get(v_b_949_, 0);
lean_inc(v_size_957_);
lean_inc(v___x_956_);
v___x_958_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_956_, v_size_957_, v_b_949_);
v___y_951_ = v___x_958_;
goto v___jp_950_;
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_956_);
v___x_960_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_956_, v___x_959_, v_b_949_);
v___y_951_ = v___x_960_;
goto v___jp_950_;
}
}
else
{
return v_b_949_;
}
v___jp_950_:
{
size_t v___x_952_; size_t v___x_953_; 
v___x_952_ = ((size_t)1ULL);
v___x_953_ = lean_usize_add(v_i_947_, v___x_952_);
v_i_947_ = v___x_953_;
v_b_949_ = v___y_951_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0___boxed(lean_object* v_as_961_, lean_object* v_i_962_, lean_object* v_stop_963_, lean_object* v_b_964_){
_start:
{
size_t v_i_boxed_965_; size_t v_stop_boxed_966_; lean_object* v_res_967_; 
v_i_boxed_965_ = lean_unbox_usize(v_i_962_);
lean_dec(v_i_962_);
v_stop_boxed_966_ = lean_unbox_usize(v_stop_963_);
lean_dec(v_stop_963_);
v_res_967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_as_961_, v_i_boxed_965_, v_stop_boxed_966_, v_b_964_);
lean_dec_ref(v_as_961_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExpr(uint8_t v_pu_968_, lean_object* v_code_969_, lean_object* v_xs_970_){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___y_975_; uint8_t v___x_978_; 
v___x_971_ = lean_box(1);
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = lean_array_get_size(v_xs_970_);
v___x_978_ = lean_nat_dec_lt(v___x_972_, v___x_973_);
if (v___x_978_ == 0)
{
v___y_975_ = v___x_971_;
goto v___jp_974_;
}
else
{
size_t v___x_979_; size_t v___x_980_; lean_object* v___x_981_; 
v___x_979_ = ((size_t)0ULL);
v___x_980_ = lean_usize_of_nat(v___x_973_);
v___x_981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_970_, v___x_979_, v___x_980_, v___x_971_);
v___y_975_ = v___x_981_;
goto v___jp_974_;
}
v___jp_974_:
{
lean_object* v___x_976_; lean_object* v_fst_977_; 
v___x_976_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_968_, v_code_969_, v___x_973_, v___y_975_);
v_fst_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_fst_977_);
lean_dec_ref(v___x_976_);
return v_fst_977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExpr___boxed(lean_object* v_pu_982_, lean_object* v_code_983_, lean_object* v_xs_984_){
_start:
{
uint8_t v_pu_boxed_985_; lean_object* v_res_986_; 
v_pu_boxed_985_ = lean_unbox(v_pu_982_);
v_res_986_ = l_Lean_Compiler_LCNF_Code_toExpr(v_pu_boxed_985_, v_code_983_, v_xs_984_);
lean_dec_ref(v_xs_984_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr(uint8_t v_pu_987_, lean_object* v_decl_988_, lean_object* v_xs_989_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___y_994_; uint8_t v___x_997_; 
v___x_990_ = lean_box(1);
v___x_991_ = lean_unsigned_to_nat(0u);
v___x_992_ = lean_array_get_size(v_xs_989_);
v___x_997_ = lean_nat_dec_lt(v___x_991_, v___x_992_);
if (v___x_997_ == 0)
{
v___y_994_ = v___x_990_;
goto v___jp_993_;
}
else
{
size_t v___x_998_; size_t v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = ((size_t)0ULL);
v___x_999_ = lean_usize_of_nat(v___x_992_);
v___x_1000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_989_, v___x_998_, v___x_999_, v___x_990_);
v___y_994_ = v___x_1000_;
goto v___jp_993_;
}
v___jp_993_:
{
lean_object* v___x_995_; lean_object* v_fst_996_; 
v___x_995_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_987_, v_decl_988_, v___x_992_, v___y_994_);
v_fst_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_fst_996_);
lean_dec_ref(v___x_995_);
return v_fst_996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr___boxed(lean_object* v_pu_1001_, lean_object* v_decl_1002_, lean_object* v_xs_1003_){
_start:
{
uint8_t v_pu_boxed_1004_; lean_object* v_res_1005_; 
v_pu_boxed_1004_ = lean_unbox(v_pu_1001_);
v_res_1005_ = l_Lean_Compiler_LCNF_FunDecl_toExpr(v_pu_boxed_1004_, v_decl_1002_, v_xs_1003_);
lean_dec_ref(v_xs_1003_);
return v_res_1005_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ToExpr(builtin);
}
#ifdef __cplusplus
}
#endif
