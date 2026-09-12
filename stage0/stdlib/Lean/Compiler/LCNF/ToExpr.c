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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* v___f_323_; uint8_t v___x_324_; 
v___f_323_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10));
v___x_324_ = lean_nat_dec_le(v___x_316_, v___x_316_);
if (v___x_324_ == 0)
{
if (v___x_322_ == 0)
{
lean_dec_ref(v_xs_313_);
v___y_318_ = v___x_314_;
goto v___jp_317_;
}
else
{
size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; 
v___x_325_ = ((size_t)0ULL);
v___x_326_ = lean_usize_of_nat(v___x_316_);
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_321_, v___f_323_, v_xs_313_, v___x_325_, v___x_326_, v___x_314_);
v___y_318_ = v___x_327_;
goto v___jp_317_;
}
}
else
{
size_t v___x_328_; size_t v___x_329_; lean_object* v___x_330_; 
v___x_328_ = ((size_t)0ULL);
v___x_329_ = lean_usize_of_nat(v___x_316_);
v___x_330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_321_, v___f_323_, v_xs_313_, v___x_328_, v___x_329_, v___x_314_);
v___y_318_ = v___x_330_;
goto v___jp_317_;
}
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27(lean_object* v_00_u03b1_331_, lean_object* v_x_332_, lean_object* v_xs_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___y_338_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_334_ = lean_box(1);
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = lean_array_get_size(v_xs_333_);
v___x_341_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__9));
v___x_342_ = lean_nat_dec_lt(v___x_335_, v___x_336_);
if (v___x_342_ == 0)
{
lean_dec_ref(v_xs_333_);
v___y_338_ = v___x_334_;
goto v___jp_337_;
}
else
{
lean_object* v___f_343_; uint8_t v___x_344_; 
v___f_343_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10));
v___x_344_ = lean_nat_dec_le(v___x_336_, v___x_336_);
if (v___x_344_ == 0)
{
if (v___x_342_ == 0)
{
lean_dec_ref(v_xs_333_);
v___y_338_ = v___x_334_;
goto v___jp_337_;
}
else
{
size_t v___x_345_; size_t v___x_346_; lean_object* v___x_347_; 
v___x_345_ = ((size_t)0ULL);
v___x_346_ = lean_usize_of_nat(v___x_336_);
v___x_347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_341_, v___f_343_, v_xs_333_, v___x_345_, v___x_346_, v___x_334_);
v___y_338_ = v___x_347_;
goto v___jp_337_;
}
}
else
{
size_t v___x_348_; size_t v___x_349_; lean_object* v___x_350_; 
v___x_348_ = ((size_t)0ULL);
v___x_349_ = lean_usize_of_nat(v___x_336_);
v___x_350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_341_, v___f_343_, v_xs_333_, v___x_348_, v___x_349_, v___x_334_);
v___y_338_ = v___x_350_;
goto v___jp_337_;
}
}
v___jp_337_:
{
lean_object* v___x_339_; lean_object* v_fst_340_; 
v___x_339_ = lean_apply_2(v_x_332_, v___x_336_, v___y_338_);
v_fst_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_fst_340_);
lean_dec_ref(v___x_339_);
return v_fst_340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(lean_object* v_arg_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_354_ = l_Lean_Compiler_LCNF_Arg_toExpr___redArg(v_arg_351_);
v___x_355_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_353_, v_a_352_, v___x_354_);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v_a_353_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg___boxed(lean_object* v_arg_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_arg_357_, v_a_358_, v_a_359_);
lean_dec(v_a_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM(uint8_t v_pu_361_, lean_object* v_arg_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_arg_362_, v_a_363_, v_a_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___boxed(lean_object* v_pu_366_, lean_object* v_arg_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
uint8_t v_pu_boxed_370_; lean_object* v_res_371_; 
v_pu_boxed_370_ = lean_unbox(v_pu_366_);
v_res_371_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM(v_pu_boxed_370_, v_arg_367_, v_a_368_, v_a_369_);
lean_dec(v_a_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(size_t v_sz_372_, size_t v_i_373_, lean_object* v_bs_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
uint8_t v___x_377_; 
v___x_377_ = lean_usize_dec_lt(v_i_373_, v_sz_372_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v_bs_374_);
lean_ctor_set(v___x_378_, 1, v___y_376_);
return v___x_378_;
}
else
{
lean_object* v_v_379_; lean_object* v___x_380_; lean_object* v_fst_381_; lean_object* v_snd_382_; lean_object* v___x_383_; lean_object* v_bs_x27_384_; size_t v___x_385_; size_t v___x_386_; lean_object* v___x_387_; 
v_v_379_ = lean_array_uget_borrowed(v_bs_374_, v_i_373_);
lean_inc(v_v_379_);
v___x_380_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_v_379_, v___y_375_, v___y_376_);
v_fst_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_fst_381_);
v_snd_382_ = lean_ctor_get(v___x_380_, 1);
lean_inc(v_snd_382_);
lean_dec_ref(v___x_380_);
v___x_383_ = lean_unsigned_to_nat(0u);
v_bs_x27_384_ = lean_array_uset(v_bs_374_, v_i_373_, v___x_383_);
v___x_385_ = ((size_t)1ULL);
v___x_386_ = lean_usize_add(v_i_373_, v___x_385_);
v___x_387_ = lean_array_uset(v_bs_x27_384_, v_i_373_, v_fst_381_);
v_i_373_ = v___x_386_;
v_bs_374_ = v___x_387_;
v___y_376_ = v_snd_382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg___boxed(lean_object* v_sz_389_, lean_object* v_i_390_, lean_object* v_bs_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
size_t v_sz_boxed_394_; size_t v_i_boxed_395_; lean_object* v_res_396_; 
v_sz_boxed_394_ = lean_unbox_usize(v_sz_389_);
lean_dec(v_sz_389_);
v_i_boxed_395_ = lean_unbox_usize(v_i_390_);
lean_dec(v_i_390_);
v_res_396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_boxed_394_, v_i_boxed_395_, v_bs_391_, v___y_392_, v___y_393_);
lean_dec(v___y_392_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(uint8_t v_pu_397_, size_t v_sz_398_, size_t v_i_399_, lean_object* v_bs_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
uint8_t v___x_403_; 
v___x_403_ = lean_usize_dec_lt(v_i_399_, v_sz_398_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; 
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v_bs_400_);
lean_ctor_set(v___x_404_, 1, v___y_402_);
return v___x_404_;
}
else
{
lean_object* v_v_405_; lean_object* v___x_406_; lean_object* v_bs_x27_407_; lean_object* v_fst_409_; lean_object* v_snd_410_; 
v_v_405_ = lean_array_uget(v_bs_400_, v_i_399_);
v___x_406_ = lean_unsigned_to_nat(0u);
v_bs_x27_407_ = lean_array_uset(v_bs_400_, v_i_399_, v___x_406_);
switch(lean_obj_tag(v_v_405_))
{
case 0:
{
lean_object* v_ctorName_415_; lean_object* v_params_416_; lean_object* v_code_417_; lean_object* v___x_418_; lean_object* v_fst_419_; lean_object* v_snd_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_ctorName_415_ = lean_ctor_get(v_v_405_, 0);
lean_inc(v_ctorName_415_);
v_params_416_ = lean_ctor_get(v_v_405_, 1);
lean_inc_ref(v_params_416_);
v_code_417_ = lean_ctor_get(v_v_405_, 2);
lean_inc_ref(v_code_417_);
lean_dec_ref_known(v_v_405_, 3);
lean_inc(v___y_401_);
v___x_418_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_397_, v_code_417_, v_params_416_, v_params_416_, v___x_406_, v___y_401_, v___y_402_);
lean_dec_ref(v_params_416_);
v_fst_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_fst_419_);
v_snd_420_ = lean_ctor_get(v___x_418_, 1);
lean_inc(v_snd_420_);
lean_dec_ref(v___x_418_);
v___x_421_ = lean_box(0);
v___x_422_ = l_Lean_mkConst(v_ctorName_415_, v___x_421_);
v___x_423_ = l_Lean_Expr_app___override(v___x_422_, v_fst_419_);
v_fst_409_ = v___x_423_;
v_snd_410_ = v_snd_420_;
goto v___jp_408_;
}
case 1:
{
lean_object* v_info_424_; lean_object* v_code_425_; lean_object* v___x_426_; lean_object* v_fst_427_; lean_object* v_snd_428_; lean_object* v_name_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_info_424_ = lean_ctor_get(v_v_405_, 0);
lean_inc_ref(v_info_424_);
v_code_425_ = lean_ctor_get(v_v_405_, 1);
lean_inc_ref(v_code_425_);
lean_dec_ref_known(v_v_405_, 2);
v___x_426_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_397_, v_code_425_, v___y_401_, v___y_402_);
v_fst_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_fst_427_);
v_snd_428_ = lean_ctor_get(v___x_426_, 1);
lean_inc(v_snd_428_);
lean_dec_ref(v___x_426_);
v_name_429_ = lean_ctor_get(v_info_424_, 0);
lean_inc(v_name_429_);
lean_dec_ref(v_info_424_);
v___x_430_ = lean_box(0);
v___x_431_ = l_Lean_mkConst(v_name_429_, v___x_430_);
v___x_432_ = l_Lean_Expr_app___override(v___x_431_, v_fst_427_);
v_fst_409_ = v___x_432_;
v_snd_410_ = v_snd_428_;
goto v___jp_408_;
}
default: 
{
lean_object* v_code_433_; lean_object* v___x_434_; lean_object* v_fst_435_; lean_object* v_snd_436_; 
v_code_433_ = lean_ctor_get(v_v_405_, 0);
lean_inc_ref(v_code_433_);
lean_dec_ref_known(v_v_405_, 1);
v___x_434_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_397_, v_code_433_, v___y_401_, v___y_402_);
v_fst_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_fst_435_);
v_snd_436_ = lean_ctor_get(v___x_434_, 1);
lean_inc(v_snd_436_);
lean_dec_ref(v___x_434_);
v_fst_409_ = v_fst_435_;
v_snd_410_ = v_snd_436_;
goto v___jp_408_;
}
}
v___jp_408_:
{
size_t v___x_411_; size_t v___x_412_; lean_object* v___x_413_; 
v___x_411_ = ((size_t)1ULL);
v___x_412_ = lean_usize_add(v_i_399_, v___x_411_);
v___x_413_ = lean_array_uset(v_bs_x27_407_, v_i_399_, v_fst_409_);
v_i_399_ = v___x_412_;
v_bs_400_ = v___x_413_;
v___y_402_ = v_snd_410_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__2(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_box(0);
v___x_441_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__1));
v___x_442_ = l_Lean_mkConst(v___x_441_, v___x_440_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__5(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_box(0);
v___x_447_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__4));
v___x_448_ = l_Lean_mkConst(v___x_447_, v___x_446_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__8(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_box(0);
v___x_453_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__7));
v___x_454_ = l_Lean_mkConst(v___x_453_, v___x_452_);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_box(0);
v___x_462_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__12));
v___x_463_ = l_Lean_mkConst(v___x_462_, v___x_461_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__16(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = lean_box(0);
v___x_468_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__15));
v___x_469_ = l_Lean_mkConst(v___x_468_, v___x_467_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__19(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = lean_box(0);
v___x_474_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__18));
v___x_475_ = l_Lean_mkConst(v___x_474_, v___x_473_);
return v___x_475_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__22(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_box(0);
v___x_480_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__21));
v___x_481_ = l_Lean_mkConst(v___x_480_, v___x_479_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__25(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = lean_box(0);
v___x_486_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__24));
v___x_487_ = l_Lean_mkConst(v___x_486_, v___x_485_);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_box(0);
v___x_494_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__28));
v___x_495_ = l_Lean_mkConst(v___x_494_, v___x_493_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = lean_box(0);
v___x_501_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__31));
v___x_502_ = l_Lean_mkConst(v___x_501_, v___x_500_);
return v___x_502_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__35(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = lean_box(0);
v___x_507_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__34));
v___x_508_ = l_Lean_mkConst(v___x_507_, v___x_506_);
return v___x_508_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = lean_box(0);
v___x_513_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__37));
v___x_514_ = l_Lean_mkConst(v___x_513_, v___x_512_);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__43(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__42));
v___x_524_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__41));
v___x_525_ = l_Lean_mkConst(v___x_524_, v___x_523_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__44(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__38, &l_Lean_Compiler_LCNF_Code_toExprM___closed__38_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38);
v___x_527_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__43, &l_Lean_Compiler_LCNF_Code_toExprM___closed__43_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__43);
v___x_528_ = l_Lean_Expr_app___override(v___x_527_, v___x_526_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__47(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__42));
v___x_534_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__46));
v___x_535_ = l_Lean_mkConst(v___x_534_, v___x_533_);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__50(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = lean_box(0);
v___x_540_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__49));
v___x_541_ = l_Lean_mkConst(v___x_540_, v___x_539_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExprM(uint8_t v_pu_542_, lean_object* v_code_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
switch(lean_obj_tag(v_code_543_))
{
case 0:
{
lean_object* v_decl_546_; lean_object* v_k_547_; lean_object* v_fvarId_548_; lean_object* v_binderName_549_; lean_object* v_type_550_; lean_object* v_value_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v_fst_559_; lean_object* v_snd_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_569_; 
v_decl_546_ = lean_ctor_get(v_code_543_, 0);
lean_inc_ref(v_decl_546_);
v_k_547_ = lean_ctor_get(v_code_543_, 1);
lean_inc_ref(v_k_547_);
lean_dec_ref_known(v_code_543_, 2);
v_fvarId_548_ = lean_ctor_get(v_decl_546_, 0);
lean_inc(v_fvarId_548_);
v_binderName_549_ = lean_ctor_get(v_decl_546_, 1);
lean_inc(v_binderName_549_);
v_type_550_ = lean_ctor_get(v_decl_546_, 2);
lean_inc_ref(v_type_550_);
v_value_551_ = lean_ctor_get(v_decl_546_, 3);
lean_inc(v_value_551_);
lean_dec_ref(v_decl_546_);
v___x_552_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_545_, v_a_544_, v_type_550_);
v___x_553_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v_pu_542_, v_value_551_);
v___x_554_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_545_, v_a_544_, v___x_553_);
lean_inc(v_a_544_);
v___x_555_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_548_, v_a_544_, v_a_545_);
v___x_556_ = lean_unsigned_to_nat(1u);
v___x_557_ = lean_nat_add(v_a_544_, v___x_556_);
v___x_558_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_542_, v_k_547_, v___x_557_, v___x_555_);
lean_dec(v___x_557_);
v_fst_559_ = lean_ctor_get(v___x_558_, 0);
v_snd_560_ = lean_ctor_get(v___x_558_, 1);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_569_ == 0)
{
v___x_562_ = v___x_558_;
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_snd_560_);
lean_inc(v_fst_559_);
lean_dec(v___x_558_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
uint8_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_564_ = 1;
v___x_565_ = l_Lean_Expr_letE___override(v_binderName_549_, v___x_552_, v___x_554_, v_fst_559_, v___x_564_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_565_);
v___x_567_ = v___x_562_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_snd_560_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
case 3:
{
lean_object* v_fvarId_570_; lean_object* v_args_571_; lean_object* v___x_572_; size_t v_sz_573_; size_t v___x_574_; lean_object* v___x_575_; lean_object* v_fst_576_; lean_object* v_snd_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_585_; 
v_fvarId_570_ = lean_ctor_get(v_code_543_, 0);
lean_inc(v_fvarId_570_);
v_args_571_ = lean_ctor_get(v_code_543_, 1);
lean_inc_ref(v_args_571_);
lean_dec_ref_known(v_code_543_, 2);
v___x_572_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_544_, v_a_545_, v_fvarId_570_);
v_sz_573_ = lean_array_size(v_args_571_);
v___x_574_ = ((size_t)0ULL);
v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_573_, v___x_574_, v_args_571_, v_a_544_, v_a_545_);
v_fst_576_ = lean_ctor_get(v___x_575_, 0);
v_snd_577_ = lean_ctor_get(v___x_575_, 1);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_585_ == 0)
{
v___x_579_ = v___x_575_;
v_isShared_580_ = v_isSharedCheck_585_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_snd_577_);
lean_inc(v_fst_576_);
lean_dec(v___x_575_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_585_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_581_ = l_Lean_mkAppN(v___x_572_, v_fst_576_);
lean_dec(v_fst_576_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_581_);
v___x_583_ = v___x_579_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_snd_577_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
case 4:
{
lean_object* v_cases_586_; lean_object* v_discr_587_; lean_object* v_alts_588_; size_t v_sz_589_; size_t v___x_590_; lean_object* v___x_591_; lean_object* v_fst_592_; lean_object* v_snd_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_607_; 
v_cases_586_ = lean_ctor_get(v_code_543_, 0);
lean_inc_ref(v_cases_586_);
lean_dec_ref_known(v_code_543_, 1);
v_discr_587_ = lean_ctor_get(v_cases_586_, 2);
lean_inc(v_discr_587_);
v_alts_588_ = lean_ctor_get(v_cases_586_, 3);
lean_inc_ref(v_alts_588_);
lean_dec_ref(v_cases_586_);
v_sz_589_ = lean_array_size(v_alts_588_);
v___x_590_ = ((size_t)0ULL);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(v_pu_542_, v_sz_589_, v___x_590_, v_alts_588_, v_a_544_, v_a_545_);
v_fst_592_ = lean_ctor_get(v___x_591_, 0);
v_snd_593_ = lean_ctor_get(v___x_591_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_607_ == 0)
{
v___x_595_ = v___x_591_;
v_isShared_596_ = v_isSharedCheck_607_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_snd_593_);
lean_inc(v_fst_592_);
lean_dec(v___x_591_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_607_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_597_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_544_, v_snd_593_, v_discr_587_);
v___x_598_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__2, &l_Lean_Compiler_LCNF_Code_toExprM___closed__2_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__2);
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = lean_mk_empty_array_with_capacity(v___x_599_);
v___x_601_ = lean_array_push(v___x_600_, v___x_597_);
v___x_602_ = l_Array_append___redArg(v___x_601_, v_fst_592_);
lean_dec(v_fst_592_);
v___x_603_ = l_Lean_mkAppN(v___x_598_, v___x_602_);
lean_dec_ref(v___x_602_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_603_);
v___x_605_ = v___x_595_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_snd_593_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
case 5:
{
lean_object* v_fvarId_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_fvarId_608_ = lean_ctor_get(v_code_543_, 0);
lean_inc(v_fvarId_608_);
lean_dec_ref_known(v_code_543_, 1);
v___x_609_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_544_, v_a_545_, v_fvarId_608_);
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v_a_545_);
return v___x_610_;
}
case 6:
{
lean_object* v_type_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_type_611_ = lean_ctor_get(v_code_543_, 0);
lean_inc_ref(v_type_611_);
lean_dec_ref_known(v_code_543_, 1);
v___x_612_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_545_, v_a_544_, v_type_611_);
v___x_613_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__5, &l_Lean_Compiler_LCNF_Code_toExprM___closed__5_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__5);
v___x_614_ = l_Lean_Expr_app___override(v___x_613_, v___x_612_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v_a_545_);
return v___x_615_;
}
case 7:
{
lean_object* v_fvarId_616_; lean_object* v_i_617_; lean_object* v_y_618_; lean_object* v_k_619_; lean_object* v___x_620_; lean_object* v_fst_621_; lean_object* v_snd_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v_fst_628_; lean_object* v_snd_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_643_; 
v_fvarId_616_ = lean_ctor_get(v_code_543_, 0);
lean_inc_n(v_fvarId_616_, 2);
v_i_617_ = lean_ctor_get(v_code_543_, 1);
lean_inc(v_i_617_);
v_y_618_ = lean_ctor_get(v_code_543_, 2);
lean_inc(v_y_618_);
v_k_619_ = lean_ctor_get(v_code_543_, 3);
lean_inc_ref(v_k_619_);
lean_dec_ref_known(v_code_543_, 4);
v___x_620_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_y_618_, v_a_544_, v_a_545_);
v_fst_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_fst_621_);
v_snd_622_ = lean_ctor_get(v___x_620_, 1);
lean_inc(v_snd_622_);
lean_dec_ref(v___x_620_);
v___x_623_ = l_Lean_Expr_fvar___override(v_fvarId_616_);
lean_inc(v_a_544_);
v___x_624_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_616_, v_a_544_, v_snd_622_);
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = lean_nat_add(v_a_544_, v___x_625_);
v___x_627_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_542_, v_k_619_, v___x_626_, v___x_624_);
lean_dec(v___x_626_);
v_fst_628_ = lean_ctor_get(v___x_627_, 0);
v_snd_629_ = lean_ctor_get(v___x_627_, 1);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_643_ == 0)
{
v___x_631_ = v___x_627_;
v_isShared_632_ = v_isSharedCheck_643_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_snd_629_);
lean_inc(v_fst_628_);
lean_dec(v___x_627_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_643_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_633_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__8, &l_Lean_Compiler_LCNF_Code_toExprM___closed__8_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__8);
v___x_634_ = l_Lean_mkNatLit(v_i_617_);
v___x_635_ = l_Lean_mkApp3(v___x_633_, v___x_623_, v___x_634_, v_fst_621_);
v___x_636_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_637_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_638_ = 1;
v___x_639_ = l_Lean_Expr_letE___override(v___x_636_, v___x_637_, v___x_635_, v_fst_628_, v___x_638_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_639_);
v___x_641_ = v___x_631_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_snd_629_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
case 8:
{
lean_object* v_fvarId_644_; lean_object* v_i_645_; lean_object* v_y_646_; lean_object* v_k_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v_fst_653_; lean_object* v_snd_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_669_; 
v_fvarId_644_ = lean_ctor_get(v_code_543_, 0);
lean_inc_n(v_fvarId_644_, 2);
v_i_645_ = lean_ctor_get(v_code_543_, 1);
lean_inc(v_i_645_);
v_y_646_ = lean_ctor_get(v_code_543_, 2);
lean_inc(v_y_646_);
v_k_647_ = lean_ctor_get(v_code_543_, 3);
lean_inc_ref(v_k_647_);
lean_dec_ref_known(v_code_543_, 4);
v___x_648_ = l_Lean_Expr_fvar___override(v_fvarId_644_);
lean_inc(v_a_544_);
v___x_649_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_644_, v_a_544_, v_a_545_);
v___x_650_ = lean_unsigned_to_nat(1u);
v___x_651_ = lean_nat_add(v_a_544_, v___x_650_);
v___x_652_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_542_, v_k_647_, v___x_651_, v___x_649_);
lean_dec(v___x_651_);
v_fst_653_ = lean_ctor_get(v___x_652_, 0);
v_snd_654_ = lean_ctor_get(v___x_652_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_669_ == 0)
{
v___x_656_ = v___x_652_;
v_isShared_657_ = v_isSharedCheck_669_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_snd_654_);
lean_inc(v_fst_653_);
lean_dec(v___x_652_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_669_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v_value_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_658_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__16, &l_Lean_Compiler_LCNF_Code_toExprM___closed__16_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__16);
v___x_659_ = l_Lean_mkNatLit(v_i_645_);
v___x_660_ = l_Lean_Expr_fvar___override(v_y_646_);
v_value_661_ = l_Lean_mkApp3(v___x_658_, v___x_648_, v___x_659_, v___x_660_);
v___x_662_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_663_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_664_ = 1;
v___x_665_ = l_Lean_Expr_letE___override(v___x_662_, v___x_663_, v_value_661_, v_fst_653_, v___x_664_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_665_);
v___x_667_ = v___x_656_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_snd_654_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
case 9:
{
lean_object* v_fvarId_670_; lean_object* v_i_671_; lean_object* v_offset_672_; lean_object* v_y_673_; lean_object* v_ty_674_; lean_object* v_k_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v_fst_681_; lean_object* v_snd_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_698_; 
v_fvarId_670_ = lean_ctor_get(v_code_543_, 0);
lean_inc_n(v_fvarId_670_, 2);
v_i_671_ = lean_ctor_get(v_code_543_, 1);
lean_inc(v_i_671_);
v_offset_672_ = lean_ctor_get(v_code_543_, 2);
lean_inc(v_offset_672_);
v_y_673_ = lean_ctor_get(v_code_543_, 3);
lean_inc(v_y_673_);
v_ty_674_ = lean_ctor_get(v_code_543_, 4);
lean_inc_ref(v_ty_674_);
v_k_675_ = lean_ctor_get(v_code_543_, 5);
lean_inc_ref(v_k_675_);
lean_dec_ref_known(v_code_543_, 6);
v___x_676_ = l_Lean_Expr_fvar___override(v_fvarId_670_);
lean_inc(v_a_544_);
v___x_677_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_670_, v_a_544_, v_a_545_);
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = lean_nat_add(v_a_544_, v___x_678_);
v___x_680_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_542_, v_k_675_, v___x_679_, v___x_677_);
lean_dec(v___x_679_);
v_fst_681_ = lean_ctor_get(v___x_680_, 0);
v_snd_682_ = lean_ctor_get(v___x_680_, 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_698_ == 0)
{
v___x_684_ = v___x_680_;
v_isShared_685_ = v_isSharedCheck_698_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_snd_682_);
lean_inc(v_fst_681_);
lean_dec(v___x_680_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_698_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v_value_690_; lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_686_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__19, &l_Lean_Compiler_LCNF_Code_toExprM___closed__19_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__19);
v___x_687_ = l_Lean_mkNatLit(v_i_671_);
v___x_688_ = l_Lean_mkNatLit(v_offset_672_);
v___x_689_ = l_Lean_Expr_fvar___override(v_y_673_);
v_value_690_ = l_Lean_mkApp5(v___x_686_, v___x_676_, v___x_687_, v___x_688_, v___x_689_, v_ty_674_);
v___x_691_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_692_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_693_ = 1;
v___x_694_ = l_Lean_Expr_letE___override(v___x_691_, v___x_692_, v_value_690_, v_fst_681_, v___x_693_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_694_);
v___x_696_ = v___x_684_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_snd_682_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
case 10:
{
lean_object* v_fvarId_699_; lean_object* v_cidx_700_; lean_object* v_k_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v_fst_706_; lean_object* v_snd_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_722_; 
v_fvarId_699_ = lean_ctor_get(v_code_543_, 0);
lean_inc_n(v_fvarId_699_, 2);
v_cidx_700_ = lean_ctor_get(v_code_543_, 1);
lean_inc(v_cidx_700_);
v_k_701_ = lean_ctor_get(v_code_543_, 2);
lean_inc_ref(v_k_701_);
lean_dec_ref_known(v_code_543_, 3);
lean_inc(v_a_544_);
v___x_702_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_699_, v_a_544_, v_a_545_);
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = lean_nat_add(v_a_544_, v___x_703_);
v___x_705_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_542_, v_k_701_, v___x_704_, v___x_702_);
lean_dec(v___x_704_);
v_fst_706_ = lean_ctor_get(v___x_705_, 0);
v_snd_707_ = lean_ctor_get(v___x_705_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_722_ == 0)
{
v___x_709_ = v___x_705_;
v_isShared_710_ = v_isSharedCheck_722_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_snd_707_);
lean_inc(v_fst_706_);
lean_dec(v___x_705_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_722_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_711_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__22, &l_Lean_Compiler_LCNF_Code_toExprM___closed__22_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__22);
v___x_712_ = l_Lean_Expr_fvar___override(v_fvarId_699_);
v___x_713_ = l_Lean_mkNatLit(v_cidx_700_);
v___x_714_ = l_Lean_mkAppB(v___x_711_, v___x_712_, v___x_713_);
v___x_715_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_716_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_717_ = 1;
v___x_718_ = l_Lean_Expr_letE___override(v___x_715_, v___x_716_, v___x_714_, v_fst_706_, v___x_717_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_718_);
v___x_720_ = v___x_709_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_snd_707_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
case 11:
{
lean_object* v_fvarId_723_; lean_object* v_n_724_; uint8_t v_check_725_; uint8_t v_persistent_726_; lean_object* v_k_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_753_; 
v_fvarId_723_ = lean_ctor_get(v_code_543_, 0);
lean_inc_n(v_fvarId_723_, 2);
v_n_724_ = lean_ctor_get(v_code_543_, 1);
lean_inc(v_n_724_);
v_check_725_ = lean_ctor_get_uint8(v_code_543_, sizeof(void*)*3);
v_persistent_726_ = lean_ctor_get_uint8(v_code_543_, sizeof(void*)*3 + 1);
v_k_727_ = lean_ctor_get(v_code_543_, 2);
lean_inc_ref(v_k_727_);
lean_dec_ref_known(v_code_543_, 3);
v___x_728_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__25, &l_Lean_Compiler_LCNF_Code_toExprM___closed__25_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__25);
v___x_729_ = l_Lean_Expr_fvar___override(v_fvarId_723_);
v___x_730_ = l_Lean_mkNatLit(v_n_724_);
if (v_check_725_ == 0)
{
lean_object* v___x_756_; 
v___x_756_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_753_ = v___x_756_;
goto v___jp_752_;
}
else
{
lean_object* v___x_757_; 
v___x_757_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_753_ = v___x_757_;
goto v___jp_752_;
}
v___jp_731_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v_fst_738_; lean_object* v_snd_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_751_; 
lean_inc(v_a_544_);
v___x_734_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_723_, v_a_544_, v_a_545_);
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = lean_nat_add(v_a_544_, v___x_735_);
v___x_737_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_542_, v_k_727_, v___x_736_, v___x_734_);
lean_dec(v___x_736_);
v_fst_738_ = lean_ctor_get(v___x_737_, 0);
v_snd_739_ = lean_ctor_get(v___x_737_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_751_ == 0)
{
v___x_741_ = v___x_737_;
v_isShared_742_ = v_isSharedCheck_751_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_snd_739_);
lean_inc(v_fst_738_);
lean_dec(v___x_737_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_751_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v_value_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
lean_inc_ref(v___y_733_);
lean_inc_ref(v___y_732_);
v_value_743_ = l_Lean_mkApp4(v___x_728_, v___x_729_, v___x_730_, v___y_732_, v___y_733_);
v___x_744_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_745_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_746_ = 1;
v___x_747_ = l_Lean_Expr_letE___override(v___x_744_, v___x_745_, v_value_743_, v_fst_738_, v___x_746_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_747_);
v___x_749_ = v___x_741_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_snd_739_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
v___jp_752_:
{
if (v_persistent_726_ == 0)
{
lean_object* v___x_754_; 
v___x_754_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_732_ = v___y_753_;
v___y_733_ = v___x_754_;
goto v___jp_731_;
}
else
{
lean_object* v___x_755_; 
v___x_755_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_732_ = v___y_753_;
v___y_733_ = v___x_755_;
goto v___jp_731_;
}
}
}
case 12:
{
lean_object* v_fvarId_758_; lean_object* v_n_759_; uint8_t v_check_760_; uint8_t v_persistent_761_; lean_object* v_objs_x3f_762_; lean_object* v_k_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v_fst_768_; lean_object* v_snd_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_803_; 
v_fvarId_758_ = lean_ctor_get(v_code_543_, 0);
lean_inc_n(v_fvarId_758_, 2);
v_n_759_ = lean_ctor_get(v_code_543_, 1);
lean_inc(v_n_759_);
v_check_760_ = lean_ctor_get_uint8(v_code_543_, sizeof(void*)*4);
v_persistent_761_ = lean_ctor_get_uint8(v_code_543_, sizeof(void*)*4 + 1);
v_objs_x3f_762_ = lean_ctor_get(v_code_543_, 2);
lean_inc(v_objs_x3f_762_);
v_k_763_ = lean_ctor_get(v_code_543_, 3);
lean_inc_ref(v_k_763_);
lean_dec_ref_known(v_code_543_, 4);
lean_inc(v_a_544_);
v___x_764_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_758_, v_a_544_, v_a_545_);
v___x_765_ = lean_unsigned_to_nat(1u);
v___x_766_ = lean_nat_add(v_a_544_, v___x_765_);
v___x_767_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_542_, v_k_763_, v___x_766_, v___x_764_);
lean_dec(v___x_766_);
v_fst_768_ = lean_ctor_get(v___x_767_, 0);
v_snd_769_ = lean_ctor_get(v___x_767_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_803_ == 0)
{
v___x_771_ = v___x_767_;
v_isShared_772_ = v_isSharedCheck_803_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_snd_769_);
lean_inc(v_fst_768_);
lean_dec(v___x_767_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_803_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_798_; 
v___x_773_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__35, &l_Lean_Compiler_LCNF_Code_toExprM___closed__35_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__35);
v___x_774_ = l_Lean_Expr_fvar___override(v_fvarId_758_);
v___x_775_ = l_Lean_mkNatLit(v_n_759_);
if (v_check_760_ == 0)
{
lean_object* v___x_801_; 
v___x_801_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_798_ = v___x_801_;
goto v___jp_797_;
}
else
{
lean_object* v___x_802_; 
v___x_802_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_798_ = v___x_802_;
goto v___jp_797_;
}
v___jp_776_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
lean_inc_ref(v___y_778_);
lean_inc_ref(v___y_777_);
v___x_780_ = l_Lean_mkApp5(v___x_773_, v___x_774_, v___x_775_, v___y_777_, v___y_778_, v___y_779_);
v___x_781_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_782_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_783_ = 1;
v___x_784_ = l_Lean_Expr_letE___override(v___x_781_, v___x_782_, v___x_780_, v_fst_768_, v___x_783_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_784_);
v___x_786_ = v___x_771_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_snd_769_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
v___jp_788_:
{
lean_object* v___x_791_; 
v___x_791_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__38, &l_Lean_Compiler_LCNF_Code_toExprM___closed__38_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38);
if (lean_obj_tag(v_objs_x3f_762_) == 0)
{
lean_object* v___x_792_; 
v___x_792_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__44, &l_Lean_Compiler_LCNF_Code_toExprM___closed__44_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__44);
v___y_777_ = v___y_789_;
v___y_778_ = v___y_790_;
v___y_779_ = v___x_792_;
goto v___jp_776_;
}
else
{
lean_object* v_val_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_val_793_ = lean_ctor_get(v_objs_x3f_762_, 0);
lean_inc(v_val_793_);
lean_dec_ref_known(v_objs_x3f_762_, 1);
v___x_794_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__47, &l_Lean_Compiler_LCNF_Code_toExprM___closed__47_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__47);
v___x_795_ = l_Lean_mkNatLit(v_val_793_);
v___x_796_ = l_Lean_mkAppB(v___x_794_, v___x_791_, v___x_795_);
v___y_777_ = v___y_789_;
v___y_778_ = v___y_790_;
v___y_779_ = v___x_796_;
goto v___jp_776_;
}
}
v___jp_797_:
{
if (v_persistent_761_ == 0)
{
lean_object* v___x_799_; 
v___x_799_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_789_ = v___y_798_;
v___y_790_ = v___x_799_;
goto v___jp_788_;
}
else
{
lean_object* v___x_800_; 
v___x_800_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_789_ = v___y_798_;
v___y_790_ = v___x_800_;
goto v___jp_788_;
}
}
}
}
case 13:
{
lean_object* v_fvarId_804_; lean_object* v_k_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_fst_810_; lean_object* v_snd_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_825_; 
v_fvarId_804_ = lean_ctor_get(v_code_543_, 0);
lean_inc_n(v_fvarId_804_, 2);
v_k_805_ = lean_ctor_get(v_code_543_, 1);
lean_inc_ref(v_k_805_);
lean_dec_ref_known(v_code_543_, 2);
lean_inc(v_a_544_);
v___x_806_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_804_, v_a_544_, v_a_545_);
v___x_807_ = lean_unsigned_to_nat(1u);
v___x_808_ = lean_nat_add(v_a_544_, v___x_807_);
v___x_809_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_542_, v_k_805_, v___x_808_, v___x_806_);
lean_dec(v___x_808_);
v_fst_810_ = lean_ctor_get(v___x_809_, 0);
v_snd_811_ = lean_ctor_get(v___x_809_, 1);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_825_ == 0)
{
v___x_813_ = v___x_809_;
v_isShared_814_ = v_isSharedCheck_825_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_snd_811_);
lean_inc(v_fst_810_);
lean_dec(v___x_809_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_825_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_815_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__50, &l_Lean_Compiler_LCNF_Code_toExprM___closed__50_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__50);
v___x_816_ = l_Lean_Expr_fvar___override(v_fvarId_804_);
v___x_817_ = l_Lean_Expr_app___override(v___x_815_, v___x_816_);
v___x_818_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_819_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_820_ = 1;
v___x_821_ = l_Lean_Expr_letE___override(v___x_818_, v___x_819_, v___x_817_, v_fst_810_, v___x_820_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_821_);
v___x_823_ = v___x_813_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_snd_811_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
default: 
{
lean_object* v_decl_826_; lean_object* v_k_827_; lean_object* v_fvarId_828_; lean_object* v_binderName_829_; lean_object* v_type_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v_fst_833_; lean_object* v_snd_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v_fst_839_; lean_object* v_snd_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_849_; 
v_decl_826_ = lean_ctor_get(v_code_543_, 0);
lean_inc_ref(v_decl_826_);
v_k_827_ = lean_ctor_get(v_code_543_, 1);
lean_inc_ref(v_k_827_);
lean_dec_ref(v_code_543_);
v_fvarId_828_ = lean_ctor_get(v_decl_826_, 0);
lean_inc(v_fvarId_828_);
v_binderName_829_ = lean_ctor_get(v_decl_826_, 1);
lean_inc(v_binderName_829_);
v_type_830_ = lean_ctor_get(v_decl_826_, 3);
lean_inc_ref(v_type_830_);
v___x_831_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_545_, v_a_544_, v_type_830_);
v___x_832_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_542_, v_decl_826_, v_a_544_, v_a_545_);
v_fst_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_fst_833_);
v_snd_834_ = lean_ctor_get(v___x_832_, 1);
lean_inc(v_snd_834_);
lean_dec_ref(v___x_832_);
lean_inc(v_a_544_);
v___x_835_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_828_, v_a_544_, v_snd_834_);
v___x_836_ = lean_unsigned_to_nat(1u);
v___x_837_ = lean_nat_add(v_a_544_, v___x_836_);
v___x_838_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_542_, v_k_827_, v___x_837_, v___x_835_);
lean_dec(v___x_837_);
v_fst_839_ = lean_ctor_get(v___x_838_, 0);
v_snd_840_ = lean_ctor_get(v___x_838_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_849_ == 0)
{
v___x_842_ = v___x_838_;
v_isShared_843_ = v_isSharedCheck_849_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_snd_840_);
lean_inc(v_fst_839_);
lean_dec(v___x_838_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_849_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_844_ = 1;
v___x_845_ = l_Lean_Expr_letE___override(v_binderName_829_, v___x_831_, v_fst_833_, v_fst_839_, v___x_844_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_845_);
v___x_847_ = v___x_842_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_snd_840_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(uint8_t v_pu_850_, lean_object* v_value_851_, lean_object* v_params_852_, lean_object* v_params_853_, lean_object* v_i_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = lean_array_get_size(v_params_853_);
v___x_858_ = lean_nat_dec_lt(v_i_854_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v_fst_860_; lean_object* v_snd_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_870_; 
lean_dec(v_i_854_);
v___x_859_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_850_, v_value_851_, v_a_855_, v_a_856_);
v_fst_860_ = lean_ctor_get(v___x_859_, 0);
v_snd_861_ = lean_ctor_get(v___x_859_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_870_ == 0)
{
v___x_863_ = v___x_859_;
v_isShared_864_ = v_isSharedCheck_870_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_snd_861_);
lean_inc(v_fst_860_);
lean_dec(v___x_859_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_870_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_865_ = lean_array_get_size(v_params_852_);
v___x_866_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg(v_params_852_, v_a_855_, v_snd_861_, v___x_865_, v_fst_860_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_866_);
v___x_868_ = v___x_863_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_snd_861_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
else
{
lean_object* v___x_871_; lean_object* v_fvarId_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_871_ = lean_array_fget_borrowed(v_params_853_, v_i_854_);
v_fvarId_872_ = lean_ctor_get(v___x_871_, 0);
v___x_873_ = lean_unsigned_to_nat(1u);
v___x_874_ = lean_nat_add(v_i_854_, v___x_873_);
lean_dec(v_i_854_);
lean_inc(v_a_855_);
lean_inc(v_fvarId_872_);
v___x_875_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_872_, v_a_855_, v_a_856_);
v___x_876_ = lean_nat_add(v_a_855_, v___x_873_);
lean_dec(v_a_855_);
v_i_854_ = v___x_874_;
v_a_855_ = v___x_876_;
v_a_856_ = v___x_875_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExprM(uint8_t v_pu_878_, lean_object* v_decl_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_params_882_; lean_object* v_value_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_params_882_ = lean_ctor_get(v_decl_879_, 2);
lean_inc_ref(v_params_882_);
v_value_883_ = lean_ctor_get(v_decl_879_, 4);
lean_inc_ref(v_value_883_);
lean_dec_ref(v_decl_879_);
v___x_884_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_880_);
v___x_885_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_878_, v_value_883_, v_params_882_, v_params_882_, v___x_884_, v_a_880_, v_a_881_);
lean_dec_ref(v_params_882_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExprM___boxed(lean_object* v_pu_886_, lean_object* v_decl_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
uint8_t v_pu_boxed_890_; lean_object* v_res_891_; 
v_pu_boxed_890_ = lean_unbox(v_pu_886_);
v_res_891_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_boxed_890_, v_decl_887_, v_a_888_, v_a_889_);
lean_dec(v_a_888_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg___boxed(lean_object* v_pu_892_, lean_object* v_value_893_, lean_object* v_params_894_, lean_object* v_params_895_, lean_object* v_i_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
uint8_t v_pu_boxed_899_; lean_object* v_res_900_; 
v_pu_boxed_899_ = lean_unbox(v_pu_892_);
v_res_900_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_boxed_899_, v_value_893_, v_params_894_, v_params_895_, v_i_896_, v_a_897_, v_a_898_);
lean_dec_ref(v_params_895_);
lean_dec_ref(v_params_894_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3___boxed(lean_object* v_pu_901_, lean_object* v_sz_902_, lean_object* v_i_903_, lean_object* v_bs_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
uint8_t v_pu_boxed_907_; size_t v_sz_boxed_908_; size_t v_i_boxed_909_; lean_object* v_res_910_; 
v_pu_boxed_907_ = lean_unbox(v_pu_901_);
v_sz_boxed_908_ = lean_unbox_usize(v_sz_902_);
lean_dec(v_sz_902_);
v_i_boxed_909_ = lean_unbox_usize(v_i_903_);
lean_dec(v_i_903_);
v_res_910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(v_pu_boxed_907_, v_sz_boxed_908_, v_i_boxed_909_, v_bs_904_, v___y_905_, v___y_906_);
lean_dec(v___y_905_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExprM___boxed(lean_object* v_pu_911_, lean_object* v_code_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
uint8_t v_pu_boxed_915_; lean_object* v_res_916_; 
v_pu_boxed_915_ = lean_unbox(v_pu_911_);
v_res_916_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_boxed_915_, v_code_912_, v_a_913_, v_a_914_);
lean_dec(v_a_913_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0(uint8_t v_pu_917_, lean_object* v_value_918_, lean_object* v_params_919_, uint8_t v_pu_920_, lean_object* v_params_921_, lean_object* v_i_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v___x_925_; 
lean_inc(v_a_923_);
v___x_925_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_917_, v_value_918_, v_params_919_, v_params_921_, v_i_922_, v_a_923_, v_a_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___boxed(lean_object* v_pu_926_, lean_object* v_value_927_, lean_object* v_params_928_, lean_object* v_pu_929_, lean_object* v_params_930_, lean_object* v_i_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
uint8_t v_pu_boxed_934_; uint8_t v_pu_boxed_935_; lean_object* v_res_936_; 
v_pu_boxed_934_ = lean_unbox(v_pu_926_);
v_pu_boxed_935_ = lean_unbox(v_pu_929_);
v_res_936_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0(v_pu_boxed_934_, v_value_927_, v_params_928_, v_pu_boxed_935_, v_params_930_, v_i_931_, v_a_932_, v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_params_930_);
lean_dec_ref(v_params_928_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2(uint8_t v_pu_937_, size_t v_sz_938_, size_t v_i_939_, lean_object* v_bs_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_938_, v_i_939_, v_bs_940_, v___y_941_, v___y_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___boxed(lean_object* v_pu_944_, lean_object* v_sz_945_, lean_object* v_i_946_, lean_object* v_bs_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
uint8_t v_pu_boxed_950_; size_t v_sz_boxed_951_; size_t v_i_boxed_952_; lean_object* v_res_953_; 
v_pu_boxed_950_ = lean_unbox(v_pu_944_);
v_sz_boxed_951_ = lean_unbox_usize(v_sz_945_);
lean_dec(v_sz_945_);
v_i_boxed_952_ = lean_unbox_usize(v_i_946_);
lean_dec(v_i_946_);
v_res_953_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2(v_pu_boxed_950_, v_sz_boxed_951_, v_i_boxed_952_, v_bs_947_, v___y_948_, v___y_949_);
lean_dec(v___y_948_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(lean_object* v_as_954_, size_t v_i_955_, size_t v_stop_956_, lean_object* v_b_957_){
_start:
{
lean_object* v___y_959_; uint8_t v___x_963_; 
v___x_963_ = lean_usize_dec_eq(v_i_955_, v_stop_956_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; 
v___x_964_ = lean_array_uget_borrowed(v_as_954_, v_i_955_);
if (lean_obj_tag(v_b_957_) == 0)
{
lean_object* v_size_965_; lean_object* v___x_966_; 
v_size_965_ = lean_ctor_get(v_b_957_, 0);
lean_inc(v_size_965_);
lean_inc(v___x_964_);
v___x_966_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_964_, v_size_965_, v_b_957_);
v___y_959_ = v___x_966_;
goto v___jp_958_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_964_);
v___x_968_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_964_, v___x_967_, v_b_957_);
v___y_959_ = v___x_968_;
goto v___jp_958_;
}
}
else
{
return v_b_957_;
}
v___jp_958_:
{
size_t v___x_960_; size_t v___x_961_; 
v___x_960_ = ((size_t)1ULL);
v___x_961_ = lean_usize_add(v_i_955_, v___x_960_);
v_i_955_ = v___x_961_;
v_b_957_ = v___y_959_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0___boxed(lean_object* v_as_969_, lean_object* v_i_970_, lean_object* v_stop_971_, lean_object* v_b_972_){
_start:
{
size_t v_i_boxed_973_; size_t v_stop_boxed_974_; lean_object* v_res_975_; 
v_i_boxed_973_ = lean_unbox_usize(v_i_970_);
lean_dec(v_i_970_);
v_stop_boxed_974_ = lean_unbox_usize(v_stop_971_);
lean_dec(v_stop_971_);
v_res_975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_as_969_, v_i_boxed_973_, v_stop_boxed_974_, v_b_972_);
lean_dec_ref(v_as_969_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExpr(uint8_t v_pu_976_, lean_object* v_code_977_, lean_object* v_xs_978_){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___y_983_; uint8_t v___x_986_; 
v___x_979_ = lean_box(1);
v___x_980_ = lean_unsigned_to_nat(0u);
v___x_981_ = lean_array_get_size(v_xs_978_);
v___x_986_ = lean_nat_dec_lt(v___x_980_, v___x_981_);
if (v___x_986_ == 0)
{
v___y_983_ = v___x_979_;
goto v___jp_982_;
}
else
{
size_t v___x_987_; size_t v___x_988_; lean_object* v___x_989_; 
v___x_987_ = ((size_t)0ULL);
v___x_988_ = lean_usize_of_nat(v___x_981_);
v___x_989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_978_, v___x_987_, v___x_988_, v___x_979_);
v___y_983_ = v___x_989_;
goto v___jp_982_;
}
v___jp_982_:
{
lean_object* v___x_984_; lean_object* v_fst_985_; 
v___x_984_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_976_, v_code_977_, v___x_981_, v___y_983_);
v_fst_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_fst_985_);
lean_dec_ref(v___x_984_);
return v_fst_985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExpr___boxed(lean_object* v_pu_990_, lean_object* v_code_991_, lean_object* v_xs_992_){
_start:
{
uint8_t v_pu_boxed_993_; lean_object* v_res_994_; 
v_pu_boxed_993_ = lean_unbox(v_pu_990_);
v_res_994_ = l_Lean_Compiler_LCNF_Code_toExpr(v_pu_boxed_993_, v_code_991_, v_xs_992_);
lean_dec_ref(v_xs_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr(uint8_t v_pu_995_, lean_object* v_decl_996_, lean_object* v_xs_997_){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___y_1002_; uint8_t v___x_1005_; 
v___x_998_ = lean_box(1);
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = lean_array_get_size(v_xs_997_);
v___x_1005_ = lean_nat_dec_lt(v___x_999_, v___x_1000_);
if (v___x_1005_ == 0)
{
v___y_1002_ = v___x_998_;
goto v___jp_1001_;
}
else
{
size_t v___x_1006_; size_t v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = ((size_t)0ULL);
v___x_1007_ = lean_usize_of_nat(v___x_1000_);
v___x_1008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_997_, v___x_1006_, v___x_1007_, v___x_998_);
v___y_1002_ = v___x_1008_;
goto v___jp_1001_;
}
v___jp_1001_:
{
lean_object* v___x_1003_; lean_object* v_fst_1004_; 
v___x_1003_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_995_, v_decl_996_, v___x_1000_, v___y_1002_);
v_fst_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_fst_1004_);
lean_dec_ref(v___x_1003_);
return v_fst_1004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr___boxed(lean_object* v_pu_1009_, lean_object* v_decl_1010_, lean_object* v_xs_1011_){
_start:
{
uint8_t v_pu_boxed_1012_; lean_object* v_res_1013_; 
v_pu_boxed_1012_ = lean_unbox(v_pu_1009_);
v_res_1013_ = l_Lean_Compiler_LCNF_FunDecl_toExpr(v_pu_boxed_1012_, v_decl_1010_, v_xs_1011_);
lean_dec_ref(v_xs_1011_);
return v_res_1013_;
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
