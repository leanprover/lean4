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
lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(uint8_t v_pu_122_, lean_object* v_params_123_, lean_object* v_offset_124_, lean_object* v_m_125_, lean_object* v_i_126_, lean_object* v_e_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg(v_params_123_, v_offset_124_, v_m_125_, v_i_126_, v_e_127_);
return v___x_128_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_122_ = stack[0].m_num;
lean_object* v_params_123_ = stack[1].m_obj;
lean_object* v_offset_124_ = stack[2].m_obj;
lean_object* v_m_125_ = stack[3].m_obj;
lean_object* v_i_126_ = stack[4].m_obj;
lean_object* v_e_127_ = stack[5].m_obj;
lean_object* v_res_129_;
v_res_129_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(v_pu_122_, v_params_123_, v_offset_124_, v_m_125_, v_i_126_, v_e_127_);
stack->m_obj
 = v_res_129_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___boxed(lean_object* v_pu_130_, lean_object* v_params_131_, lean_object* v_offset_132_, lean_object* v_m_133_, lean_object* v_i_134_, lean_object* v_e_135_){
_start:
{
uint8_t v_pu_boxed_136_; lean_object* v_res_137_; 
v_pu_boxed_136_ = lean_unbox(v_pu_130_);
v_res_137_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(v_pu_boxed_136_, v_params_131_, v_offset_132_, v_m_133_, v_i_134_, v_e_135_);
lean_dec(v_m_133_);
lean_dec_ref(v_params_131_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM___redArg(lean_object* v_params_138_, lean_object* v_e_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = lean_array_get_size(v_params_138_);
lean_inc(v_a_140_);
v___x_143_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg(v_params_138_, v_a_140_, v_a_141_, v___x_142_, v_e_139_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v_a_141_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM___redArg___boxed(lean_object* v_params_145_, lean_object* v_e_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Compiler_LCNF_ToExpr_mkLambdaM___redArg(v_params_145_, v_e_146_, v_a_147_, v_a_148_);
lean_dec(v_a_147_);
lean_dec_ref(v_params_145_);
return v_res_149_;
}
}
lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM(uint8_t v_pu_150_, lean_object* v_params_151_, lean_object* v_e_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_array_get_size(v_params_151_);
lean_inc(v_a_153_);
v___x_156_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg(v_params_151_, v_a_153_, v_a_154_, v___x_155_, v_e_152_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v_a_154_);
return v___x_157_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ToExpr_mkLambdaM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_150_ = stack[0].m_num;
lean_object* v_params_151_ = stack[1].m_obj;
lean_object* v_e_152_ = stack[2].m_obj;
lean_object* v_a_153_ = stack[3].m_obj;
lean_object* v_a_154_ = stack[4].m_obj;
lean_object* v_res_158_;
v_res_158_ = l_Lean_Compiler_LCNF_ToExpr_mkLambdaM(v_pu_150_, v_params_151_, v_e_152_, v_a_153_, v_a_154_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM___boxed(lean_object* v_pu_159_, lean_object* v_params_160_, lean_object* v_e_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
uint8_t v_pu_boxed_164_; lean_object* v_res_165_; 
v_pu_boxed_164_ = lean_unbox(v_pu_159_);
v_res_165_ = l_Lean_Compiler_LCNF_ToExpr_mkLambdaM(v_pu_boxed_164_, v_params_160_, v_e_161_, v_a_162_, v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_params_160_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExprM(lean_object* v_fvarId_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_167_, v_a_168_, v_fvarId_166_);
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v_a_168_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExprM___boxed(lean_object* v_fvarId_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExprM(v_fvarId_171_, v_a_172_, v_a_173_);
lean_dec(v_a_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_abstractM(lean_object* v_e_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_177_, v_a_176_, v_e_175_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v_a_177_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_abstractM___boxed(lean_object* v_e_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Compiler_LCNF_ToExpr_abstractM(v_e_180_, v_a_181_, v_a_182_);
lean_dec(v_a_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar___redArg(lean_object* v_fvarId_184_, lean_object* v_k_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
lean_inc(v_a_186_);
v___x_188_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_184_, v_a_186_, v_a_187_);
v___x_189_ = lean_unsigned_to_nat(1u);
v___x_190_ = lean_nat_add(v_a_186_, v___x_189_);
v___x_191_ = lean_apply_2(v_k_185_, v___x_190_, v___x_188_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar___redArg___boxed(lean_object* v_fvarId_192_, lean_object* v_k_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_Compiler_LCNF_ToExpr_withFVar___redArg(v_fvarId_192_, v_k_193_, v_a_194_, v_a_195_);
lean_dec(v_a_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar(lean_object* v_00_u03b1_197_, lean_object* v_fvarId_198_, lean_object* v_k_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
lean_inc(v_a_200_);
v___x_202_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_198_, v_a_200_, v_a_201_);
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = lean_nat_add(v_a_200_, v___x_203_);
v___x_205_ = lean_apply_2(v_k_199_, v___x_204_, v___x_202_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar___boxed(lean_object* v_00_u03b1_206_, lean_object* v_fvarId_207_, lean_object* v_k_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Compiler_LCNF_ToExpr_withFVar(v_00_u03b1_206_, v_fvarId_207_, v_k_208_, v_a_209_, v_a_210_);
lean_dec(v_a_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(lean_object* v_params_212_, lean_object* v_k_213_, lean_object* v_i_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = lean_array_get_size(v_params_212_);
v___x_218_ = lean_nat_dec_lt(v_i_214_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; 
lean_dec(v_i_214_);
v___x_219_ = lean_apply_2(v_k_213_, v_a_215_, v_a_216_);
return v___x_219_;
}
else
{
lean_object* v___x_220_; lean_object* v_fvarId_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_220_ = lean_array_fget_borrowed(v_params_212_, v_i_214_);
v_fvarId_221_ = lean_ctor_get(v___x_220_, 0);
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_add(v_i_214_, v___x_222_);
lean_dec(v_i_214_);
lean_inc(v_a_215_);
lean_inc(v_fvarId_221_);
v___x_224_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_221_, v_a_215_, v_a_216_);
v___x_225_ = lean_nat_add(v_a_215_, v___x_222_);
lean_dec(v_a_215_);
v_i_214_ = v___x_223_;
v_a_215_ = v___x_225_;
v_a_216_ = v___x_224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg___boxed(lean_object* v_params_227_, lean_object* v_k_228_, lean_object* v_i_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(v_params_227_, v_k_228_, v_i_229_, v_a_230_, v_a_231_);
lean_dec_ref(v_params_227_);
return v_res_232_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go(uint8_t v_pu_233_, lean_object* v_00_u03b1_234_, lean_object* v_params_235_, lean_object* v_k_236_, lean_object* v_i_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v___x_240_; 
lean_inc(v_a_238_);
v___x_240_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(v_params_235_, v_k_236_, v_i_237_, v_a_238_, v_a_239_);
return v___x_240_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_233_ = stack[0].m_num;
lean_object* v_params_235_ = stack[2].m_obj;
lean_object* v_k_236_ = stack[3].m_obj;
lean_object* v_i_237_ = stack[4].m_obj;
lean_object* v_a_238_ = stack[5].m_obj;
lean_object* v_a_239_ = stack[6].m_obj;
lean_object* v_res_241_;
v_res_241_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go(v_pu_233_, lean_box(0), v_params_235_, v_k_236_, v_i_237_, v_a_238_, v_a_239_);
stack->m_obj
 = v_res_241_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___boxed(lean_object* v_pu_242_, lean_object* v_00_u03b1_243_, lean_object* v_params_244_, lean_object* v_k_245_, lean_object* v_i_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
uint8_t v_pu_boxed_249_; lean_object* v_res_250_; 
v_pu_boxed_249_ = lean_unbox(v_pu_242_);
v_res_250_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go(v_pu_boxed_249_, v_00_u03b1_243_, v_params_244_, v_k_245_, v_i_246_, v_a_247_, v_a_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_params_244_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams___redArg(lean_object* v_params_251_, lean_object* v_k_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_253_);
v___x_256_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(v_params_251_, v_k_252_, v___x_255_, v_a_253_, v_a_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams___redArg___boxed(lean_object* v_params_257_, lean_object* v_k_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Compiler_LCNF_ToExpr_withParams___redArg(v_params_257_, v_k_258_, v_a_259_, v_a_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_params_257_);
return v_res_261_;
}
}
lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams(uint8_t v_pu_262_, lean_object* v_00_u03b1_263_, lean_object* v_params_264_, lean_object* v_k_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_266_);
v___x_269_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(v_params_264_, v_k_265_, v___x_268_, v_a_266_, v_a_267_);
return v___x_269_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ToExpr_withParams_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_262_ = stack[0].m_num;
lean_object* v_params_264_ = stack[2].m_obj;
lean_object* v_k_265_ = stack[3].m_obj;
lean_object* v_a_266_ = stack[4].m_obj;
lean_object* v_a_267_ = stack[5].m_obj;
lean_object* v_res_270_;
v_res_270_ = l_Lean_Compiler_LCNF_ToExpr_withParams(v_pu_262_, lean_box(0), v_params_264_, v_k_265_, v_a_266_, v_a_267_);
stack->m_obj
 = v_res_270_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams___boxed(lean_object* v_pu_271_, lean_object* v_00_u03b1_272_, lean_object* v_params_273_, lean_object* v_k_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
uint8_t v_pu_boxed_277_; lean_object* v_res_278_; 
v_pu_boxed_277_ = lean_unbox(v_pu_271_);
v_res_278_ = l_Lean_Compiler_LCNF_ToExpr_withParams(v_pu_boxed_277_, v_00_u03b1_272_, v_params_273_, v_k_274_, v_a_275_, v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_params_273_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run___redArg(lean_object* v_x_279_, lean_object* v_offset_280_, lean_object* v_levelMap_281_){
_start:
{
lean_object* v___x_282_; lean_object* v_fst_283_; 
v___x_282_ = lean_apply_2(v_x_279_, v_offset_280_, v_levelMap_281_);
v_fst_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_fst_283_);
lean_dec_ref(v___x_282_);
return v_fst_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run(lean_object* v_00_u03b1_284_, lean_object* v_x_285_, lean_object* v_offset_286_, lean_object* v_levelMap_287_){
_start:
{
lean_object* v___x_288_; lean_object* v_fst_289_; 
v___x_288_ = lean_apply_2(v_x_285_, v_offset_286_, v_levelMap_287_);
v_fst_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_fst_289_);
lean_dec_ref(v___x_288_);
return v_fst_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___lam__0(lean_object* v_x1_290_, lean_object* v_x2_291_){
_start:
{
if (lean_obj_tag(v_x1_290_) == 0)
{
lean_object* v_size_292_; lean_object* v___x_293_; 
v_size_292_ = lean_ctor_get(v_x1_290_, 0);
lean_inc(v_size_292_);
v___x_293_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_x2_291_, v_size_292_, v_x1_290_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_x2_291_, v___x_294_, v_x1_290_);
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg(lean_object* v_x_316_, lean_object* v_xs_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___y_322_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_318_ = lean_box(1);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_array_get_size(v_xs_317_);
v___x_325_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__9));
v___x_326_ = lean_nat_dec_lt(v___x_319_, v___x_320_);
if (v___x_326_ == 0)
{
lean_dec_ref(v_xs_317_);
v___y_322_ = v___x_318_;
goto v___jp_321_;
}
else
{
lean_object* v___f_327_; uint8_t v___x_328_; 
v___f_327_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10));
v___x_328_ = lean_nat_dec_le(v___x_320_, v___x_320_);
if (v___x_328_ == 0)
{
if (v___x_326_ == 0)
{
lean_dec_ref(v_xs_317_);
v___y_322_ = v___x_318_;
goto v___jp_321_;
}
else
{
size_t v___x_329_; size_t v___x_330_; lean_object* v___x_331_; 
v___x_329_ = ((size_t)0ULL);
v___x_330_ = lean_usize_of_nat(v___x_320_);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_325_, v___f_327_, v_xs_317_, v___x_329_, v___x_330_, v___x_318_);
v___y_322_ = v___x_331_;
goto v___jp_321_;
}
}
else
{
size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; 
v___x_332_ = ((size_t)0ULL);
v___x_333_ = lean_usize_of_nat(v___x_320_);
v___x_334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_325_, v___f_327_, v_xs_317_, v___x_332_, v___x_333_, v___x_318_);
v___y_322_ = v___x_334_;
goto v___jp_321_;
}
}
v___jp_321_:
{
lean_object* v___x_323_; lean_object* v_fst_324_; 
v___x_323_ = lean_apply_2(v_x_316_, v___x_320_, v___y_322_);
v_fst_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_fst_324_);
lean_dec_ref(v___x_323_);
return v_fst_324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27(lean_object* v_00_u03b1_335_, lean_object* v_x_336_, lean_object* v_xs_337_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___y_342_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_338_ = lean_box(1);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_array_get_size(v_xs_337_);
v___x_345_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__9));
v___x_346_ = lean_nat_dec_lt(v___x_339_, v___x_340_);
if (v___x_346_ == 0)
{
lean_dec_ref(v_xs_337_);
v___y_342_ = v___x_338_;
goto v___jp_341_;
}
else
{
lean_object* v___f_347_; uint8_t v___x_348_; 
v___f_347_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10));
v___x_348_ = lean_nat_dec_le(v___x_340_, v___x_340_);
if (v___x_348_ == 0)
{
if (v___x_346_ == 0)
{
lean_dec_ref(v_xs_337_);
v___y_342_ = v___x_338_;
goto v___jp_341_;
}
else
{
size_t v___x_349_; size_t v___x_350_; lean_object* v___x_351_; 
v___x_349_ = ((size_t)0ULL);
v___x_350_ = lean_usize_of_nat(v___x_340_);
v___x_351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_345_, v___f_347_, v_xs_337_, v___x_349_, v___x_350_, v___x_338_);
v___y_342_ = v___x_351_;
goto v___jp_341_;
}
}
else
{
size_t v___x_352_; size_t v___x_353_; lean_object* v___x_354_; 
v___x_352_ = ((size_t)0ULL);
v___x_353_ = lean_usize_of_nat(v___x_340_);
v___x_354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_345_, v___f_347_, v_xs_337_, v___x_352_, v___x_353_, v___x_338_);
v___y_342_ = v___x_354_;
goto v___jp_341_;
}
}
v___jp_341_:
{
lean_object* v___x_343_; lean_object* v_fst_344_; 
v___x_343_ = lean_apply_2(v_x_336_, v___x_340_, v___y_342_);
v_fst_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_fst_344_);
lean_dec_ref(v___x_343_);
return v_fst_344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(lean_object* v_arg_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = l_Lean_Compiler_LCNF_Arg_toExpr___redArg(v_arg_355_);
v___x_359_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_357_, v_a_356_, v___x_358_);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v_a_357_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg___boxed(lean_object* v_arg_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_arg_361_, v_a_362_, v_a_363_);
lean_dec(v_a_362_);
return v_res_364_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM(uint8_t v_pu_365_, lean_object* v_arg_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_arg_366_, v_a_367_, v_a_368_);
return v___x_369_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_365_ = stack[0].m_num;
lean_object* v_arg_366_ = stack[1].m_obj;
lean_object* v_a_367_ = stack[2].m_obj;
lean_object* v_a_368_ = stack[3].m_obj;
lean_object* v_res_370_;
v_res_370_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM(v_pu_365_, v_arg_366_, v_a_367_, v_a_368_);
stack->m_obj
 = v_res_370_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___boxed(lean_object* v_pu_371_, lean_object* v_arg_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
uint8_t v_pu_boxed_375_; lean_object* v_res_376_; 
v_pu_boxed_375_ = lean_unbox(v_pu_371_);
v_res_376_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM(v_pu_boxed_375_, v_arg_372_, v_a_373_, v_a_374_);
lean_dec(v_a_373_);
return v_res_376_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(size_t v_sz_377_, size_t v_i_378_, lean_object* v_bs_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
uint8_t v___x_382_; 
v___x_382_ = lean_usize_dec_lt(v_i_378_, v_sz_377_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v_bs_379_);
lean_ctor_set(v___x_383_, 1, v___y_381_);
return v___x_383_;
}
else
{
lean_object* v_v_384_; lean_object* v___x_385_; lean_object* v_fst_386_; lean_object* v_snd_387_; lean_object* v___x_388_; lean_object* v_bs_x27_389_; size_t v___x_390_; size_t v___x_391_; lean_object* v___x_392_; 
v_v_384_ = lean_array_uget_borrowed(v_bs_379_, v_i_378_);
lean_inc(v_v_384_);
v___x_385_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_v_384_, v___y_380_, v___y_381_);
v_fst_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_fst_386_);
v_snd_387_ = lean_ctor_get(v___x_385_, 1);
lean_inc(v_snd_387_);
lean_dec_ref(v___x_385_);
v___x_388_ = lean_unsigned_to_nat(0u);
v_bs_x27_389_ = lean_array_uset(v_bs_379_, v_i_378_, v___x_388_);
v___x_390_ = ((size_t)1ULL);
v___x_391_ = lean_usize_add(v_i_378_, v___x_390_);
v___x_392_ = lean_array_uset(v_bs_x27_389_, v_i_378_, v_fst_386_);
v_i_378_ = v___x_391_;
v_bs_379_ = v___x_392_;
v___y_381_ = v_snd_387_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_377_ = stack[0].m_num;
size_t v_i_378_ = stack[1].m_num;
lean_object* v_bs_379_ = stack[2].m_obj;
lean_object* v___y_380_ = stack[3].m_obj;
lean_object* v___y_381_ = stack[4].m_obj;
lean_object* v_res_394_;
v_res_394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_377_, v_i_378_, v_bs_379_, v___y_380_, v___y_381_);
stack->m_obj
 = v_res_394_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg___boxed(lean_object* v_sz_395_, lean_object* v_i_396_, lean_object* v_bs_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
size_t v_sz_boxed_400_; size_t v_i_boxed_401_; lean_object* v_res_402_; 
v_sz_boxed_400_ = lean_unbox_usize(v_sz_395_);
lean_dec(v_sz_395_);
v_i_boxed_401_ = lean_unbox_usize(v_i_396_);
lean_dec(v_i_396_);
v_res_402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_boxed_400_, v_i_boxed_401_, v_bs_397_, v___y_398_, v___y_399_);
lean_dec(v___y_398_);
return v_res_402_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(uint8_t v_pu_403_, size_t v_sz_404_, size_t v_i_405_, lean_object* v_bs_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
uint8_t v___x_409_; 
v___x_409_ = lean_usize_dec_lt(v_i_405_, v_sz_404_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; 
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v_bs_406_);
lean_ctor_set(v___x_410_, 1, v___y_408_);
return v___x_410_;
}
else
{
lean_object* v_v_411_; lean_object* v___x_412_; lean_object* v_bs_x27_413_; lean_object* v_fst_415_; lean_object* v_snd_416_; 
v_v_411_ = lean_array_uget(v_bs_406_, v_i_405_);
v___x_412_ = lean_unsigned_to_nat(0u);
v_bs_x27_413_ = lean_array_uset(v_bs_406_, v_i_405_, v___x_412_);
switch(lean_obj_tag(v_v_411_))
{
case 0:
{
lean_object* v_ctorName_421_; lean_object* v_params_422_; lean_object* v_code_423_; lean_object* v___x_424_; lean_object* v_fst_425_; lean_object* v_snd_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v_ctorName_421_ = lean_ctor_get(v_v_411_, 0);
lean_inc(v_ctorName_421_);
v_params_422_ = lean_ctor_get(v_v_411_, 1);
lean_inc_ref(v_params_422_);
v_code_423_ = lean_ctor_get(v_v_411_, 2);
lean_inc_ref(v_code_423_);
lean_dec_ref_known(v_v_411_, 3);
lean_inc(v___y_407_);
v___x_424_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_403_, v_code_423_, v_params_422_, v_params_422_, v___x_412_, v___y_407_, v___y_408_);
lean_dec_ref(v_params_422_);
v_fst_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_fst_425_);
v_snd_426_ = lean_ctor_get(v___x_424_, 1);
lean_inc(v_snd_426_);
lean_dec_ref(v___x_424_);
v___x_427_ = lean_box(0);
v___x_428_ = l_Lean_mkConst(v_ctorName_421_, v___x_427_);
v___x_429_ = l_Lean_Expr_app___override(v___x_428_, v_fst_425_);
v_fst_415_ = v___x_429_;
v_snd_416_ = v_snd_426_;
goto v___jp_414_;
}
case 1:
{
lean_object* v_info_430_; lean_object* v_code_431_; lean_object* v___x_432_; lean_object* v_fst_433_; lean_object* v_snd_434_; lean_object* v_name_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_info_430_ = lean_ctor_get(v_v_411_, 0);
lean_inc_ref(v_info_430_);
v_code_431_ = lean_ctor_get(v_v_411_, 1);
lean_inc_ref(v_code_431_);
lean_dec_ref_known(v_v_411_, 2);
v___x_432_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_403_, v_code_431_, v___y_407_, v___y_408_);
v_fst_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_fst_433_);
v_snd_434_ = lean_ctor_get(v___x_432_, 1);
lean_inc(v_snd_434_);
lean_dec_ref(v___x_432_);
v_name_435_ = lean_ctor_get(v_info_430_, 0);
lean_inc(v_name_435_);
lean_dec_ref(v_info_430_);
v___x_436_ = lean_box(0);
v___x_437_ = l_Lean_mkConst(v_name_435_, v___x_436_);
v___x_438_ = l_Lean_Expr_app___override(v___x_437_, v_fst_433_);
v_fst_415_ = v___x_438_;
v_snd_416_ = v_snd_434_;
goto v___jp_414_;
}
default: 
{
lean_object* v_code_439_; lean_object* v___x_440_; lean_object* v_fst_441_; lean_object* v_snd_442_; 
v_code_439_ = lean_ctor_get(v_v_411_, 0);
lean_inc_ref(v_code_439_);
lean_dec_ref_known(v_v_411_, 1);
v___x_440_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_403_, v_code_439_, v___y_407_, v___y_408_);
v_fst_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_fst_441_);
v_snd_442_ = lean_ctor_get(v___x_440_, 1);
lean_inc(v_snd_442_);
lean_dec_ref(v___x_440_);
v_fst_415_ = v_fst_441_;
v_snd_416_ = v_snd_442_;
goto v___jp_414_;
}
}
v___jp_414_:
{
size_t v___x_417_; size_t v___x_418_; lean_object* v___x_419_; 
v___x_417_ = ((size_t)1ULL);
v___x_418_ = lean_usize_add(v_i_405_, v___x_417_);
v___x_419_ = lean_array_uset(v_bs_x27_413_, v_i_405_, v_fst_415_);
v_i_405_ = v___x_418_;
v_bs_406_ = v___x_419_;
v___y_408_ = v_snd_416_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_403_ = stack[0].m_num;
size_t v_sz_404_ = stack[1].m_num;
size_t v_i_405_ = stack[2].m_num;
lean_object* v_bs_406_ = stack[3].m_obj;
lean_object* v___y_407_ = stack[4].m_obj;
lean_object* v___y_408_ = stack[5].m_obj;
lean_object* v_res_443_;
v_res_443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(v_pu_403_, v_sz_404_, v_i_405_, v_bs_406_, v___y_407_, v___y_408_);
stack->m_obj
 = v_res_443_;
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__2(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_box(0);
v___x_448_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__1));
v___x_449_ = l_Lean_mkConst(v___x_448_, v___x_447_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__5(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = lean_box(0);
v___x_454_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__4));
v___x_455_ = l_Lean_mkConst(v___x_454_, v___x_453_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__8(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_box(0);
v___x_460_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__7));
v___x_461_ = l_Lean_mkConst(v___x_460_, v___x_459_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_box(0);
v___x_469_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__12));
v___x_470_ = l_Lean_mkConst(v___x_469_, v___x_468_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__16(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_box(0);
v___x_475_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__15));
v___x_476_ = l_Lean_mkConst(v___x_475_, v___x_474_);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__19(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = lean_box(0);
v___x_481_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__18));
v___x_482_ = l_Lean_mkConst(v___x_481_, v___x_480_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__22(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_box(0);
v___x_487_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__21));
v___x_488_ = l_Lean_mkConst(v___x_487_, v___x_486_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__25(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_box(0);
v___x_493_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__24));
v___x_494_ = l_Lean_mkConst(v___x_493_, v___x_492_);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = lean_box(0);
v___x_501_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__28));
v___x_502_ = l_Lean_mkConst(v___x_501_, v___x_500_);
return v___x_502_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_box(0);
v___x_508_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__31));
v___x_509_ = l_Lean_mkConst(v___x_508_, v___x_507_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__35(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_513_ = lean_box(0);
v___x_514_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__34));
v___x_515_ = l_Lean_mkConst(v___x_514_, v___x_513_);
return v___x_515_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_519_ = lean_box(0);
v___x_520_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__37));
v___x_521_ = l_Lean_mkConst(v___x_520_, v___x_519_);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__43(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__42));
v___x_531_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__41));
v___x_532_ = l_Lean_mkConst(v___x_531_, v___x_530_);
return v___x_532_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__44(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__38, &l_Lean_Compiler_LCNF_Code_toExprM___closed__38_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38);
v___x_534_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__43, &l_Lean_Compiler_LCNF_Code_toExprM___closed__43_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__43);
v___x_535_ = l_Lean_Expr_app___override(v___x_534_, v___x_533_);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__47(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__42));
v___x_541_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__46));
v___x_542_ = l_Lean_mkConst(v___x_541_, v___x_540_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__50(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = lean_box(0);
v___x_547_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__49));
v___x_548_ = l_Lean_mkConst(v___x_547_, v___x_546_);
return v___x_548_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_toExprM(uint8_t v_pu_549_, lean_object* v_code_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
switch(lean_obj_tag(v_code_550_))
{
case 0:
{
lean_object* v_decl_553_; lean_object* v_k_554_; lean_object* v_fvarId_555_; lean_object* v_binderName_556_; lean_object* v_type_557_; lean_object* v_value_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v_fst_566_; lean_object* v_snd_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_576_; 
v_decl_553_ = lean_ctor_get(v_code_550_, 0);
lean_inc_ref(v_decl_553_);
v_k_554_ = lean_ctor_get(v_code_550_, 1);
lean_inc_ref(v_k_554_);
lean_dec_ref_known(v_code_550_, 2);
v_fvarId_555_ = lean_ctor_get(v_decl_553_, 0);
lean_inc(v_fvarId_555_);
v_binderName_556_ = lean_ctor_get(v_decl_553_, 1);
lean_inc(v_binderName_556_);
v_type_557_ = lean_ctor_get(v_decl_553_, 2);
lean_inc_ref(v_type_557_);
v_value_558_ = lean_ctor_get(v_decl_553_, 3);
lean_inc(v_value_558_);
lean_dec_ref(v_decl_553_);
v___x_559_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_552_, v_a_551_, v_type_557_);
v___x_560_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v_pu_549_, v_value_558_);
v___x_561_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_552_, v_a_551_, v___x_560_);
lean_inc(v_a_551_);
v___x_562_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_555_, v_a_551_, v_a_552_);
v___x_563_ = lean_unsigned_to_nat(1u);
v___x_564_ = lean_nat_add(v_a_551_, v___x_563_);
v___x_565_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_549_, v_k_554_, v___x_564_, v___x_562_);
lean_dec(v___x_564_);
v_fst_566_ = lean_ctor_get(v___x_565_, 0);
v_snd_567_ = lean_ctor_get(v___x_565_, 1);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_576_ == 0)
{
v___x_569_ = v___x_565_;
v_isShared_570_ = v_isSharedCheck_576_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_snd_567_);
lean_inc(v_fst_566_);
lean_dec(v___x_565_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_576_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_571_ = 1;
v___x_572_ = l_Lean_Expr_letE___override(v_binderName_556_, v___x_559_, v___x_561_, v_fst_566_, v___x_571_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_572_);
v___x_574_ = v___x_569_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_snd_567_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
case 3:
{
lean_object* v_fvarId_577_; lean_object* v_args_578_; lean_object* v___x_579_; size_t v_sz_580_; size_t v___x_581_; lean_object* v___x_582_; lean_object* v_fst_583_; lean_object* v_snd_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_592_; 
v_fvarId_577_ = lean_ctor_get(v_code_550_, 0);
lean_inc(v_fvarId_577_);
v_args_578_ = lean_ctor_get(v_code_550_, 1);
lean_inc_ref(v_args_578_);
lean_dec_ref_known(v_code_550_, 2);
v___x_579_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_551_, v_a_552_, v_fvarId_577_);
v_sz_580_ = lean_array_size(v_args_578_);
v___x_581_ = ((size_t)0ULL);
v___x_582_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_580_, v___x_581_, v_args_578_, v_a_551_, v_a_552_);
v_fst_583_ = lean_ctor_get(v___x_582_, 0);
v_snd_584_ = lean_ctor_get(v___x_582_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_592_ == 0)
{
v___x_586_ = v___x_582_;
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_snd_584_);
lean_inc(v_fst_583_);
lean_dec(v___x_582_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = l_Lean_mkAppN(v___x_579_, v_fst_583_);
lean_dec(v_fst_583_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_588_);
v___x_590_ = v___x_586_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_snd_584_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
case 4:
{
lean_object* v_cases_593_; lean_object* v_discr_594_; lean_object* v_alts_595_; size_t v_sz_596_; size_t v___x_597_; lean_object* v___x_598_; lean_object* v_fst_599_; lean_object* v_snd_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_614_; 
v_cases_593_ = lean_ctor_get(v_code_550_, 0);
lean_inc_ref(v_cases_593_);
lean_dec_ref_known(v_code_550_, 1);
v_discr_594_ = lean_ctor_get(v_cases_593_, 2);
lean_inc(v_discr_594_);
v_alts_595_ = lean_ctor_get(v_cases_593_, 3);
lean_inc_ref(v_alts_595_);
lean_dec_ref(v_cases_593_);
v_sz_596_ = lean_array_size(v_alts_595_);
v___x_597_ = ((size_t)0ULL);
v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(v_pu_549_, v_sz_596_, v___x_597_, v_alts_595_, v_a_551_, v_a_552_);
v_fst_599_ = lean_ctor_get(v___x_598_, 0);
v_snd_600_ = lean_ctor_get(v___x_598_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_614_ == 0)
{
v___x_602_ = v___x_598_;
v_isShared_603_ = v_isSharedCheck_614_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_snd_600_);
lean_inc(v_fst_599_);
lean_dec(v___x_598_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_614_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_604_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_551_, v_snd_600_, v_discr_594_);
v___x_605_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__2, &l_Lean_Compiler_LCNF_Code_toExprM___closed__2_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__2);
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_mk_empty_array_with_capacity(v___x_606_);
v___x_608_ = lean_array_push(v___x_607_, v___x_604_);
v___x_609_ = l_Array_append___redArg(v___x_608_, v_fst_599_);
lean_dec(v_fst_599_);
v___x_610_ = l_Lean_mkAppN(v___x_605_, v___x_609_);
lean_dec_ref(v___x_609_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_610_);
v___x_612_ = v___x_602_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_snd_600_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
case 5:
{
lean_object* v_fvarId_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_fvarId_615_ = lean_ctor_get(v_code_550_, 0);
lean_inc(v_fvarId_615_);
lean_dec_ref_known(v_code_550_, 1);
v___x_616_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_551_, v_a_552_, v_fvarId_615_);
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v_a_552_);
return v___x_617_;
}
case 6:
{
lean_object* v_type_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_type_618_ = lean_ctor_get(v_code_550_, 0);
lean_inc_ref(v_type_618_);
lean_dec_ref_known(v_code_550_, 1);
v___x_619_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_552_, v_a_551_, v_type_618_);
v___x_620_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__5, &l_Lean_Compiler_LCNF_Code_toExprM___closed__5_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__5);
v___x_621_ = l_Lean_Expr_app___override(v___x_620_, v___x_619_);
v___x_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v_a_552_);
return v___x_622_;
}
case 7:
{
lean_object* v_fvarId_623_; lean_object* v_i_624_; lean_object* v_y_625_; lean_object* v_k_626_; lean_object* v___x_627_; lean_object* v_fst_628_; lean_object* v_snd_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v_fst_635_; lean_object* v_snd_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_650_; 
v_fvarId_623_ = lean_ctor_get(v_code_550_, 0);
lean_inc_n(v_fvarId_623_, 2);
v_i_624_ = lean_ctor_get(v_code_550_, 1);
lean_inc(v_i_624_);
v_y_625_ = lean_ctor_get(v_code_550_, 2);
lean_inc(v_y_625_);
v_k_626_ = lean_ctor_get(v_code_550_, 3);
lean_inc_ref(v_k_626_);
lean_dec_ref_known(v_code_550_, 4);
v___x_627_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_y_625_, v_a_551_, v_a_552_);
v_fst_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_fst_628_);
v_snd_629_ = lean_ctor_get(v___x_627_, 1);
lean_inc(v_snd_629_);
lean_dec_ref(v___x_627_);
v___x_630_ = l_Lean_Expr_fvar___override(v_fvarId_623_);
lean_inc(v_a_551_);
v___x_631_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_623_, v_a_551_, v_snd_629_);
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = lean_nat_add(v_a_551_, v___x_632_);
v___x_634_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_549_, v_k_626_, v___x_633_, v___x_631_);
lean_dec(v___x_633_);
v_fst_635_ = lean_ctor_get(v___x_634_, 0);
v_snd_636_ = lean_ctor_get(v___x_634_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_650_ == 0)
{
v___x_638_ = v___x_634_;
v_isShared_639_ = v_isSharedCheck_650_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_snd_636_);
lean_inc(v_fst_635_);
lean_dec(v___x_634_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_650_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_640_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__8, &l_Lean_Compiler_LCNF_Code_toExprM___closed__8_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__8);
v___x_641_ = l_Lean_mkNatLit(v_i_624_);
v___x_642_ = l_Lean_mkApp3(v___x_640_, v___x_630_, v___x_641_, v_fst_628_);
v___x_643_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_644_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_645_ = 1;
v___x_646_ = l_Lean_Expr_letE___override(v___x_643_, v___x_644_, v___x_642_, v_fst_635_, v___x_645_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_646_);
v___x_648_ = v___x_638_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_snd_636_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
case 8:
{
lean_object* v_fvarId_651_; lean_object* v_i_652_; lean_object* v_y_653_; lean_object* v_k_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v_fst_660_; lean_object* v_snd_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_676_; 
v_fvarId_651_ = lean_ctor_get(v_code_550_, 0);
lean_inc_n(v_fvarId_651_, 2);
v_i_652_ = lean_ctor_get(v_code_550_, 1);
lean_inc(v_i_652_);
v_y_653_ = lean_ctor_get(v_code_550_, 2);
lean_inc(v_y_653_);
v_k_654_ = lean_ctor_get(v_code_550_, 3);
lean_inc_ref(v_k_654_);
lean_dec_ref_known(v_code_550_, 4);
v___x_655_ = l_Lean_Expr_fvar___override(v_fvarId_651_);
lean_inc(v_a_551_);
v___x_656_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_651_, v_a_551_, v_a_552_);
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_nat_add(v_a_551_, v___x_657_);
v___x_659_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_549_, v_k_654_, v___x_658_, v___x_656_);
lean_dec(v___x_658_);
v_fst_660_ = lean_ctor_get(v___x_659_, 0);
v_snd_661_ = lean_ctor_get(v___x_659_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_676_ == 0)
{
v___x_663_ = v___x_659_;
v_isShared_664_ = v_isSharedCheck_676_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_snd_661_);
lean_inc(v_fst_660_);
lean_dec(v___x_659_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_676_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v_value_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_665_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__16, &l_Lean_Compiler_LCNF_Code_toExprM___closed__16_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__16);
v___x_666_ = l_Lean_mkNatLit(v_i_652_);
v___x_667_ = l_Lean_Expr_fvar___override(v_y_653_);
v_value_668_ = l_Lean_mkApp3(v___x_665_, v___x_655_, v___x_666_, v___x_667_);
v___x_669_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_670_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_671_ = 1;
v___x_672_ = l_Lean_Expr_letE___override(v___x_669_, v___x_670_, v_value_668_, v_fst_660_, v___x_671_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_672_);
v___x_674_ = v___x_663_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_snd_661_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
case 9:
{
lean_object* v_fvarId_677_; lean_object* v_i_678_; lean_object* v_offset_679_; lean_object* v_y_680_; lean_object* v_ty_681_; lean_object* v_k_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_fst_688_; lean_object* v_snd_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_705_; 
v_fvarId_677_ = lean_ctor_get(v_code_550_, 0);
lean_inc_n(v_fvarId_677_, 2);
v_i_678_ = lean_ctor_get(v_code_550_, 1);
lean_inc(v_i_678_);
v_offset_679_ = lean_ctor_get(v_code_550_, 2);
lean_inc(v_offset_679_);
v_y_680_ = lean_ctor_get(v_code_550_, 3);
lean_inc(v_y_680_);
v_ty_681_ = lean_ctor_get(v_code_550_, 4);
lean_inc_ref(v_ty_681_);
v_k_682_ = lean_ctor_get(v_code_550_, 5);
lean_inc_ref(v_k_682_);
lean_dec_ref_known(v_code_550_, 6);
v___x_683_ = l_Lean_Expr_fvar___override(v_fvarId_677_);
lean_inc(v_a_551_);
v___x_684_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_677_, v_a_551_, v_a_552_);
v___x_685_ = lean_unsigned_to_nat(1u);
v___x_686_ = lean_nat_add(v_a_551_, v___x_685_);
v___x_687_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_549_, v_k_682_, v___x_686_, v___x_684_);
lean_dec(v___x_686_);
v_fst_688_ = lean_ctor_get(v___x_687_, 0);
v_snd_689_ = lean_ctor_get(v___x_687_, 1);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_705_ == 0)
{
v___x_691_ = v___x_687_;
v_isShared_692_ = v_isSharedCheck_705_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_snd_689_);
lean_inc(v_fst_688_);
lean_dec(v___x_687_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_705_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v_value_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_693_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__19, &l_Lean_Compiler_LCNF_Code_toExprM___closed__19_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__19);
v___x_694_ = l_Lean_mkNatLit(v_i_678_);
v___x_695_ = l_Lean_mkNatLit(v_offset_679_);
v___x_696_ = l_Lean_Expr_fvar___override(v_y_680_);
v_value_697_ = l_Lean_mkApp5(v___x_693_, v___x_683_, v___x_694_, v___x_695_, v___x_696_, v_ty_681_);
v___x_698_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_699_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_700_ = 1;
v___x_701_ = l_Lean_Expr_letE___override(v___x_698_, v___x_699_, v_value_697_, v_fst_688_, v___x_700_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_701_);
v___x_703_ = v___x_691_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_snd_689_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
case 10:
{
lean_object* v_fvarId_706_; lean_object* v_cidx_707_; lean_object* v_k_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_fst_713_; lean_object* v_snd_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_729_; 
v_fvarId_706_ = lean_ctor_get(v_code_550_, 0);
lean_inc_n(v_fvarId_706_, 2);
v_cidx_707_ = lean_ctor_get(v_code_550_, 1);
lean_inc(v_cidx_707_);
v_k_708_ = lean_ctor_get(v_code_550_, 2);
lean_inc_ref(v_k_708_);
lean_dec_ref_known(v_code_550_, 3);
lean_inc(v_a_551_);
v___x_709_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_706_, v_a_551_, v_a_552_);
v___x_710_ = lean_unsigned_to_nat(1u);
v___x_711_ = lean_nat_add(v_a_551_, v___x_710_);
v___x_712_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_549_, v_k_708_, v___x_711_, v___x_709_);
lean_dec(v___x_711_);
v_fst_713_ = lean_ctor_get(v___x_712_, 0);
v_snd_714_ = lean_ctor_get(v___x_712_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_729_ == 0)
{
v___x_716_ = v___x_712_;
v_isShared_717_ = v_isSharedCheck_729_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_snd_714_);
lean_inc(v_fst_713_);
lean_dec(v___x_712_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_729_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_718_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__22, &l_Lean_Compiler_LCNF_Code_toExprM___closed__22_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__22);
v___x_719_ = l_Lean_Expr_fvar___override(v_fvarId_706_);
v___x_720_ = l_Lean_mkNatLit(v_cidx_707_);
v___x_721_ = l_Lean_mkAppB(v___x_718_, v___x_719_, v___x_720_);
v___x_722_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_723_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_724_ = 1;
v___x_725_ = l_Lean_Expr_letE___override(v___x_722_, v___x_723_, v___x_721_, v_fst_713_, v___x_724_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_725_);
v___x_727_ = v___x_716_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_snd_714_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
case 11:
{
lean_object* v_fvarId_730_; lean_object* v_n_731_; uint8_t v_check_732_; uint8_t v_persistent_733_; lean_object* v_k_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_760_; 
v_fvarId_730_ = lean_ctor_get(v_code_550_, 0);
lean_inc_n(v_fvarId_730_, 2);
v_n_731_ = lean_ctor_get(v_code_550_, 1);
lean_inc(v_n_731_);
v_check_732_ = lean_ctor_get_uint8(v_code_550_, sizeof(void*)*3);
v_persistent_733_ = lean_ctor_get_uint8(v_code_550_, sizeof(void*)*3 + 1);
v_k_734_ = lean_ctor_get(v_code_550_, 2);
lean_inc_ref(v_k_734_);
lean_dec_ref_known(v_code_550_, 3);
v___x_735_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__25, &l_Lean_Compiler_LCNF_Code_toExprM___closed__25_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__25);
v___x_736_ = l_Lean_Expr_fvar___override(v_fvarId_730_);
v___x_737_ = l_Lean_mkNatLit(v_n_731_);
if (v_check_732_ == 0)
{
lean_object* v___x_763_; 
v___x_763_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_760_ = v___x_763_;
goto v___jp_759_;
}
else
{
lean_object* v___x_764_; 
v___x_764_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_760_ = v___x_764_;
goto v___jp_759_;
}
v___jp_738_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_fst_745_; lean_object* v_snd_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_758_; 
lean_inc(v_a_551_);
v___x_741_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_730_, v_a_551_, v_a_552_);
v___x_742_ = lean_unsigned_to_nat(1u);
v___x_743_ = lean_nat_add(v_a_551_, v___x_742_);
v___x_744_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_549_, v_k_734_, v___x_743_, v___x_741_);
lean_dec(v___x_743_);
v_fst_745_ = lean_ctor_get(v___x_744_, 0);
v_snd_746_ = lean_ctor_get(v___x_744_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_758_ == 0)
{
v___x_748_ = v___x_744_;
v_isShared_749_ = v_isSharedCheck_758_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_snd_746_);
lean_inc(v_fst_745_);
lean_dec(v___x_744_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_758_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v_value_750_; lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
lean_inc_ref(v___y_740_);
lean_inc_ref(v___y_739_);
v_value_750_ = l_Lean_mkApp4(v___x_735_, v___x_736_, v___x_737_, v___y_739_, v___y_740_);
v___x_751_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_752_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_753_ = 1;
v___x_754_ = l_Lean_Expr_letE___override(v___x_751_, v___x_752_, v_value_750_, v_fst_745_, v___x_753_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_754_);
v___x_756_ = v___x_748_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_snd_746_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
v___jp_759_:
{
if (v_persistent_733_ == 0)
{
lean_object* v___x_761_; 
v___x_761_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_739_ = v___y_760_;
v___y_740_ = v___x_761_;
goto v___jp_738_;
}
else
{
lean_object* v___x_762_; 
v___x_762_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_739_ = v___y_760_;
v___y_740_ = v___x_762_;
goto v___jp_738_;
}
}
}
case 12:
{
lean_object* v_fvarId_765_; lean_object* v_n_766_; uint8_t v_check_767_; uint8_t v_persistent_768_; lean_object* v_objs_x3f_769_; lean_object* v_k_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v_fst_775_; lean_object* v_snd_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_810_; 
v_fvarId_765_ = lean_ctor_get(v_code_550_, 0);
lean_inc_n(v_fvarId_765_, 2);
v_n_766_ = lean_ctor_get(v_code_550_, 1);
lean_inc(v_n_766_);
v_check_767_ = lean_ctor_get_uint8(v_code_550_, sizeof(void*)*4);
v_persistent_768_ = lean_ctor_get_uint8(v_code_550_, sizeof(void*)*4 + 1);
v_objs_x3f_769_ = lean_ctor_get(v_code_550_, 2);
lean_inc(v_objs_x3f_769_);
v_k_770_ = lean_ctor_get(v_code_550_, 3);
lean_inc_ref(v_k_770_);
lean_dec_ref_known(v_code_550_, 4);
lean_inc(v_a_551_);
v___x_771_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_765_, v_a_551_, v_a_552_);
v___x_772_ = lean_unsigned_to_nat(1u);
v___x_773_ = lean_nat_add(v_a_551_, v___x_772_);
v___x_774_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_549_, v_k_770_, v___x_773_, v___x_771_);
lean_dec(v___x_773_);
v_fst_775_ = lean_ctor_get(v___x_774_, 0);
v_snd_776_ = lean_ctor_get(v___x_774_, 1);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_810_ == 0)
{
v___x_778_ = v___x_774_;
v_isShared_779_ = v_isSharedCheck_810_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_snd_776_);
lean_inc(v_fst_775_);
lean_dec(v___x_774_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_810_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_805_; 
v___x_780_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__35, &l_Lean_Compiler_LCNF_Code_toExprM___closed__35_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__35);
v___x_781_ = l_Lean_Expr_fvar___override(v_fvarId_765_);
v___x_782_ = l_Lean_mkNatLit(v_n_766_);
if (v_check_767_ == 0)
{
lean_object* v___x_808_; 
v___x_808_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_805_ = v___x_808_;
goto v___jp_804_;
}
else
{
lean_object* v___x_809_; 
v___x_809_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_805_ = v___x_809_;
goto v___jp_804_;
}
v___jp_783_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
lean_inc_ref(v___y_784_);
lean_inc_ref(v___y_785_);
v___x_787_ = l_Lean_mkApp5(v___x_780_, v___x_781_, v___x_782_, v___y_785_, v___y_784_, v___y_786_);
v___x_788_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_789_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_790_ = 1;
v___x_791_ = l_Lean_Expr_letE___override(v___x_788_, v___x_789_, v___x_787_, v_fst_775_, v___x_790_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_791_);
v___x_793_ = v___x_778_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_snd_776_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
v___jp_795_:
{
lean_object* v___x_798_; 
v___x_798_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__38, &l_Lean_Compiler_LCNF_Code_toExprM___closed__38_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38);
if (lean_obj_tag(v_objs_x3f_769_) == 0)
{
lean_object* v___x_799_; 
v___x_799_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__44, &l_Lean_Compiler_LCNF_Code_toExprM___closed__44_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__44);
v___y_784_ = v___y_797_;
v___y_785_ = v___y_796_;
v___y_786_ = v___x_799_;
goto v___jp_783_;
}
else
{
lean_object* v_val_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_val_800_ = lean_ctor_get(v_objs_x3f_769_, 0);
lean_inc(v_val_800_);
lean_dec_ref_known(v_objs_x3f_769_, 1);
v___x_801_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__47, &l_Lean_Compiler_LCNF_Code_toExprM___closed__47_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__47);
v___x_802_ = l_Lean_mkNatLit(v_val_800_);
v___x_803_ = l_Lean_mkAppB(v___x_801_, v___x_798_, v___x_802_);
v___y_784_ = v___y_797_;
v___y_785_ = v___y_796_;
v___y_786_ = v___x_803_;
goto v___jp_783_;
}
}
v___jp_804_:
{
if (v_persistent_768_ == 0)
{
lean_object* v___x_806_; 
v___x_806_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_796_ = v___y_805_;
v___y_797_ = v___x_806_;
goto v___jp_795_;
}
else
{
lean_object* v___x_807_; 
v___x_807_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_796_ = v___y_805_;
v___y_797_ = v___x_807_;
goto v___jp_795_;
}
}
}
}
case 13:
{
lean_object* v_fvarId_811_; lean_object* v_k_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v_fst_817_; lean_object* v_snd_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_832_; 
v_fvarId_811_ = lean_ctor_get(v_code_550_, 0);
lean_inc_n(v_fvarId_811_, 2);
v_k_812_ = lean_ctor_get(v_code_550_, 1);
lean_inc_ref(v_k_812_);
lean_dec_ref_known(v_code_550_, 2);
lean_inc(v_a_551_);
v___x_813_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_811_, v_a_551_, v_a_552_);
v___x_814_ = lean_unsigned_to_nat(1u);
v___x_815_ = lean_nat_add(v_a_551_, v___x_814_);
v___x_816_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_549_, v_k_812_, v___x_815_, v___x_813_);
lean_dec(v___x_815_);
v_fst_817_ = lean_ctor_get(v___x_816_, 0);
v_snd_818_ = lean_ctor_get(v___x_816_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_832_ == 0)
{
v___x_820_ = v___x_816_;
v_isShared_821_ = v_isSharedCheck_832_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_snd_818_);
lean_inc(v_fst_817_);
lean_dec(v___x_816_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_832_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_822_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__50, &l_Lean_Compiler_LCNF_Code_toExprM___closed__50_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__50);
v___x_823_ = l_Lean_Expr_fvar___override(v_fvarId_811_);
v___x_824_ = l_Lean_Expr_app___override(v___x_822_, v___x_823_);
v___x_825_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_826_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_827_ = 1;
v___x_828_ = l_Lean_Expr_letE___override(v___x_825_, v___x_826_, v___x_824_, v_fst_817_, v___x_827_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_828_);
v___x_830_ = v___x_820_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_snd_818_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
default: 
{
lean_object* v_decl_833_; lean_object* v_k_834_; lean_object* v_fvarId_835_; lean_object* v_binderName_836_; lean_object* v_type_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v_fst_840_; lean_object* v_snd_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_fst_846_; lean_object* v_snd_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_856_; 
v_decl_833_ = lean_ctor_get(v_code_550_, 0);
lean_inc_ref(v_decl_833_);
v_k_834_ = lean_ctor_get(v_code_550_, 1);
lean_inc_ref(v_k_834_);
lean_dec_ref(v_code_550_);
v_fvarId_835_ = lean_ctor_get(v_decl_833_, 0);
lean_inc(v_fvarId_835_);
v_binderName_836_ = lean_ctor_get(v_decl_833_, 1);
lean_inc(v_binderName_836_);
v_type_837_ = lean_ctor_get(v_decl_833_, 3);
lean_inc_ref(v_type_837_);
v___x_838_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_552_, v_a_551_, v_type_837_);
v___x_839_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_549_, v_decl_833_, v_a_551_, v_a_552_);
v_fst_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_fst_840_);
v_snd_841_ = lean_ctor_get(v___x_839_, 1);
lean_inc(v_snd_841_);
lean_dec_ref(v___x_839_);
lean_inc(v_a_551_);
v___x_842_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_835_, v_a_551_, v_snd_841_);
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = lean_nat_add(v_a_551_, v___x_843_);
v___x_845_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_549_, v_k_834_, v___x_844_, v___x_842_);
lean_dec(v___x_844_);
v_fst_846_ = lean_ctor_get(v___x_845_, 0);
v_snd_847_ = lean_ctor_get(v___x_845_, 1);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_856_ == 0)
{
v___x_849_ = v___x_845_;
v_isShared_850_ = v_isSharedCheck_856_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_snd_847_);
lean_inc(v_fst_846_);
lean_dec(v___x_845_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_856_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_851_ = 1;
v___x_852_ = l_Lean_Expr_letE___override(v_binderName_836_, v___x_838_, v_fst_840_, v_fst_846_, v___x_851_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_852_);
v___x_854_ = v___x_849_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_snd_847_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_toExprM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_549_ = stack[0].m_num;
lean_object* v_code_550_ = stack[1].m_obj;
lean_object* v_a_551_ = stack[2].m_obj;
lean_object* v_a_552_ = stack[3].m_obj;
lean_object* v_res_857_;
v_res_857_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_549_, v_code_550_, v_a_551_, v_a_552_);
stack->m_obj
 = v_res_857_;
}
lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(uint8_t v_pu_858_, lean_object* v_value_859_, lean_object* v_params_860_, lean_object* v_params_861_, lean_object* v_i_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_865_ = lean_array_get_size(v_params_861_);
v___x_866_ = lean_nat_dec_lt(v_i_862_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v_fst_868_; lean_object* v_snd_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_878_; 
lean_dec(v_i_862_);
v___x_867_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_858_, v_value_859_, v_a_863_, v_a_864_);
v_fst_868_ = lean_ctor_get(v___x_867_, 0);
v_snd_869_ = lean_ctor_get(v___x_867_, 1);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_878_ == 0)
{
v___x_871_ = v___x_867_;
v_isShared_872_ = v_isSharedCheck_878_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_snd_869_);
lean_inc(v_fst_868_);
lean_dec(v___x_867_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_878_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_873_ = lean_array_get_size(v_params_860_);
v___x_874_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___redArg(v_params_860_, v_a_863_, v_snd_869_, v___x_873_, v_fst_868_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_874_);
v___x_876_ = v___x_871_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_snd_869_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
else
{
lean_object* v___x_879_; lean_object* v_fvarId_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_879_ = lean_array_fget_borrowed(v_params_861_, v_i_862_);
v_fvarId_880_ = lean_ctor_get(v___x_879_, 0);
v___x_881_ = lean_unsigned_to_nat(1u);
v___x_882_ = lean_nat_add(v_i_862_, v___x_881_);
lean_dec(v_i_862_);
lean_inc(v_a_863_);
lean_inc(v_fvarId_880_);
v___x_883_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_880_, v_a_863_, v_a_864_);
v___x_884_ = lean_nat_add(v_a_863_, v___x_881_);
lean_dec(v_a_863_);
v_i_862_ = v___x_882_;
v_a_863_ = v___x_884_;
v_a_864_ = v___x_883_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_858_ = stack[0].m_num;
lean_object* v_value_859_ = stack[1].m_obj;
lean_object* v_params_860_ = stack[2].m_obj;
lean_object* v_params_861_ = stack[3].m_obj;
lean_object* v_i_862_ = stack[4].m_obj;
lean_object* v_a_863_ = stack[5].m_obj;
lean_object* v_a_864_ = stack[6].m_obj;
lean_object* v_res_886_;
v_res_886_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_858_, v_value_859_, v_params_860_, v_params_861_, v_i_862_, v_a_863_, v_a_864_);
stack->m_obj
 = v_res_886_;
}
lean_object* l_Lean_Compiler_LCNF_FunDecl_toExprM(uint8_t v_pu_887_, lean_object* v_decl_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_params_891_; lean_object* v_value_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_params_891_ = lean_ctor_get(v_decl_888_, 2);
lean_inc_ref(v_params_891_);
v_value_892_ = lean_ctor_get(v_decl_888_, 4);
lean_inc_ref(v_value_892_);
lean_dec_ref(v_decl_888_);
v___x_893_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_889_);
v___x_894_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_887_, v_value_892_, v_params_891_, v_params_891_, v___x_893_, v_a_889_, v_a_890_);
lean_dec_ref(v_params_891_);
return v___x_894_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_toExprM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_887_ = stack[0].m_num;
lean_object* v_decl_888_ = stack[1].m_obj;
lean_object* v_a_889_ = stack[2].m_obj;
lean_object* v_a_890_ = stack[3].m_obj;
lean_object* v_res_895_;
v_res_895_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_887_, v_decl_888_, v_a_889_, v_a_890_);
stack->m_obj
 = v_res_895_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExprM___boxed(lean_object* v_pu_896_, lean_object* v_decl_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
uint8_t v_pu_boxed_900_; lean_object* v_res_901_; 
v_pu_boxed_900_ = lean_unbox(v_pu_896_);
v_res_901_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_boxed_900_, v_decl_897_, v_a_898_, v_a_899_);
lean_dec(v_a_898_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg___boxed(lean_object* v_pu_902_, lean_object* v_value_903_, lean_object* v_params_904_, lean_object* v_params_905_, lean_object* v_i_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
uint8_t v_pu_boxed_909_; lean_object* v_res_910_; 
v_pu_boxed_909_ = lean_unbox(v_pu_902_);
v_res_910_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_boxed_909_, v_value_903_, v_params_904_, v_params_905_, v_i_906_, v_a_907_, v_a_908_);
lean_dec_ref(v_params_905_);
lean_dec_ref(v_params_904_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3___boxed(lean_object* v_pu_911_, lean_object* v_sz_912_, lean_object* v_i_913_, lean_object* v_bs_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
uint8_t v_pu_boxed_917_; size_t v_sz_boxed_918_; size_t v_i_boxed_919_; lean_object* v_res_920_; 
v_pu_boxed_917_ = lean_unbox(v_pu_911_);
v_sz_boxed_918_ = lean_unbox_usize(v_sz_912_);
lean_dec(v_sz_912_);
v_i_boxed_919_ = lean_unbox_usize(v_i_913_);
lean_dec(v_i_913_);
v_res_920_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(v_pu_boxed_917_, v_sz_boxed_918_, v_i_boxed_919_, v_bs_914_, v___y_915_, v___y_916_);
lean_dec(v___y_915_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExprM___boxed(lean_object* v_pu_921_, lean_object* v_code_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
uint8_t v_pu_boxed_925_; lean_object* v_res_926_; 
v_pu_boxed_925_ = lean_unbox(v_pu_921_);
v_res_926_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_boxed_925_, v_code_922_, v_a_923_, v_a_924_);
lean_dec(v_a_923_);
return v_res_926_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0(uint8_t v_pu_927_, lean_object* v_value_928_, lean_object* v_params_929_, uint8_t v_pu_930_, lean_object* v_params_931_, lean_object* v_i_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v___x_935_; 
lean_inc(v_a_933_);
v___x_935_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_927_, v_value_928_, v_params_929_, v_params_931_, v_i_932_, v_a_933_, v_a_934_);
return v___x_935_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_927_ = stack[0].m_num;
lean_object* v_value_928_ = stack[1].m_obj;
lean_object* v_params_929_ = stack[2].m_obj;
uint8_t v_pu_930_ = stack[3].m_num;
lean_object* v_params_931_ = stack[4].m_obj;
lean_object* v_i_932_ = stack[5].m_obj;
lean_object* v_a_933_ = stack[6].m_obj;
lean_object* v_a_934_ = stack[7].m_obj;
lean_object* v_res_936_;
v_res_936_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0(v_pu_927_, v_value_928_, v_params_929_, v_pu_930_, v_params_931_, v_i_932_, v_a_933_, v_a_934_);
stack->m_obj
 = v_res_936_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___boxed(lean_object* v_pu_937_, lean_object* v_value_938_, lean_object* v_params_939_, lean_object* v_pu_940_, lean_object* v_params_941_, lean_object* v_i_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
uint8_t v_pu_boxed_945_; uint8_t v_pu_boxed_946_; lean_object* v_res_947_; 
v_pu_boxed_945_ = lean_unbox(v_pu_937_);
v_pu_boxed_946_ = lean_unbox(v_pu_940_);
v_res_947_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0(v_pu_boxed_945_, v_value_938_, v_params_939_, v_pu_boxed_946_, v_params_941_, v_i_942_, v_a_943_, v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_params_941_);
lean_dec_ref(v_params_939_);
return v_res_947_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2(uint8_t v_pu_948_, size_t v_sz_949_, size_t v_i_950_, lean_object* v_bs_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_949_, v_i_950_, v_bs_951_, v___y_952_, v___y_953_);
return v___x_954_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_948_ = stack[0].m_num;
size_t v_sz_949_ = stack[1].m_num;
size_t v_i_950_ = stack[2].m_num;
lean_object* v_bs_951_ = stack[3].m_obj;
lean_object* v___y_952_ = stack[4].m_obj;
lean_object* v___y_953_ = stack[5].m_obj;
lean_object* v_res_955_;
v_res_955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2(v_pu_948_, v_sz_949_, v_i_950_, v_bs_951_, v___y_952_, v___y_953_);
stack->m_obj
 = v_res_955_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___boxed(lean_object* v_pu_956_, lean_object* v_sz_957_, lean_object* v_i_958_, lean_object* v_bs_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
uint8_t v_pu_boxed_962_; size_t v_sz_boxed_963_; size_t v_i_boxed_964_; lean_object* v_res_965_; 
v_pu_boxed_962_ = lean_unbox(v_pu_956_);
v_sz_boxed_963_ = lean_unbox_usize(v_sz_957_);
lean_dec(v_sz_957_);
v_i_boxed_964_ = lean_unbox_usize(v_i_958_);
lean_dec(v_i_958_);
v_res_965_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2(v_pu_boxed_962_, v_sz_boxed_963_, v_i_boxed_964_, v_bs_959_, v___y_960_, v___y_961_);
lean_dec(v___y_960_);
return v_res_965_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(lean_object* v_as_966_, size_t v_i_967_, size_t v_stop_968_, lean_object* v_b_969_){
_start:
{
lean_object* v___y_971_; uint8_t v___x_975_; 
v___x_975_ = lean_usize_dec_eq(v_i_967_, v_stop_968_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; 
v___x_976_ = lean_array_uget_borrowed(v_as_966_, v_i_967_);
if (lean_obj_tag(v_b_969_) == 0)
{
lean_object* v_size_977_; lean_object* v___x_978_; 
v_size_977_ = lean_ctor_get(v_b_969_, 0);
lean_inc(v_size_977_);
lean_inc(v___x_976_);
v___x_978_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_976_, v_size_977_, v_b_969_);
v___y_971_ = v___x_978_;
goto v___jp_970_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_976_);
v___x_980_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_976_, v___x_979_, v_b_969_);
v___y_971_ = v___x_980_;
goto v___jp_970_;
}
}
else
{
return v_b_969_;
}
v___jp_970_:
{
size_t v___x_972_; size_t v___x_973_; 
v___x_972_ = ((size_t)1ULL);
v___x_973_ = lean_usize_add(v_i_967_, v___x_972_);
v_i_967_ = v___x_973_;
v_b_969_ = v___y_971_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_966_ = stack[0].m_obj;
size_t v_i_967_ = stack[1].m_num;
size_t v_stop_968_ = stack[2].m_num;
lean_object* v_b_969_ = stack[3].m_obj;
lean_object* v_res_981_;
v_res_981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_as_966_, v_i_967_, v_stop_968_, v_b_969_);
stack->m_obj
 = v_res_981_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0___boxed(lean_object* v_as_982_, lean_object* v_i_983_, lean_object* v_stop_984_, lean_object* v_b_985_){
_start:
{
size_t v_i_boxed_986_; size_t v_stop_boxed_987_; lean_object* v_res_988_; 
v_i_boxed_986_ = lean_unbox_usize(v_i_983_);
lean_dec(v_i_983_);
v_stop_boxed_987_ = lean_unbox_usize(v_stop_984_);
lean_dec(v_stop_984_);
v_res_988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_as_982_, v_i_boxed_986_, v_stop_boxed_987_, v_b_985_);
lean_dec_ref(v_as_982_);
return v_res_988_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_toExpr(uint8_t v_pu_989_, lean_object* v_code_990_, lean_object* v_xs_991_){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___y_996_; uint8_t v___x_999_; 
v___x_992_ = lean_box(1);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_array_get_size(v_xs_991_);
v___x_999_ = lean_nat_dec_lt(v___x_993_, v___x_994_);
if (v___x_999_ == 0)
{
v___y_996_ = v___x_992_;
goto v___jp_995_;
}
else
{
size_t v___x_1000_; size_t v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = ((size_t)0ULL);
v___x_1001_ = lean_usize_of_nat(v___x_994_);
v___x_1002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_991_, v___x_1000_, v___x_1001_, v___x_992_);
v___y_996_ = v___x_1002_;
goto v___jp_995_;
}
v___jp_995_:
{
lean_object* v___x_997_; lean_object* v_fst_998_; 
v___x_997_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_989_, v_code_990_, v___x_994_, v___y_996_);
v_fst_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_fst_998_);
lean_dec_ref(v___x_997_);
return v_fst_998_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_toExpr_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_989_ = stack[0].m_num;
lean_object* v_code_990_ = stack[1].m_obj;
lean_object* v_xs_991_ = stack[2].m_obj;
lean_object* v_res_1003_;
v_res_1003_ = l_Lean_Compiler_LCNF_Code_toExpr(v_pu_989_, v_code_990_, v_xs_991_);
stack->m_obj
 = v_res_1003_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExpr___boxed(lean_object* v_pu_1004_, lean_object* v_code_1005_, lean_object* v_xs_1006_){
_start:
{
uint8_t v_pu_boxed_1007_; lean_object* v_res_1008_; 
v_pu_boxed_1007_ = lean_unbox(v_pu_1004_);
v_res_1008_ = l_Lean_Compiler_LCNF_Code_toExpr(v_pu_boxed_1007_, v_code_1005_, v_xs_1006_);
lean_dec_ref(v_xs_1006_);
return v_res_1008_;
}
}
lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr(uint8_t v_pu_1009_, lean_object* v_decl_1010_, lean_object* v_xs_1011_){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___y_1016_; uint8_t v___x_1019_; 
v___x_1012_ = lean_box(1);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_array_get_size(v_xs_1011_);
v___x_1019_ = lean_nat_dec_lt(v___x_1013_, v___x_1014_);
if (v___x_1019_ == 0)
{
v___y_1016_ = v___x_1012_;
goto v___jp_1015_;
}
else
{
size_t v___x_1020_; size_t v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = ((size_t)0ULL);
v___x_1021_ = lean_usize_of_nat(v___x_1014_);
v___x_1022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_1011_, v___x_1020_, v___x_1021_, v___x_1012_);
v___y_1016_ = v___x_1022_;
goto v___jp_1015_;
}
v___jp_1015_:
{
lean_object* v___x_1017_; lean_object* v_fst_1018_; 
v___x_1017_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_1009_, v_decl_1010_, v___x_1014_, v___y_1016_);
v_fst_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_fst_1018_);
lean_dec_ref(v___x_1017_);
return v_fst_1018_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_toExpr_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1009_ = stack[0].m_num;
lean_object* v_decl_1010_ = stack[1].m_obj;
lean_object* v_xs_1011_ = stack[2].m_obj;
lean_object* v_res_1023_;
v_res_1023_ = l_Lean_Compiler_LCNF_FunDecl_toExpr(v_pu_1009_, v_decl_1010_, v_xs_1011_);
stack->m_obj
 = v_res_1023_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr___boxed(lean_object* v_pu_1024_, lean_object* v_decl_1025_, lean_object* v_xs_1026_){
_start:
{
uint8_t v_pu_boxed_1027_; lean_object* v_res_1028_; 
v_pu_boxed_1027_ = lean_unbox(v_pu_1024_);
v_res_1028_ = l_Lean_Compiler_LCNF_FunDecl_toExpr(v_pu_boxed_1027_, v_decl_1025_, v_xs_1026_);
lean_dec_ref(v_xs_1026_);
return v_res_1028_;
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
