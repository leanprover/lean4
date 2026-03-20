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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(uint8_t, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExprM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExprM___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_abstractM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_abstractM___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Compiler_LCNF_Code_toExprM___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "del"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__36 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__36_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toExprM___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__36_value),LEAN_SCALAR_PTR_LITERAL(59, 0, 194, 149, 61, 187, 104, 96)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__37 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toExprM___closed__37_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toExprM___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toExprM___closed__38;
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
lean_dec_ref(v___x_18_);
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
lean_dec_ref(v_e_39_);
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
lean_dec_ref(v_e_39_);
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
lean_dec_ref(v_e_39_);
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
lean_dec_ref(v_e_39_);
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
lean_dec_ref(v_e_39_);
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
lean_dec_ref(v_e_39_);
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
lean_dec_ref(v_e_39_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(uint8_t v_pu_97_, lean_object* v_params_98_, lean_object* v_offset_99_, lean_object* v_m_100_, lean_object* v_i_101_, lean_object* v_e_102_){
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
v___x_105_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v_pu_97_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___boxed(lean_object* v_pu_116_, lean_object* v_params_117_, lean_object* v_offset_118_, lean_object* v_m_119_, lean_object* v_i_120_, lean_object* v_e_121_){
_start:
{
uint8_t v_pu_boxed_122_; lean_object* v_res_123_; 
v_pu_boxed_122_ = lean_unbox(v_pu_116_);
v_res_123_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(v_pu_boxed_122_, v_params_117_, v_offset_118_, v_m_119_, v_i_120_, v_e_121_);
lean_dec(v_m_119_);
lean_dec_ref(v_params_117_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM(uint8_t v_pu_124_, lean_object* v_params_125_, lean_object* v_e_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_array_get_size(v_params_125_);
v___x_130_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(v_pu_124_, v_params_125_, v_a_127_, v_a_128_, v___x_129_, v_e_126_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v_a_128_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM___boxed(lean_object* v_pu_132_, lean_object* v_params_133_, lean_object* v_e_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
uint8_t v_pu_boxed_137_; lean_object* v_res_138_; 
v_pu_boxed_137_ = lean_unbox(v_pu_132_);
v_res_138_ = l_Lean_Compiler_LCNF_ToExpr_mkLambdaM(v_pu_boxed_137_, v_params_133_, v_e_134_, v_a_135_, v_a_136_);
lean_dec_ref(v_params_133_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExprM(lean_object* v_fvarId_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_140_, v_a_141_, v_fvarId_139_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v_a_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExprM___boxed(lean_object* v_fvarId_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExprM(v_fvarId_144_, v_a_145_, v_a_146_);
lean_dec(v_a_145_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_abstractM(lean_object* v_e_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_150_, v_a_149_, v_e_148_);
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v_a_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_abstractM___boxed(lean_object* v_e_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Compiler_LCNF_ToExpr_abstractM(v_e_153_, v_a_154_, v_a_155_);
lean_dec(v_a_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar___redArg(lean_object* v_fvarId_157_, lean_object* v_k_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
lean_inc(v_a_159_);
v___x_161_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_157_, v_a_159_, v_a_160_);
v___x_162_ = lean_unsigned_to_nat(1u);
v___x_163_ = lean_nat_add(v_a_159_, v___x_162_);
lean_dec(v_a_159_);
v___x_164_ = lean_apply_2(v_k_158_, v___x_163_, v___x_161_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar(lean_object* v_00_u03b1_165_, lean_object* v_fvarId_166_, lean_object* v_k_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
lean_inc(v_a_168_);
v___x_170_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_166_, v_a_168_, v_a_169_);
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_nat_add(v_a_168_, v___x_171_);
lean_dec(v_a_168_);
v___x_173_ = lean_apply_2(v_k_167_, v___x_172_, v___x_170_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(lean_object* v_params_174_, lean_object* v_k_175_, lean_object* v_i_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_array_get_size(v_params_174_);
v___x_180_ = lean_nat_dec_lt(v_i_176_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; 
lean_dec(v_i_176_);
v___x_181_ = lean_apply_2(v_k_175_, v_a_177_, v_a_178_);
return v___x_181_;
}
else
{
lean_object* v___x_182_; lean_object* v_fvarId_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_182_ = lean_array_fget_borrowed(v_params_174_, v_i_176_);
v_fvarId_183_ = lean_ctor_get(v___x_182_, 0);
v___x_184_ = lean_unsigned_to_nat(1u);
v___x_185_ = lean_nat_add(v_i_176_, v___x_184_);
lean_dec(v_i_176_);
lean_inc(v_a_177_);
lean_inc(v_fvarId_183_);
v___x_186_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_183_, v_a_177_, v_a_178_);
v___x_187_ = lean_nat_add(v_a_177_, v___x_184_);
lean_dec(v_a_177_);
v_i_176_ = v___x_185_;
v_a_177_ = v___x_187_;
v_a_178_ = v___x_186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg___boxed(lean_object* v_params_189_, lean_object* v_k_190_, lean_object* v_i_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(v_params_189_, v_k_190_, v_i_191_, v_a_192_, v_a_193_);
lean_dec_ref(v_params_189_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go(uint8_t v_pu_195_, lean_object* v_00_u03b1_196_, lean_object* v_params_197_, lean_object* v_k_198_, lean_object* v_i_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(v_params_197_, v_k_198_, v_i_199_, v_a_200_, v_a_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___boxed(lean_object* v_pu_203_, lean_object* v_00_u03b1_204_, lean_object* v_params_205_, lean_object* v_k_206_, lean_object* v_i_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
uint8_t v_pu_boxed_210_; lean_object* v_res_211_; 
v_pu_boxed_210_ = lean_unbox(v_pu_203_);
v_res_211_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go(v_pu_boxed_210_, v_00_u03b1_204_, v_params_205_, v_k_206_, v_i_207_, v_a_208_, v_a_209_);
lean_dec_ref(v_params_205_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams___redArg(lean_object* v_params_212_, lean_object* v_k_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(v_params_212_, v_k_213_, v___x_216_, v_a_214_, v_a_215_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams___redArg___boxed(lean_object* v_params_218_, lean_object* v_k_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Compiler_LCNF_ToExpr_withParams___redArg(v_params_218_, v_k_219_, v_a_220_, v_a_221_);
lean_dec_ref(v_params_218_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams(uint8_t v_pu_223_, lean_object* v_00_u03b1_224_, lean_object* v_params_225_, lean_object* v_k_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(v_params_225_, v_k_226_, v___x_229_, v_a_227_, v_a_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams___boxed(lean_object* v_pu_231_, lean_object* v_00_u03b1_232_, lean_object* v_params_233_, lean_object* v_k_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
uint8_t v_pu_boxed_237_; lean_object* v_res_238_; 
v_pu_boxed_237_ = lean_unbox(v_pu_231_);
v_res_238_ = l_Lean_Compiler_LCNF_ToExpr_withParams(v_pu_boxed_237_, v_00_u03b1_232_, v_params_233_, v_k_234_, v_a_235_, v_a_236_);
lean_dec_ref(v_params_233_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run___redArg(lean_object* v_x_239_, lean_object* v_offset_240_, lean_object* v_levelMap_241_){
_start:
{
lean_object* v___x_242_; lean_object* v_fst_243_; 
v___x_242_ = lean_apply_2(v_x_239_, v_offset_240_, v_levelMap_241_);
v_fst_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_fst_243_);
lean_dec_ref(v___x_242_);
return v_fst_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run(lean_object* v_00_u03b1_244_, lean_object* v_x_245_, lean_object* v_offset_246_, lean_object* v_levelMap_247_){
_start:
{
lean_object* v___x_248_; lean_object* v_fst_249_; 
v___x_248_ = lean_apply_2(v_x_245_, v_offset_246_, v_levelMap_247_);
v_fst_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_fst_249_);
lean_dec_ref(v___x_248_);
return v_fst_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___lam__0(lean_object* v_x1_250_, lean_object* v_x2_251_){
_start:
{
if (lean_obj_tag(v_x1_250_) == 0)
{
lean_object* v_size_252_; lean_object* v___x_253_; 
v_size_252_ = lean_ctor_get(v_x1_250_, 0);
lean_inc(v_size_252_);
v___x_253_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_x2_251_, v_size_252_, v_x1_250_);
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_x2_251_, v___x_254_, v_x1_250_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg(lean_object* v_x_276_, lean_object* v_xs_277_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___y_282_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_278_ = lean_box(1);
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = lean_array_get_size(v_xs_277_);
v___x_285_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__9));
v___x_286_ = lean_nat_dec_lt(v___x_279_, v___x_280_);
if (v___x_286_ == 0)
{
lean_dec_ref(v_xs_277_);
v___y_282_ = v___x_278_;
goto v___jp_281_;
}
else
{
lean_object* v___f_287_; uint8_t v___x_288_; 
v___f_287_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10));
v___x_288_ = lean_nat_dec_le(v___x_280_, v___x_280_);
if (v___x_288_ == 0)
{
if (v___x_286_ == 0)
{
lean_dec_ref(v_xs_277_);
v___y_282_ = v___x_278_;
goto v___jp_281_;
}
else
{
size_t v___x_289_; size_t v___x_290_; lean_object* v___x_291_; 
v___x_289_ = ((size_t)0ULL);
v___x_290_ = lean_usize_of_nat(v___x_280_);
v___x_291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_285_, v___f_287_, v_xs_277_, v___x_289_, v___x_290_, v___x_278_);
v___y_282_ = v___x_291_;
goto v___jp_281_;
}
}
else
{
size_t v___x_292_; size_t v___x_293_; lean_object* v___x_294_; 
v___x_292_ = ((size_t)0ULL);
v___x_293_ = lean_usize_of_nat(v___x_280_);
v___x_294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_285_, v___f_287_, v_xs_277_, v___x_292_, v___x_293_, v___x_278_);
v___y_282_ = v___x_294_;
goto v___jp_281_;
}
}
v___jp_281_:
{
lean_object* v___x_283_; lean_object* v_fst_284_; 
v___x_283_ = lean_apply_2(v_x_276_, v___x_280_, v___y_282_);
v_fst_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_fst_284_);
lean_dec_ref(v___x_283_);
return v_fst_284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27(lean_object* v_00_u03b1_295_, lean_object* v_x_296_, lean_object* v_xs_297_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___y_302_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_298_ = lean_box(1);
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = lean_array_get_size(v_xs_297_);
v___x_305_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__9));
v___x_306_ = lean_nat_dec_lt(v___x_299_, v___x_300_);
if (v___x_306_ == 0)
{
lean_dec_ref(v_xs_297_);
v___y_302_ = v___x_298_;
goto v___jp_301_;
}
else
{
lean_object* v___f_307_; uint8_t v___x_308_; 
v___f_307_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10));
v___x_308_ = lean_nat_dec_le(v___x_300_, v___x_300_);
if (v___x_308_ == 0)
{
if (v___x_306_ == 0)
{
lean_dec_ref(v_xs_297_);
v___y_302_ = v___x_298_;
goto v___jp_301_;
}
else
{
size_t v___x_309_; size_t v___x_310_; lean_object* v___x_311_; 
v___x_309_ = ((size_t)0ULL);
v___x_310_ = lean_usize_of_nat(v___x_300_);
v___x_311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_305_, v___f_307_, v_xs_297_, v___x_309_, v___x_310_, v___x_298_);
v___y_302_ = v___x_311_;
goto v___jp_301_;
}
}
else
{
size_t v___x_312_; size_t v___x_313_; lean_object* v___x_314_; 
v___x_312_ = ((size_t)0ULL);
v___x_313_ = lean_usize_of_nat(v___x_300_);
v___x_314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_305_, v___f_307_, v_xs_297_, v___x_312_, v___x_313_, v___x_298_);
v___y_302_ = v___x_314_;
goto v___jp_301_;
}
}
v___jp_301_:
{
lean_object* v___x_303_; lean_object* v_fst_304_; 
v___x_303_ = lean_apply_2(v_x_296_, v___x_300_, v___y_302_);
v_fst_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_fst_304_);
lean_dec_ref(v___x_303_);
return v_fst_304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(lean_object* v_arg_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_318_ = l_Lean_Compiler_LCNF_Arg_toExpr___redArg(v_arg_315_);
v___x_319_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_317_, v_a_316_, v___x_318_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_a_317_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg___boxed(lean_object* v_arg_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_arg_321_, v_a_322_, v_a_323_);
lean_dec(v_a_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM(uint8_t v_pu_325_, lean_object* v_arg_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_arg_326_, v_a_327_, v_a_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___boxed(lean_object* v_pu_330_, lean_object* v_arg_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
uint8_t v_pu_boxed_334_; lean_object* v_res_335_; 
v_pu_boxed_334_ = lean_unbox(v_pu_330_);
v_res_335_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM(v_pu_boxed_334_, v_arg_331_, v_a_332_, v_a_333_);
lean_dec(v_a_332_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(size_t v_sz_336_, size_t v_i_337_, lean_object* v_bs_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
uint8_t v___x_341_; 
v___x_341_ = lean_usize_dec_lt(v_i_337_, v_sz_336_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v_bs_338_);
lean_ctor_set(v___x_342_, 1, v___y_340_);
return v___x_342_;
}
else
{
lean_object* v_v_343_; lean_object* v___x_344_; lean_object* v_fst_345_; lean_object* v_snd_346_; lean_object* v___x_347_; lean_object* v_bs_x27_348_; size_t v___x_349_; size_t v___x_350_; lean_object* v___x_351_; 
v_v_343_ = lean_array_uget_borrowed(v_bs_338_, v_i_337_);
lean_inc(v_v_343_);
v___x_344_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_v_343_, v___y_339_, v___y_340_);
v_fst_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_fst_345_);
v_snd_346_ = lean_ctor_get(v___x_344_, 1);
lean_inc(v_snd_346_);
lean_dec_ref(v___x_344_);
v___x_347_ = lean_unsigned_to_nat(0u);
v_bs_x27_348_ = lean_array_uset(v_bs_338_, v_i_337_, v___x_347_);
v___x_349_ = ((size_t)1ULL);
v___x_350_ = lean_usize_add(v_i_337_, v___x_349_);
v___x_351_ = lean_array_uset(v_bs_x27_348_, v_i_337_, v_fst_345_);
v_i_337_ = v___x_350_;
v_bs_338_ = v___x_351_;
v___y_340_ = v_snd_346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg___boxed(lean_object* v_sz_353_, lean_object* v_i_354_, lean_object* v_bs_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
size_t v_sz_boxed_358_; size_t v_i_boxed_359_; lean_object* v_res_360_; 
v_sz_boxed_358_ = lean_unbox_usize(v_sz_353_);
lean_dec(v_sz_353_);
v_i_boxed_359_ = lean_unbox_usize(v_i_354_);
lean_dec(v_i_354_);
v_res_360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_boxed_358_, v_i_boxed_359_, v_bs_355_, v___y_356_, v___y_357_);
lean_dec(v___y_356_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(uint8_t v_pu_361_, size_t v_sz_362_, size_t v_i_363_, lean_object* v_bs_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
uint8_t v___x_367_; 
v___x_367_ = lean_usize_dec_lt(v_i_363_, v_sz_362_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; 
lean_dec(v___y_365_);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v_bs_364_);
lean_ctor_set(v___x_368_, 1, v___y_366_);
return v___x_368_;
}
else
{
lean_object* v_v_369_; lean_object* v___x_370_; lean_object* v_bs_x27_371_; lean_object* v_fst_373_; lean_object* v_snd_374_; 
v_v_369_ = lean_array_uget(v_bs_364_, v_i_363_);
v___x_370_ = lean_unsigned_to_nat(0u);
v_bs_x27_371_ = lean_array_uset(v_bs_364_, v_i_363_, v___x_370_);
switch(lean_obj_tag(v_v_369_))
{
case 0:
{
lean_object* v_ctorName_379_; lean_object* v_params_380_; lean_object* v_code_381_; lean_object* v___x_382_; lean_object* v_fst_383_; lean_object* v_snd_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_ctorName_379_ = lean_ctor_get(v_v_369_, 0);
lean_inc(v_ctorName_379_);
v_params_380_ = lean_ctor_get(v_v_369_, 1);
lean_inc_ref(v_params_380_);
v_code_381_ = lean_ctor_get(v_v_369_, 2);
lean_inc_ref(v_code_381_);
lean_dec_ref(v_v_369_);
lean_inc(v___y_365_);
v___x_382_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_361_, v_code_381_, v_params_380_, v_params_380_, v___x_370_, v___y_365_, v___y_366_);
lean_dec_ref(v_params_380_);
v_fst_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_fst_383_);
v_snd_384_ = lean_ctor_get(v___x_382_, 1);
lean_inc(v_snd_384_);
lean_dec_ref(v___x_382_);
v___x_385_ = lean_box(0);
v___x_386_ = l_Lean_mkConst(v_ctorName_379_, v___x_385_);
v___x_387_ = l_Lean_Expr_app___override(v___x_386_, v_fst_383_);
v_fst_373_ = v___x_387_;
v_snd_374_ = v_snd_384_;
goto v___jp_372_;
}
case 1:
{
lean_object* v_info_388_; lean_object* v_code_389_; lean_object* v___x_390_; lean_object* v_fst_391_; lean_object* v_snd_392_; lean_object* v_name_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_info_388_ = lean_ctor_get(v_v_369_, 0);
lean_inc_ref(v_info_388_);
v_code_389_ = lean_ctor_get(v_v_369_, 1);
lean_inc_ref(v_code_389_);
lean_dec_ref(v_v_369_);
lean_inc(v___y_365_);
v___x_390_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_361_, v_code_389_, v___y_365_, v___y_366_);
v_fst_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_fst_391_);
v_snd_392_ = lean_ctor_get(v___x_390_, 1);
lean_inc(v_snd_392_);
lean_dec_ref(v___x_390_);
v_name_393_ = lean_ctor_get(v_info_388_, 0);
lean_inc(v_name_393_);
lean_dec_ref(v_info_388_);
v___x_394_ = lean_box(0);
v___x_395_ = l_Lean_mkConst(v_name_393_, v___x_394_);
v___x_396_ = l_Lean_Expr_app___override(v___x_395_, v_fst_391_);
v_fst_373_ = v___x_396_;
v_snd_374_ = v_snd_392_;
goto v___jp_372_;
}
default: 
{
lean_object* v_code_397_; lean_object* v___x_398_; lean_object* v_fst_399_; lean_object* v_snd_400_; 
v_code_397_ = lean_ctor_get(v_v_369_, 0);
lean_inc_ref(v_code_397_);
lean_dec_ref(v_v_369_);
lean_inc(v___y_365_);
v___x_398_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_361_, v_code_397_, v___y_365_, v___y_366_);
v_fst_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_fst_399_);
v_snd_400_ = lean_ctor_get(v___x_398_, 1);
lean_inc(v_snd_400_);
lean_dec_ref(v___x_398_);
v_fst_373_ = v_fst_399_;
v_snd_374_ = v_snd_400_;
goto v___jp_372_;
}
}
v___jp_372_:
{
size_t v___x_375_; size_t v___x_376_; lean_object* v___x_377_; 
v___x_375_ = ((size_t)1ULL);
v___x_376_ = lean_usize_add(v_i_363_, v___x_375_);
v___x_377_ = lean_array_uset(v_bs_x27_371_, v_i_363_, v_fst_373_);
v_i_363_ = v___x_376_;
v_bs_364_ = v___x_377_;
v___y_366_ = v_snd_374_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__2(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_box(0);
v___x_405_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__1));
v___x_406_ = l_Lean_mkConst(v___x_405_, v___x_404_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__5(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = lean_box(0);
v___x_411_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__4));
v___x_412_ = l_Lean_mkConst(v___x_411_, v___x_410_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__8(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_box(0);
v___x_417_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__7));
v___x_418_ = l_Lean_mkConst(v___x_417_, v___x_416_);
return v___x_418_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_box(0);
v___x_426_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__12));
v___x_427_ = l_Lean_mkConst(v___x_426_, v___x_425_);
return v___x_427_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__16(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = lean_box(0);
v___x_432_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__15));
v___x_433_ = l_Lean_mkConst(v___x_432_, v___x_431_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__19(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_437_ = lean_box(0);
v___x_438_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__18));
v___x_439_ = l_Lean_mkConst(v___x_438_, v___x_437_);
return v___x_439_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__22(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_box(0);
v___x_444_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__21));
v___x_445_ = l_Lean_mkConst(v___x_444_, v___x_443_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__25(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_449_ = lean_box(0);
v___x_450_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__24));
v___x_451_ = l_Lean_mkConst(v___x_450_, v___x_449_);
return v___x_451_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = lean_box(0);
v___x_458_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__28));
v___x_459_ = l_Lean_mkConst(v___x_458_, v___x_457_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_464_ = lean_box(0);
v___x_465_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__31));
v___x_466_ = l_Lean_mkConst(v___x_465_, v___x_464_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__35(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_box(0);
v___x_471_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__34));
v___x_472_ = l_Lean_mkConst(v___x_471_, v___x_470_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = lean_box(0);
v___x_477_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__37));
v___x_478_ = l_Lean_mkConst(v___x_477_, v___x_476_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExprM(uint8_t v_pu_479_, lean_object* v_code_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
switch(lean_obj_tag(v_code_480_))
{
case 0:
{
lean_object* v_decl_483_; lean_object* v_k_484_; lean_object* v_fvarId_485_; lean_object* v_binderName_486_; lean_object* v_type_487_; lean_object* v_value_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_fst_496_; lean_object* v_snd_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_506_; 
v_decl_483_ = lean_ctor_get(v_code_480_, 0);
lean_inc_ref(v_decl_483_);
v_k_484_ = lean_ctor_get(v_code_480_, 1);
lean_inc_ref(v_k_484_);
lean_dec_ref(v_code_480_);
v_fvarId_485_ = lean_ctor_get(v_decl_483_, 0);
lean_inc(v_fvarId_485_);
v_binderName_486_ = lean_ctor_get(v_decl_483_, 1);
lean_inc(v_binderName_486_);
v_type_487_ = lean_ctor_get(v_decl_483_, 2);
lean_inc_ref(v_type_487_);
v_value_488_ = lean_ctor_get(v_decl_483_, 3);
lean_inc(v_value_488_);
lean_dec_ref(v_decl_483_);
v___x_489_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_482_, v_a_481_, v_type_487_);
v___x_490_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v_pu_479_, v_value_488_);
v___x_491_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_482_, v_a_481_, v___x_490_);
lean_inc(v_a_481_);
v___x_492_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_485_, v_a_481_, v_a_482_);
v___x_493_ = lean_unsigned_to_nat(1u);
v___x_494_ = lean_nat_add(v_a_481_, v___x_493_);
lean_dec(v_a_481_);
v___x_495_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_479_, v_k_484_, v___x_494_, v___x_492_);
v_fst_496_ = lean_ctor_get(v___x_495_, 0);
v_snd_497_ = lean_ctor_get(v___x_495_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_506_ == 0)
{
v___x_499_ = v___x_495_;
v_isShared_500_ = v_isSharedCheck_506_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_snd_497_);
lean_inc(v_fst_496_);
lean_dec(v___x_495_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_506_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_501_ = 1;
v___x_502_ = l_Lean_Expr_letE___override(v_binderName_486_, v___x_489_, v___x_491_, v_fst_496_, v___x_501_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_502_);
v___x_504_ = v___x_499_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_snd_497_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
case 3:
{
lean_object* v_fvarId_507_; lean_object* v_args_508_; lean_object* v___x_509_; size_t v_sz_510_; size_t v___x_511_; lean_object* v___x_512_; lean_object* v_fst_513_; lean_object* v_snd_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_522_; 
v_fvarId_507_ = lean_ctor_get(v_code_480_, 0);
lean_inc(v_fvarId_507_);
v_args_508_ = lean_ctor_get(v_code_480_, 1);
lean_inc_ref(v_args_508_);
lean_dec_ref(v_code_480_);
v___x_509_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_481_, v_a_482_, v_fvarId_507_);
v_sz_510_ = lean_array_size(v_args_508_);
v___x_511_ = ((size_t)0ULL);
v___x_512_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_510_, v___x_511_, v_args_508_, v_a_481_, v_a_482_);
lean_dec(v_a_481_);
v_fst_513_ = lean_ctor_get(v___x_512_, 0);
v_snd_514_ = lean_ctor_get(v___x_512_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_522_ == 0)
{
v___x_516_ = v___x_512_;
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_snd_514_);
lean_inc(v_fst_513_);
lean_dec(v___x_512_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = l_Lean_mkAppN(v___x_509_, v_fst_513_);
lean_dec(v_fst_513_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_518_);
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_snd_514_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
case 4:
{
lean_object* v_cases_523_; lean_object* v_discr_524_; lean_object* v_alts_525_; size_t v_sz_526_; size_t v___x_527_; lean_object* v___x_528_; lean_object* v_fst_529_; lean_object* v_snd_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_544_; 
v_cases_523_ = lean_ctor_get(v_code_480_, 0);
lean_inc_ref(v_cases_523_);
lean_dec_ref(v_code_480_);
v_discr_524_ = lean_ctor_get(v_cases_523_, 2);
lean_inc(v_discr_524_);
v_alts_525_ = lean_ctor_get(v_cases_523_, 3);
lean_inc_ref(v_alts_525_);
lean_dec_ref(v_cases_523_);
v_sz_526_ = lean_array_size(v_alts_525_);
v___x_527_ = ((size_t)0ULL);
lean_inc(v_a_481_);
v___x_528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(v_pu_479_, v_sz_526_, v___x_527_, v_alts_525_, v_a_481_, v_a_482_);
v_fst_529_ = lean_ctor_get(v___x_528_, 0);
v_snd_530_ = lean_ctor_get(v___x_528_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_544_ == 0)
{
v___x_532_ = v___x_528_;
v_isShared_533_ = v_isSharedCheck_544_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_snd_530_);
lean_inc(v_fst_529_);
lean_dec(v___x_528_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_544_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_534_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_481_, v_snd_530_, v_discr_524_);
lean_dec(v_a_481_);
v___x_535_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__2, &l_Lean_Compiler_LCNF_Code_toExprM___closed__2_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__2);
v___x_536_ = lean_unsigned_to_nat(1u);
v___x_537_ = lean_mk_empty_array_with_capacity(v___x_536_);
v___x_538_ = lean_array_push(v___x_537_, v___x_534_);
v___x_539_ = l_Array_append___redArg(v___x_538_, v_fst_529_);
lean_dec(v_fst_529_);
v___x_540_ = l_Lean_mkAppN(v___x_535_, v___x_539_);
lean_dec_ref(v___x_539_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_540_);
v___x_542_ = v___x_532_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_snd_530_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
case 5:
{
lean_object* v_fvarId_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_fvarId_545_ = lean_ctor_get(v_code_480_, 0);
lean_inc(v_fvarId_545_);
lean_dec_ref(v_code_480_);
v___x_546_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_481_, v_a_482_, v_fvarId_545_);
lean_dec(v_a_481_);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v_a_482_);
return v___x_547_;
}
case 6:
{
lean_object* v_type_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_type_548_ = lean_ctor_get(v_code_480_, 0);
lean_inc_ref(v_type_548_);
lean_dec_ref(v_code_480_);
v___x_549_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_482_, v_a_481_, v_type_548_);
lean_dec(v_a_481_);
v___x_550_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__5, &l_Lean_Compiler_LCNF_Code_toExprM___closed__5_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__5);
v___x_551_ = l_Lean_Expr_app___override(v___x_550_, v___x_549_);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v_a_482_);
return v___x_552_;
}
case 7:
{
lean_object* v_fvarId_553_; lean_object* v_i_554_; lean_object* v_y_555_; lean_object* v_k_556_; lean_object* v___x_557_; lean_object* v_fst_558_; lean_object* v_snd_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_fst_565_; lean_object* v_snd_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_580_; 
v_fvarId_553_ = lean_ctor_get(v_code_480_, 0);
lean_inc(v_fvarId_553_);
v_i_554_ = lean_ctor_get(v_code_480_, 1);
lean_inc(v_i_554_);
v_y_555_ = lean_ctor_get(v_code_480_, 2);
lean_inc(v_y_555_);
v_k_556_ = lean_ctor_get(v_code_480_, 3);
lean_inc_ref(v_k_556_);
lean_dec_ref(v_code_480_);
v___x_557_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_y_555_, v_a_481_, v_a_482_);
v_fst_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_fst_558_);
v_snd_559_ = lean_ctor_get(v___x_557_, 1);
lean_inc(v_snd_559_);
lean_dec_ref(v___x_557_);
lean_inc(v_fvarId_553_);
v___x_560_ = l_Lean_Expr_fvar___override(v_fvarId_553_);
lean_inc(v_a_481_);
v___x_561_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_553_, v_a_481_, v_snd_559_);
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_a_481_, v___x_562_);
lean_dec(v_a_481_);
v___x_564_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_479_, v_k_556_, v___x_563_, v___x_561_);
v_fst_565_ = lean_ctor_get(v___x_564_, 0);
v_snd_566_ = lean_ctor_get(v___x_564_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_580_ == 0)
{
v___x_568_ = v___x_564_;
v_isShared_569_ = v_isSharedCheck_580_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_snd_566_);
lean_inc(v_fst_565_);
lean_dec(v___x_564_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_580_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_570_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__8, &l_Lean_Compiler_LCNF_Code_toExprM___closed__8_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__8);
v___x_571_ = l_Lean_mkNatLit(v_i_554_);
v___x_572_ = l_Lean_mkApp3(v___x_570_, v___x_560_, v___x_571_, v_fst_558_);
v___x_573_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_574_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_575_ = 1;
v___x_576_ = l_Lean_Expr_letE___override(v___x_573_, v___x_574_, v___x_572_, v_fst_565_, v___x_575_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_576_);
v___x_578_ = v___x_568_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_snd_566_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
case 8:
{
lean_object* v_fvarId_581_; lean_object* v_i_582_; lean_object* v_y_583_; lean_object* v_k_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v_fst_590_; lean_object* v_snd_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_606_; 
v_fvarId_581_ = lean_ctor_get(v_code_480_, 0);
lean_inc(v_fvarId_581_);
v_i_582_ = lean_ctor_get(v_code_480_, 1);
lean_inc(v_i_582_);
v_y_583_ = lean_ctor_get(v_code_480_, 2);
lean_inc(v_y_583_);
v_k_584_ = lean_ctor_get(v_code_480_, 3);
lean_inc_ref(v_k_584_);
lean_dec_ref(v_code_480_);
lean_inc(v_fvarId_581_);
v___x_585_ = l_Lean_Expr_fvar___override(v_fvarId_581_);
lean_inc(v_a_481_);
v___x_586_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_581_, v_a_481_, v_a_482_);
v___x_587_ = lean_unsigned_to_nat(1u);
v___x_588_ = lean_nat_add(v_a_481_, v___x_587_);
lean_dec(v_a_481_);
v___x_589_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_479_, v_k_584_, v___x_588_, v___x_586_);
v_fst_590_ = lean_ctor_get(v___x_589_, 0);
v_snd_591_ = lean_ctor_get(v___x_589_, 1);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_606_ == 0)
{
v___x_593_ = v___x_589_;
v_isShared_594_ = v_isSharedCheck_606_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_snd_591_);
lean_inc(v_fst_590_);
lean_dec(v___x_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_606_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v_value_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_595_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__16, &l_Lean_Compiler_LCNF_Code_toExprM___closed__16_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__16);
v___x_596_ = l_Lean_mkNatLit(v_i_582_);
v___x_597_ = l_Lean_Expr_fvar___override(v_y_583_);
v_value_598_ = l_Lean_mkApp3(v___x_595_, v___x_585_, v___x_596_, v___x_597_);
v___x_599_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_600_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_601_ = 1;
v___x_602_ = l_Lean_Expr_letE___override(v___x_599_, v___x_600_, v_value_598_, v_fst_590_, v___x_601_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_602_);
v___x_604_ = v___x_593_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_snd_591_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
case 9:
{
lean_object* v_fvarId_607_; lean_object* v_i_608_; lean_object* v_offset_609_; lean_object* v_y_610_; lean_object* v_ty_611_; lean_object* v_k_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v_fst_618_; lean_object* v_snd_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_635_; 
v_fvarId_607_ = lean_ctor_get(v_code_480_, 0);
lean_inc(v_fvarId_607_);
v_i_608_ = lean_ctor_get(v_code_480_, 1);
lean_inc(v_i_608_);
v_offset_609_ = lean_ctor_get(v_code_480_, 2);
lean_inc(v_offset_609_);
v_y_610_ = lean_ctor_get(v_code_480_, 3);
lean_inc(v_y_610_);
v_ty_611_ = lean_ctor_get(v_code_480_, 4);
lean_inc_ref(v_ty_611_);
v_k_612_ = lean_ctor_get(v_code_480_, 5);
lean_inc_ref(v_k_612_);
lean_dec_ref(v_code_480_);
lean_inc(v_fvarId_607_);
v___x_613_ = l_Lean_Expr_fvar___override(v_fvarId_607_);
lean_inc(v_a_481_);
v___x_614_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_607_, v_a_481_, v_a_482_);
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_nat_add(v_a_481_, v___x_615_);
lean_dec(v_a_481_);
v___x_617_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_479_, v_k_612_, v___x_616_, v___x_614_);
v_fst_618_ = lean_ctor_get(v___x_617_, 0);
v_snd_619_ = lean_ctor_get(v___x_617_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_635_ == 0)
{
v___x_621_ = v___x_617_;
v_isShared_622_ = v_isSharedCheck_635_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_snd_619_);
lean_inc(v_fst_618_);
lean_dec(v___x_617_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_635_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v_value_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_623_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__19, &l_Lean_Compiler_LCNF_Code_toExprM___closed__19_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__19);
v___x_624_ = l_Lean_mkNatLit(v_i_608_);
v___x_625_ = l_Lean_mkNatLit(v_offset_609_);
v___x_626_ = l_Lean_Expr_fvar___override(v_y_610_);
v_value_627_ = l_Lean_mkApp5(v___x_623_, v___x_613_, v___x_624_, v___x_625_, v___x_626_, v_ty_611_);
v___x_628_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_629_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_630_ = 1;
v___x_631_ = l_Lean_Expr_letE___override(v___x_628_, v___x_629_, v_value_627_, v_fst_618_, v___x_630_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_631_);
v___x_633_ = v___x_621_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_snd_619_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
case 10:
{
lean_object* v_fvarId_636_; lean_object* v_cidx_637_; lean_object* v_k_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v_fst_643_; lean_object* v_snd_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_659_; 
v_fvarId_636_ = lean_ctor_get(v_code_480_, 0);
lean_inc(v_fvarId_636_);
v_cidx_637_ = lean_ctor_get(v_code_480_, 1);
lean_inc(v_cidx_637_);
v_k_638_ = lean_ctor_get(v_code_480_, 2);
lean_inc_ref(v_k_638_);
lean_dec_ref(v_code_480_);
lean_inc(v_a_481_);
lean_inc(v_fvarId_636_);
v___x_639_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_636_, v_a_481_, v_a_482_);
v___x_640_ = lean_unsigned_to_nat(1u);
v___x_641_ = lean_nat_add(v_a_481_, v___x_640_);
lean_dec(v_a_481_);
v___x_642_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_479_, v_k_638_, v___x_641_, v___x_639_);
v_fst_643_ = lean_ctor_get(v___x_642_, 0);
v_snd_644_ = lean_ctor_get(v___x_642_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_659_ == 0)
{
v___x_646_ = v___x_642_;
v_isShared_647_ = v_isSharedCheck_659_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_snd_644_);
lean_inc(v_fst_643_);
lean_dec(v___x_642_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_659_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_648_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__22, &l_Lean_Compiler_LCNF_Code_toExprM___closed__22_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__22);
v___x_649_ = l_Lean_Expr_fvar___override(v_fvarId_636_);
v___x_650_ = l_Lean_mkNatLit(v_cidx_637_);
v___x_651_ = l_Lean_mkAppB(v___x_648_, v___x_649_, v___x_650_);
v___x_652_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_653_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_654_ = 1;
v___x_655_ = l_Lean_Expr_letE___override(v___x_652_, v___x_653_, v___x_651_, v_fst_643_, v___x_654_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_655_);
v___x_657_ = v___x_646_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_snd_644_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
case 11:
{
lean_object* v_fvarId_660_; lean_object* v_n_661_; uint8_t v_check_662_; uint8_t v_persistent_663_; lean_object* v_k_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_690_; 
v_fvarId_660_ = lean_ctor_get(v_code_480_, 0);
lean_inc(v_fvarId_660_);
v_n_661_ = lean_ctor_get(v_code_480_, 1);
lean_inc(v_n_661_);
v_check_662_ = lean_ctor_get_uint8(v_code_480_, sizeof(void*)*3);
v_persistent_663_ = lean_ctor_get_uint8(v_code_480_, sizeof(void*)*3 + 1);
v_k_664_ = lean_ctor_get(v_code_480_, 2);
lean_inc_ref(v_k_664_);
lean_dec_ref(v_code_480_);
v___x_665_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__25, &l_Lean_Compiler_LCNF_Code_toExprM___closed__25_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__25);
lean_inc(v_fvarId_660_);
v___x_666_ = l_Lean_Expr_fvar___override(v_fvarId_660_);
v___x_667_ = l_Lean_mkNatLit(v_n_661_);
if (v_check_662_ == 0)
{
lean_object* v___x_693_; 
v___x_693_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_690_ = v___x_693_;
goto v___jp_689_;
}
else
{
lean_object* v___x_694_; 
v___x_694_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_690_ = v___x_694_;
goto v___jp_689_;
}
v___jp_668_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v_fst_675_; lean_object* v_snd_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_688_; 
lean_inc(v_a_481_);
v___x_671_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_660_, v_a_481_, v_a_482_);
v___x_672_ = lean_unsigned_to_nat(1u);
v___x_673_ = lean_nat_add(v_a_481_, v___x_672_);
lean_dec(v_a_481_);
v___x_674_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_479_, v_k_664_, v___x_673_, v___x_671_);
v_fst_675_ = lean_ctor_get(v___x_674_, 0);
v_snd_676_ = lean_ctor_get(v___x_674_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_688_ == 0)
{
v___x_678_ = v___x_674_;
v_isShared_679_ = v_isSharedCheck_688_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_snd_676_);
lean_inc(v_fst_675_);
lean_dec(v___x_674_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_688_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_value_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v_value_680_ = l_Lean_mkApp4(v___x_665_, v___x_666_, v___x_667_, v___y_669_, v___y_670_);
v___x_681_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_682_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_683_ = 1;
v___x_684_ = l_Lean_Expr_letE___override(v___x_681_, v___x_682_, v_value_680_, v_fst_675_, v___x_683_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_684_);
v___x_686_ = v___x_678_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_snd_676_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
v___jp_689_:
{
if (v_persistent_663_ == 0)
{
lean_object* v___x_691_; 
v___x_691_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_669_ = v___y_690_;
v___y_670_ = v___x_691_;
goto v___jp_668_;
}
else
{
lean_object* v___x_692_; 
v___x_692_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_669_ = v___y_690_;
v___y_670_ = v___x_692_;
goto v___jp_668_;
}
}
}
case 12:
{
lean_object* v_fvarId_695_; lean_object* v_n_696_; uint8_t v_check_697_; uint8_t v_persistent_698_; lean_object* v_k_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v_fst_704_; lean_object* v_snd_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_729_; 
v_fvarId_695_ = lean_ctor_get(v_code_480_, 0);
lean_inc(v_fvarId_695_);
v_n_696_ = lean_ctor_get(v_code_480_, 1);
lean_inc(v_n_696_);
v_check_697_ = lean_ctor_get_uint8(v_code_480_, sizeof(void*)*3);
v_persistent_698_ = lean_ctor_get_uint8(v_code_480_, sizeof(void*)*3 + 1);
v_k_699_ = lean_ctor_get(v_code_480_, 2);
lean_inc_ref(v_k_699_);
lean_dec_ref(v_code_480_);
lean_inc(v_a_481_);
lean_inc(v_fvarId_695_);
v___x_700_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_695_, v_a_481_, v_a_482_);
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_702_ = lean_nat_add(v_a_481_, v___x_701_);
lean_dec(v_a_481_);
v___x_703_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_479_, v_k_699_, v___x_702_, v___x_700_);
v_fst_704_ = lean_ctor_get(v___x_703_, 0);
v_snd_705_ = lean_ctor_get(v___x_703_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_729_ == 0)
{
v___x_707_ = v___x_703_;
v_isShared_708_ = v_isSharedCheck_729_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_snd_705_);
lean_inc(v_fst_704_);
lean_dec(v___x_703_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_729_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_724_; 
v___x_709_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__35, &l_Lean_Compiler_LCNF_Code_toExprM___closed__35_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__35);
v___x_710_ = l_Lean_Expr_fvar___override(v_fvarId_695_);
v___x_711_ = l_Lean_mkNatLit(v_n_696_);
if (v_check_697_ == 0)
{
lean_object* v___x_727_; 
v___x_727_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_724_ = v___x_727_;
goto v___jp_723_;
}
else
{
lean_object* v___x_728_; 
v___x_728_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_724_ = v___x_728_;
goto v___jp_723_;
}
v___jp_712_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_715_ = l_Lean_mkApp4(v___x_709_, v___x_710_, v___x_711_, v___y_713_, v___y_714_);
v___x_716_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_717_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_718_ = 1;
v___x_719_ = l_Lean_Expr_letE___override(v___x_716_, v___x_717_, v___x_715_, v_fst_704_, v___x_718_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_719_);
v___x_721_ = v___x_707_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_snd_705_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
v___jp_723_:
{
if (v_persistent_698_ == 0)
{
lean_object* v___x_725_; 
v___x_725_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_713_ = v___y_724_;
v___y_714_ = v___x_725_;
goto v___jp_712_;
}
else
{
lean_object* v___x_726_; 
v___x_726_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_713_ = v___y_724_;
v___y_714_ = v___x_726_;
goto v___jp_712_;
}
}
}
}
case 13:
{
lean_object* v_fvarId_730_; lean_object* v_k_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v_fst_736_; lean_object* v_snd_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_751_; 
v_fvarId_730_ = lean_ctor_get(v_code_480_, 0);
lean_inc(v_fvarId_730_);
v_k_731_ = lean_ctor_get(v_code_480_, 1);
lean_inc_ref(v_k_731_);
lean_dec_ref(v_code_480_);
lean_inc(v_a_481_);
lean_inc(v_fvarId_730_);
v___x_732_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_730_, v_a_481_, v_a_482_);
v___x_733_ = lean_unsigned_to_nat(1u);
v___x_734_ = lean_nat_add(v_a_481_, v___x_733_);
lean_dec(v_a_481_);
v___x_735_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_479_, v_k_731_, v___x_734_, v___x_732_);
v_fst_736_ = lean_ctor_get(v___x_735_, 0);
v_snd_737_ = lean_ctor_get(v___x_735_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_751_ == 0)
{
v___x_739_ = v___x_735_;
v_isShared_740_ = v_isSharedCheck_751_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_snd_737_);
lean_inc(v_fst_736_);
lean_dec(v___x_735_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_751_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_741_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__38, &l_Lean_Compiler_LCNF_Code_toExprM___closed__38_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38);
v___x_742_ = l_Lean_Expr_fvar___override(v_fvarId_730_);
v___x_743_ = l_Lean_Expr_app___override(v___x_741_, v___x_742_);
v___x_744_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_745_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_746_ = 1;
v___x_747_ = l_Lean_Expr_letE___override(v___x_744_, v___x_745_, v___x_743_, v_fst_736_, v___x_746_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_747_);
v___x_749_ = v___x_739_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_snd_737_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
default: 
{
lean_object* v_decl_752_; lean_object* v_k_753_; lean_object* v_fvarId_754_; lean_object* v_binderName_755_; lean_object* v_type_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_fst_759_; lean_object* v_snd_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v_fst_765_; lean_object* v_snd_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_775_; 
v_decl_752_ = lean_ctor_get(v_code_480_, 0);
lean_inc_ref(v_decl_752_);
v_k_753_ = lean_ctor_get(v_code_480_, 1);
lean_inc_ref(v_k_753_);
lean_dec_ref(v_code_480_);
v_fvarId_754_ = lean_ctor_get(v_decl_752_, 0);
lean_inc(v_fvarId_754_);
v_binderName_755_ = lean_ctor_get(v_decl_752_, 1);
lean_inc(v_binderName_755_);
v_type_756_ = lean_ctor_get(v_decl_752_, 3);
lean_inc_ref(v_type_756_);
v___x_757_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_482_, v_a_481_, v_type_756_);
lean_inc(v_a_481_);
v___x_758_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_479_, v_decl_752_, v_a_481_, v_a_482_);
v_fst_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_fst_759_);
v_snd_760_ = lean_ctor_get(v___x_758_, 1);
lean_inc(v_snd_760_);
lean_dec_ref(v___x_758_);
lean_inc(v_a_481_);
v___x_761_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_754_, v_a_481_, v_snd_760_);
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_add(v_a_481_, v___x_762_);
lean_dec(v_a_481_);
v___x_764_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_479_, v_k_753_, v___x_763_, v___x_761_);
v_fst_765_ = lean_ctor_get(v___x_764_, 0);
v_snd_766_ = lean_ctor_get(v___x_764_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_775_ == 0)
{
v___x_768_ = v___x_764_;
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_snd_766_);
lean_inc(v_fst_765_);
lean_dec(v___x_764_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
uint8_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_770_ = 1;
v___x_771_ = l_Lean_Expr_letE___override(v_binderName_755_, v___x_757_, v_fst_759_, v_fst_765_, v___x_770_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_771_);
v___x_773_ = v___x_768_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_snd_766_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(uint8_t v_pu_776_, lean_object* v_value_777_, lean_object* v_params_778_, lean_object* v_params_779_, lean_object* v_i_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_783_ = lean_array_get_size(v_params_779_);
v___x_784_ = lean_nat_dec_lt(v_i_780_, v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v_fst_786_; lean_object* v_snd_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_796_; 
lean_dec(v_i_780_);
lean_inc(v_a_781_);
v___x_785_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_776_, v_value_777_, v_a_781_, v_a_782_);
v_fst_786_ = lean_ctor_get(v___x_785_, 0);
v_snd_787_ = lean_ctor_get(v___x_785_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_796_ == 0)
{
v___x_789_ = v___x_785_;
v_isShared_790_ = v_isSharedCheck_796_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_snd_787_);
lean_inc(v_fst_786_);
lean_dec(v___x_785_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_796_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_791_ = lean_array_get_size(v_params_778_);
v___x_792_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(v_pu_776_, v_params_778_, v_a_781_, v_snd_787_, v___x_791_, v_fst_786_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_792_);
v___x_794_ = v___x_789_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_snd_787_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v___x_797_; lean_object* v_fvarId_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_797_ = lean_array_fget_borrowed(v_params_779_, v_i_780_);
v_fvarId_798_ = lean_ctor_get(v___x_797_, 0);
v___x_799_ = lean_unsigned_to_nat(1u);
v___x_800_ = lean_nat_add(v_i_780_, v___x_799_);
lean_dec(v_i_780_);
lean_inc(v_a_781_);
lean_inc(v_fvarId_798_);
v___x_801_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_798_, v_a_781_, v_a_782_);
v___x_802_ = lean_nat_add(v_a_781_, v___x_799_);
lean_dec(v_a_781_);
v_i_780_ = v___x_800_;
v_a_781_ = v___x_802_;
v_a_782_ = v___x_801_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExprM(uint8_t v_pu_804_, lean_object* v_decl_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_params_808_; lean_object* v_value_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_params_808_ = lean_ctor_get(v_decl_805_, 2);
lean_inc_ref(v_params_808_);
v_value_809_ = lean_ctor_get(v_decl_805_, 4);
lean_inc_ref(v_value_809_);
lean_dec_ref(v_decl_805_);
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_804_, v_value_809_, v_params_808_, v_params_808_, v___x_810_, v_a_806_, v_a_807_);
lean_dec_ref(v_params_808_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExprM___boxed(lean_object* v_pu_812_, lean_object* v_decl_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
uint8_t v_pu_boxed_816_; lean_object* v_res_817_; 
v_pu_boxed_816_ = lean_unbox(v_pu_812_);
v_res_817_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_boxed_816_, v_decl_813_, v_a_814_, v_a_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg___boxed(lean_object* v_pu_818_, lean_object* v_value_819_, lean_object* v_params_820_, lean_object* v_params_821_, lean_object* v_i_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
uint8_t v_pu_boxed_825_; lean_object* v_res_826_; 
v_pu_boxed_825_ = lean_unbox(v_pu_818_);
v_res_826_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_boxed_825_, v_value_819_, v_params_820_, v_params_821_, v_i_822_, v_a_823_, v_a_824_);
lean_dec_ref(v_params_821_);
lean_dec_ref(v_params_820_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3___boxed(lean_object* v_pu_827_, lean_object* v_sz_828_, lean_object* v_i_829_, lean_object* v_bs_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
uint8_t v_pu_boxed_833_; size_t v_sz_boxed_834_; size_t v_i_boxed_835_; lean_object* v_res_836_; 
v_pu_boxed_833_ = lean_unbox(v_pu_827_);
v_sz_boxed_834_ = lean_unbox_usize(v_sz_828_);
lean_dec(v_sz_828_);
v_i_boxed_835_ = lean_unbox_usize(v_i_829_);
lean_dec(v_i_829_);
v_res_836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(v_pu_boxed_833_, v_sz_boxed_834_, v_i_boxed_835_, v_bs_830_, v___y_831_, v___y_832_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExprM___boxed(lean_object* v_pu_837_, lean_object* v_code_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
uint8_t v_pu_boxed_841_; lean_object* v_res_842_; 
v_pu_boxed_841_ = lean_unbox(v_pu_837_);
v_res_842_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_boxed_841_, v_code_838_, v_a_839_, v_a_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0(uint8_t v_pu_843_, lean_object* v_value_844_, lean_object* v_params_845_, uint8_t v_pu_846_, lean_object* v_params_847_, lean_object* v_i_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_843_, v_value_844_, v_params_845_, v_params_847_, v_i_848_, v_a_849_, v_a_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___boxed(lean_object* v_pu_852_, lean_object* v_value_853_, lean_object* v_params_854_, lean_object* v_pu_855_, lean_object* v_params_856_, lean_object* v_i_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
uint8_t v_pu_boxed_860_; uint8_t v_pu_boxed_861_; lean_object* v_res_862_; 
v_pu_boxed_860_ = lean_unbox(v_pu_852_);
v_pu_boxed_861_ = lean_unbox(v_pu_855_);
v_res_862_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0(v_pu_boxed_860_, v_value_853_, v_params_854_, v_pu_boxed_861_, v_params_856_, v_i_857_, v_a_858_, v_a_859_);
lean_dec_ref(v_params_856_);
lean_dec_ref(v_params_854_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2(uint8_t v_pu_863_, size_t v_sz_864_, size_t v_i_865_, lean_object* v_bs_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_864_, v_i_865_, v_bs_866_, v___y_867_, v___y_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___boxed(lean_object* v_pu_870_, lean_object* v_sz_871_, lean_object* v_i_872_, lean_object* v_bs_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
uint8_t v_pu_boxed_876_; size_t v_sz_boxed_877_; size_t v_i_boxed_878_; lean_object* v_res_879_; 
v_pu_boxed_876_ = lean_unbox(v_pu_870_);
v_sz_boxed_877_ = lean_unbox_usize(v_sz_871_);
lean_dec(v_sz_871_);
v_i_boxed_878_ = lean_unbox_usize(v_i_872_);
lean_dec(v_i_872_);
v_res_879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2(v_pu_boxed_876_, v_sz_boxed_877_, v_i_boxed_878_, v_bs_873_, v___y_874_, v___y_875_);
lean_dec(v___y_874_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(lean_object* v_as_880_, size_t v_i_881_, size_t v_stop_882_, lean_object* v_b_883_){
_start:
{
lean_object* v___y_885_; uint8_t v___x_889_; 
v___x_889_ = lean_usize_dec_eq(v_i_881_, v_stop_882_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
v___x_890_ = lean_array_uget_borrowed(v_as_880_, v_i_881_);
if (lean_obj_tag(v_b_883_) == 0)
{
lean_object* v_size_891_; lean_object* v___x_892_; 
v_size_891_ = lean_ctor_get(v_b_883_, 0);
lean_inc(v_size_891_);
lean_inc(v___x_890_);
v___x_892_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v___x_890_, v_size_891_, v_b_883_);
v___y_885_ = v___x_892_;
goto v___jp_884_;
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_890_);
v___x_894_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v___x_890_, v___x_893_, v_b_883_);
v___y_885_ = v___x_894_;
goto v___jp_884_;
}
}
else
{
return v_b_883_;
}
v___jp_884_:
{
size_t v___x_886_; size_t v___x_887_; 
v___x_886_ = ((size_t)1ULL);
v___x_887_ = lean_usize_add(v_i_881_, v___x_886_);
v_i_881_ = v___x_887_;
v_b_883_ = v___y_885_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0___boxed(lean_object* v_as_895_, lean_object* v_i_896_, lean_object* v_stop_897_, lean_object* v_b_898_){
_start:
{
size_t v_i_boxed_899_; size_t v_stop_boxed_900_; lean_object* v_res_901_; 
v_i_boxed_899_ = lean_unbox_usize(v_i_896_);
lean_dec(v_i_896_);
v_stop_boxed_900_ = lean_unbox_usize(v_stop_897_);
lean_dec(v_stop_897_);
v_res_901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_as_895_, v_i_boxed_899_, v_stop_boxed_900_, v_b_898_);
lean_dec_ref(v_as_895_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExpr(uint8_t v_pu_902_, lean_object* v_code_903_, lean_object* v_xs_904_){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___y_909_; uint8_t v___x_912_; 
v___x_905_ = lean_box(1);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_array_get_size(v_xs_904_);
v___x_912_ = lean_nat_dec_lt(v___x_906_, v___x_907_);
if (v___x_912_ == 0)
{
v___y_909_ = v___x_905_;
goto v___jp_908_;
}
else
{
uint8_t v___x_913_; 
v___x_913_ = lean_nat_dec_le(v___x_907_, v___x_907_);
if (v___x_913_ == 0)
{
if (v___x_912_ == 0)
{
v___y_909_ = v___x_905_;
goto v___jp_908_;
}
else
{
size_t v___x_914_; size_t v___x_915_; lean_object* v___x_916_; 
v___x_914_ = ((size_t)0ULL);
v___x_915_ = lean_usize_of_nat(v___x_907_);
v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_904_, v___x_914_, v___x_915_, v___x_905_);
v___y_909_ = v___x_916_;
goto v___jp_908_;
}
}
else
{
size_t v___x_917_; size_t v___x_918_; lean_object* v___x_919_; 
v___x_917_ = ((size_t)0ULL);
v___x_918_ = lean_usize_of_nat(v___x_907_);
v___x_919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_904_, v___x_917_, v___x_918_, v___x_905_);
v___y_909_ = v___x_919_;
goto v___jp_908_;
}
}
v___jp_908_:
{
lean_object* v___x_910_; lean_object* v_fst_911_; 
v___x_910_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_902_, v_code_903_, v___x_907_, v___y_909_);
v_fst_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_fst_911_);
lean_dec_ref(v___x_910_);
return v_fst_911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExpr___boxed(lean_object* v_pu_920_, lean_object* v_code_921_, lean_object* v_xs_922_){
_start:
{
uint8_t v_pu_boxed_923_; lean_object* v_res_924_; 
v_pu_boxed_923_ = lean_unbox(v_pu_920_);
v_res_924_ = l_Lean_Compiler_LCNF_Code_toExpr(v_pu_boxed_923_, v_code_921_, v_xs_922_);
lean_dec_ref(v_xs_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr(uint8_t v_pu_925_, lean_object* v_decl_926_, lean_object* v_xs_927_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___y_932_; uint8_t v___x_935_; 
v___x_928_ = lean_box(1);
v___x_929_ = lean_unsigned_to_nat(0u);
v___x_930_ = lean_array_get_size(v_xs_927_);
v___x_935_ = lean_nat_dec_lt(v___x_929_, v___x_930_);
if (v___x_935_ == 0)
{
v___y_932_ = v___x_928_;
goto v___jp_931_;
}
else
{
uint8_t v___x_936_; 
v___x_936_ = lean_nat_dec_le(v___x_930_, v___x_930_);
if (v___x_936_ == 0)
{
if (v___x_935_ == 0)
{
v___y_932_ = v___x_928_;
goto v___jp_931_;
}
else
{
size_t v___x_937_; size_t v___x_938_; lean_object* v___x_939_; 
v___x_937_ = ((size_t)0ULL);
v___x_938_ = lean_usize_of_nat(v___x_930_);
v___x_939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_927_, v___x_937_, v___x_938_, v___x_928_);
v___y_932_ = v___x_939_;
goto v___jp_931_;
}
}
else
{
size_t v___x_940_; size_t v___x_941_; lean_object* v___x_942_; 
v___x_940_ = ((size_t)0ULL);
v___x_941_ = lean_usize_of_nat(v___x_930_);
v___x_942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_927_, v___x_940_, v___x_941_, v___x_928_);
v___y_932_ = v___x_942_;
goto v___jp_931_;
}
}
v___jp_931_:
{
lean_object* v___x_933_; lean_object* v_fst_934_; 
v___x_933_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_925_, v_decl_926_, v___x_930_, v___y_932_);
v_fst_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_fst_934_);
lean_dec_ref(v___x_933_);
return v_fst_934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr___boxed(lean_object* v_pu_943_, lean_object* v_decl_944_, lean_object* v_xs_945_){
_start:
{
uint8_t v_pu_boxed_946_; lean_object* v_res_947_; 
v_pu_boxed_946_ = lean_unbox(v_pu_943_);
v_res_947_ = l_Lean_Compiler_LCNF_FunDecl_toExpr(v_pu_boxed_946_, v_decl_944_, v_xs_945_);
lean_dec_ref(v_xs_945_);
return v_res_947_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
