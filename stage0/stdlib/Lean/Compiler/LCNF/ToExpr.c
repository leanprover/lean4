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
lean_inc(v_a_127_);
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
lean_dec(v_a_135_);
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
v___x_161_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_157_, v_a_159_, v_a_160_);
v___x_162_ = lean_unsigned_to_nat(1u);
v___x_163_ = lean_nat_add(v_a_159_, v___x_162_);
v___x_164_ = lean_apply_2(v_k_158_, v___x_163_, v___x_161_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar___redArg___boxed(lean_object* v_fvarId_165_, lean_object* v_k_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Compiler_LCNF_ToExpr_withFVar___redArg(v_fvarId_165_, v_k_166_, v_a_167_, v_a_168_);
lean_dec(v_a_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar(lean_object* v_00_u03b1_170_, lean_object* v_fvarId_171_, lean_object* v_k_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
lean_inc(v_a_173_);
v___x_175_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_171_, v_a_173_, v_a_174_);
v___x_176_ = lean_unsigned_to_nat(1u);
v___x_177_ = lean_nat_add(v_a_173_, v___x_176_);
v___x_178_ = lean_apply_2(v_k_172_, v___x_177_, v___x_175_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withFVar___boxed(lean_object* v_00_u03b1_179_, lean_object* v_fvarId_180_, lean_object* v_k_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Compiler_LCNF_ToExpr_withFVar(v_00_u03b1_179_, v_fvarId_180_, v_k_181_, v_a_182_, v_a_183_);
lean_dec(v_a_182_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(lean_object* v_params_185_, lean_object* v_k_186_, lean_object* v_i_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_190_ = lean_array_get_size(v_params_185_);
v___x_191_ = lean_nat_dec_lt(v_i_187_, v___x_190_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; 
lean_dec(v_i_187_);
v___x_192_ = lean_apply_2(v_k_186_, v_a_188_, v_a_189_);
return v___x_192_;
}
else
{
lean_object* v___x_193_; lean_object* v_fvarId_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_193_ = lean_array_fget_borrowed(v_params_185_, v_i_187_);
v_fvarId_194_ = lean_ctor_get(v___x_193_, 0);
v___x_195_ = lean_unsigned_to_nat(1u);
v___x_196_ = lean_nat_add(v_i_187_, v___x_195_);
lean_dec(v_i_187_);
lean_inc(v_a_188_);
lean_inc(v_fvarId_194_);
v___x_197_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_194_, v_a_188_, v_a_189_);
v___x_198_ = lean_nat_add(v_a_188_, v___x_195_);
lean_dec(v_a_188_);
v_i_187_ = v___x_196_;
v_a_188_ = v___x_198_;
v_a_189_ = v___x_197_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg___boxed(lean_object* v_params_200_, lean_object* v_k_201_, lean_object* v_i_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(v_params_200_, v_k_201_, v_i_202_, v_a_203_, v_a_204_);
lean_dec_ref(v_params_200_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go(uint8_t v_pu_206_, lean_object* v_00_u03b1_207_, lean_object* v_params_208_, lean_object* v_k_209_, lean_object* v_i_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v___x_213_; 
lean_inc(v_a_211_);
v___x_213_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(v_params_208_, v_k_209_, v_i_210_, v_a_211_, v_a_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___boxed(lean_object* v_pu_214_, lean_object* v_00_u03b1_215_, lean_object* v_params_216_, lean_object* v_k_217_, lean_object* v_i_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
uint8_t v_pu_boxed_221_; lean_object* v_res_222_; 
v_pu_boxed_221_ = lean_unbox(v_pu_214_);
v_res_222_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go(v_pu_boxed_221_, v_00_u03b1_215_, v_params_216_, v_k_217_, v_i_218_, v_a_219_, v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_params_216_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams___redArg(lean_object* v_params_223_, lean_object* v_k_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_225_);
v___x_228_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(v_params_223_, v_k_224_, v___x_227_, v_a_225_, v_a_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams___redArg___boxed(lean_object* v_params_229_, lean_object* v_k_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Compiler_LCNF_ToExpr_withParams___redArg(v_params_229_, v_k_230_, v_a_231_, v_a_232_);
lean_dec(v_a_231_);
lean_dec_ref(v_params_229_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams(uint8_t v_pu_234_, lean_object* v_00_u03b1_235_, lean_object* v_params_236_, lean_object* v_k_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_238_);
v___x_241_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(v_params_236_, v_k_237_, v___x_240_, v_a_238_, v_a_239_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams___boxed(lean_object* v_pu_242_, lean_object* v_00_u03b1_243_, lean_object* v_params_244_, lean_object* v_k_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
uint8_t v_pu_boxed_248_; lean_object* v_res_249_; 
v_pu_boxed_248_ = lean_unbox(v_pu_242_);
v_res_249_ = l_Lean_Compiler_LCNF_ToExpr_withParams(v_pu_boxed_248_, v_00_u03b1_243_, v_params_244_, v_k_245_, v_a_246_, v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_params_244_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run___redArg(lean_object* v_x_250_, lean_object* v_offset_251_, lean_object* v_levelMap_252_){
_start:
{
lean_object* v___x_253_; lean_object* v_fst_254_; 
v___x_253_ = lean_apply_2(v_x_250_, v_offset_251_, v_levelMap_252_);
v_fst_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_fst_254_);
lean_dec_ref(v___x_253_);
return v_fst_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run(lean_object* v_00_u03b1_255_, lean_object* v_x_256_, lean_object* v_offset_257_, lean_object* v_levelMap_258_){
_start:
{
lean_object* v___x_259_; lean_object* v_fst_260_; 
v___x_259_ = lean_apply_2(v_x_256_, v_offset_257_, v_levelMap_258_);
v_fst_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_fst_260_);
lean_dec_ref(v___x_259_);
return v_fst_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___lam__0(lean_object* v_x1_261_, lean_object* v_x2_262_){
_start:
{
if (lean_obj_tag(v_x1_261_) == 0)
{
lean_object* v_size_263_; lean_object* v___x_264_; 
v_size_263_ = lean_ctor_get(v_x1_261_, 0);
lean_inc(v_size_263_);
v___x_264_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_x2_262_, v_size_263_, v_x1_261_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_x2_262_, v___x_265_, v_x1_261_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg(lean_object* v_x_287_, lean_object* v_xs_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___y_293_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_289_ = lean_box(1);
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = lean_array_get_size(v_xs_288_);
v___x_296_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__9));
v___x_297_ = lean_nat_dec_lt(v___x_290_, v___x_291_);
if (v___x_297_ == 0)
{
lean_dec_ref(v_xs_288_);
v___y_293_ = v___x_289_;
goto v___jp_292_;
}
else
{
lean_object* v___f_298_; uint8_t v___x_299_; 
v___f_298_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10));
v___x_299_ = lean_nat_dec_le(v___x_291_, v___x_291_);
if (v___x_299_ == 0)
{
if (v___x_297_ == 0)
{
lean_dec_ref(v_xs_288_);
v___y_293_ = v___x_289_;
goto v___jp_292_;
}
else
{
size_t v___x_300_; size_t v___x_301_; lean_object* v___x_302_; 
v___x_300_ = ((size_t)0ULL);
v___x_301_ = lean_usize_of_nat(v___x_291_);
v___x_302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_296_, v___f_298_, v_xs_288_, v___x_300_, v___x_301_, v___x_289_);
v___y_293_ = v___x_302_;
goto v___jp_292_;
}
}
else
{
size_t v___x_303_; size_t v___x_304_; lean_object* v___x_305_; 
v___x_303_ = ((size_t)0ULL);
v___x_304_ = lean_usize_of_nat(v___x_291_);
v___x_305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_296_, v___f_298_, v_xs_288_, v___x_303_, v___x_304_, v___x_289_);
v___y_293_ = v___x_305_;
goto v___jp_292_;
}
}
v___jp_292_:
{
lean_object* v___x_294_; lean_object* v_fst_295_; 
v___x_294_ = lean_apply_2(v_x_287_, v___x_291_, v___y_293_);
v_fst_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_fst_295_);
lean_dec_ref(v___x_294_);
return v_fst_295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_run_x27(lean_object* v_00_u03b1_306_, lean_object* v_x_307_, lean_object* v_xs_308_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___y_313_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_309_ = lean_box(1);
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_array_get_size(v_xs_308_);
v___x_316_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__9));
v___x_317_ = lean_nat_dec_lt(v___x_310_, v___x_311_);
if (v___x_317_ == 0)
{
lean_dec_ref(v_xs_308_);
v___y_313_ = v___x_309_;
goto v___jp_312_;
}
else
{
lean_object* v___f_318_; uint8_t v___x_319_; 
v___f_318_ = ((lean_object*)(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10));
v___x_319_ = lean_nat_dec_le(v___x_311_, v___x_311_);
if (v___x_319_ == 0)
{
if (v___x_317_ == 0)
{
lean_dec_ref(v_xs_308_);
v___y_313_ = v___x_309_;
goto v___jp_312_;
}
else
{
size_t v___x_320_; size_t v___x_321_; lean_object* v___x_322_; 
v___x_320_ = ((size_t)0ULL);
v___x_321_ = lean_usize_of_nat(v___x_311_);
v___x_322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_316_, v___f_318_, v_xs_308_, v___x_320_, v___x_321_, v___x_309_);
v___y_313_ = v___x_322_;
goto v___jp_312_;
}
}
else
{
size_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; 
v___x_323_ = ((size_t)0ULL);
v___x_324_ = lean_usize_of_nat(v___x_311_);
v___x_325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_316_, v___f_318_, v_xs_308_, v___x_323_, v___x_324_, v___x_309_);
v___y_313_ = v___x_325_;
goto v___jp_312_;
}
}
v___jp_312_:
{
lean_object* v___x_314_; lean_object* v_fst_315_; 
v___x_314_ = lean_apply_2(v_x_307_, v___x_311_, v___y_313_);
v_fst_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_fst_315_);
lean_dec_ref(v___x_314_);
return v_fst_315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(lean_object* v_arg_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = l_Lean_Compiler_LCNF_Arg_toExpr___redArg(v_arg_326_);
v___x_330_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_328_, v_a_327_, v___x_329_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v_a_328_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg___boxed(lean_object* v_arg_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_arg_332_, v_a_333_, v_a_334_);
lean_dec(v_a_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM(uint8_t v_pu_336_, lean_object* v_arg_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_arg_337_, v_a_338_, v_a_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___boxed(lean_object* v_pu_341_, lean_object* v_arg_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
uint8_t v_pu_boxed_345_; lean_object* v_res_346_; 
v_pu_boxed_345_ = lean_unbox(v_pu_341_);
v_res_346_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM(v_pu_boxed_345_, v_arg_342_, v_a_343_, v_a_344_);
lean_dec(v_a_343_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(size_t v_sz_347_, size_t v_i_348_, lean_object* v_bs_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
uint8_t v___x_352_; 
v___x_352_ = lean_usize_dec_lt(v_i_348_, v_sz_347_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; 
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v_bs_349_);
lean_ctor_set(v___x_353_, 1, v___y_351_);
return v___x_353_;
}
else
{
lean_object* v_v_354_; lean_object* v___x_355_; lean_object* v_fst_356_; lean_object* v_snd_357_; lean_object* v___x_358_; lean_object* v_bs_x27_359_; size_t v___x_360_; size_t v___x_361_; lean_object* v___x_362_; 
v_v_354_ = lean_array_uget_borrowed(v_bs_349_, v_i_348_);
lean_inc(v_v_354_);
v___x_355_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_v_354_, v___y_350_, v___y_351_);
v_fst_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_fst_356_);
v_snd_357_ = lean_ctor_get(v___x_355_, 1);
lean_inc(v_snd_357_);
lean_dec_ref(v___x_355_);
v___x_358_ = lean_unsigned_to_nat(0u);
v_bs_x27_359_ = lean_array_uset(v_bs_349_, v_i_348_, v___x_358_);
v___x_360_ = ((size_t)1ULL);
v___x_361_ = lean_usize_add(v_i_348_, v___x_360_);
v___x_362_ = lean_array_uset(v_bs_x27_359_, v_i_348_, v_fst_356_);
v_i_348_ = v___x_361_;
v_bs_349_ = v___x_362_;
v___y_351_ = v_snd_357_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg___boxed(lean_object* v_sz_364_, lean_object* v_i_365_, lean_object* v_bs_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
size_t v_sz_boxed_369_; size_t v_i_boxed_370_; lean_object* v_res_371_; 
v_sz_boxed_369_ = lean_unbox_usize(v_sz_364_);
lean_dec(v_sz_364_);
v_i_boxed_370_ = lean_unbox_usize(v_i_365_);
lean_dec(v_i_365_);
v_res_371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_boxed_369_, v_i_boxed_370_, v_bs_366_, v___y_367_, v___y_368_);
lean_dec(v___y_367_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(uint8_t v_pu_372_, size_t v_sz_373_, size_t v_i_374_, lean_object* v_bs_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = lean_usize_dec_lt(v_i_374_, v_sz_373_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v_bs_375_);
lean_ctor_set(v___x_379_, 1, v___y_377_);
return v___x_379_;
}
else
{
lean_object* v_v_380_; lean_object* v___x_381_; lean_object* v_bs_x27_382_; lean_object* v_fst_384_; lean_object* v_snd_385_; 
v_v_380_ = lean_array_uget(v_bs_375_, v_i_374_);
v___x_381_ = lean_unsigned_to_nat(0u);
v_bs_x27_382_ = lean_array_uset(v_bs_375_, v_i_374_, v___x_381_);
switch(lean_obj_tag(v_v_380_))
{
case 0:
{
lean_object* v_ctorName_390_; lean_object* v_params_391_; lean_object* v_code_392_; lean_object* v___x_393_; lean_object* v_fst_394_; lean_object* v_snd_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_ctorName_390_ = lean_ctor_get(v_v_380_, 0);
lean_inc(v_ctorName_390_);
v_params_391_ = lean_ctor_get(v_v_380_, 1);
lean_inc_ref(v_params_391_);
v_code_392_ = lean_ctor_get(v_v_380_, 2);
lean_inc_ref(v_code_392_);
lean_dec_ref(v_v_380_);
lean_inc(v___y_376_);
v___x_393_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_372_, v_code_392_, v_params_391_, v_params_391_, v___x_381_, v___y_376_, v___y_377_);
lean_dec_ref(v_params_391_);
v_fst_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_fst_394_);
v_snd_395_ = lean_ctor_get(v___x_393_, 1);
lean_inc(v_snd_395_);
lean_dec_ref(v___x_393_);
v___x_396_ = lean_box(0);
v___x_397_ = l_Lean_mkConst(v_ctorName_390_, v___x_396_);
v___x_398_ = l_Lean_Expr_app___override(v___x_397_, v_fst_394_);
v_fst_384_ = v___x_398_;
v_snd_385_ = v_snd_395_;
goto v___jp_383_;
}
case 1:
{
lean_object* v_info_399_; lean_object* v_code_400_; lean_object* v___x_401_; lean_object* v_fst_402_; lean_object* v_snd_403_; lean_object* v_name_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_info_399_ = lean_ctor_get(v_v_380_, 0);
lean_inc_ref(v_info_399_);
v_code_400_ = lean_ctor_get(v_v_380_, 1);
lean_inc_ref(v_code_400_);
lean_dec_ref(v_v_380_);
v___x_401_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_372_, v_code_400_, v___y_376_, v___y_377_);
v_fst_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_fst_402_);
v_snd_403_ = lean_ctor_get(v___x_401_, 1);
lean_inc(v_snd_403_);
lean_dec_ref(v___x_401_);
v_name_404_ = lean_ctor_get(v_info_399_, 0);
lean_inc(v_name_404_);
lean_dec_ref(v_info_399_);
v___x_405_ = lean_box(0);
v___x_406_ = l_Lean_mkConst(v_name_404_, v___x_405_);
v___x_407_ = l_Lean_Expr_app___override(v___x_406_, v_fst_402_);
v_fst_384_ = v___x_407_;
v_snd_385_ = v_snd_403_;
goto v___jp_383_;
}
default: 
{
lean_object* v_code_408_; lean_object* v___x_409_; lean_object* v_fst_410_; lean_object* v_snd_411_; 
v_code_408_ = lean_ctor_get(v_v_380_, 0);
lean_inc_ref(v_code_408_);
lean_dec_ref(v_v_380_);
v___x_409_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_372_, v_code_408_, v___y_376_, v___y_377_);
v_fst_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_fst_410_);
v_snd_411_ = lean_ctor_get(v___x_409_, 1);
lean_inc(v_snd_411_);
lean_dec_ref(v___x_409_);
v_fst_384_ = v_fst_410_;
v_snd_385_ = v_snd_411_;
goto v___jp_383_;
}
}
v___jp_383_:
{
size_t v___x_386_; size_t v___x_387_; lean_object* v___x_388_; 
v___x_386_ = ((size_t)1ULL);
v___x_387_ = lean_usize_add(v_i_374_, v___x_386_);
v___x_388_ = lean_array_uset(v_bs_x27_382_, v_i_374_, v_fst_384_);
v_i_374_ = v___x_387_;
v_bs_375_ = v___x_388_;
v___y_377_ = v_snd_385_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__2(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = lean_box(0);
v___x_416_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__1));
v___x_417_ = l_Lean_mkConst(v___x_416_, v___x_415_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__5(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_421_ = lean_box(0);
v___x_422_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__4));
v___x_423_ = l_Lean_mkConst(v___x_422_, v___x_421_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__8(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = lean_box(0);
v___x_428_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__7));
v___x_429_ = l_Lean_mkConst(v___x_428_, v___x_427_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_box(0);
v___x_437_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__12));
v___x_438_ = l_Lean_mkConst(v___x_437_, v___x_436_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__16(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_box(0);
v___x_443_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__15));
v___x_444_ = l_Lean_mkConst(v___x_443_, v___x_442_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__19(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_448_ = lean_box(0);
v___x_449_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__18));
v___x_450_ = l_Lean_mkConst(v___x_449_, v___x_448_);
return v___x_450_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__22(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_box(0);
v___x_455_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__21));
v___x_456_ = l_Lean_mkConst(v___x_455_, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__25(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_box(0);
v___x_461_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__24));
v___x_462_ = l_Lean_mkConst(v___x_461_, v___x_460_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_box(0);
v___x_469_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__28));
v___x_470_ = l_Lean_mkConst(v___x_469_, v___x_468_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = lean_box(0);
v___x_476_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__31));
v___x_477_ = l_Lean_mkConst(v___x_476_, v___x_475_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__35(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = lean_box(0);
v___x_482_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__34));
v___x_483_ = l_Lean_mkConst(v___x_482_, v___x_481_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_box(0);
v___x_488_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__37));
v___x_489_ = l_Lean_mkConst(v___x_488_, v___x_487_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExprM(uint8_t v_pu_490_, lean_object* v_code_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
switch(lean_obj_tag(v_code_491_))
{
case 0:
{
lean_object* v_decl_494_; lean_object* v_k_495_; lean_object* v_fvarId_496_; lean_object* v_binderName_497_; lean_object* v_type_498_; lean_object* v_value_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v_fst_507_; lean_object* v_snd_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_517_; 
v_decl_494_ = lean_ctor_get(v_code_491_, 0);
lean_inc_ref(v_decl_494_);
v_k_495_ = lean_ctor_get(v_code_491_, 1);
lean_inc_ref(v_k_495_);
lean_dec_ref(v_code_491_);
v_fvarId_496_ = lean_ctor_get(v_decl_494_, 0);
lean_inc(v_fvarId_496_);
v_binderName_497_ = lean_ctor_get(v_decl_494_, 1);
lean_inc(v_binderName_497_);
v_type_498_ = lean_ctor_get(v_decl_494_, 2);
lean_inc_ref(v_type_498_);
v_value_499_ = lean_ctor_get(v_decl_494_, 3);
lean_inc(v_value_499_);
lean_dec_ref(v_decl_494_);
v___x_500_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_493_, v_a_492_, v_type_498_);
v___x_501_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v_pu_490_, v_value_499_);
v___x_502_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_493_, v_a_492_, v___x_501_);
lean_inc(v_a_492_);
v___x_503_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_496_, v_a_492_, v_a_493_);
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_505_ = lean_nat_add(v_a_492_, v___x_504_);
v___x_506_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_490_, v_k_495_, v___x_505_, v___x_503_);
lean_dec(v___x_505_);
v_fst_507_ = lean_ctor_get(v___x_506_, 0);
v_snd_508_ = lean_ctor_get(v___x_506_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_517_ == 0)
{
v___x_510_ = v___x_506_;
v_isShared_511_ = v_isSharedCheck_517_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_snd_508_);
lean_inc(v_fst_507_);
lean_dec(v___x_506_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_517_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
uint8_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_512_ = 1;
v___x_513_ = l_Lean_Expr_letE___override(v_binderName_497_, v___x_500_, v___x_502_, v_fst_507_, v___x_512_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_513_);
v___x_515_ = v___x_510_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_snd_508_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
case 3:
{
lean_object* v_fvarId_518_; lean_object* v_args_519_; lean_object* v___x_520_; size_t v_sz_521_; size_t v___x_522_; lean_object* v___x_523_; lean_object* v_fst_524_; lean_object* v_snd_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_533_; 
v_fvarId_518_ = lean_ctor_get(v_code_491_, 0);
lean_inc(v_fvarId_518_);
v_args_519_ = lean_ctor_get(v_code_491_, 1);
lean_inc_ref(v_args_519_);
lean_dec_ref(v_code_491_);
v___x_520_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_492_, v_a_493_, v_fvarId_518_);
v_sz_521_ = lean_array_size(v_args_519_);
v___x_522_ = ((size_t)0ULL);
v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_521_, v___x_522_, v_args_519_, v_a_492_, v_a_493_);
v_fst_524_ = lean_ctor_get(v___x_523_, 0);
v_snd_525_ = lean_ctor_get(v___x_523_, 1);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_533_ == 0)
{
v___x_527_ = v___x_523_;
v_isShared_528_ = v_isSharedCheck_533_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_snd_525_);
lean_inc(v_fst_524_);
lean_dec(v___x_523_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_533_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_529_ = l_Lean_mkAppN(v___x_520_, v_fst_524_);
lean_dec(v_fst_524_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_529_);
v___x_531_ = v___x_527_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_snd_525_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
case 4:
{
lean_object* v_cases_534_; lean_object* v_discr_535_; lean_object* v_alts_536_; size_t v_sz_537_; size_t v___x_538_; lean_object* v___x_539_; lean_object* v_fst_540_; lean_object* v_snd_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_555_; 
v_cases_534_ = lean_ctor_get(v_code_491_, 0);
lean_inc_ref(v_cases_534_);
lean_dec_ref(v_code_491_);
v_discr_535_ = lean_ctor_get(v_cases_534_, 2);
lean_inc(v_discr_535_);
v_alts_536_ = lean_ctor_get(v_cases_534_, 3);
lean_inc_ref(v_alts_536_);
lean_dec_ref(v_cases_534_);
v_sz_537_ = lean_array_size(v_alts_536_);
v___x_538_ = ((size_t)0ULL);
v___x_539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(v_pu_490_, v_sz_537_, v___x_538_, v_alts_536_, v_a_492_, v_a_493_);
v_fst_540_ = lean_ctor_get(v___x_539_, 0);
v_snd_541_ = lean_ctor_get(v___x_539_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_555_ == 0)
{
v___x_543_ = v___x_539_;
v_isShared_544_ = v_isSharedCheck_555_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_snd_541_);
lean_inc(v_fst_540_);
lean_dec(v___x_539_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_555_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_545_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_492_, v_snd_541_, v_discr_535_);
v___x_546_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__2, &l_Lean_Compiler_LCNF_Code_toExprM___closed__2_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__2);
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_mk_empty_array_with_capacity(v___x_547_);
v___x_549_ = lean_array_push(v___x_548_, v___x_545_);
v___x_550_ = l_Array_append___redArg(v___x_549_, v_fst_540_);
lean_dec(v_fst_540_);
v___x_551_ = l_Lean_mkAppN(v___x_546_, v___x_550_);
lean_dec_ref(v___x_550_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_551_);
v___x_553_ = v___x_543_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_snd_541_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
case 5:
{
lean_object* v_fvarId_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_fvarId_556_ = lean_ctor_get(v_code_491_, 0);
lean_inc(v_fvarId_556_);
lean_dec_ref(v_code_491_);
v___x_557_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_492_, v_a_493_, v_fvarId_556_);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v_a_493_);
return v___x_558_;
}
case 6:
{
lean_object* v_type_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_type_559_ = lean_ctor_get(v_code_491_, 0);
lean_inc_ref(v_type_559_);
lean_dec_ref(v_code_491_);
v___x_560_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_493_, v_a_492_, v_type_559_);
v___x_561_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__5, &l_Lean_Compiler_LCNF_Code_toExprM___closed__5_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__5);
v___x_562_ = l_Lean_Expr_app___override(v___x_561_, v___x_560_);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v_a_493_);
return v___x_563_;
}
case 7:
{
lean_object* v_fvarId_564_; lean_object* v_i_565_; lean_object* v_y_566_; lean_object* v_k_567_; lean_object* v___x_568_; lean_object* v_fst_569_; lean_object* v_snd_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v_fst_576_; lean_object* v_snd_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_591_; 
v_fvarId_564_ = lean_ctor_get(v_code_491_, 0);
lean_inc(v_fvarId_564_);
v_i_565_ = lean_ctor_get(v_code_491_, 1);
lean_inc(v_i_565_);
v_y_566_ = lean_ctor_get(v_code_491_, 2);
lean_inc(v_y_566_);
v_k_567_ = lean_ctor_get(v_code_491_, 3);
lean_inc_ref(v_k_567_);
lean_dec_ref(v_code_491_);
v___x_568_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_y_566_, v_a_492_, v_a_493_);
v_fst_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_fst_569_);
v_snd_570_ = lean_ctor_get(v___x_568_, 1);
lean_inc(v_snd_570_);
lean_dec_ref(v___x_568_);
lean_inc(v_fvarId_564_);
v___x_571_ = l_Lean_Expr_fvar___override(v_fvarId_564_);
lean_inc(v_a_492_);
v___x_572_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_564_, v_a_492_, v_snd_570_);
v___x_573_ = lean_unsigned_to_nat(1u);
v___x_574_ = lean_nat_add(v_a_492_, v___x_573_);
v___x_575_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_490_, v_k_567_, v___x_574_, v___x_572_);
lean_dec(v___x_574_);
v_fst_576_ = lean_ctor_get(v___x_575_, 0);
v_snd_577_ = lean_ctor_get(v___x_575_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_591_ == 0)
{
v___x_579_ = v___x_575_;
v_isShared_580_ = v_isSharedCheck_591_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_snd_577_);
lean_inc(v_fst_576_);
lean_dec(v___x_575_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_591_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_581_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__8, &l_Lean_Compiler_LCNF_Code_toExprM___closed__8_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__8);
v___x_582_ = l_Lean_mkNatLit(v_i_565_);
v___x_583_ = l_Lean_mkApp3(v___x_581_, v___x_571_, v___x_582_, v_fst_569_);
v___x_584_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_585_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_586_ = 1;
v___x_587_ = l_Lean_Expr_letE___override(v___x_584_, v___x_585_, v___x_583_, v_fst_576_, v___x_586_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_587_);
v___x_589_ = v___x_579_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_snd_577_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
case 8:
{
lean_object* v_fvarId_592_; lean_object* v_i_593_; lean_object* v_y_594_; lean_object* v_k_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v_fst_601_; lean_object* v_snd_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_617_; 
v_fvarId_592_ = lean_ctor_get(v_code_491_, 0);
lean_inc(v_fvarId_592_);
v_i_593_ = lean_ctor_get(v_code_491_, 1);
lean_inc(v_i_593_);
v_y_594_ = lean_ctor_get(v_code_491_, 2);
lean_inc(v_y_594_);
v_k_595_ = lean_ctor_get(v_code_491_, 3);
lean_inc_ref(v_k_595_);
lean_dec_ref(v_code_491_);
lean_inc(v_fvarId_592_);
v___x_596_ = l_Lean_Expr_fvar___override(v_fvarId_592_);
lean_inc(v_a_492_);
v___x_597_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_592_, v_a_492_, v_a_493_);
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = lean_nat_add(v_a_492_, v___x_598_);
v___x_600_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_490_, v_k_595_, v___x_599_, v___x_597_);
lean_dec(v___x_599_);
v_fst_601_ = lean_ctor_get(v___x_600_, 0);
v_snd_602_ = lean_ctor_get(v___x_600_, 1);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_617_ == 0)
{
v___x_604_ = v___x_600_;
v_isShared_605_ = v_isSharedCheck_617_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_snd_602_);
lean_inc(v_fst_601_);
lean_dec(v___x_600_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_617_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v_value_609_; lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_606_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__16, &l_Lean_Compiler_LCNF_Code_toExprM___closed__16_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__16);
v___x_607_ = l_Lean_mkNatLit(v_i_593_);
v___x_608_ = l_Lean_Expr_fvar___override(v_y_594_);
v_value_609_ = l_Lean_mkApp3(v___x_606_, v___x_596_, v___x_607_, v___x_608_);
v___x_610_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_611_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_612_ = 1;
v___x_613_ = l_Lean_Expr_letE___override(v___x_610_, v___x_611_, v_value_609_, v_fst_601_, v___x_612_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_613_);
v___x_615_ = v___x_604_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_snd_602_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
case 9:
{
lean_object* v_fvarId_618_; lean_object* v_i_619_; lean_object* v_offset_620_; lean_object* v_y_621_; lean_object* v_ty_622_; lean_object* v_k_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_fst_629_; lean_object* v_snd_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_646_; 
v_fvarId_618_ = lean_ctor_get(v_code_491_, 0);
lean_inc(v_fvarId_618_);
v_i_619_ = lean_ctor_get(v_code_491_, 1);
lean_inc(v_i_619_);
v_offset_620_ = lean_ctor_get(v_code_491_, 2);
lean_inc(v_offset_620_);
v_y_621_ = lean_ctor_get(v_code_491_, 3);
lean_inc(v_y_621_);
v_ty_622_ = lean_ctor_get(v_code_491_, 4);
lean_inc_ref(v_ty_622_);
v_k_623_ = lean_ctor_get(v_code_491_, 5);
lean_inc_ref(v_k_623_);
lean_dec_ref(v_code_491_);
lean_inc(v_fvarId_618_);
v___x_624_ = l_Lean_Expr_fvar___override(v_fvarId_618_);
lean_inc(v_a_492_);
v___x_625_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_618_, v_a_492_, v_a_493_);
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_add(v_a_492_, v___x_626_);
v___x_628_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_490_, v_k_623_, v___x_627_, v___x_625_);
lean_dec(v___x_627_);
v_fst_629_ = lean_ctor_get(v___x_628_, 0);
v_snd_630_ = lean_ctor_get(v___x_628_, 1);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_646_ == 0)
{
v___x_632_ = v___x_628_;
v_isShared_633_ = v_isSharedCheck_646_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_snd_630_);
lean_inc(v_fst_629_);
lean_dec(v___x_628_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_646_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v_value_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_634_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__19, &l_Lean_Compiler_LCNF_Code_toExprM___closed__19_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__19);
v___x_635_ = l_Lean_mkNatLit(v_i_619_);
v___x_636_ = l_Lean_mkNatLit(v_offset_620_);
v___x_637_ = l_Lean_Expr_fvar___override(v_y_621_);
v_value_638_ = l_Lean_mkApp5(v___x_634_, v___x_624_, v___x_635_, v___x_636_, v___x_637_, v_ty_622_);
v___x_639_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_640_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_641_ = 1;
v___x_642_ = l_Lean_Expr_letE___override(v___x_639_, v___x_640_, v_value_638_, v_fst_629_, v___x_641_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_642_);
v___x_644_ = v___x_632_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_snd_630_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
case 10:
{
lean_object* v_fvarId_647_; lean_object* v_cidx_648_; lean_object* v_k_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v_fst_654_; lean_object* v_snd_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_670_; 
v_fvarId_647_ = lean_ctor_get(v_code_491_, 0);
lean_inc(v_fvarId_647_);
v_cidx_648_ = lean_ctor_get(v_code_491_, 1);
lean_inc(v_cidx_648_);
v_k_649_ = lean_ctor_get(v_code_491_, 2);
lean_inc_ref(v_k_649_);
lean_dec_ref(v_code_491_);
lean_inc(v_a_492_);
lean_inc(v_fvarId_647_);
v___x_650_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_647_, v_a_492_, v_a_493_);
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_nat_add(v_a_492_, v___x_651_);
v___x_653_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_490_, v_k_649_, v___x_652_, v___x_650_);
lean_dec(v___x_652_);
v_fst_654_ = lean_ctor_get(v___x_653_, 0);
v_snd_655_ = lean_ctor_get(v___x_653_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_670_ == 0)
{
v___x_657_ = v___x_653_;
v_isShared_658_ = v_isSharedCheck_670_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_snd_655_);
lean_inc(v_fst_654_);
lean_dec(v___x_653_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_670_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_659_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__22, &l_Lean_Compiler_LCNF_Code_toExprM___closed__22_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__22);
v___x_660_ = l_Lean_Expr_fvar___override(v_fvarId_647_);
v___x_661_ = l_Lean_mkNatLit(v_cidx_648_);
v___x_662_ = l_Lean_mkAppB(v___x_659_, v___x_660_, v___x_661_);
v___x_663_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_664_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_665_ = 1;
v___x_666_ = l_Lean_Expr_letE___override(v___x_663_, v___x_664_, v___x_662_, v_fst_654_, v___x_665_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_666_);
v___x_668_ = v___x_657_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_snd_655_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
case 11:
{
lean_object* v_fvarId_671_; lean_object* v_n_672_; uint8_t v_check_673_; uint8_t v_persistent_674_; lean_object* v_k_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_701_; 
v_fvarId_671_ = lean_ctor_get(v_code_491_, 0);
lean_inc(v_fvarId_671_);
v_n_672_ = lean_ctor_get(v_code_491_, 1);
lean_inc(v_n_672_);
v_check_673_ = lean_ctor_get_uint8(v_code_491_, sizeof(void*)*3);
v_persistent_674_ = lean_ctor_get_uint8(v_code_491_, sizeof(void*)*3 + 1);
v_k_675_ = lean_ctor_get(v_code_491_, 2);
lean_inc_ref(v_k_675_);
lean_dec_ref(v_code_491_);
v___x_676_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__25, &l_Lean_Compiler_LCNF_Code_toExprM___closed__25_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__25);
lean_inc(v_fvarId_671_);
v___x_677_ = l_Lean_Expr_fvar___override(v_fvarId_671_);
v___x_678_ = l_Lean_mkNatLit(v_n_672_);
if (v_check_673_ == 0)
{
lean_object* v___x_704_; 
v___x_704_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_701_ = v___x_704_;
goto v___jp_700_;
}
else
{
lean_object* v___x_705_; 
v___x_705_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_701_ = v___x_705_;
goto v___jp_700_;
}
v___jp_679_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v_fst_686_; lean_object* v_snd_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_699_; 
lean_inc(v_a_492_);
v___x_682_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_671_, v_a_492_, v_a_493_);
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = lean_nat_add(v_a_492_, v___x_683_);
v___x_685_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_490_, v_k_675_, v___x_684_, v___x_682_);
lean_dec(v___x_684_);
v_fst_686_ = lean_ctor_get(v___x_685_, 0);
v_snd_687_ = lean_ctor_get(v___x_685_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_699_ == 0)
{
v___x_689_ = v___x_685_;
v_isShared_690_ = v_isSharedCheck_699_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_snd_687_);
lean_inc(v_fst_686_);
lean_dec(v___x_685_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_699_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v_value_691_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v_value_691_ = l_Lean_mkApp4(v___x_676_, v___x_677_, v___x_678_, v___y_680_, v___y_681_);
v___x_692_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_693_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_694_ = 1;
v___x_695_ = l_Lean_Expr_letE___override(v___x_692_, v___x_693_, v_value_691_, v_fst_686_, v___x_694_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_695_);
v___x_697_ = v___x_689_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_snd_687_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
v___jp_700_:
{
if (v_persistent_674_ == 0)
{
lean_object* v___x_702_; 
v___x_702_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_680_ = v___y_701_;
v___y_681_ = v___x_702_;
goto v___jp_679_;
}
else
{
lean_object* v___x_703_; 
v___x_703_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_680_ = v___y_701_;
v___y_681_ = v___x_703_;
goto v___jp_679_;
}
}
}
case 12:
{
lean_object* v_fvarId_706_; lean_object* v_n_707_; uint8_t v_check_708_; uint8_t v_persistent_709_; lean_object* v_k_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_fst_715_; lean_object* v_snd_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_740_; 
v_fvarId_706_ = lean_ctor_get(v_code_491_, 0);
lean_inc(v_fvarId_706_);
v_n_707_ = lean_ctor_get(v_code_491_, 1);
lean_inc(v_n_707_);
v_check_708_ = lean_ctor_get_uint8(v_code_491_, sizeof(void*)*3);
v_persistent_709_ = lean_ctor_get_uint8(v_code_491_, sizeof(void*)*3 + 1);
v_k_710_ = lean_ctor_get(v_code_491_, 2);
lean_inc_ref(v_k_710_);
lean_dec_ref(v_code_491_);
lean_inc(v_a_492_);
lean_inc(v_fvarId_706_);
v___x_711_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_706_, v_a_492_, v_a_493_);
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = lean_nat_add(v_a_492_, v___x_712_);
v___x_714_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_490_, v_k_710_, v___x_713_, v___x_711_);
lean_dec(v___x_713_);
v_fst_715_ = lean_ctor_get(v___x_714_, 0);
v_snd_716_ = lean_ctor_get(v___x_714_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_740_ == 0)
{
v___x_718_ = v___x_714_;
v_isShared_719_ = v_isSharedCheck_740_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_snd_716_);
lean_inc(v_fst_715_);
lean_dec(v___x_714_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_740_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_735_; 
v___x_720_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__35, &l_Lean_Compiler_LCNF_Code_toExprM___closed__35_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__35);
v___x_721_ = l_Lean_Expr_fvar___override(v_fvarId_706_);
v___x_722_ = l_Lean_mkNatLit(v_n_707_);
if (v_check_708_ == 0)
{
lean_object* v___x_738_; 
v___x_738_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_735_ = v___x_738_;
goto v___jp_734_;
}
else
{
lean_object* v___x_739_; 
v___x_739_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_735_ = v___x_739_;
goto v___jp_734_;
}
v___jp_723_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_726_ = l_Lean_mkApp4(v___x_720_, v___x_721_, v___x_722_, v___y_724_, v___y_725_);
v___x_727_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_728_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_729_ = 1;
v___x_730_ = l_Lean_Expr_letE___override(v___x_727_, v___x_728_, v___x_726_, v_fst_715_, v___x_729_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_730_);
v___x_732_ = v___x_718_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_snd_716_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
v___jp_734_:
{
if (v_persistent_709_ == 0)
{
lean_object* v___x_736_; 
v___x_736_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_724_ = v___y_735_;
v___y_725_ = v___x_736_;
goto v___jp_723_;
}
else
{
lean_object* v___x_737_; 
v___x_737_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_724_ = v___y_735_;
v___y_725_ = v___x_737_;
goto v___jp_723_;
}
}
}
}
case 13:
{
lean_object* v_fvarId_741_; lean_object* v_k_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v_fst_747_; lean_object* v_snd_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_762_; 
v_fvarId_741_ = lean_ctor_get(v_code_491_, 0);
lean_inc(v_fvarId_741_);
v_k_742_ = lean_ctor_get(v_code_491_, 1);
lean_inc_ref(v_k_742_);
lean_dec_ref(v_code_491_);
lean_inc(v_a_492_);
lean_inc(v_fvarId_741_);
v___x_743_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_741_, v_a_492_, v_a_493_);
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = lean_nat_add(v_a_492_, v___x_744_);
v___x_746_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_490_, v_k_742_, v___x_745_, v___x_743_);
lean_dec(v___x_745_);
v_fst_747_ = lean_ctor_get(v___x_746_, 0);
v_snd_748_ = lean_ctor_get(v___x_746_, 1);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_762_ == 0)
{
v___x_750_ = v___x_746_;
v_isShared_751_ = v_isSharedCheck_762_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_snd_748_);
lean_inc(v_fst_747_);
lean_dec(v___x_746_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_762_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_752_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__38, &l_Lean_Compiler_LCNF_Code_toExprM___closed__38_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38);
v___x_753_ = l_Lean_Expr_fvar___override(v_fvarId_741_);
v___x_754_ = l_Lean_Expr_app___override(v___x_752_, v___x_753_);
v___x_755_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_756_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_757_ = 1;
v___x_758_ = l_Lean_Expr_letE___override(v___x_755_, v___x_756_, v___x_754_, v_fst_747_, v___x_757_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_758_);
v___x_760_ = v___x_750_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_snd_748_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
default: 
{
lean_object* v_decl_763_; lean_object* v_k_764_; lean_object* v_fvarId_765_; lean_object* v_binderName_766_; lean_object* v_type_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v_fst_770_; lean_object* v_snd_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v_fst_776_; lean_object* v_snd_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_786_; 
v_decl_763_ = lean_ctor_get(v_code_491_, 0);
lean_inc_ref(v_decl_763_);
v_k_764_ = lean_ctor_get(v_code_491_, 1);
lean_inc_ref(v_k_764_);
lean_dec_ref(v_code_491_);
v_fvarId_765_ = lean_ctor_get(v_decl_763_, 0);
lean_inc(v_fvarId_765_);
v_binderName_766_ = lean_ctor_get(v_decl_763_, 1);
lean_inc(v_binderName_766_);
v_type_767_ = lean_ctor_get(v_decl_763_, 3);
lean_inc_ref(v_type_767_);
v___x_768_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_493_, v_a_492_, v_type_767_);
v___x_769_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_490_, v_decl_763_, v_a_492_, v_a_493_);
v_fst_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_fst_770_);
v_snd_771_ = lean_ctor_get(v___x_769_, 1);
lean_inc(v_snd_771_);
lean_dec_ref(v___x_769_);
lean_inc(v_a_492_);
v___x_772_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_765_, v_a_492_, v_snd_771_);
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = lean_nat_add(v_a_492_, v___x_773_);
v___x_775_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_490_, v_k_764_, v___x_774_, v___x_772_);
lean_dec(v___x_774_);
v_fst_776_ = lean_ctor_get(v___x_775_, 0);
v_snd_777_ = lean_ctor_get(v___x_775_, 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_786_ == 0)
{
v___x_779_ = v___x_775_;
v_isShared_780_ = v_isSharedCheck_786_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_snd_777_);
lean_inc(v_fst_776_);
lean_dec(v___x_775_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_786_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
uint8_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_781_ = 1;
v___x_782_ = l_Lean_Expr_letE___override(v_binderName_766_, v___x_768_, v_fst_770_, v_fst_776_, v___x_781_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_782_);
v___x_784_ = v___x_779_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_snd_777_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(uint8_t v_pu_787_, lean_object* v_value_788_, lean_object* v_params_789_, lean_object* v_params_790_, lean_object* v_i_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = lean_array_get_size(v_params_790_);
v___x_795_ = lean_nat_dec_lt(v_i_791_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v_fst_797_; lean_object* v_snd_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_807_; 
lean_dec(v_i_791_);
v___x_796_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_787_, v_value_788_, v_a_792_, v_a_793_);
v_fst_797_ = lean_ctor_get(v___x_796_, 0);
v_snd_798_ = lean_ctor_get(v___x_796_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_807_ == 0)
{
v___x_800_ = v___x_796_;
v_isShared_801_ = v_isSharedCheck_807_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_snd_798_);
lean_inc(v_fst_797_);
lean_dec(v___x_796_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_807_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_802_ = lean_array_get_size(v_params_789_);
v___x_803_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(v_pu_787_, v_params_789_, v_a_792_, v_snd_798_, v___x_802_, v_fst_797_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_803_);
v___x_805_ = v___x_800_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_snd_798_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
else
{
lean_object* v___x_808_; lean_object* v_fvarId_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_808_ = lean_array_fget_borrowed(v_params_790_, v_i_791_);
v_fvarId_809_ = lean_ctor_get(v___x_808_, 0);
v___x_810_ = lean_unsigned_to_nat(1u);
v___x_811_ = lean_nat_add(v_i_791_, v___x_810_);
lean_dec(v_i_791_);
lean_inc(v_a_792_);
lean_inc(v_fvarId_809_);
v___x_812_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_809_, v_a_792_, v_a_793_);
v___x_813_ = lean_nat_add(v_a_792_, v___x_810_);
lean_dec(v_a_792_);
v_i_791_ = v___x_811_;
v_a_792_ = v___x_813_;
v_a_793_ = v___x_812_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExprM(uint8_t v_pu_815_, lean_object* v_decl_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_params_819_; lean_object* v_value_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_params_819_ = lean_ctor_get(v_decl_816_, 2);
lean_inc_ref(v_params_819_);
v_value_820_ = lean_ctor_get(v_decl_816_, 4);
lean_inc_ref(v_value_820_);
lean_dec_ref(v_decl_816_);
v___x_821_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_817_);
v___x_822_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_815_, v_value_820_, v_params_819_, v_params_819_, v___x_821_, v_a_817_, v_a_818_);
lean_dec_ref(v_params_819_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExprM___boxed(lean_object* v_pu_823_, lean_object* v_decl_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
uint8_t v_pu_boxed_827_; lean_object* v_res_828_; 
v_pu_boxed_827_ = lean_unbox(v_pu_823_);
v_res_828_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_boxed_827_, v_decl_824_, v_a_825_, v_a_826_);
lean_dec(v_a_825_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg___boxed(lean_object* v_pu_829_, lean_object* v_value_830_, lean_object* v_params_831_, lean_object* v_params_832_, lean_object* v_i_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
uint8_t v_pu_boxed_836_; lean_object* v_res_837_; 
v_pu_boxed_836_ = lean_unbox(v_pu_829_);
v_res_837_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_boxed_836_, v_value_830_, v_params_831_, v_params_832_, v_i_833_, v_a_834_, v_a_835_);
lean_dec_ref(v_params_832_);
lean_dec_ref(v_params_831_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3___boxed(lean_object* v_pu_838_, lean_object* v_sz_839_, lean_object* v_i_840_, lean_object* v_bs_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
uint8_t v_pu_boxed_844_; size_t v_sz_boxed_845_; size_t v_i_boxed_846_; lean_object* v_res_847_; 
v_pu_boxed_844_ = lean_unbox(v_pu_838_);
v_sz_boxed_845_ = lean_unbox_usize(v_sz_839_);
lean_dec(v_sz_839_);
v_i_boxed_846_ = lean_unbox_usize(v_i_840_);
lean_dec(v_i_840_);
v_res_847_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(v_pu_boxed_844_, v_sz_boxed_845_, v_i_boxed_846_, v_bs_841_, v___y_842_, v___y_843_);
lean_dec(v___y_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExprM___boxed(lean_object* v_pu_848_, lean_object* v_code_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
uint8_t v_pu_boxed_852_; lean_object* v_res_853_; 
v_pu_boxed_852_ = lean_unbox(v_pu_848_);
v_res_853_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_boxed_852_, v_code_849_, v_a_850_, v_a_851_);
lean_dec(v_a_850_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0(uint8_t v_pu_854_, lean_object* v_value_855_, lean_object* v_params_856_, uint8_t v_pu_857_, lean_object* v_params_858_, lean_object* v_i_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___x_862_; 
lean_inc(v_a_860_);
v___x_862_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_854_, v_value_855_, v_params_856_, v_params_858_, v_i_859_, v_a_860_, v_a_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___boxed(lean_object* v_pu_863_, lean_object* v_value_864_, lean_object* v_params_865_, lean_object* v_pu_866_, lean_object* v_params_867_, lean_object* v_i_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
uint8_t v_pu_boxed_871_; uint8_t v_pu_boxed_872_; lean_object* v_res_873_; 
v_pu_boxed_871_ = lean_unbox(v_pu_863_);
v_pu_boxed_872_ = lean_unbox(v_pu_866_);
v_res_873_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0(v_pu_boxed_871_, v_value_864_, v_params_865_, v_pu_boxed_872_, v_params_867_, v_i_868_, v_a_869_, v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_params_867_);
lean_dec_ref(v_params_865_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2(uint8_t v_pu_874_, size_t v_sz_875_, size_t v_i_876_, lean_object* v_bs_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_875_, v_i_876_, v_bs_877_, v___y_878_, v___y_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___boxed(lean_object* v_pu_881_, lean_object* v_sz_882_, lean_object* v_i_883_, lean_object* v_bs_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
uint8_t v_pu_boxed_887_; size_t v_sz_boxed_888_; size_t v_i_boxed_889_; lean_object* v_res_890_; 
v_pu_boxed_887_ = lean_unbox(v_pu_881_);
v_sz_boxed_888_ = lean_unbox_usize(v_sz_882_);
lean_dec(v_sz_882_);
v_i_boxed_889_ = lean_unbox_usize(v_i_883_);
lean_dec(v_i_883_);
v_res_890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2(v_pu_boxed_887_, v_sz_boxed_888_, v_i_boxed_889_, v_bs_884_, v___y_885_, v___y_886_);
lean_dec(v___y_885_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(lean_object* v_as_891_, size_t v_i_892_, size_t v_stop_893_, lean_object* v_b_894_){
_start:
{
lean_object* v___y_896_; uint8_t v___x_900_; 
v___x_900_ = lean_usize_dec_eq(v_i_892_, v_stop_893_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
v___x_901_ = lean_array_uget_borrowed(v_as_891_, v_i_892_);
if (lean_obj_tag(v_b_894_) == 0)
{
lean_object* v_size_902_; lean_object* v___x_903_; 
v_size_902_ = lean_ctor_get(v_b_894_, 0);
lean_inc(v_size_902_);
lean_inc(v___x_901_);
v___x_903_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_901_, v_size_902_, v_b_894_);
v___y_896_ = v___x_903_;
goto v___jp_895_;
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_901_);
v___x_905_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_901_, v___x_904_, v_b_894_);
v___y_896_ = v___x_905_;
goto v___jp_895_;
}
}
else
{
return v_b_894_;
}
v___jp_895_:
{
size_t v___x_897_; size_t v___x_898_; 
v___x_897_ = ((size_t)1ULL);
v___x_898_ = lean_usize_add(v_i_892_, v___x_897_);
v_i_892_ = v___x_898_;
v_b_894_ = v___y_896_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0___boxed(lean_object* v_as_906_, lean_object* v_i_907_, lean_object* v_stop_908_, lean_object* v_b_909_){
_start:
{
size_t v_i_boxed_910_; size_t v_stop_boxed_911_; lean_object* v_res_912_; 
v_i_boxed_910_ = lean_unbox_usize(v_i_907_);
lean_dec(v_i_907_);
v_stop_boxed_911_ = lean_unbox_usize(v_stop_908_);
lean_dec(v_stop_908_);
v_res_912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_as_906_, v_i_boxed_910_, v_stop_boxed_911_, v_b_909_);
lean_dec_ref(v_as_906_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExpr(uint8_t v_pu_913_, lean_object* v_code_914_, lean_object* v_xs_915_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___y_920_; uint8_t v___x_923_; 
v___x_916_ = lean_box(1);
v___x_917_ = lean_unsigned_to_nat(0u);
v___x_918_ = lean_array_get_size(v_xs_915_);
v___x_923_ = lean_nat_dec_lt(v___x_917_, v___x_918_);
if (v___x_923_ == 0)
{
v___y_920_ = v___x_916_;
goto v___jp_919_;
}
else
{
uint8_t v___x_924_; 
v___x_924_ = lean_nat_dec_le(v___x_918_, v___x_918_);
if (v___x_924_ == 0)
{
if (v___x_923_ == 0)
{
v___y_920_ = v___x_916_;
goto v___jp_919_;
}
else
{
size_t v___x_925_; size_t v___x_926_; lean_object* v___x_927_; 
v___x_925_ = ((size_t)0ULL);
v___x_926_ = lean_usize_of_nat(v___x_918_);
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_915_, v___x_925_, v___x_926_, v___x_916_);
v___y_920_ = v___x_927_;
goto v___jp_919_;
}
}
else
{
size_t v___x_928_; size_t v___x_929_; lean_object* v___x_930_; 
v___x_928_ = ((size_t)0ULL);
v___x_929_ = lean_usize_of_nat(v___x_918_);
v___x_930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_915_, v___x_928_, v___x_929_, v___x_916_);
v___y_920_ = v___x_930_;
goto v___jp_919_;
}
}
v___jp_919_:
{
lean_object* v___x_921_; lean_object* v_fst_922_; 
v___x_921_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_913_, v_code_914_, v___x_918_, v___y_920_);
v_fst_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_fst_922_);
lean_dec_ref(v___x_921_);
return v_fst_922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExpr___boxed(lean_object* v_pu_931_, lean_object* v_code_932_, lean_object* v_xs_933_){
_start:
{
uint8_t v_pu_boxed_934_; lean_object* v_res_935_; 
v_pu_boxed_934_ = lean_unbox(v_pu_931_);
v_res_935_ = l_Lean_Compiler_LCNF_Code_toExpr(v_pu_boxed_934_, v_code_932_, v_xs_933_);
lean_dec_ref(v_xs_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr(uint8_t v_pu_936_, lean_object* v_decl_937_, lean_object* v_xs_938_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___y_943_; uint8_t v___x_946_; 
v___x_939_ = lean_box(1);
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = lean_array_get_size(v_xs_938_);
v___x_946_ = lean_nat_dec_lt(v___x_940_, v___x_941_);
if (v___x_946_ == 0)
{
v___y_943_ = v___x_939_;
goto v___jp_942_;
}
else
{
uint8_t v___x_947_; 
v___x_947_ = lean_nat_dec_le(v___x_941_, v___x_941_);
if (v___x_947_ == 0)
{
if (v___x_946_ == 0)
{
v___y_943_ = v___x_939_;
goto v___jp_942_;
}
else
{
size_t v___x_948_; size_t v___x_949_; lean_object* v___x_950_; 
v___x_948_ = ((size_t)0ULL);
v___x_949_ = lean_usize_of_nat(v___x_941_);
v___x_950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_938_, v___x_948_, v___x_949_, v___x_939_);
v___y_943_ = v___x_950_;
goto v___jp_942_;
}
}
else
{
size_t v___x_951_; size_t v___x_952_; lean_object* v___x_953_; 
v___x_951_ = ((size_t)0ULL);
v___x_952_ = lean_usize_of_nat(v___x_941_);
v___x_953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_938_, v___x_951_, v___x_952_, v___x_939_);
v___y_943_ = v___x_953_;
goto v___jp_942_;
}
}
v___jp_942_:
{
lean_object* v___x_944_; lean_object* v_fst_945_; 
v___x_944_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_936_, v_decl_937_, v___x_941_, v___y_943_);
v_fst_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_fst_945_);
lean_dec_ref(v___x_944_);
return v_fst_945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr___boxed(lean_object* v_pu_954_, lean_object* v_decl_955_, lean_object* v_xs_956_){
_start:
{
uint8_t v_pu_boxed_957_; lean_object* v_res_958_; 
v_pu_boxed_957_ = lean_unbox(v_pu_954_);
v_res_958_ = l_Lean_Compiler_LCNF_FunDecl_toExpr(v_pu_boxed_957_, v_decl_955_, v_xs_956_);
lean_dec_ref(v_xs_956_);
return v_res_958_;
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
