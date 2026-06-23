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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
v_param_108_ = lean_array_get(v___x_105_, v_params_98_, v___x_107_);
lean_dec_ref(v___x_105_);
v_binderName_109_ = lean_ctor_get(v_param_108_, 1);
lean_inc(v_binderName_109_);
v_type_110_ = lean_ctor_get(v_param_108_, 2);
lean_inc_ref(v_type_110_);
lean_dec(v_param_108_);
v___x_111_ = lean_nat_sub(v_offset_99_, v___x_106_);
lean_dec(v_offset_99_);
v_domain_112_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_m_100_, v___x_111_, v_type_110_);
v___x_113_ = 0;
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
lean_dec_ref_known(v_v_380_, 3);
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
lean_dec_ref_known(v_v_380_, 2);
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
lean_dec_ref_known(v_v_380_, 1);
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
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__43(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__42));
v___x_499_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__41));
v___x_500_ = l_Lean_mkConst(v___x_499_, v___x_498_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__44(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__38, &l_Lean_Compiler_LCNF_Code_toExprM___closed__38_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38);
v___x_502_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__43, &l_Lean_Compiler_LCNF_Code_toExprM___closed__43_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__43);
v___x_503_ = l_Lean_Expr_app___override(v___x_502_, v___x_501_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__47(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__42));
v___x_509_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__46));
v___x_510_ = l_Lean_mkConst(v___x_509_, v___x_508_);
return v___x_510_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__50(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_514_ = lean_box(0);
v___x_515_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__49));
v___x_516_ = l_Lean_mkConst(v___x_515_, v___x_514_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExprM(uint8_t v_pu_517_, lean_object* v_code_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
switch(lean_obj_tag(v_code_518_))
{
case 0:
{
lean_object* v_decl_521_; lean_object* v_k_522_; lean_object* v_fvarId_523_; lean_object* v_binderName_524_; lean_object* v_type_525_; lean_object* v_value_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v_fst_534_; lean_object* v_snd_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_544_; 
v_decl_521_ = lean_ctor_get(v_code_518_, 0);
lean_inc_ref(v_decl_521_);
v_k_522_ = lean_ctor_get(v_code_518_, 1);
lean_inc_ref(v_k_522_);
lean_dec_ref_known(v_code_518_, 2);
v_fvarId_523_ = lean_ctor_get(v_decl_521_, 0);
lean_inc(v_fvarId_523_);
v_binderName_524_ = lean_ctor_get(v_decl_521_, 1);
lean_inc(v_binderName_524_);
v_type_525_ = lean_ctor_get(v_decl_521_, 2);
lean_inc_ref(v_type_525_);
v_value_526_ = lean_ctor_get(v_decl_521_, 3);
lean_inc(v_value_526_);
lean_dec_ref(v_decl_521_);
v___x_527_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_520_, v_a_519_, v_type_525_);
v___x_528_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v_pu_517_, v_value_526_);
v___x_529_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_520_, v_a_519_, v___x_528_);
lean_inc(v_a_519_);
v___x_530_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_523_, v_a_519_, v_a_520_);
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_nat_add(v_a_519_, v___x_531_);
v___x_533_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_517_, v_k_522_, v___x_532_, v___x_530_);
lean_dec(v___x_532_);
v_fst_534_ = lean_ctor_get(v___x_533_, 0);
v_snd_535_ = lean_ctor_get(v___x_533_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_544_ == 0)
{
v___x_537_ = v___x_533_;
v_isShared_538_ = v_isSharedCheck_544_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_snd_535_);
lean_inc(v_fst_534_);
lean_dec(v___x_533_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_544_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
uint8_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_539_ = 1;
v___x_540_ = l_Lean_Expr_letE___override(v_binderName_524_, v___x_527_, v___x_529_, v_fst_534_, v___x_539_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_540_);
v___x_542_ = v___x_537_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_snd_535_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
case 3:
{
lean_object* v_fvarId_545_; lean_object* v_args_546_; lean_object* v___x_547_; size_t v_sz_548_; size_t v___x_549_; lean_object* v___x_550_; lean_object* v_fst_551_; lean_object* v_snd_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_560_; 
v_fvarId_545_ = lean_ctor_get(v_code_518_, 0);
lean_inc(v_fvarId_545_);
v_args_546_ = lean_ctor_get(v_code_518_, 1);
lean_inc_ref(v_args_546_);
lean_dec_ref_known(v_code_518_, 2);
v___x_547_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_519_, v_a_520_, v_fvarId_545_);
v_sz_548_ = lean_array_size(v_args_546_);
v___x_549_ = ((size_t)0ULL);
v___x_550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_548_, v___x_549_, v_args_546_, v_a_519_, v_a_520_);
v_fst_551_ = lean_ctor_get(v___x_550_, 0);
v_snd_552_ = lean_ctor_get(v___x_550_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_560_ == 0)
{
v___x_554_ = v___x_550_;
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_snd_552_);
lean_inc(v_fst_551_);
lean_dec(v___x_550_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_556_ = l_Lean_mkAppN(v___x_547_, v_fst_551_);
lean_dec(v_fst_551_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_556_);
v___x_558_ = v___x_554_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_snd_552_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
case 4:
{
lean_object* v_cases_561_; lean_object* v_discr_562_; lean_object* v_alts_563_; size_t v_sz_564_; size_t v___x_565_; lean_object* v___x_566_; lean_object* v_fst_567_; lean_object* v_snd_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_582_; 
v_cases_561_ = lean_ctor_get(v_code_518_, 0);
lean_inc_ref(v_cases_561_);
lean_dec_ref_known(v_code_518_, 1);
v_discr_562_ = lean_ctor_get(v_cases_561_, 2);
lean_inc(v_discr_562_);
v_alts_563_ = lean_ctor_get(v_cases_561_, 3);
lean_inc_ref(v_alts_563_);
lean_dec_ref(v_cases_561_);
v_sz_564_ = lean_array_size(v_alts_563_);
v___x_565_ = ((size_t)0ULL);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(v_pu_517_, v_sz_564_, v___x_565_, v_alts_563_, v_a_519_, v_a_520_);
v_fst_567_ = lean_ctor_get(v___x_566_, 0);
v_snd_568_ = lean_ctor_get(v___x_566_, 1);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_582_ == 0)
{
v___x_570_ = v___x_566_;
v_isShared_571_ = v_isSharedCheck_582_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_snd_568_);
lean_inc(v_fst_567_);
lean_dec(v___x_566_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_582_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_572_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_519_, v_snd_568_, v_discr_562_);
v___x_573_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__2, &l_Lean_Compiler_LCNF_Code_toExprM___closed__2_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__2);
v___x_574_ = lean_unsigned_to_nat(1u);
v___x_575_ = lean_mk_empty_array_with_capacity(v___x_574_);
v___x_576_ = lean_array_push(v___x_575_, v___x_572_);
v___x_577_ = l_Array_append___redArg(v___x_576_, v_fst_567_);
lean_dec(v_fst_567_);
v___x_578_ = l_Lean_mkAppN(v___x_573_, v___x_577_);
lean_dec_ref(v___x_577_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_578_);
v___x_580_ = v___x_570_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_snd_568_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
case 5:
{
lean_object* v_fvarId_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_fvarId_583_ = lean_ctor_get(v_code_518_, 0);
lean_inc(v_fvarId_583_);
lean_dec_ref_known(v_code_518_, 1);
v___x_584_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(v_a_519_, v_a_520_, v_fvarId_583_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v_a_520_);
return v___x_585_;
}
case 6:
{
lean_object* v_type_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_type_586_ = lean_ctor_get(v_code_518_, 0);
lean_inc_ref(v_type_586_);
lean_dec_ref_known(v_code_518_, 1);
v___x_587_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_520_, v_a_519_, v_type_586_);
v___x_588_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__5, &l_Lean_Compiler_LCNF_Code_toExprM___closed__5_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__5);
v___x_589_ = l_Lean_Expr_app___override(v___x_588_, v___x_587_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v_a_520_);
return v___x_590_;
}
case 7:
{
lean_object* v_fvarId_591_; lean_object* v_i_592_; lean_object* v_y_593_; lean_object* v_k_594_; lean_object* v___x_595_; lean_object* v_fst_596_; lean_object* v_snd_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v_fst_603_; lean_object* v_snd_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_618_; 
v_fvarId_591_ = lean_ctor_get(v_code_518_, 0);
lean_inc_n(v_fvarId_591_, 2);
v_i_592_ = lean_ctor_get(v_code_518_, 1);
lean_inc(v_i_592_);
v_y_593_ = lean_ctor_get(v_code_518_, 2);
lean_inc(v_y_593_);
v_k_594_ = lean_ctor_get(v_code_518_, 3);
lean_inc_ref(v_k_594_);
lean_dec_ref_known(v_code_518_, 4);
v___x_595_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_y_593_, v_a_519_, v_a_520_);
v_fst_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_fst_596_);
v_snd_597_ = lean_ctor_get(v___x_595_, 1);
lean_inc(v_snd_597_);
lean_dec_ref(v___x_595_);
v___x_598_ = l_Lean_Expr_fvar___override(v_fvarId_591_);
lean_inc(v_a_519_);
v___x_599_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_591_, v_a_519_, v_snd_597_);
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_add(v_a_519_, v___x_600_);
v___x_602_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_517_, v_k_594_, v___x_601_, v___x_599_);
lean_dec(v___x_601_);
v_fst_603_ = lean_ctor_get(v___x_602_, 0);
v_snd_604_ = lean_ctor_get(v___x_602_, 1);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_618_ == 0)
{
v___x_606_ = v___x_602_;
v_isShared_607_ = v_isSharedCheck_618_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_snd_604_);
lean_inc(v_fst_603_);
lean_dec(v___x_602_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_618_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_608_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__8, &l_Lean_Compiler_LCNF_Code_toExprM___closed__8_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__8);
v___x_609_ = l_Lean_mkNatLit(v_i_592_);
v___x_610_ = l_Lean_mkApp3(v___x_608_, v___x_598_, v___x_609_, v_fst_596_);
v___x_611_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_612_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_613_ = 1;
v___x_614_ = l_Lean_Expr_letE___override(v___x_611_, v___x_612_, v___x_610_, v_fst_603_, v___x_613_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_614_);
v___x_616_ = v___x_606_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_snd_604_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
case 8:
{
lean_object* v_fvarId_619_; lean_object* v_i_620_; lean_object* v_y_621_; lean_object* v_k_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v_fst_628_; lean_object* v_snd_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_644_; 
v_fvarId_619_ = lean_ctor_get(v_code_518_, 0);
lean_inc_n(v_fvarId_619_, 2);
v_i_620_ = lean_ctor_get(v_code_518_, 1);
lean_inc(v_i_620_);
v_y_621_ = lean_ctor_get(v_code_518_, 2);
lean_inc(v_y_621_);
v_k_622_ = lean_ctor_get(v_code_518_, 3);
lean_inc_ref(v_k_622_);
lean_dec_ref_known(v_code_518_, 4);
v___x_623_ = l_Lean_Expr_fvar___override(v_fvarId_619_);
lean_inc(v_a_519_);
v___x_624_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_619_, v_a_519_, v_a_520_);
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = lean_nat_add(v_a_519_, v___x_625_);
v___x_627_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_517_, v_k_622_, v___x_626_, v___x_624_);
lean_dec(v___x_626_);
v_fst_628_ = lean_ctor_get(v___x_627_, 0);
v_snd_629_ = lean_ctor_get(v___x_627_, 1);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_644_ == 0)
{
v___x_631_ = v___x_627_;
v_isShared_632_ = v_isSharedCheck_644_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_snd_629_);
lean_inc(v_fst_628_);
lean_dec(v___x_627_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_644_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v_value_636_; lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_633_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__16, &l_Lean_Compiler_LCNF_Code_toExprM___closed__16_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__16);
v___x_634_ = l_Lean_mkNatLit(v_i_620_);
v___x_635_ = l_Lean_Expr_fvar___override(v_y_621_);
v_value_636_ = l_Lean_mkApp3(v___x_633_, v___x_623_, v___x_634_, v___x_635_);
v___x_637_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_638_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_639_ = 1;
v___x_640_ = l_Lean_Expr_letE___override(v___x_637_, v___x_638_, v_value_636_, v_fst_628_, v___x_639_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_640_);
v___x_642_ = v___x_631_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_snd_629_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
case 9:
{
lean_object* v_fvarId_645_; lean_object* v_i_646_; lean_object* v_offset_647_; lean_object* v_y_648_; lean_object* v_ty_649_; lean_object* v_k_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v_fst_656_; lean_object* v_snd_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_673_; 
v_fvarId_645_ = lean_ctor_get(v_code_518_, 0);
lean_inc_n(v_fvarId_645_, 2);
v_i_646_ = lean_ctor_get(v_code_518_, 1);
lean_inc(v_i_646_);
v_offset_647_ = lean_ctor_get(v_code_518_, 2);
lean_inc(v_offset_647_);
v_y_648_ = lean_ctor_get(v_code_518_, 3);
lean_inc(v_y_648_);
v_ty_649_ = lean_ctor_get(v_code_518_, 4);
lean_inc_ref(v_ty_649_);
v_k_650_ = lean_ctor_get(v_code_518_, 5);
lean_inc_ref(v_k_650_);
lean_dec_ref_known(v_code_518_, 6);
v___x_651_ = l_Lean_Expr_fvar___override(v_fvarId_645_);
lean_inc(v_a_519_);
v___x_652_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_645_, v_a_519_, v_a_520_);
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_nat_add(v_a_519_, v___x_653_);
v___x_655_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_517_, v_k_650_, v___x_654_, v___x_652_);
lean_dec(v___x_654_);
v_fst_656_ = lean_ctor_get(v___x_655_, 0);
v_snd_657_ = lean_ctor_get(v___x_655_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_673_ == 0)
{
v___x_659_ = v___x_655_;
v_isShared_660_ = v_isSharedCheck_673_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_snd_657_);
lean_inc(v_fst_656_);
lean_dec(v___x_655_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_673_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v_value_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_661_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__19, &l_Lean_Compiler_LCNF_Code_toExprM___closed__19_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__19);
v___x_662_ = l_Lean_mkNatLit(v_i_646_);
v___x_663_ = l_Lean_mkNatLit(v_offset_647_);
v___x_664_ = l_Lean_Expr_fvar___override(v_y_648_);
v_value_665_ = l_Lean_mkApp5(v___x_661_, v___x_651_, v___x_662_, v___x_663_, v___x_664_, v_ty_649_);
v___x_666_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_667_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_668_ = 1;
v___x_669_ = l_Lean_Expr_letE___override(v___x_666_, v___x_667_, v_value_665_, v_fst_656_, v___x_668_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_669_);
v___x_671_ = v___x_659_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_snd_657_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
case 10:
{
lean_object* v_fvarId_674_; lean_object* v_cidx_675_; lean_object* v_k_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v_fst_681_; lean_object* v_snd_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_697_; 
v_fvarId_674_ = lean_ctor_get(v_code_518_, 0);
lean_inc_n(v_fvarId_674_, 2);
v_cidx_675_ = lean_ctor_get(v_code_518_, 1);
lean_inc(v_cidx_675_);
v_k_676_ = lean_ctor_get(v_code_518_, 2);
lean_inc_ref(v_k_676_);
lean_dec_ref_known(v_code_518_, 3);
lean_inc(v_a_519_);
v___x_677_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_674_, v_a_519_, v_a_520_);
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = lean_nat_add(v_a_519_, v___x_678_);
v___x_680_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_517_, v_k_676_, v___x_679_, v___x_677_);
lean_dec(v___x_679_);
v_fst_681_ = lean_ctor_get(v___x_680_, 0);
v_snd_682_ = lean_ctor_get(v___x_680_, 1);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_697_ == 0)
{
v___x_684_ = v___x_680_;
v_isShared_685_ = v_isSharedCheck_697_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_snd_682_);
lean_inc(v_fst_681_);
lean_dec(v___x_680_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_697_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_686_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__22, &l_Lean_Compiler_LCNF_Code_toExprM___closed__22_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__22);
v___x_687_ = l_Lean_Expr_fvar___override(v_fvarId_674_);
v___x_688_ = l_Lean_mkNatLit(v_cidx_675_);
v___x_689_ = l_Lean_mkAppB(v___x_686_, v___x_687_, v___x_688_);
v___x_690_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_691_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_692_ = 1;
v___x_693_ = l_Lean_Expr_letE___override(v___x_690_, v___x_691_, v___x_689_, v_fst_681_, v___x_692_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_693_);
v___x_695_ = v___x_684_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_snd_682_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
case 11:
{
lean_object* v_fvarId_698_; lean_object* v_n_699_; uint8_t v_check_700_; uint8_t v_persistent_701_; lean_object* v_k_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_728_; 
v_fvarId_698_ = lean_ctor_get(v_code_518_, 0);
lean_inc_n(v_fvarId_698_, 2);
v_n_699_ = lean_ctor_get(v_code_518_, 1);
lean_inc(v_n_699_);
v_check_700_ = lean_ctor_get_uint8(v_code_518_, sizeof(void*)*3);
v_persistent_701_ = lean_ctor_get_uint8(v_code_518_, sizeof(void*)*3 + 1);
v_k_702_ = lean_ctor_get(v_code_518_, 2);
lean_inc_ref(v_k_702_);
lean_dec_ref_known(v_code_518_, 3);
v___x_703_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__25, &l_Lean_Compiler_LCNF_Code_toExprM___closed__25_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__25);
v___x_704_ = l_Lean_Expr_fvar___override(v_fvarId_698_);
v___x_705_ = l_Lean_mkNatLit(v_n_699_);
if (v_check_700_ == 0)
{
lean_object* v___x_731_; 
v___x_731_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_728_ = v___x_731_;
goto v___jp_727_;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_728_ = v___x_732_;
goto v___jp_727_;
}
v___jp_706_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_fst_713_; lean_object* v_snd_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_726_; 
lean_inc(v_a_519_);
v___x_709_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_698_, v_a_519_, v_a_520_);
v___x_710_ = lean_unsigned_to_nat(1u);
v___x_711_ = lean_nat_add(v_a_519_, v___x_710_);
v___x_712_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_517_, v_k_702_, v___x_711_, v___x_709_);
lean_dec(v___x_711_);
v_fst_713_ = lean_ctor_get(v___x_712_, 0);
v_snd_714_ = lean_ctor_get(v___x_712_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_726_ == 0)
{
v___x_716_ = v___x_712_;
v_isShared_717_ = v_isSharedCheck_726_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_snd_714_);
lean_inc(v_fst_713_);
lean_dec(v___x_712_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_726_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_value_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
lean_inc_ref(v___y_708_);
lean_inc_ref(v___y_707_);
v_value_718_ = l_Lean_mkApp4(v___x_703_, v___x_704_, v___x_705_, v___y_707_, v___y_708_);
v___x_719_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_720_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_721_ = 1;
v___x_722_ = l_Lean_Expr_letE___override(v___x_719_, v___x_720_, v_value_718_, v_fst_713_, v___x_721_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_722_);
v___x_724_ = v___x_716_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_snd_714_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
v___jp_727_:
{
if (v_persistent_701_ == 0)
{
lean_object* v___x_729_; 
v___x_729_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_707_ = v___y_728_;
v___y_708_ = v___x_729_;
goto v___jp_706_;
}
else
{
lean_object* v___x_730_; 
v___x_730_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_707_ = v___y_728_;
v___y_708_ = v___x_730_;
goto v___jp_706_;
}
}
}
case 12:
{
lean_object* v_fvarId_733_; lean_object* v_n_734_; uint8_t v_check_735_; uint8_t v_persistent_736_; lean_object* v_objs_x3f_737_; lean_object* v_k_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v_fst_743_; lean_object* v_snd_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_778_; 
v_fvarId_733_ = lean_ctor_get(v_code_518_, 0);
lean_inc_n(v_fvarId_733_, 2);
v_n_734_ = lean_ctor_get(v_code_518_, 1);
lean_inc(v_n_734_);
v_check_735_ = lean_ctor_get_uint8(v_code_518_, sizeof(void*)*4);
v_persistent_736_ = lean_ctor_get_uint8(v_code_518_, sizeof(void*)*4 + 1);
v_objs_x3f_737_ = lean_ctor_get(v_code_518_, 2);
lean_inc(v_objs_x3f_737_);
v_k_738_ = lean_ctor_get(v_code_518_, 3);
lean_inc_ref(v_k_738_);
lean_dec_ref_known(v_code_518_, 4);
lean_inc(v_a_519_);
v___x_739_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_733_, v_a_519_, v_a_520_);
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_add(v_a_519_, v___x_740_);
v___x_742_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_517_, v_k_738_, v___x_741_, v___x_739_);
lean_dec(v___x_741_);
v_fst_743_ = lean_ctor_get(v___x_742_, 0);
v_snd_744_ = lean_ctor_get(v___x_742_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_778_ == 0)
{
v___x_746_ = v___x_742_;
v_isShared_747_ = v_isSharedCheck_778_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_snd_744_);
lean_inc(v_fst_743_);
lean_dec(v___x_742_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_778_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_773_; 
v___x_748_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__35, &l_Lean_Compiler_LCNF_Code_toExprM___closed__35_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__35);
v___x_749_ = l_Lean_Expr_fvar___override(v_fvarId_733_);
v___x_750_ = l_Lean_mkNatLit(v_n_734_);
if (v_check_735_ == 0)
{
lean_object* v___x_776_; 
v___x_776_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_773_ = v___x_776_;
goto v___jp_772_;
}
else
{
lean_object* v___x_777_; 
v___x_777_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_773_ = v___x_777_;
goto v___jp_772_;
}
v___jp_751_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
lean_inc_ref(v___y_752_);
lean_inc_ref(v___y_753_);
v___x_755_ = l_Lean_mkApp5(v___x_748_, v___x_749_, v___x_750_, v___y_753_, v___y_752_, v___y_754_);
v___x_756_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_757_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_758_ = 1;
v___x_759_ = l_Lean_Expr_letE___override(v___x_756_, v___x_757_, v___x_755_, v_fst_743_, v___x_758_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_759_);
v___x_761_ = v___x_746_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_snd_744_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
v___jp_763_:
{
lean_object* v___x_766_; 
v___x_766_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__38, &l_Lean_Compiler_LCNF_Code_toExprM___closed__38_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38);
if (lean_obj_tag(v_objs_x3f_737_) == 0)
{
lean_object* v___x_767_; 
v___x_767_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__44, &l_Lean_Compiler_LCNF_Code_toExprM___closed__44_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__44);
v___y_752_ = v___y_765_;
v___y_753_ = v___y_764_;
v___y_754_ = v___x_767_;
goto v___jp_751_;
}
else
{
lean_object* v_val_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_val_768_ = lean_ctor_get(v_objs_x3f_737_, 0);
lean_inc(v_val_768_);
lean_dec_ref_known(v_objs_x3f_737_, 1);
v___x_769_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__47, &l_Lean_Compiler_LCNF_Code_toExprM___closed__47_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__47);
v___x_770_ = l_Lean_mkNatLit(v_val_768_);
v___x_771_ = l_Lean_mkAppB(v___x_769_, v___x_766_, v___x_770_);
v___y_752_ = v___y_765_;
v___y_753_ = v___y_764_;
v___y_754_ = v___x_771_;
goto v___jp_751_;
}
}
v___jp_772_:
{
if (v_persistent_736_ == 0)
{
lean_object* v___x_774_; 
v___x_774_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__29, &l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29);
v___y_764_ = v___y_773_;
v___y_765_ = v___x_774_;
goto v___jp_763_;
}
else
{
lean_object* v___x_775_; 
v___x_775_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__32, &l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32);
v___y_764_ = v___y_773_;
v___y_765_ = v___x_775_;
goto v___jp_763_;
}
}
}
}
case 13:
{
lean_object* v_fvarId_779_; lean_object* v_k_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v_fst_785_; lean_object* v_snd_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_800_; 
v_fvarId_779_ = lean_ctor_get(v_code_518_, 0);
lean_inc_n(v_fvarId_779_, 2);
v_k_780_ = lean_ctor_get(v_code_518_, 1);
lean_inc_ref(v_k_780_);
lean_dec_ref_known(v_code_518_, 2);
lean_inc(v_a_519_);
v___x_781_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_779_, v_a_519_, v_a_520_);
v___x_782_ = lean_unsigned_to_nat(1u);
v___x_783_ = lean_nat_add(v_a_519_, v___x_782_);
v___x_784_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_517_, v_k_780_, v___x_783_, v___x_781_);
lean_dec(v___x_783_);
v_fst_785_ = lean_ctor_get(v___x_784_, 0);
v_snd_786_ = lean_ctor_get(v___x_784_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_800_ == 0)
{
v___x_788_ = v___x_784_;
v_isShared_789_ = v_isSharedCheck_800_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_snd_786_);
lean_inc(v_fst_785_);
lean_dec(v___x_784_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_800_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_790_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__50, &l_Lean_Compiler_LCNF_Code_toExprM___closed__50_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__50);
v___x_791_ = l_Lean_Expr_fvar___override(v_fvarId_779_);
v___x_792_ = l_Lean_Expr_app___override(v___x_790_, v___x_791_);
v___x_793_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toExprM___closed__10));
v___x_794_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toExprM___closed__13, &l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once, _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13);
v___x_795_ = 1;
v___x_796_ = l_Lean_Expr_letE___override(v___x_793_, v___x_794_, v___x_792_, v_fst_785_, v___x_795_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_796_);
v___x_798_ = v___x_788_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_snd_786_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
default: 
{
lean_object* v_decl_801_; lean_object* v_k_802_; lean_object* v_fvarId_803_; lean_object* v_binderName_804_; lean_object* v_type_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v_fst_808_; lean_object* v_snd_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v_fst_814_; lean_object* v_snd_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_824_; 
v_decl_801_ = lean_ctor_get(v_code_518_, 0);
lean_inc_ref(v_decl_801_);
v_k_802_ = lean_ctor_get(v_code_518_, 1);
lean_inc_ref(v_k_802_);
lean_dec_ref(v_code_518_);
v_fvarId_803_ = lean_ctor_get(v_decl_801_, 0);
lean_inc(v_fvarId_803_);
v_binderName_804_ = lean_ctor_get(v_decl_801_, 1);
lean_inc(v_binderName_804_);
v_type_805_ = lean_ctor_get(v_decl_801_, 3);
lean_inc_ref(v_type_805_);
v___x_806_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(v_a_520_, v_a_519_, v_type_805_);
v___x_807_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_517_, v_decl_801_, v_a_519_, v_a_520_);
v_fst_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_fst_808_);
v_snd_809_ = lean_ctor_get(v___x_807_, 1);
lean_inc(v_snd_809_);
lean_dec_ref(v___x_807_);
lean_inc(v_a_519_);
v___x_810_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_803_, v_a_519_, v_snd_809_);
v___x_811_ = lean_unsigned_to_nat(1u);
v___x_812_ = lean_nat_add(v_a_519_, v___x_811_);
v___x_813_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_517_, v_k_802_, v___x_812_, v___x_810_);
lean_dec(v___x_812_);
v_fst_814_ = lean_ctor_get(v___x_813_, 0);
v_snd_815_ = lean_ctor_get(v___x_813_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_824_ == 0)
{
v___x_817_ = v___x_813_;
v_isShared_818_ = v_isSharedCheck_824_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_snd_815_);
lean_inc(v_fst_814_);
lean_dec(v___x_813_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_824_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_819_ = 1;
v___x_820_ = l_Lean_Expr_letE___override(v_binderName_804_, v___x_806_, v_fst_808_, v_fst_814_, v___x_819_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_820_);
v___x_822_ = v___x_817_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_snd_815_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(uint8_t v_pu_825_, lean_object* v_value_826_, lean_object* v_params_827_, lean_object* v_params_828_, lean_object* v_i_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = lean_array_get_size(v_params_828_);
v___x_833_ = lean_nat_dec_lt(v_i_829_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v_fst_835_; lean_object* v_snd_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_845_; 
lean_dec(v_i_829_);
v___x_834_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_825_, v_value_826_, v_a_830_, v_a_831_);
v_fst_835_ = lean_ctor_get(v___x_834_, 0);
v_snd_836_ = lean_ctor_get(v___x_834_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_845_ == 0)
{
v___x_838_ = v___x_834_;
v_isShared_839_ = v_isSharedCheck_845_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_snd_836_);
lean_inc(v_fst_835_);
lean_dec(v___x_834_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_845_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_840_ = lean_array_get_size(v_params_827_);
v___x_841_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(v_pu_825_, v_params_827_, v_a_830_, v_snd_836_, v___x_840_, v_fst_835_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_841_);
v___x_843_ = v___x_838_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v_snd_836_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
else
{
lean_object* v___x_846_; lean_object* v_fvarId_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_846_ = lean_array_fget_borrowed(v_params_828_, v_i_829_);
v_fvarId_847_ = lean_ctor_get(v___x_846_, 0);
v___x_848_ = lean_unsigned_to_nat(1u);
v___x_849_ = lean_nat_add(v_i_829_, v___x_848_);
lean_dec(v_i_829_);
lean_inc(v_a_830_);
lean_inc(v_fvarId_847_);
v___x_850_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_847_, v_a_830_, v_a_831_);
v___x_851_ = lean_nat_add(v_a_830_, v___x_848_);
lean_dec(v_a_830_);
v_i_829_ = v___x_849_;
v_a_830_ = v___x_851_;
v_a_831_ = v___x_850_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExprM(uint8_t v_pu_853_, lean_object* v_decl_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_params_857_; lean_object* v_value_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v_params_857_ = lean_ctor_get(v_decl_854_, 2);
lean_inc_ref(v_params_857_);
v_value_858_ = lean_ctor_get(v_decl_854_, 4);
lean_inc_ref(v_value_858_);
lean_dec_ref(v_decl_854_);
v___x_859_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_855_);
v___x_860_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_853_, v_value_858_, v_params_857_, v_params_857_, v___x_859_, v_a_855_, v_a_856_);
lean_dec_ref(v_params_857_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExprM___boxed(lean_object* v_pu_861_, lean_object* v_decl_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
uint8_t v_pu_boxed_865_; lean_object* v_res_866_; 
v_pu_boxed_865_ = lean_unbox(v_pu_861_);
v_res_866_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_boxed_865_, v_decl_862_, v_a_863_, v_a_864_);
lean_dec(v_a_863_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg___boxed(lean_object* v_pu_867_, lean_object* v_value_868_, lean_object* v_params_869_, lean_object* v_params_870_, lean_object* v_i_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
uint8_t v_pu_boxed_874_; lean_object* v_res_875_; 
v_pu_boxed_874_ = lean_unbox(v_pu_867_);
v_res_875_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_boxed_874_, v_value_868_, v_params_869_, v_params_870_, v_i_871_, v_a_872_, v_a_873_);
lean_dec_ref(v_params_870_);
lean_dec_ref(v_params_869_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3___boxed(lean_object* v_pu_876_, lean_object* v_sz_877_, lean_object* v_i_878_, lean_object* v_bs_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
uint8_t v_pu_boxed_882_; size_t v_sz_boxed_883_; size_t v_i_boxed_884_; lean_object* v_res_885_; 
v_pu_boxed_882_ = lean_unbox(v_pu_876_);
v_sz_boxed_883_ = lean_unbox_usize(v_sz_877_);
lean_dec(v_sz_877_);
v_i_boxed_884_ = lean_unbox_usize(v_i_878_);
lean_dec(v_i_878_);
v_res_885_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(v_pu_boxed_882_, v_sz_boxed_883_, v_i_boxed_884_, v_bs_879_, v___y_880_, v___y_881_);
lean_dec(v___y_880_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExprM___boxed(lean_object* v_pu_886_, lean_object* v_code_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
uint8_t v_pu_boxed_890_; lean_object* v_res_891_; 
v_pu_boxed_890_ = lean_unbox(v_pu_886_);
v_res_891_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_boxed_890_, v_code_887_, v_a_888_, v_a_889_);
lean_dec(v_a_888_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0(uint8_t v_pu_892_, lean_object* v_value_893_, lean_object* v_params_894_, uint8_t v_pu_895_, lean_object* v_params_896_, lean_object* v_i_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v___x_900_; 
lean_inc(v_a_898_);
v___x_900_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_892_, v_value_893_, v_params_894_, v_params_896_, v_i_897_, v_a_898_, v_a_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___boxed(lean_object* v_pu_901_, lean_object* v_value_902_, lean_object* v_params_903_, lean_object* v_pu_904_, lean_object* v_params_905_, lean_object* v_i_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
uint8_t v_pu_boxed_909_; uint8_t v_pu_boxed_910_; lean_object* v_res_911_; 
v_pu_boxed_909_ = lean_unbox(v_pu_901_);
v_pu_boxed_910_ = lean_unbox(v_pu_904_);
v_res_911_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0(v_pu_boxed_909_, v_value_902_, v_params_903_, v_pu_boxed_910_, v_params_905_, v_i_906_, v_a_907_, v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_params_905_);
lean_dec_ref(v_params_903_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2(uint8_t v_pu_912_, size_t v_sz_913_, size_t v_i_914_, lean_object* v_bs_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_913_, v_i_914_, v_bs_915_, v___y_916_, v___y_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___boxed(lean_object* v_pu_919_, lean_object* v_sz_920_, lean_object* v_i_921_, lean_object* v_bs_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
uint8_t v_pu_boxed_925_; size_t v_sz_boxed_926_; size_t v_i_boxed_927_; lean_object* v_res_928_; 
v_pu_boxed_925_ = lean_unbox(v_pu_919_);
v_sz_boxed_926_ = lean_unbox_usize(v_sz_920_);
lean_dec(v_sz_920_);
v_i_boxed_927_ = lean_unbox_usize(v_i_921_);
lean_dec(v_i_921_);
v_res_928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2(v_pu_boxed_925_, v_sz_boxed_926_, v_i_boxed_927_, v_bs_922_, v___y_923_, v___y_924_);
lean_dec(v___y_923_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(lean_object* v_as_929_, size_t v_i_930_, size_t v_stop_931_, lean_object* v_b_932_){
_start:
{
lean_object* v___y_934_; uint8_t v___x_938_; 
v___x_938_ = lean_usize_dec_eq(v_i_930_, v_stop_931_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; 
v___x_939_ = lean_array_uget_borrowed(v_as_929_, v_i_930_);
if (lean_obj_tag(v_b_932_) == 0)
{
lean_object* v_size_940_; lean_object* v___x_941_; 
v_size_940_ = lean_ctor_get(v_b_932_, 0);
lean_inc(v_size_940_);
lean_inc(v___x_939_);
v___x_941_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_939_, v_size_940_, v_b_932_);
v___y_934_ = v___x_941_;
goto v___jp_933_;
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_939_);
v___x_943_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_939_, v___x_942_, v_b_932_);
v___y_934_ = v___x_943_;
goto v___jp_933_;
}
}
else
{
return v_b_932_;
}
v___jp_933_:
{
size_t v___x_935_; size_t v___x_936_; 
v___x_935_ = ((size_t)1ULL);
v___x_936_ = lean_usize_add(v_i_930_, v___x_935_);
v_i_930_ = v___x_936_;
v_b_932_ = v___y_934_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0___boxed(lean_object* v_as_944_, lean_object* v_i_945_, lean_object* v_stop_946_, lean_object* v_b_947_){
_start:
{
size_t v_i_boxed_948_; size_t v_stop_boxed_949_; lean_object* v_res_950_; 
v_i_boxed_948_ = lean_unbox_usize(v_i_945_);
lean_dec(v_i_945_);
v_stop_boxed_949_ = lean_unbox_usize(v_stop_946_);
lean_dec(v_stop_946_);
v_res_950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_as_944_, v_i_boxed_948_, v_stop_boxed_949_, v_b_947_);
lean_dec_ref(v_as_944_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExpr(uint8_t v_pu_951_, lean_object* v_code_952_, lean_object* v_xs_953_){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___y_958_; uint8_t v___x_961_; 
v___x_954_ = lean_box(1);
v___x_955_ = lean_unsigned_to_nat(0u);
v___x_956_ = lean_array_get_size(v_xs_953_);
v___x_961_ = lean_nat_dec_lt(v___x_955_, v___x_956_);
if (v___x_961_ == 0)
{
v___y_958_ = v___x_954_;
goto v___jp_957_;
}
else
{
uint8_t v___x_962_; 
v___x_962_ = lean_nat_dec_le(v___x_956_, v___x_956_);
if (v___x_962_ == 0)
{
if (v___x_961_ == 0)
{
v___y_958_ = v___x_954_;
goto v___jp_957_;
}
else
{
size_t v___x_963_; size_t v___x_964_; lean_object* v___x_965_; 
v___x_963_ = ((size_t)0ULL);
v___x_964_ = lean_usize_of_nat(v___x_956_);
v___x_965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_953_, v___x_963_, v___x_964_, v___x_954_);
v___y_958_ = v___x_965_;
goto v___jp_957_;
}
}
else
{
size_t v___x_966_; size_t v___x_967_; lean_object* v___x_968_; 
v___x_966_ = ((size_t)0ULL);
v___x_967_ = lean_usize_of_nat(v___x_956_);
v___x_968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_953_, v___x_966_, v___x_967_, v___x_954_);
v___y_958_ = v___x_968_;
goto v___jp_957_;
}
}
v___jp_957_:
{
lean_object* v___x_959_; lean_object* v_fst_960_; 
v___x_959_ = l_Lean_Compiler_LCNF_Code_toExprM(v_pu_951_, v_code_952_, v___x_956_, v___y_958_);
v_fst_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_fst_960_);
lean_dec_ref(v___x_959_);
return v_fst_960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toExpr___boxed(lean_object* v_pu_969_, lean_object* v_code_970_, lean_object* v_xs_971_){
_start:
{
uint8_t v_pu_boxed_972_; lean_object* v_res_973_; 
v_pu_boxed_972_ = lean_unbox(v_pu_969_);
v_res_973_ = l_Lean_Compiler_LCNF_Code_toExpr(v_pu_boxed_972_, v_code_970_, v_xs_971_);
lean_dec_ref(v_xs_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr(uint8_t v_pu_974_, lean_object* v_decl_975_, lean_object* v_xs_976_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___y_981_; uint8_t v___x_984_; 
v___x_977_ = lean_box(1);
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = lean_array_get_size(v_xs_976_);
v___x_984_ = lean_nat_dec_lt(v___x_978_, v___x_979_);
if (v___x_984_ == 0)
{
v___y_981_ = v___x_977_;
goto v___jp_980_;
}
else
{
uint8_t v___x_985_; 
v___x_985_ = lean_nat_dec_le(v___x_979_, v___x_979_);
if (v___x_985_ == 0)
{
if (v___x_984_ == 0)
{
v___y_981_ = v___x_977_;
goto v___jp_980_;
}
else
{
size_t v___x_986_; size_t v___x_987_; lean_object* v___x_988_; 
v___x_986_ = ((size_t)0ULL);
v___x_987_ = lean_usize_of_nat(v___x_979_);
v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_976_, v___x_986_, v___x_987_, v___x_977_);
v___y_981_ = v___x_988_;
goto v___jp_980_;
}
}
else
{
size_t v___x_989_; size_t v___x_990_; lean_object* v___x_991_; 
v___x_989_ = ((size_t)0ULL);
v___x_990_ = lean_usize_of_nat(v___x_979_);
v___x_991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_976_, v___x_989_, v___x_990_, v___x_977_);
v___y_981_ = v___x_991_;
goto v___jp_980_;
}
}
v___jp_980_:
{
lean_object* v___x_982_; lean_object* v_fst_983_; 
v___x_982_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_974_, v_decl_975_, v___x_979_, v___y_981_);
v_fst_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_fst_983_);
lean_dec_ref(v___x_982_);
return v_fst_983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr___boxed(lean_object* v_pu_992_, lean_object* v_decl_993_, lean_object* v_xs_994_){
_start:
{
uint8_t v_pu_boxed_995_; lean_object* v_res_996_; 
v_pu_boxed_995_ = lean_unbox(v_pu_992_);
v_res_996_ = l_Lean_Compiler_LCNF_FunDecl_toExpr(v_pu_boxed_995_, v_decl_993_, v_xs_994_);
lean_dec_ref(v_xs_994_);
return v_res_996_;
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
