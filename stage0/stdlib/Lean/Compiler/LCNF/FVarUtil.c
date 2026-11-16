// Lean compiler output
// Module: Lean.Compiler.LCNF.FVarUtil
// Imports: public import Lean.Compiler.LCNF.CompilerM
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
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_pure(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Compiler.LCNF.Expr.mapFVarM"};
static const lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Compiler.LCNF.FVarUtil"};
static const lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Compiler.LCNF.Expr.forFVarM"};
static const lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__1_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr = (const lean_object*)&l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instTraverseFVarArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instTraverseFVarArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instTraverseFVarLetValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instTraverseFVarLetValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instTraverseFVarParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instTraverseFVarParam___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__19(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__19, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__7, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_anyFVar___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_anyFVar___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_anyFVar___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_anyFVar___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_anyFVar___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_anyFVar___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__5_value;
static const lean_closure_object l_Lean_Compiler_LCNF_anyFVar___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_anyFVar___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__1_value)}};
static const lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_anyFVar___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__7_value),((lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__3_value),((lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__4_value),((lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__5_value)}};
static const lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__8_value),((lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__6_value)}};
static const lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0(lean_object* v_fvarId_1_, lean_object* v_toPure_2_, lean_object* v_e_3_, lean_object* v_____do__lift_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = l_Lean_instBEqFVarId_beq(v_fvarId_1_, v_____do__lift_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; lean_object* v___x_7_; 
lean_dec_ref(v_e_3_);
v___x_6_ = l_Lean_Expr_fvar___override(v_____do__lift_4_);
v___x_7_ = lean_apply_2(v_toPure_2_, lean_box(0), v___x_6_);
return v___x_7_;
}
else
{
lean_object* v___x_8_; 
lean_dec(v_____do__lift_4_);
v___x_8_ = lean_apply_2(v_toPure_2_, lean_box(0), v_e_3_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0___boxed(lean_object* v_fvarId_9_, lean_object* v_toPure_10_, lean_object* v_e_11_, lean_object* v_____do__lift_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0(v_fvarId_9_, v_toPure_10_, v_e_11_, v_____do__lift_12_);
lean_dec(v_fvarId_9_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1(lean_object* v_fn_14_, lean_object* v_____do__lift_15_, lean_object* v_toPure_16_, lean_object* v_arg_17_, lean_object* v_e_18_, lean_object* v_____do__lift_19_){
_start:
{
size_t v___x_20_; size_t v___x_21_; uint8_t v___x_22_; 
v___x_20_ = lean_ptr_addr(v_fn_14_);
v___x_21_ = lean_ptr_addr(v_____do__lift_15_);
v___x_22_ = lean_usize_dec_eq(v___x_20_, v___x_21_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; 
lean_dec_ref(v_e_18_);
v___x_23_ = l_Lean_Expr_app___override(v_____do__lift_15_, v_____do__lift_19_);
v___x_24_ = lean_apply_2(v_toPure_16_, lean_box(0), v___x_23_);
return v___x_24_;
}
else
{
size_t v___x_25_; size_t v___x_26_; uint8_t v___x_27_; 
v___x_25_ = lean_ptr_addr(v_arg_17_);
v___x_26_ = lean_ptr_addr(v_____do__lift_19_);
v___x_27_ = lean_usize_dec_eq(v___x_25_, v___x_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; lean_object* v___x_29_; 
lean_dec_ref(v_e_18_);
v___x_28_ = l_Lean_Expr_app___override(v_____do__lift_15_, v_____do__lift_19_);
v___x_29_ = lean_apply_2(v_toPure_16_, lean_box(0), v___x_28_);
return v___x_29_;
}
else
{
lean_object* v___x_30_; 
lean_dec_ref(v_____do__lift_19_);
lean_dec_ref(v_____do__lift_15_);
v___x_30_ = lean_apply_2(v_toPure_16_, lean_box(0), v_e_18_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1___boxed(lean_object* v_fn_31_, lean_object* v_____do__lift_32_, lean_object* v_toPure_33_, lean_object* v_arg_34_, lean_object* v_e_35_, lean_object* v_____do__lift_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1(v_fn_31_, v_____do__lift_32_, v_toPure_33_, v_arg_34_, v_e_35_, v_____do__lift_36_);
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_fn_31_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3(lean_object* v_binderType_38_, lean_object* v_____do__lift_39_, lean_object* v_binderName_40_, uint8_t v_binderInfo_41_, lean_object* v_toPure_42_, lean_object* v_body_43_, lean_object* v_e_44_, lean_object* v_____do__lift_45_){
_start:
{
size_t v___x_46_; size_t v___x_47_; uint8_t v___x_48_; 
v___x_46_ = lean_ptr_addr(v_binderType_38_);
v___x_47_ = lean_ptr_addr(v_____do__lift_39_);
v___x_48_ = lean_usize_dec_eq(v___x_46_, v___x_47_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec_ref(v_e_44_);
v___x_49_ = l_Lean_Expr_lam___override(v_binderName_40_, v_____do__lift_39_, v_____do__lift_45_, v_binderInfo_41_);
v___x_50_ = lean_apply_2(v_toPure_42_, lean_box(0), v___x_49_);
return v___x_50_;
}
else
{
size_t v___x_51_; size_t v___x_52_; uint8_t v___x_53_; 
v___x_51_ = lean_ptr_addr(v_body_43_);
v___x_52_ = lean_ptr_addr(v_____do__lift_45_);
v___x_53_ = lean_usize_dec_eq(v___x_51_, v___x_52_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec_ref(v_e_44_);
v___x_54_ = l_Lean_Expr_lam___override(v_binderName_40_, v_____do__lift_39_, v_____do__lift_45_, v_binderInfo_41_);
v___x_55_ = lean_apply_2(v_toPure_42_, lean_box(0), v___x_54_);
return v___x_55_;
}
else
{
uint8_t v___x_56_; 
v___x_56_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_41_, v_binderInfo_41_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec_ref(v_e_44_);
v___x_57_ = l_Lean_Expr_lam___override(v_binderName_40_, v_____do__lift_39_, v_____do__lift_45_, v_binderInfo_41_);
v___x_58_ = lean_apply_2(v_toPure_42_, lean_box(0), v___x_57_);
return v___x_58_;
}
else
{
lean_object* v___x_59_; 
lean_dec_ref(v_____do__lift_45_);
lean_dec(v_binderName_40_);
lean_dec_ref(v_____do__lift_39_);
v___x_59_ = lean_apply_2(v_toPure_42_, lean_box(0), v_e_44_);
return v___x_59_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3___boxed(lean_object* v_binderType_60_, lean_object* v_____do__lift_61_, lean_object* v_binderName_62_, lean_object* v_binderInfo_63_, lean_object* v_toPure_64_, lean_object* v_body_65_, lean_object* v_e_66_, lean_object* v_____do__lift_67_){
_start:
{
uint8_t v_binderInfo_648__boxed_68_; lean_object* v_res_69_; 
v_binderInfo_648__boxed_68_ = lean_unbox(v_binderInfo_63_);
v_res_69_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3(v_binderType_60_, v_____do__lift_61_, v_binderName_62_, v_binderInfo_648__boxed_68_, v_toPure_64_, v_body_65_, v_e_66_, v_____do__lift_67_);
lean_dec_ref(v_body_65_);
lean_dec_ref(v_binderType_60_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5(lean_object* v_binderType_70_, lean_object* v_____do__lift_71_, lean_object* v_binderName_72_, uint8_t v_binderInfo_73_, lean_object* v_toPure_74_, lean_object* v_body_75_, lean_object* v_e_76_, lean_object* v_____do__lift_77_){
_start:
{
size_t v___x_78_; size_t v___x_79_; uint8_t v___x_80_; 
v___x_78_ = lean_ptr_addr(v_binderType_70_);
v___x_79_ = lean_ptr_addr(v_____do__lift_71_);
v___x_80_ = lean_usize_dec_eq(v___x_78_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec_ref(v_e_76_);
v___x_81_ = l_Lean_Expr_forallE___override(v_binderName_72_, v_____do__lift_71_, v_____do__lift_77_, v_binderInfo_73_);
v___x_82_ = lean_apply_2(v_toPure_74_, lean_box(0), v___x_81_);
return v___x_82_;
}
else
{
size_t v___x_83_; size_t v___x_84_; uint8_t v___x_85_; 
v___x_83_ = lean_ptr_addr(v_body_75_);
v___x_84_ = lean_ptr_addr(v_____do__lift_77_);
v___x_85_ = lean_usize_dec_eq(v___x_83_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec_ref(v_e_76_);
v___x_86_ = l_Lean_Expr_forallE___override(v_binderName_72_, v_____do__lift_71_, v_____do__lift_77_, v_binderInfo_73_);
v___x_87_ = lean_apply_2(v_toPure_74_, lean_box(0), v___x_86_);
return v___x_87_;
}
else
{
uint8_t v___x_88_; 
v___x_88_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_73_, v_binderInfo_73_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec_ref(v_e_76_);
v___x_89_ = l_Lean_Expr_forallE___override(v_binderName_72_, v_____do__lift_71_, v_____do__lift_77_, v_binderInfo_73_);
v___x_90_ = lean_apply_2(v_toPure_74_, lean_box(0), v___x_89_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; 
lean_dec_ref(v_____do__lift_77_);
lean_dec(v_binderName_72_);
lean_dec_ref(v_____do__lift_71_);
v___x_91_ = lean_apply_2(v_toPure_74_, lean_box(0), v_e_76_);
return v___x_91_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5___boxed(lean_object* v_binderType_92_, lean_object* v_____do__lift_93_, lean_object* v_binderName_94_, lean_object* v_binderInfo_95_, lean_object* v_toPure_96_, lean_object* v_body_97_, lean_object* v_e_98_, lean_object* v_____do__lift_99_){
_start:
{
uint8_t v_binderInfo_694__boxed_100_; lean_object* v_res_101_; 
v_binderInfo_694__boxed_100_ = lean_unbox(v_binderInfo_95_);
v_res_101_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5(v_binderType_92_, v_____do__lift_93_, v_binderName_94_, v_binderInfo_694__boxed_100_, v_toPure_96_, v_body_97_, v_e_98_, v_____do__lift_99_);
lean_dec_ref(v_body_97_);
lean_dec_ref(v_binderType_92_);
return v_res_101_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_105_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2));
v___x_106_ = lean_unsigned_to_nat(41u);
v___x_107_ = lean_unsigned_to_nat(30u);
v___x_108_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1));
v___x_109_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0));
v___x_110_ = l_mkPanicMessageWithDecl(v___x_109_, v___x_108_, v___x_107_, v___x_106_, v___x_105_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4(lean_object* v_binderType_111_, lean_object* v_binderName_112_, uint8_t v_binderInfo_113_, lean_object* v_toPure_114_, lean_object* v_body_115_, lean_object* v_e_116_, lean_object* v_inst_117_, lean_object* v_f_118_, lean_object* v_toBind_119_, lean_object* v_____do__lift_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___f_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_121_ = lean_box(v_binderInfo_113_);
lean_inc_ref(v_body_115_);
v___f_122_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_122_, 0, v_binderType_111_);
lean_closure_set(v___f_122_, 1, v_____do__lift_120_);
lean_closure_set(v___f_122_, 2, v_binderName_112_);
lean_closure_set(v___f_122_, 3, v___x_121_);
lean_closure_set(v___f_122_, 4, v_toPure_114_);
lean_closure_set(v___f_122_, 5, v_body_115_);
lean_closure_set(v___f_122_, 6, v_e_116_);
v___x_123_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_117_, v_f_118_, v_body_115_);
v___x_124_ = lean_apply_4(v_toBind_119_, lean_box(0), lean_box(0), v___x_123_, v___f_122_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4___boxed(lean_object* v_binderType_125_, lean_object* v_binderName_126_, lean_object* v_binderInfo_127_, lean_object* v_toPure_128_, lean_object* v_body_129_, lean_object* v_e_130_, lean_object* v_inst_131_, lean_object* v_f_132_, lean_object* v_toBind_133_, lean_object* v_____do__lift_134_){
_start:
{
uint8_t v_binderInfo_773__boxed_135_; lean_object* v_res_136_; 
v_binderInfo_773__boxed_135_ = lean_unbox(v_binderInfo_127_);
v_res_136_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4(v_binderType_125_, v_binderName_126_, v_binderInfo_773__boxed_135_, v_toPure_128_, v_body_129_, v_e_130_, v_inst_131_, v_f_132_, v_toBind_133_, v_____do__lift_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6(lean_object* v_binderType_137_, lean_object* v_binderName_138_, uint8_t v_binderInfo_139_, lean_object* v_toPure_140_, lean_object* v_body_141_, lean_object* v_e_142_, lean_object* v_inst_143_, lean_object* v_f_144_, lean_object* v_toBind_145_, lean_object* v_____do__lift_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___f_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = lean_box(v_binderInfo_139_);
lean_inc_ref(v_body_141_);
v___f_148_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_148_, 0, v_binderType_137_);
lean_closure_set(v___f_148_, 1, v_____do__lift_146_);
lean_closure_set(v___f_148_, 2, v_binderName_138_);
lean_closure_set(v___f_148_, 3, v___x_147_);
lean_closure_set(v___f_148_, 4, v_toPure_140_);
lean_closure_set(v___f_148_, 5, v_body_141_);
lean_closure_set(v___f_148_, 6, v_e_142_);
v___x_149_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_143_, v_f_144_, v_body_141_);
v___x_150_ = lean_apply_4(v_toBind_145_, lean_box(0), lean_box(0), v___x_149_, v___f_148_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6___boxed(lean_object* v_binderType_151_, lean_object* v_binderName_152_, lean_object* v_binderInfo_153_, lean_object* v_toPure_154_, lean_object* v_body_155_, lean_object* v_e_156_, lean_object* v_inst_157_, lean_object* v_f_158_, lean_object* v_toBind_159_, lean_object* v_____do__lift_160_){
_start:
{
uint8_t v_binderInfo_782__boxed_161_; lean_object* v_res_162_; 
v_binderInfo_782__boxed_161_ = lean_unbox(v_binderInfo_153_);
v_res_162_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6(v_binderType_151_, v_binderName_152_, v_binderInfo_782__boxed_161_, v_toPure_154_, v_body_155_, v_e_156_, v_inst_157_, v_f_158_, v_toBind_159_, v_____do__lift_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(lean_object* v_inst_163_, lean_object* v_f_164_, lean_object* v_e_165_){
_start:
{
lean_object* v_toApplicative_166_; lean_object* v_toBind_167_; lean_object* v_toPure_168_; uint8_t v___x_169_; 
v_toApplicative_166_ = lean_ctor_get(v_inst_163_, 0);
v_toBind_167_ = lean_ctor_get(v_inst_163_, 1);
lean_inc(v_toBind_167_);
v_toPure_168_ = lean_ctor_get(v_toApplicative_166_, 1);
v___x_169_ = l_Lean_Expr_hasFVar(v_e_165_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
lean_inc(v_toPure_168_);
lean_dec(v_toBind_167_);
lean_dec(v_f_164_);
lean_dec_ref(v_inst_163_);
v___x_170_ = lean_apply_2(v_toPure_168_, lean_box(0), v_e_165_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_inst_163_);
v___x_172_ = l_instInhabitedOfMonad___redArg(v_inst_163_, v___x_171_);
switch(lean_obj_tag(v_e_165_))
{
case 1:
{
lean_object* v_fvarId_173_; lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
lean_inc(v_toPure_168_);
lean_dec(v___x_172_);
lean_dec_ref(v_inst_163_);
v_fvarId_173_ = lean_ctor_get(v_e_165_, 0);
lean_inc_n(v_fvarId_173_, 2);
v___f_174_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_174_, 0, v_fvarId_173_);
lean_closure_set(v___f_174_, 1, v_toPure_168_);
lean_closure_set(v___f_174_, 2, v_e_165_);
v___x_175_ = lean_apply_1(v_f_164_, v_fvarId_173_);
v___x_176_ = lean_apply_4(v_toBind_167_, lean_box(0), lean_box(0), v___x_175_, v___f_174_);
return v___x_176_;
}
case 2:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec_ref_known(v_e_165_, 1);
lean_dec(v_toBind_167_);
lean_dec(v_f_164_);
lean_dec_ref(v_inst_163_);
v___x_177_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3, &l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3);
v___x_178_ = l_panic___redArg(v___x_172_, v___x_177_);
lean_dec(v___x_172_);
return v___x_178_;
}
case 5:
{
lean_object* v_fn_179_; lean_object* v_arg_180_; lean_object* v___f_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec(v___x_172_);
v_fn_179_ = lean_ctor_get(v_e_165_, 0);
lean_inc_ref_n(v_fn_179_, 2);
v_arg_180_ = lean_ctor_get(v_e_165_, 1);
lean_inc_ref(v_arg_180_);
lean_inc(v_toBind_167_);
lean_inc(v_f_164_);
lean_inc_ref(v_inst_163_);
lean_inc(v_toPure_168_);
v___f_181_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__2), 8, 7);
lean_closure_set(v___f_181_, 0, v_fn_179_);
lean_closure_set(v___f_181_, 1, v_toPure_168_);
lean_closure_set(v___f_181_, 2, v_arg_180_);
lean_closure_set(v___f_181_, 3, v_e_165_);
lean_closure_set(v___f_181_, 4, v_inst_163_);
lean_closure_set(v___f_181_, 5, v_f_164_);
lean_closure_set(v___f_181_, 6, v_toBind_167_);
v___x_182_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_163_, v_f_164_, v_fn_179_);
v___x_183_ = lean_apply_4(v_toBind_167_, lean_box(0), lean_box(0), v___x_182_, v___f_181_);
return v___x_183_;
}
case 6:
{
lean_object* v_binderName_184_; lean_object* v_binderType_185_; lean_object* v_body_186_; uint8_t v_binderInfo_187_; lean_object* v___x_188_; lean_object* v___f_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec(v___x_172_);
v_binderName_184_ = lean_ctor_get(v_e_165_, 0);
lean_inc(v_binderName_184_);
v_binderType_185_ = lean_ctor_get(v_e_165_, 1);
lean_inc_ref_n(v_binderType_185_, 2);
v_body_186_ = lean_ctor_get(v_e_165_, 2);
lean_inc_ref(v_body_186_);
v_binderInfo_187_ = lean_ctor_get_uint8(v_e_165_, sizeof(void*)*3 + 8);
v___x_188_ = lean_box(v_binderInfo_187_);
lean_inc(v_toBind_167_);
lean_inc(v_f_164_);
lean_inc_ref(v_inst_163_);
lean_inc(v_toPure_168_);
v___f_189_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_189_, 0, v_binderType_185_);
lean_closure_set(v___f_189_, 1, v_binderName_184_);
lean_closure_set(v___f_189_, 2, v___x_188_);
lean_closure_set(v___f_189_, 3, v_toPure_168_);
lean_closure_set(v___f_189_, 4, v_body_186_);
lean_closure_set(v___f_189_, 5, v_e_165_);
lean_closure_set(v___f_189_, 6, v_inst_163_);
lean_closure_set(v___f_189_, 7, v_f_164_);
lean_closure_set(v___f_189_, 8, v_toBind_167_);
v___x_190_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_163_, v_f_164_, v_binderType_185_);
v___x_191_ = lean_apply_4(v_toBind_167_, lean_box(0), lean_box(0), v___x_190_, v___f_189_);
return v___x_191_;
}
case 7:
{
lean_object* v_binderName_192_; lean_object* v_binderType_193_; lean_object* v_body_194_; uint8_t v_binderInfo_195_; lean_object* v___x_196_; lean_object* v___f_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec(v___x_172_);
v_binderName_192_ = lean_ctor_get(v_e_165_, 0);
lean_inc(v_binderName_192_);
v_binderType_193_ = lean_ctor_get(v_e_165_, 1);
lean_inc_ref_n(v_binderType_193_, 2);
v_body_194_ = lean_ctor_get(v_e_165_, 2);
lean_inc_ref(v_body_194_);
v_binderInfo_195_ = lean_ctor_get_uint8(v_e_165_, sizeof(void*)*3 + 8);
v___x_196_ = lean_box(v_binderInfo_195_);
lean_inc(v_toBind_167_);
lean_inc(v_f_164_);
lean_inc_ref(v_inst_163_);
lean_inc(v_toPure_168_);
v___f_197_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_197_, 0, v_binderType_193_);
lean_closure_set(v___f_197_, 1, v_binderName_192_);
lean_closure_set(v___f_197_, 2, v___x_196_);
lean_closure_set(v___f_197_, 3, v_toPure_168_);
lean_closure_set(v___f_197_, 4, v_body_194_);
lean_closure_set(v___f_197_, 5, v_e_165_);
lean_closure_set(v___f_197_, 6, v_inst_163_);
lean_closure_set(v___f_197_, 7, v_f_164_);
lean_closure_set(v___f_197_, 8, v_toBind_167_);
v___x_198_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_163_, v_f_164_, v_binderType_193_);
v___x_199_ = lean_apply_4(v_toBind_167_, lean_box(0), lean_box(0), v___x_198_, v___f_197_);
return v___x_199_;
}
case 8:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec_ref_known(v_e_165_, 4);
lean_dec(v_toBind_167_);
lean_dec(v_f_164_);
lean_dec_ref(v_inst_163_);
v___x_200_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3, &l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3);
v___x_201_ = l_panic___redArg(v___x_172_, v___x_200_);
lean_dec(v___x_172_);
return v___x_201_;
}
case 11:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec_ref_known(v_e_165_, 3);
lean_dec(v_toBind_167_);
lean_dec(v_f_164_);
lean_dec_ref(v_inst_163_);
v___x_202_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3, &l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3);
v___x_203_ = l_panic___redArg(v___x_172_, v___x_202_);
lean_dec(v___x_172_);
return v___x_203_;
}
default: 
{
lean_object* v___x_204_; 
lean_inc(v_toPure_168_);
lean_dec(v___x_172_);
lean_dec(v_toBind_167_);
lean_dec(v_f_164_);
lean_dec_ref(v_inst_163_);
v___x_204_ = lean_apply_2(v_toPure_168_, lean_box(0), v_e_165_);
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__2(lean_object* v_fn_205_, lean_object* v_toPure_206_, lean_object* v_arg_207_, lean_object* v_e_208_, lean_object* v_inst_209_, lean_object* v_f_210_, lean_object* v_toBind_211_, lean_object* v_____do__lift_212_){
_start:
{
lean_object* v___f_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
lean_inc_ref(v_arg_207_);
v___f_213_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_213_, 0, v_fn_205_);
lean_closure_set(v___f_213_, 1, v_____do__lift_212_);
lean_closure_set(v___f_213_, 2, v_toPure_206_);
lean_closure_set(v___f_213_, 3, v_arg_207_);
lean_closure_set(v___f_213_, 4, v_e_208_);
v___x_214_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_209_, v_f_210_, v_arg_207_);
v___x_215_ = lean_apply_4(v_toBind_211_, lean_box(0), lean_box(0), v___x_214_, v___f_213_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM(lean_object* v_m_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_f_219_, lean_object* v_e_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_218_, v_f_219_, v_e_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___boxed(lean_object* v_m_222_, lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_f_225_, lean_object* v_e_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Compiler_LCNF_Expr_mapFVarM(v_m_222_, v_inst_223_, v_inst_224_, v_f_225_, v_e_226_);
lean_dec(v_inst_223_);
return v_res_227_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_229_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2));
v___x_230_ = lean_unsigned_to_nat(40u);
v___x_231_ = lean_unsigned_to_nat(49u);
v___x_232_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0));
v___x_233_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0));
v___x_234_ = l_mkPanicMessageWithDecl(v___x_233_, v___x_232_, v___x_231_, v___x_230_, v___x_229_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__1(lean_object* v_inst_235_, lean_object* v_f_236_, lean_object* v_arg_237_, lean_object* v_____r_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_235_, v_f_236_, v_arg_237_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(lean_object* v_inst_240_, lean_object* v_f_241_, lean_object* v_e_242_){
_start:
{
lean_object* v_toApplicative_243_; lean_object* v_toBind_244_; lean_object* v_ty_246_; lean_object* v_body_247_; lean_object* v_toPure_251_; uint8_t v___x_252_; 
v_toApplicative_243_ = lean_ctor_get(v_inst_240_, 0);
v_toBind_244_ = lean_ctor_get(v_inst_240_, 1);
lean_inc(v_toBind_244_);
v_toPure_251_ = lean_ctor_get(v_toApplicative_243_, 1);
v___x_252_ = l_Lean_Expr_hasFVar(v_e_242_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_inc(v_toPure_251_);
lean_dec(v_toBind_244_);
lean_dec_ref(v_e_242_);
lean_dec(v_f_241_);
lean_dec_ref(v_inst_240_);
v___x_253_ = lean_box(0);
v___x_254_ = lean_apply_2(v_toPure_251_, lean_box(0), v___x_253_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_box(0);
lean_inc_ref(v_inst_240_);
v___x_256_ = l_instInhabitedOfMonad___redArg(v_inst_240_, v___x_255_);
switch(lean_obj_tag(v_e_242_))
{
case 1:
{
lean_object* v_fvarId_257_; lean_object* v___x_258_; 
lean_dec(v___x_256_);
lean_dec(v_toBind_244_);
lean_dec_ref(v_inst_240_);
v_fvarId_257_ = lean_ctor_get(v_e_242_, 0);
lean_inc(v_fvarId_257_);
lean_dec_ref_known(v_e_242_, 1);
v___x_258_ = lean_apply_1(v_f_241_, v_fvarId_257_);
return v___x_258_;
}
case 2:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec_ref_known(v_e_242_, 1);
lean_dec(v_toBind_244_);
lean_dec(v_f_241_);
lean_dec_ref(v_inst_240_);
v___x_259_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1, &l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1);
v___x_260_ = l_panic___redArg(v___x_256_, v___x_259_);
lean_dec(v___x_256_);
return v___x_260_;
}
case 5:
{
lean_object* v_fn_261_; lean_object* v_arg_262_; lean_object* v___f_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v___x_256_);
v_fn_261_ = lean_ctor_get(v_e_242_, 0);
lean_inc_ref(v_fn_261_);
v_arg_262_ = lean_ctor_get(v_e_242_, 1);
lean_inc_ref(v_arg_262_);
lean_dec_ref_known(v_e_242_, 2);
lean_inc(v_f_241_);
lean_inc_ref(v_inst_240_);
v___f_263_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_263_, 0, v_inst_240_);
lean_closure_set(v___f_263_, 1, v_f_241_);
lean_closure_set(v___f_263_, 2, v_arg_262_);
v___x_264_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_240_, v_f_241_, v_fn_261_);
v___x_265_ = lean_apply_4(v_toBind_244_, lean_box(0), lean_box(0), v___x_264_, v___f_263_);
return v___x_265_;
}
case 6:
{
lean_object* v_binderType_266_; lean_object* v_body_267_; 
lean_dec(v___x_256_);
v_binderType_266_ = lean_ctor_get(v_e_242_, 1);
lean_inc_ref(v_binderType_266_);
v_body_267_ = lean_ctor_get(v_e_242_, 2);
lean_inc_ref(v_body_267_);
lean_dec_ref_known(v_e_242_, 3);
v_ty_246_ = v_binderType_266_;
v_body_247_ = v_body_267_;
goto v___jp_245_;
}
case 7:
{
lean_object* v_binderType_268_; lean_object* v_body_269_; 
lean_dec(v___x_256_);
v_binderType_268_ = lean_ctor_get(v_e_242_, 1);
lean_inc_ref(v_binderType_268_);
v_body_269_ = lean_ctor_get(v_e_242_, 2);
lean_inc_ref(v_body_269_);
lean_dec_ref_known(v_e_242_, 3);
v_ty_246_ = v_binderType_268_;
v_body_247_ = v_body_269_;
goto v___jp_245_;
}
case 8:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec_ref_known(v_e_242_, 4);
lean_dec(v_toBind_244_);
lean_dec(v_f_241_);
lean_dec_ref(v_inst_240_);
v___x_270_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1, &l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1);
v___x_271_ = l_panic___redArg(v___x_256_, v___x_270_);
lean_dec(v___x_256_);
return v___x_271_;
}
case 11:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec_ref_known(v_e_242_, 3);
lean_dec(v_toBind_244_);
lean_dec(v_f_241_);
lean_dec_ref(v_inst_240_);
v___x_272_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1, &l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1);
v___x_273_ = l_panic___redArg(v___x_256_, v___x_272_);
lean_dec(v___x_256_);
return v___x_273_;
}
default: 
{
lean_object* v___x_274_; 
lean_inc(v_toPure_251_);
lean_dec(v___x_256_);
lean_dec(v_toBind_244_);
lean_dec_ref(v_e_242_);
lean_dec(v_f_241_);
lean_dec_ref(v_inst_240_);
v___x_274_ = lean_apply_2(v_toPure_251_, lean_box(0), v___x_255_);
return v___x_274_;
}
}
}
v___jp_245_:
{
lean_object* v___f_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
lean_inc(v_f_241_);
lean_inc_ref(v_inst_240_);
v___f_248_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_248_, 0, v_inst_240_);
lean_closure_set(v___f_248_, 1, v_f_241_);
lean_closure_set(v___f_248_, 2, v_body_247_);
v___x_249_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_240_, v_f_241_, v_ty_246_);
v___x_250_ = lean_apply_4(v_toBind_244_, lean_box(0), lean_box(0), v___x_249_, v___f_248_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__0(lean_object* v_inst_275_, lean_object* v_f_276_, lean_object* v_body_277_, lean_object* v_____r_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_275_, v_f_276_, v_body_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM(lean_object* v_m_280_, lean_object* v_inst_281_, lean_object* v_f_282_, lean_object* v_e_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_281_, v_f_282_, v_e_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0(lean_object* v_m_285_, lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_287_, v___y_288_, v___y_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0___boxed(lean_object* v_m_291_, lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0(v_m_291_, v_inst_292_, v_inst_293_, v___y_294_, v___y_295_);
lean_dec(v_inst_292_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__1(lean_object* v_m_297_, lean_object* v_inst_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_298_, v___y_299_, v___y_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__0(lean_object* v_arg_308_, lean_object* v_toPure_309_, lean_object* v_____do__lift_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(v_arg_308_, v_____do__lift_310_);
v___x_312_ = lean_apply_2(v_toPure_309_, lean_box(0), v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1(uint8_t v_pu_313_, lean_object* v_arg_314_, lean_object* v_toPure_315_, lean_object* v_____do__lift_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_313_, v_arg_314_, v_____do__lift_316_);
v___x_318_ = lean_apply_2(v_toPure_315_, lean_box(0), v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1___boxed(lean_object* v_pu_319_, lean_object* v_arg_320_, lean_object* v_toPure_321_, lean_object* v_____do__lift_322_){
_start:
{
uint8_t v_pu_boxed_323_; lean_object* v_res_324_; 
v_pu_boxed_323_ = lean_unbox(v_pu_319_);
v_res_324_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1(v_pu_boxed_323_, v_arg_320_, v_toPure_321_, v_____do__lift_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(uint8_t v_pu_325_, lean_object* v_inst_326_, lean_object* v_f_327_, lean_object* v_arg_328_){
_start:
{
switch(lean_obj_tag(v_arg_328_))
{
case 0:
{
lean_object* v_toApplicative_329_; lean_object* v_toPure_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_toApplicative_329_ = lean_ctor_get(v_inst_326_, 0);
lean_inc_ref(v_toApplicative_329_);
lean_dec(v_f_327_);
lean_dec_ref(v_inst_326_);
v_toPure_330_ = lean_ctor_get(v_toApplicative_329_, 1);
lean_inc(v_toPure_330_);
lean_dec_ref(v_toApplicative_329_);
v___x_331_ = lean_box(0);
v___x_332_ = lean_apply_2(v_toPure_330_, lean_box(0), v___x_331_);
return v___x_332_;
}
case 1:
{
lean_object* v_toApplicative_333_; lean_object* v_toBind_334_; lean_object* v_toPure_335_; lean_object* v_fvarId_336_; lean_object* v___f_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_toApplicative_333_ = lean_ctor_get(v_inst_326_, 0);
lean_inc_ref(v_toApplicative_333_);
v_toBind_334_ = lean_ctor_get(v_inst_326_, 1);
lean_inc(v_toBind_334_);
lean_dec_ref(v_inst_326_);
v_toPure_335_ = lean_ctor_get(v_toApplicative_333_, 1);
lean_inc(v_toPure_335_);
lean_dec_ref(v_toApplicative_333_);
v_fvarId_336_ = lean_ctor_get(v_arg_328_, 0);
lean_inc(v_fvarId_336_);
v___f_337_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_337_, 0, v_arg_328_);
lean_closure_set(v___f_337_, 1, v_toPure_335_);
v___x_338_ = lean_apply_1(v_f_327_, v_fvarId_336_);
v___x_339_ = lean_apply_4(v_toBind_334_, lean_box(0), lean_box(0), v___x_338_, v___f_337_);
return v___x_339_;
}
default: 
{
lean_object* v_toApplicative_340_; lean_object* v_toBind_341_; lean_object* v_toPure_342_; lean_object* v_expr_343_; lean_object* v___x_344_; lean_object* v___f_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_toApplicative_340_ = lean_ctor_get(v_inst_326_, 0);
v_toBind_341_ = lean_ctor_get(v_inst_326_, 1);
lean_inc(v_toBind_341_);
v_toPure_342_ = lean_ctor_get(v_toApplicative_340_, 1);
v_expr_343_ = lean_ctor_get(v_arg_328_, 0);
lean_inc_ref(v_expr_343_);
v___x_344_ = lean_box(v_pu_325_);
lean_inc(v_toPure_342_);
v___f_345_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_345_, 0, v___x_344_);
lean_closure_set(v___f_345_, 1, v_arg_328_);
lean_closure_set(v___f_345_, 2, v_toPure_342_);
v___x_346_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_326_, v_f_327_, v_expr_343_);
v___x_347_ = lean_apply_4(v_toBind_341_, lean_box(0), lean_box(0), v___x_346_, v___f_345_);
return v___x_347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___boxed(lean_object* v_pu_348_, lean_object* v_inst_349_, lean_object* v_f_350_, lean_object* v_arg_351_){
_start:
{
uint8_t v_pu_boxed_352_; lean_object* v_res_353_; 
v_pu_boxed_352_ = lean_unbox(v_pu_348_);
v_res_353_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_boxed_352_, v_inst_349_, v_f_350_, v_arg_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM(lean_object* v_m_354_, uint8_t v_pu_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_f_358_, lean_object* v_arg_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_355_, v_inst_357_, v_f_358_, v_arg_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___boxed(lean_object* v_m_361_, lean_object* v_pu_362_, lean_object* v_inst_363_, lean_object* v_inst_364_, lean_object* v_f_365_, lean_object* v_arg_366_){
_start:
{
uint8_t v_pu_boxed_367_; lean_object* v_res_368_; 
v_pu_boxed_367_ = lean_unbox(v_pu_362_);
v_res_368_ = l_Lean_Compiler_LCNF_Arg_mapFVarM(v_m_361_, v_pu_boxed_367_, v_inst_363_, v_inst_364_, v_f_365_, v_arg_366_);
lean_dec(v_inst_363_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(lean_object* v_inst_369_, lean_object* v_f_370_, lean_object* v_arg_371_){
_start:
{
switch(lean_obj_tag(v_arg_371_))
{
case 0:
{
lean_object* v_toApplicative_372_; lean_object* v_toPure_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_toApplicative_372_ = lean_ctor_get(v_inst_369_, 0);
lean_inc_ref(v_toApplicative_372_);
lean_dec(v_f_370_);
lean_dec_ref(v_inst_369_);
v_toPure_373_ = lean_ctor_get(v_toApplicative_372_, 1);
lean_inc(v_toPure_373_);
lean_dec_ref(v_toApplicative_372_);
v___x_374_ = lean_box(0);
v___x_375_ = lean_apply_2(v_toPure_373_, lean_box(0), v___x_374_);
return v___x_375_;
}
case 1:
{
lean_object* v_fvarId_376_; lean_object* v___x_377_; 
lean_dec_ref(v_inst_369_);
v_fvarId_376_ = lean_ctor_get(v_arg_371_, 0);
lean_inc(v_fvarId_376_);
lean_dec_ref_known(v_arg_371_, 1);
v___x_377_ = lean_apply_1(v_f_370_, v_fvarId_376_);
return v___x_377_;
}
default: 
{
lean_object* v_expr_378_; lean_object* v___x_379_; 
v_expr_378_ = lean_ctor_get(v_arg_371_, 0);
lean_inc_ref(v_expr_378_);
lean_dec_ref_known(v_arg_371_, 1);
v___x_379_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_369_, v_f_370_, v_expr_378_);
return v___x_379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM(lean_object* v_m_380_, uint8_t v_pu_381_, lean_object* v_inst_382_, lean_object* v_f_383_, lean_object* v_arg_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_382_, v_f_383_, v_arg_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___boxed(lean_object* v_m_386_, lean_object* v_pu_387_, lean_object* v_inst_388_, lean_object* v_f_389_, lean_object* v_arg_390_){
_start:
{
uint8_t v_pu_boxed_391_; lean_object* v_res_392_; 
v_pu_boxed_391_ = lean_unbox(v_pu_387_);
v_res_392_ = l_Lean_Compiler_LCNF_Arg_forFVarM(v_m_386_, v_pu_boxed_391_, v_inst_388_, v_f_389_, v_arg_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0(uint8_t v_pu_393_, lean_object* v_m_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_393_, v_inst_396_, v___y_397_, v___y_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0___boxed(lean_object* v_pu_400_, lean_object* v_m_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
uint8_t v_pu_boxed_406_; lean_object* v_res_407_; 
v_pu_boxed_406_ = lean_unbox(v_pu_400_);
v_res_407_ = l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0(v_pu_boxed_406_, v_m_401_, v_inst_402_, v_inst_403_, v___y_404_, v___y_405_);
lean_dec(v_inst_402_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__1(lean_object* v_m_408_, lean_object* v_inst_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_409_, v___y_410_, v___y_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg(uint8_t v_pu_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___f_416_; lean_object* v___f_417_; lean_object* v___x_418_; 
v___x_415_ = lean_box(v_pu_414_);
v___f_416_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_416_, 0, v___x_415_);
v___f_417_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarArg___closed__0));
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v___f_416_);
lean_ctor_set(v___x_418_, 1, v___f_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___boxed(lean_object* v_pu_419_){
_start:
{
uint8_t v_pu_boxed_420_; lean_object* v_res_421_; 
v_pu_boxed_420_ = lean_unbox(v_pu_419_);
v_res_421_ = l_Lean_Compiler_LCNF_instTraverseFVarArg(v_pu_boxed_420_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0(uint8_t v_pu_422_, lean_object* v_inst_423_, lean_object* v_f_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_422_, v_inst_423_, v_f_424_, v___y_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_427_, lean_object* v_inst_428_, lean_object* v_f_429_, lean_object* v___y_430_){
_start:
{
uint8_t v_pu_boxed_431_; lean_object* v_res_432_; 
v_pu_boxed_431_ = lean_unbox(v_pu_427_);
v_res_432_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0(v_pu_boxed_431_, v_inst_428_, v_f_429_, v___y_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1(lean_object* v_e_433_, lean_object* v_toPure_434_, lean_object* v_____do__lift_435_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_433_, v_____do__lift_435_);
v___x_437_ = lean_apply_2(v_toPure_434_, lean_box(0), v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(uint8_t v_pu_438_, lean_object* v_e_439_, lean_object* v_toPure_440_, lean_object* v_____do__lift_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_438_, v_e_439_, v_____do__lift_441_);
v___x_443_ = lean_apply_2(v_toPure_440_, lean_box(0), v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed(lean_object* v_pu_444_, lean_object* v_e_445_, lean_object* v_toPure_446_, lean_object* v_____do__lift_447_){
_start:
{
uint8_t v_pu_boxed_448_; lean_object* v_res_449_; 
v_pu_boxed_448_ = lean_unbox(v_pu_444_);
v_res_449_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(v_pu_boxed_448_, v_e_445_, v_toPure_446_, v_____do__lift_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7(lean_object* v_e_450_, lean_object* v_____do__lift_451_, lean_object* v_toPure_452_, lean_object* v_____do__lift_453_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___redArg(v_e_450_, v_____do__lift_451_, v_____do__lift_453_);
v___x_455_ = lean_apply_2(v_toPure_452_, lean_box(0), v___x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3(lean_object* v_e_456_, lean_object* v_toPure_457_, lean_object* v_args_458_, lean_object* v_inst_459_, lean_object* v___f_460_, lean_object* v_toBind_461_, lean_object* v_____do__lift_462_){
_start:
{
lean_object* v___f_463_; size_t v_sz_464_; size_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___f_463_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7), 4, 3);
lean_closure_set(v___f_463_, 0, v_e_456_);
lean_closure_set(v___f_463_, 1, v_____do__lift_462_);
lean_closure_set(v___f_463_, 2, v_toPure_457_);
v_sz_464_ = lean_array_size(v_args_458_);
v___x_465_ = ((size_t)0ULL);
v___x_466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_459_, v___f_460_, v_sz_464_, v___x_465_, v_args_458_);
v___x_467_ = lean_apply_4(v_toBind_461_, lean_box(0), lean_box(0), v___x_466_, v___f_463_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8(lean_object* v_e_468_, lean_object* v_n_469_, lean_object* v_toPure_470_, lean_object* v_____do__lift_471_){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp___redArg(v_e_468_, v_n_469_, v_____do__lift_471_);
v___x_473_ = lean_apply_2(v_toPure_470_, lean_box(0), v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(lean_object* v_e_474_, lean_object* v_____do__lift_475_, lean_object* v_i_476_, uint8_t v_updateHeader_477_, lean_object* v_toPure_478_, lean_object* v_____do__lift_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp___redArg(v_e_474_, v_____do__lift_475_, v_i_476_, v_updateHeader_477_, v_____do__lift_479_);
v___x_481_ = lean_apply_2(v_toPure_478_, lean_box(0), v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed(lean_object* v_e_482_, lean_object* v_____do__lift_483_, lean_object* v_i_484_, lean_object* v_updateHeader_485_, lean_object* v_toPure_486_, lean_object* v_____do__lift_487_){
_start:
{
uint8_t v_updateHeader_630__boxed_488_; lean_object* v_res_489_; 
v_updateHeader_630__boxed_488_ = lean_unbox(v_updateHeader_485_);
v_res_489_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(v_e_482_, v_____do__lift_483_, v_i_484_, v_updateHeader_630__boxed_488_, v_toPure_486_, v_____do__lift_487_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(lean_object* v_e_490_, lean_object* v_i_491_, uint8_t v_updateHeader_492_, lean_object* v_toPure_493_, lean_object* v_args_494_, lean_object* v_inst_495_, lean_object* v___f_496_, lean_object* v_toBind_497_, lean_object* v_____do__lift_498_){
_start:
{
lean_object* v___x_499_; lean_object* v___f_500_; size_t v_sz_501_; size_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_499_ = lean_box(v_updateHeader_492_);
v___f_500_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_500_, 0, v_e_490_);
lean_closure_set(v___f_500_, 1, v_____do__lift_498_);
lean_closure_set(v___f_500_, 2, v_i_491_);
lean_closure_set(v___f_500_, 3, v___x_499_);
lean_closure_set(v___f_500_, 4, v_toPure_493_);
v_sz_501_ = lean_array_size(v_args_494_);
v___x_502_ = ((size_t)0ULL);
v___x_503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_495_, v___f_496_, v_sz_501_, v___x_502_, v_args_494_);
v___x_504_ = lean_apply_4(v_toBind_497_, lean_box(0), lean_box(0), v___x_503_, v___f_500_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed(lean_object* v_e_505_, lean_object* v_i_506_, lean_object* v_updateHeader_507_, lean_object* v_toPure_508_, lean_object* v_args_509_, lean_object* v_inst_510_, lean_object* v___f_511_, lean_object* v_toBind_512_, lean_object* v_____do__lift_513_){
_start:
{
uint8_t v_updateHeader_645__boxed_514_; lean_object* v_res_515_; 
v_updateHeader_645__boxed_514_ = lean_unbox(v_updateHeader_507_);
v_res_515_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(v_e_505_, v_i_506_, v_updateHeader_645__boxed_514_, v_toPure_508_, v_args_509_, v_inst_510_, v___f_511_, v_toBind_512_, v_____do__lift_513_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6(lean_object* v_e_516_, lean_object* v_ty_517_, lean_object* v_toPure_518_, lean_object* v_____do__lift_519_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp___redArg(v_e_516_, v_ty_517_, v_____do__lift_519_);
v___x_521_ = lean_apply_2(v_toPure_518_, lean_box(0), v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9(lean_object* v_e_522_, lean_object* v_toPure_523_, lean_object* v_____do__lift_524_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp___redArg(v_e_522_, v_____do__lift_524_);
v___x_526_ = lean_apply_2(v_toPure_523_, lean_box(0), v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10(lean_object* v_e_527_, lean_object* v_toPure_528_, lean_object* v_____do__lift_529_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp___redArg(v_e_527_, v_____do__lift_529_);
v___x_531_ = lean_apply_2(v_toPure_528_, lean_box(0), v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(uint8_t v_pu_532_, lean_object* v_inst_533_, lean_object* v_f_534_, lean_object* v_e_535_){
_start:
{
lean_object* v_toApplicative_536_; lean_object* v_toBind_537_; lean_object* v_toPure_538_; lean_object* v___x_539_; lean_object* v___f_540_; lean_object* v___f_541_; lean_object* v_args_543_; lean_object* v___x_548_; lean_object* v___f_549_; lean_object* v_fvarId_551_; 
v_toApplicative_536_ = lean_ctor_get(v_inst_533_, 0);
v_toBind_537_ = lean_ctor_get(v_inst_533_, 1);
lean_inc(v_toBind_537_);
v_toPure_538_ = lean_ctor_get(v_toApplicative_536_, 1);
v___x_539_ = lean_box(v_pu_532_);
lean_inc(v_f_534_);
lean_inc_ref(v_inst_533_);
v___f_540_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_540_, 0, v___x_539_);
lean_closure_set(v___f_540_, 1, v_inst_533_);
lean_closure_set(v___f_540_, 2, v_f_534_);
lean_inc_n(v_toPure_538_, 2);
lean_inc_n(v_e_535_, 2);
v___f_541_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1), 3, 2);
lean_closure_set(v___f_541_, 0, v_e_535_);
lean_closure_set(v___f_541_, 1, v_toPure_538_);
v___x_548_ = lean_box(v_pu_532_);
v___f_549_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_549_, 0, v___x_548_);
lean_closure_set(v___f_549_, 1, v_e_535_);
lean_closure_set(v___f_549_, 2, v_toPure_538_);
switch(lean_obj_tag(v_e_535_))
{
case 2:
{
lean_object* v_struct_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref(v___f_541_);
lean_dec_ref(v___f_540_);
lean_dec_ref(v_inst_533_);
v_struct_554_ = lean_ctor_get(v_e_535_, 2);
lean_inc(v_struct_554_);
lean_dec_ref_known(v_e_535_, 3);
v___x_555_ = lean_apply_1(v_f_534_, v_struct_554_);
v___x_556_ = lean_apply_4(v_toBind_537_, lean_box(0), lean_box(0), v___x_555_, v___f_549_);
return v___x_556_;
}
case 3:
{
lean_object* v_args_557_; size_t v_sz_558_; size_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec_ref(v___f_549_);
lean_dec(v_f_534_);
v_args_557_ = lean_ctor_get(v_e_535_, 2);
lean_inc_ref(v_args_557_);
lean_dec_ref_known(v_e_535_, 3);
v_sz_558_ = lean_array_size(v_args_557_);
v___x_559_ = ((size_t)0ULL);
v___x_560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_533_, v___f_540_, v_sz_558_, v___x_559_, v_args_557_);
v___x_561_ = lean_apply_4(v_toBind_537_, lean_box(0), lean_box(0), v___x_560_, v___f_541_);
return v___x_561_;
}
case 4:
{
lean_object* v_fvarId_562_; lean_object* v_args_563_; lean_object* v___f_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
lean_inc(v_toPure_538_);
lean_dec_ref(v___f_549_);
lean_dec_ref(v___f_541_);
v_fvarId_562_ = lean_ctor_get(v_e_535_, 0);
lean_inc(v_fvarId_562_);
v_args_563_ = lean_ctor_get(v_e_535_, 1);
lean_inc_ref(v_args_563_);
lean_inc(v_toBind_537_);
v___f_564_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3), 7, 6);
lean_closure_set(v___f_564_, 0, v_e_535_);
lean_closure_set(v___f_564_, 1, v_toPure_538_);
lean_closure_set(v___f_564_, 2, v_args_563_);
lean_closure_set(v___f_564_, 3, v_inst_533_);
lean_closure_set(v___f_564_, 4, v___f_540_);
lean_closure_set(v___f_564_, 5, v_toBind_537_);
v___x_565_ = lean_apply_1(v_f_534_, v_fvarId_562_);
v___x_566_ = lean_apply_4(v_toBind_537_, lean_box(0), lean_box(0), v___x_565_, v___f_564_);
return v___x_566_;
}
case 5:
{
lean_object* v_args_567_; size_t v_sz_568_; size_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec_ref(v___f_549_);
lean_dec(v_f_534_);
v_args_567_ = lean_ctor_get(v_e_535_, 1);
lean_inc_ref(v_args_567_);
lean_dec_ref_known(v_e_535_, 2);
v_sz_568_ = lean_array_size(v_args_567_);
v___x_569_ = ((size_t)0ULL);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_533_, v___f_540_, v_sz_568_, v___x_569_, v_args_567_);
v___x_571_ = lean_apply_4(v_toBind_537_, lean_box(0), lean_box(0), v___x_570_, v___f_541_);
return v___x_571_;
}
case 6:
{
lean_object* v_var_572_; 
lean_dec_ref(v___f_541_);
lean_dec_ref(v___f_540_);
lean_dec_ref(v_inst_533_);
v_var_572_ = lean_ctor_get(v_e_535_, 1);
lean_inc(v_var_572_);
lean_dec_ref_known(v_e_535_, 2);
v_fvarId_551_ = v_var_572_;
goto v___jp_550_;
}
case 7:
{
lean_object* v_var_573_; 
lean_dec_ref(v___f_541_);
lean_dec_ref(v___f_540_);
lean_dec_ref(v_inst_533_);
v_var_573_ = lean_ctor_get(v_e_535_, 1);
lean_inc(v_var_573_);
lean_dec_ref_known(v_e_535_, 2);
v_fvarId_551_ = v_var_573_;
goto v___jp_550_;
}
case 8:
{
lean_object* v_var_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec_ref(v___f_541_);
lean_dec_ref(v___f_540_);
lean_dec_ref(v_inst_533_);
v_var_574_ = lean_ctor_get(v_e_535_, 2);
lean_inc(v_var_574_);
lean_dec_ref_known(v_e_535_, 3);
v___x_575_ = lean_apply_1(v_f_534_, v_var_574_);
v___x_576_ = lean_apply_4(v_toBind_537_, lean_box(0), lean_box(0), v___x_575_, v___f_549_);
return v___x_576_;
}
case 9:
{
lean_object* v_args_577_; 
lean_dec_ref(v___f_549_);
lean_dec(v_f_534_);
v_args_577_ = lean_ctor_get(v_e_535_, 1);
lean_inc_ref(v_args_577_);
lean_dec_ref_known(v_e_535_, 2);
v_args_543_ = v_args_577_;
goto v___jp_542_;
}
case 10:
{
lean_object* v_args_578_; 
lean_dec_ref(v___f_549_);
lean_dec(v_f_534_);
v_args_578_ = lean_ctor_get(v_e_535_, 1);
lean_inc_ref(v_args_578_);
lean_dec_ref_known(v_e_535_, 2);
v_args_543_ = v_args_578_;
goto v___jp_542_;
}
case 11:
{
lean_object* v_n_579_; lean_object* v_var_580_; lean_object* v___f_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_inc(v_toPure_538_);
lean_dec_ref(v___f_549_);
lean_dec_ref(v___f_541_);
lean_dec_ref(v___f_540_);
lean_dec_ref(v_inst_533_);
v_n_579_ = lean_ctor_get(v_e_535_, 0);
lean_inc(v_n_579_);
v_var_580_ = lean_ctor_get(v_e_535_, 1);
lean_inc(v_var_580_);
v___f_581_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8), 4, 3);
lean_closure_set(v___f_581_, 0, v_e_535_);
lean_closure_set(v___f_581_, 1, v_n_579_);
lean_closure_set(v___f_581_, 2, v_toPure_538_);
v___x_582_ = lean_apply_1(v_f_534_, v_var_580_);
v___x_583_ = lean_apply_4(v_toBind_537_, lean_box(0), lean_box(0), v___x_582_, v___f_581_);
return v___x_583_;
}
case 12:
{
lean_object* v_var_584_; lean_object* v_i_585_; uint8_t v_updateHeader_586_; lean_object* v_args_587_; lean_object* v___x_588_; lean_object* v___f_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
lean_inc(v_toPure_538_);
lean_dec_ref(v___f_549_);
lean_dec_ref(v___f_541_);
v_var_584_ = lean_ctor_get(v_e_535_, 0);
lean_inc(v_var_584_);
v_i_585_ = lean_ctor_get(v_e_535_, 1);
lean_inc_ref(v_i_585_);
v_updateHeader_586_ = lean_ctor_get_uint8(v_e_535_, sizeof(void*)*3);
v_args_587_ = lean_ctor_get(v_e_535_, 2);
lean_inc_ref(v_args_587_);
v___x_588_ = lean_box(v_updateHeader_586_);
lean_inc(v_toBind_537_);
v___f_589_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_589_, 0, v_e_535_);
lean_closure_set(v___f_589_, 1, v_i_585_);
lean_closure_set(v___f_589_, 2, v___x_588_);
lean_closure_set(v___f_589_, 3, v_toPure_538_);
lean_closure_set(v___f_589_, 4, v_args_587_);
lean_closure_set(v___f_589_, 5, v_inst_533_);
lean_closure_set(v___f_589_, 6, v___f_540_);
lean_closure_set(v___f_589_, 7, v_toBind_537_);
v___x_590_ = lean_apply_1(v_f_534_, v_var_584_);
v___x_591_ = lean_apply_4(v_toBind_537_, lean_box(0), lean_box(0), v___x_590_, v___f_589_);
return v___x_591_;
}
case 13:
{
lean_object* v_ty_592_; lean_object* v_fvarId_593_; lean_object* v___f_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
lean_inc(v_toPure_538_);
lean_dec_ref(v___f_549_);
lean_dec_ref(v___f_541_);
lean_dec_ref(v___f_540_);
lean_dec_ref(v_inst_533_);
v_ty_592_ = lean_ctor_get(v_e_535_, 0);
lean_inc_ref(v_ty_592_);
v_fvarId_593_ = lean_ctor_get(v_e_535_, 1);
lean_inc(v_fvarId_593_);
v___f_594_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6), 4, 3);
lean_closure_set(v___f_594_, 0, v_e_535_);
lean_closure_set(v___f_594_, 1, v_ty_592_);
lean_closure_set(v___f_594_, 2, v_toPure_538_);
v___x_595_ = lean_apply_1(v_f_534_, v_fvarId_593_);
v___x_596_ = lean_apply_4(v_toBind_537_, lean_box(0), lean_box(0), v___x_595_, v___f_594_);
return v___x_596_;
}
case 14:
{
lean_object* v_fvarId_597_; lean_object* v___f_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
lean_inc(v_toPure_538_);
lean_dec_ref(v___f_549_);
lean_dec_ref(v___f_541_);
lean_dec_ref(v___f_540_);
lean_dec_ref(v_inst_533_);
v_fvarId_597_ = lean_ctor_get(v_e_535_, 0);
lean_inc(v_fvarId_597_);
v___f_598_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9), 3, 2);
lean_closure_set(v___f_598_, 0, v_e_535_);
lean_closure_set(v___f_598_, 1, v_toPure_538_);
v___x_599_ = lean_apply_1(v_f_534_, v_fvarId_597_);
v___x_600_ = lean_apply_4(v_toBind_537_, lean_box(0), lean_box(0), v___x_599_, v___f_598_);
return v___x_600_;
}
case 15:
{
lean_object* v_fvarId_601_; lean_object* v___f_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
lean_inc(v_toPure_538_);
lean_dec_ref(v___f_549_);
lean_dec_ref(v___f_541_);
lean_dec_ref(v___f_540_);
lean_dec_ref(v_inst_533_);
v_fvarId_601_ = lean_ctor_get(v_e_535_, 0);
lean_inc(v_fvarId_601_);
v___f_602_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10), 3, 2);
lean_closure_set(v___f_602_, 0, v_e_535_);
lean_closure_set(v___f_602_, 1, v_toPure_538_);
v___x_603_ = lean_apply_1(v_f_534_, v_fvarId_601_);
v___x_604_ = lean_apply_4(v_toBind_537_, lean_box(0), lean_box(0), v___x_603_, v___f_602_);
return v___x_604_;
}
default: 
{
lean_object* v___x_605_; 
lean_inc(v_toPure_538_);
lean_dec_ref(v___f_549_);
lean_dec_ref(v___f_541_);
lean_dec_ref(v___f_540_);
lean_dec(v_toBind_537_);
lean_dec(v_f_534_);
lean_dec_ref(v_inst_533_);
v___x_605_ = lean_apply_2(v_toPure_538_, lean_box(0), v_e_535_);
return v___x_605_;
}
}
v___jp_542_:
{
size_t v_sz_544_; size_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_sz_544_ = lean_array_size(v_args_543_);
v___x_545_ = ((size_t)0ULL);
v___x_546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_533_, v___f_540_, v_sz_544_, v___x_545_, v_args_543_);
v___x_547_ = lean_apply_4(v_toBind_537_, lean_box(0), lean_box(0), v___x_546_, v___f_541_);
return v___x_547_;
}
v___jp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_apply_1(v_f_534_, v_fvarId_551_);
v___x_553_ = lean_apply_4(v_toBind_537_, lean_box(0), lean_box(0), v___x_552_, v___f_549_);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___boxed(lean_object* v_pu_606_, lean_object* v_inst_607_, lean_object* v_f_608_, lean_object* v_e_609_){
_start:
{
uint8_t v_pu_boxed_610_; lean_object* v_res_611_; 
v_pu_boxed_610_ = lean_unbox(v_pu_606_);
v_res_611_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_boxed_610_, v_inst_607_, v_f_608_, v_e_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM(lean_object* v_m_612_, uint8_t v_pu_613_, lean_object* v_inst_614_, lean_object* v_inst_615_, lean_object* v_f_616_, lean_object* v_e_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_613_, v_inst_615_, v_f_616_, v_e_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___boxed(lean_object* v_m_619_, lean_object* v_pu_620_, lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_f_623_, lean_object* v_e_624_){
_start:
{
uint8_t v_pu_boxed_625_; lean_object* v_res_626_; 
v_pu_boxed_625_ = lean_unbox(v_pu_620_);
v_res_626_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM(v_m_619_, v_pu_boxed_625_, v_inst_621_, v_inst_622_, v_f_623_, v_e_624_);
lean_dec(v_inst_621_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0(lean_object* v_inst_627_, lean_object* v_f_628_, lean_object* v_x_629_, lean_object* v___y_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_627_, v_f_628_, v___y_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3(lean_object* v_args_632_, lean_object* v_toPure_633_, lean_object* v_inst_634_, lean_object* v___f_635_, lean_object* v_____r_636_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_array_get_size(v_args_632_);
v___x_639_ = lean_box(0);
v___x_640_ = lean_nat_dec_lt(v___x_637_, v___x_638_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
lean_dec(v___f_635_);
lean_dec_ref(v_inst_634_);
lean_dec_ref(v_args_632_);
v___x_641_ = lean_apply_2(v_toPure_633_, lean_box(0), v___x_639_);
return v___x_641_;
}
else
{
size_t v___x_642_; size_t v___x_643_; lean_object* v___x_644_; 
lean_dec(v_toPure_633_);
v___x_642_ = ((size_t)0ULL);
v___x_643_ = lean_usize_of_nat(v___x_638_);
v___x_644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_634_, v___f_635_, v_args_632_, v___x_642_, v___x_643_, v___x_639_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(lean_object* v_inst_645_, lean_object* v_f_646_, lean_object* v_e_647_){
_start:
{
lean_object* v_toApplicative_648_; lean_object* v_toBind_649_; lean_object* v_toPure_650_; lean_object* v___f_651_; lean_object* v_args_653_; 
v_toApplicative_648_ = lean_ctor_get(v_inst_645_, 0);
v_toBind_649_ = lean_ctor_get(v_inst_645_, 1);
v_toPure_650_ = lean_ctor_get(v_toApplicative_648_, 1);
lean_inc(v_f_646_);
lean_inc_ref(v_inst_645_);
v___f_651_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_651_, 0, v_inst_645_);
lean_closure_set(v___f_651_, 1, v_f_646_);
switch(lean_obj_tag(v_e_647_))
{
case 2:
{
lean_object* v_struct_662_; lean_object* v___x_663_; 
lean_dec_ref(v___f_651_);
lean_dec_ref(v_inst_645_);
v_struct_662_ = lean_ctor_get(v_e_647_, 2);
lean_inc(v_struct_662_);
lean_dec_ref_known(v_e_647_, 3);
v___x_663_ = lean_apply_1(v_f_646_, v_struct_662_);
return v___x_663_;
}
case 3:
{
lean_object* v_args_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
lean_dec(v_f_646_);
v_args_664_ = lean_ctor_get(v_e_647_, 2);
lean_inc_ref(v_args_664_);
lean_dec_ref_known(v_e_647_, 3);
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_array_get_size(v_args_664_);
v___x_667_ = lean_box(0);
v___x_668_ = lean_nat_dec_lt(v___x_665_, v___x_666_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
lean_inc(v_toPure_650_);
lean_dec_ref(v_args_664_);
lean_dec_ref(v___f_651_);
lean_dec_ref(v_inst_645_);
v___x_669_ = lean_apply_2(v_toPure_650_, lean_box(0), v___x_667_);
return v___x_669_;
}
else
{
size_t v___x_670_; size_t v___x_671_; lean_object* v___x_672_; 
v___x_670_ = ((size_t)0ULL);
v___x_671_ = lean_usize_of_nat(v___x_666_);
v___x_672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_645_, v___f_651_, v_args_664_, v___x_670_, v___x_671_, v___x_667_);
return v___x_672_;
}
}
case 4:
{
lean_object* v_fvarId_673_; lean_object* v_args_674_; lean_object* v___f_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_inc(v_toPure_650_);
lean_inc(v_toBind_649_);
v_fvarId_673_ = lean_ctor_get(v_e_647_, 0);
lean_inc(v_fvarId_673_);
v_args_674_ = lean_ctor_get(v_e_647_, 1);
lean_inc_ref(v_args_674_);
lean_dec_ref_known(v_e_647_, 2);
v___f_675_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3), 5, 4);
lean_closure_set(v___f_675_, 0, v_args_674_);
lean_closure_set(v___f_675_, 1, v_toPure_650_);
lean_closure_set(v___f_675_, 2, v_inst_645_);
lean_closure_set(v___f_675_, 3, v___f_651_);
v___x_676_ = lean_apply_1(v_f_646_, v_fvarId_673_);
v___x_677_ = lean_apply_4(v_toBind_649_, lean_box(0), lean_box(0), v___x_676_, v___f_675_);
return v___x_677_;
}
case 5:
{
lean_object* v_args_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
lean_dec(v_f_646_);
v_args_678_ = lean_ctor_get(v_e_647_, 1);
lean_inc_ref(v_args_678_);
lean_dec_ref_known(v_e_647_, 2);
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_array_get_size(v_args_678_);
v___x_681_ = lean_box(0);
v___x_682_ = lean_nat_dec_lt(v___x_679_, v___x_680_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; 
lean_inc(v_toPure_650_);
lean_dec_ref(v_args_678_);
lean_dec_ref(v___f_651_);
lean_dec_ref(v_inst_645_);
v___x_683_ = lean_apply_2(v_toPure_650_, lean_box(0), v___x_681_);
return v___x_683_;
}
else
{
size_t v___x_684_; size_t v___x_685_; lean_object* v___x_686_; 
v___x_684_ = ((size_t)0ULL);
v___x_685_ = lean_usize_of_nat(v___x_680_);
v___x_686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_645_, v___f_651_, v_args_678_, v___x_684_, v___x_685_, v___x_681_);
return v___x_686_;
}
}
case 6:
{
lean_object* v_var_687_; lean_object* v___x_688_; 
lean_dec_ref(v___f_651_);
lean_dec_ref(v_inst_645_);
v_var_687_ = lean_ctor_get(v_e_647_, 1);
lean_inc(v_var_687_);
lean_dec_ref_known(v_e_647_, 2);
v___x_688_ = lean_apply_1(v_f_646_, v_var_687_);
return v___x_688_;
}
case 7:
{
lean_object* v_var_689_; lean_object* v___x_690_; 
lean_dec_ref(v___f_651_);
lean_dec_ref(v_inst_645_);
v_var_689_ = lean_ctor_get(v_e_647_, 1);
lean_inc(v_var_689_);
lean_dec_ref_known(v_e_647_, 2);
v___x_690_ = lean_apply_1(v_f_646_, v_var_689_);
return v___x_690_;
}
case 8:
{
lean_object* v_var_691_; lean_object* v___x_692_; 
lean_dec_ref(v___f_651_);
lean_dec_ref(v_inst_645_);
v_var_691_ = lean_ctor_get(v_e_647_, 2);
lean_inc(v_var_691_);
lean_dec_ref_known(v_e_647_, 3);
v___x_692_ = lean_apply_1(v_f_646_, v_var_691_);
return v___x_692_;
}
case 9:
{
lean_object* v_args_693_; 
lean_dec(v_f_646_);
v_args_693_ = lean_ctor_get(v_e_647_, 1);
lean_inc_ref(v_args_693_);
lean_dec_ref_known(v_e_647_, 2);
v_args_653_ = v_args_693_;
goto v___jp_652_;
}
case 10:
{
lean_object* v_args_694_; 
lean_dec(v_f_646_);
v_args_694_ = lean_ctor_get(v_e_647_, 1);
lean_inc_ref(v_args_694_);
lean_dec_ref_known(v_e_647_, 2);
v_args_653_ = v_args_694_;
goto v___jp_652_;
}
case 11:
{
lean_object* v_var_695_; lean_object* v___x_696_; 
lean_dec_ref(v___f_651_);
lean_dec_ref(v_inst_645_);
v_var_695_ = lean_ctor_get(v_e_647_, 1);
lean_inc(v_var_695_);
lean_dec_ref_known(v_e_647_, 2);
v___x_696_ = lean_apply_1(v_f_646_, v_var_695_);
return v___x_696_;
}
case 12:
{
lean_object* v_var_697_; lean_object* v_args_698_; lean_object* v___f_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
lean_inc(v_toPure_650_);
lean_inc(v_toBind_649_);
v_var_697_ = lean_ctor_get(v_e_647_, 0);
lean_inc(v_var_697_);
v_args_698_ = lean_ctor_get(v_e_647_, 2);
lean_inc_ref(v_args_698_);
lean_dec_ref_known(v_e_647_, 3);
v___f_699_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3), 5, 4);
lean_closure_set(v___f_699_, 0, v_args_698_);
lean_closure_set(v___f_699_, 1, v_toPure_650_);
lean_closure_set(v___f_699_, 2, v_inst_645_);
lean_closure_set(v___f_699_, 3, v___f_651_);
v___x_700_ = lean_apply_1(v_f_646_, v_var_697_);
v___x_701_ = lean_apply_4(v_toBind_649_, lean_box(0), lean_box(0), v___x_700_, v___f_699_);
return v___x_701_;
}
case 13:
{
lean_object* v_fvarId_702_; lean_object* v___x_703_; 
lean_dec_ref(v___f_651_);
lean_dec_ref(v_inst_645_);
v_fvarId_702_ = lean_ctor_get(v_e_647_, 1);
lean_inc(v_fvarId_702_);
lean_dec_ref_known(v_e_647_, 2);
v___x_703_ = lean_apply_1(v_f_646_, v_fvarId_702_);
return v___x_703_;
}
case 14:
{
lean_object* v_fvarId_704_; lean_object* v___x_705_; 
lean_dec_ref(v___f_651_);
lean_dec_ref(v_inst_645_);
v_fvarId_704_ = lean_ctor_get(v_e_647_, 0);
lean_inc(v_fvarId_704_);
lean_dec_ref_known(v_e_647_, 1);
v___x_705_ = lean_apply_1(v_f_646_, v_fvarId_704_);
return v___x_705_;
}
case 15:
{
lean_object* v_fvarId_706_; lean_object* v___x_707_; 
lean_dec_ref(v___f_651_);
lean_dec_ref(v_inst_645_);
v_fvarId_706_ = lean_ctor_get(v_e_647_, 0);
lean_inc(v_fvarId_706_);
lean_dec_ref_known(v_e_647_, 1);
v___x_707_ = lean_apply_1(v_f_646_, v_fvarId_706_);
return v___x_707_;
}
default: 
{
lean_object* v___x_708_; lean_object* v___x_709_; 
lean_inc(v_toPure_650_);
lean_dec_ref(v___f_651_);
lean_dec(v_e_647_);
lean_dec(v_f_646_);
lean_dec_ref(v_inst_645_);
v___x_708_ = lean_box(0);
v___x_709_ = lean_apply_2(v_toPure_650_, lean_box(0), v___x_708_);
return v___x_709_;
}
}
v___jp_652_:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = lean_array_get_size(v_args_653_);
v___x_656_ = lean_box(0);
v___x_657_ = lean_nat_dec_lt(v___x_654_, v___x_655_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_inc(v_toPure_650_);
lean_dec_ref(v_args_653_);
lean_dec_ref(v___f_651_);
lean_dec_ref(v_inst_645_);
v___x_658_ = lean_apply_2(v_toPure_650_, lean_box(0), v___x_656_);
return v___x_658_;
}
else
{
size_t v___x_659_; size_t v___x_660_; lean_object* v___x_661_; 
v___x_659_ = ((size_t)0ULL);
v___x_660_ = lean_usize_of_nat(v___x_655_);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_645_, v___f_651_, v_args_653_, v___x_659_, v___x_660_, v___x_656_);
return v___x_661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM(lean_object* v_m_710_, uint8_t v_pu_711_, lean_object* v_inst_712_, lean_object* v_f_713_, lean_object* v_e_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_712_, v_f_713_, v_e_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___boxed(lean_object* v_m_716_, lean_object* v_pu_717_, lean_object* v_inst_718_, lean_object* v_f_719_, lean_object* v_e_720_){
_start:
{
uint8_t v_pu_boxed_721_; lean_object* v_res_722_; 
v_pu_boxed_721_ = lean_unbox(v_pu_717_);
v_res_722_ = l_Lean_Compiler_LCNF_LetValue_forFVarM(v_m_716_, v_pu_boxed_721_, v_inst_718_, v_f_719_, v_e_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(uint8_t v_pu_723_, lean_object* v_m_724_, lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_723_, v_inst_726_, v___y_727_, v___y_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0___boxed(lean_object* v_pu_730_, lean_object* v_m_731_, lean_object* v_inst_732_, lean_object* v_inst_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
uint8_t v_pu_boxed_736_; lean_object* v_res_737_; 
v_pu_boxed_736_ = lean_unbox(v_pu_730_);
v_res_737_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(v_pu_boxed_736_, v_m_731_, v_inst_732_, v_inst_733_, v___y_734_, v___y_735_);
lean_dec(v_inst_732_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__1(lean_object* v_m_738_, lean_object* v_inst_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_739_, v___y_740_, v___y_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue(uint8_t v_pu_744_){
_start:
{
lean_object* v___x_745_; lean_object* v___f_746_; lean_object* v___f_747_; lean_object* v___x_748_; 
v___x_745_ = lean_box(v_pu_744_);
v___f_746_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0___boxed), 6, 1);
lean_closure_set(v___f_746_, 0, v___x_745_);
v___f_747_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarLetValue___closed__0));
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v___f_746_);
lean_ctor_set(v___x_748_, 1, v___f_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___boxed(lean_object* v_pu_749_){
_start:
{
uint8_t v_pu_boxed_750_; lean_object* v_res_751_; 
v_pu_boxed_750_ = lean_unbox(v_pu_749_);
v_res_751_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue(v_pu_boxed_750_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(uint8_t v_pu_752_, lean_object* v_decl_753_, lean_object* v_____do__lift_754_, lean_object* v_inst_755_, lean_object* v_____do__lift_756_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = lean_box(v_pu_752_);
v___x_758_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_758_, 0, v___x_757_);
lean_closure_set(v___x_758_, 1, v_decl_753_);
lean_closure_set(v___x_758_, 2, v_____do__lift_754_);
lean_closure_set(v___x_758_, 3, v_____do__lift_756_);
v___x_759_ = lean_apply_2(v_inst_755_, lean_box(0), v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_760_, lean_object* v_decl_761_, lean_object* v_____do__lift_762_, lean_object* v_inst_763_, lean_object* v_____do__lift_764_){
_start:
{
uint8_t v_pu_boxed_765_; lean_object* v_res_766_; 
v_pu_boxed_765_ = lean_unbox(v_pu_760_);
v_res_766_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(v_pu_boxed_765_, v_decl_761_, v_____do__lift_762_, v_inst_763_, v_____do__lift_764_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(uint8_t v_pu_767_, lean_object* v_decl_768_, lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_f_771_, lean_object* v_value_772_, lean_object* v_toBind_773_, lean_object* v_____do__lift_774_){
_start:
{
lean_object* v___x_775_; lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_775_ = lean_box(v_pu_767_);
v___f_776_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_776_, 0, v___x_775_);
lean_closure_set(v___f_776_, 1, v_decl_768_);
lean_closure_set(v___f_776_, 2, v_____do__lift_774_);
lean_closure_set(v___f_776_, 3, v_inst_769_);
v___x_777_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_767_, v_inst_770_, v_f_771_, v_value_772_);
v___x_778_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v___x_777_, v___f_776_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1___boxed(lean_object* v_pu_779_, lean_object* v_decl_780_, lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_f_783_, lean_object* v_value_784_, lean_object* v_toBind_785_, lean_object* v_____do__lift_786_){
_start:
{
uint8_t v_pu_boxed_787_; lean_object* v_res_788_; 
v_pu_boxed_787_ = lean_unbox(v_pu_779_);
v_res_788_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(v_pu_boxed_787_, v_decl_780_, v_inst_781_, v_inst_782_, v_f_783_, v_value_784_, v_toBind_785_, v_____do__lift_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(uint8_t v_pu_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_f_792_, lean_object* v_decl_793_){
_start:
{
lean_object* v_toBind_794_; lean_object* v_type_795_; lean_object* v_value_796_; lean_object* v___x_797_; lean_object* v___f_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_toBind_794_ = lean_ctor_get(v_inst_791_, 1);
lean_inc_n(v_toBind_794_, 2);
v_type_795_ = lean_ctor_get(v_decl_793_, 2);
lean_inc_ref(v_type_795_);
v_value_796_ = lean_ctor_get(v_decl_793_, 3);
lean_inc(v_value_796_);
v___x_797_ = lean_box(v_pu_789_);
lean_inc(v_f_792_);
lean_inc_ref(v_inst_791_);
v___f_798_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_798_, 0, v___x_797_);
lean_closure_set(v___f_798_, 1, v_decl_793_);
lean_closure_set(v___f_798_, 2, v_inst_790_);
lean_closure_set(v___f_798_, 3, v_inst_791_);
lean_closure_set(v___f_798_, 4, v_f_792_);
lean_closure_set(v___f_798_, 5, v_value_796_);
lean_closure_set(v___f_798_, 6, v_toBind_794_);
v___x_799_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_791_, v_f_792_, v_type_795_);
v___x_800_ = lean_apply_4(v_toBind_794_, lean_box(0), lean_box(0), v___x_799_, v___f_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___boxed(lean_object* v_pu_801_, lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_f_804_, lean_object* v_decl_805_){
_start:
{
uint8_t v_pu_boxed_806_; lean_object* v_res_807_; 
v_pu_boxed_806_ = lean_unbox(v_pu_801_);
v_res_807_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_boxed_806_, v_inst_802_, v_inst_803_, v_f_804_, v_decl_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM(lean_object* v_m_808_, uint8_t v_pu_809_, lean_object* v_inst_810_, lean_object* v_inst_811_, lean_object* v_f_812_, lean_object* v_decl_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_809_, v_inst_810_, v_inst_811_, v_f_812_, v_decl_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___boxed(lean_object* v_m_815_, lean_object* v_pu_816_, lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_f_819_, lean_object* v_decl_820_){
_start:
{
uint8_t v_pu_boxed_821_; lean_object* v_res_822_; 
v_pu_boxed_821_ = lean_unbox(v_pu_816_);
v_res_822_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM(v_m_815_, v_pu_boxed_821_, v_inst_817_, v_inst_818_, v_f_819_, v_decl_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg___lam__0(lean_object* v_inst_823_, lean_object* v_f_824_, lean_object* v_value_825_, lean_object* v_____r_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_823_, v_f_824_, v_value_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(lean_object* v_inst_828_, lean_object* v_f_829_, lean_object* v_decl_830_){
_start:
{
lean_object* v_toBind_831_; lean_object* v_type_832_; lean_object* v_value_833_; lean_object* v___f_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v_toBind_831_ = lean_ctor_get(v_inst_828_, 1);
lean_inc(v_toBind_831_);
v_type_832_ = lean_ctor_get(v_decl_830_, 2);
lean_inc_ref(v_type_832_);
v_value_833_ = lean_ctor_get(v_decl_830_, 3);
lean_inc(v_value_833_);
lean_dec_ref(v_decl_830_);
lean_inc(v_f_829_);
lean_inc_ref(v_inst_828_);
v___f_834_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_834_, 0, v_inst_828_);
lean_closure_set(v___f_834_, 1, v_f_829_);
lean_closure_set(v___f_834_, 2, v_value_833_);
v___x_835_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_828_, v_f_829_, v_type_832_);
v___x_836_ = lean_apply_4(v_toBind_831_, lean_box(0), lean_box(0), v___x_835_, v___f_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM(lean_object* v_m_837_, uint8_t v_pu_838_, lean_object* v_inst_839_, lean_object* v_f_840_, lean_object* v_decl_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_839_, v_f_840_, v_decl_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___boxed(lean_object* v_m_843_, lean_object* v_pu_844_, lean_object* v_inst_845_, lean_object* v_f_846_, lean_object* v_decl_847_){
_start:
{
uint8_t v_pu_boxed_848_; lean_object* v_res_849_; 
v_pu_boxed_848_ = lean_unbox(v_pu_844_);
v_res_849_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM(v_m_843_, v_pu_boxed_848_, v_inst_845_, v_f_846_, v_decl_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(uint8_t v_pu_850_, lean_object* v_m_851_, lean_object* v_inst_852_, lean_object* v_inst_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_850_, v_inst_852_, v_inst_853_, v___y_854_, v___y_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0___boxed(lean_object* v_pu_857_, lean_object* v_m_858_, lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
uint8_t v_pu_boxed_863_; lean_object* v_res_864_; 
v_pu_boxed_863_ = lean_unbox(v_pu_857_);
v_res_864_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(v_pu_boxed_863_, v_m_858_, v_inst_859_, v_inst_860_, v___y_861_, v___y_862_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__1(lean_object* v_m_865_, lean_object* v_inst_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_866_, v___y_867_, v___y_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(uint8_t v_pu_871_){
_start:
{
lean_object* v___x_872_; lean_object* v___f_873_; lean_object* v___f_874_; lean_object* v___x_875_; 
v___x_872_ = lean_box(v_pu_871_);
v___f_873_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0___boxed), 6, 1);
lean_closure_set(v___f_873_, 0, v___x_872_);
v___f_874_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___closed__0));
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v___f_873_);
lean_ctor_set(v___x_875_, 1, v___f_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___boxed(lean_object* v_pu_876_){
_start:
{
uint8_t v_pu_boxed_877_; lean_object* v_res_878_; 
v_pu_boxed_877_ = lean_unbox(v_pu_876_);
v_res_878_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(v_pu_boxed_877_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(uint8_t v_pu_879_, lean_object* v_param_880_, lean_object* v_inst_881_, lean_object* v_____do__lift_882_){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_883_ = lean_box(v_pu_879_);
v___x_884_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_884_, 0, v___x_883_);
lean_closure_set(v___x_884_, 1, v_param_880_);
lean_closure_set(v___x_884_, 2, v_____do__lift_882_);
v___x_885_ = lean_apply_2(v_inst_881_, lean_box(0), v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_886_, lean_object* v_param_887_, lean_object* v_inst_888_, lean_object* v_____do__lift_889_){
_start:
{
uint8_t v_pu_boxed_890_; lean_object* v_res_891_; 
v_pu_boxed_890_ = lean_unbox(v_pu_886_);
v_res_891_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(v_pu_boxed_890_, v_param_887_, v_inst_888_, v_____do__lift_889_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(uint8_t v_pu_892_, lean_object* v_inst_893_, lean_object* v_inst_894_, lean_object* v_f_895_, lean_object* v_param_896_){
_start:
{
lean_object* v_toBind_897_; lean_object* v_type_898_; lean_object* v___x_899_; lean_object* v___f_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_toBind_897_ = lean_ctor_get(v_inst_894_, 1);
lean_inc(v_toBind_897_);
v_type_898_ = lean_ctor_get(v_param_896_, 2);
lean_inc_ref(v_type_898_);
v___x_899_ = lean_box(v_pu_892_);
v___f_900_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_900_, 0, v___x_899_);
lean_closure_set(v___f_900_, 1, v_param_896_);
lean_closure_set(v___f_900_, 2, v_inst_893_);
v___x_901_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_894_, v_f_895_, v_type_898_);
v___x_902_ = lean_apply_4(v_toBind_897_, lean_box(0), lean_box(0), v___x_901_, v___f_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___boxed(lean_object* v_pu_903_, lean_object* v_inst_904_, lean_object* v_inst_905_, lean_object* v_f_906_, lean_object* v_param_907_){
_start:
{
uint8_t v_pu_boxed_908_; lean_object* v_res_909_; 
v_pu_boxed_908_ = lean_unbox(v_pu_903_);
v_res_909_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(v_pu_boxed_908_, v_inst_904_, v_inst_905_, v_f_906_, v_param_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM(lean_object* v_m_910_, uint8_t v_pu_911_, lean_object* v_inst_912_, lean_object* v_inst_913_, lean_object* v_f_914_, lean_object* v_param_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(v_pu_911_, v_inst_912_, v_inst_913_, v_f_914_, v_param_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___boxed(lean_object* v_m_917_, lean_object* v_pu_918_, lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_f_921_, lean_object* v_param_922_){
_start:
{
uint8_t v_pu_boxed_923_; lean_object* v_res_924_; 
v_pu_boxed_923_ = lean_unbox(v_pu_918_);
v_res_924_ = l_Lean_Compiler_LCNF_Param_mapFVarM(v_m_917_, v_pu_boxed_923_, v_inst_919_, v_inst_920_, v_f_921_, v_param_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___redArg(lean_object* v_inst_925_, lean_object* v_f_926_, lean_object* v_param_927_){
_start:
{
lean_object* v_type_928_; lean_object* v___x_929_; 
v_type_928_ = lean_ctor_get(v_param_927_, 2);
lean_inc_ref(v_type_928_);
lean_dec_ref(v_param_927_);
v___x_929_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_925_, v_f_926_, v_type_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM(lean_object* v_m_930_, uint8_t v_pu_931_, lean_object* v_inst_932_, lean_object* v_f_933_, lean_object* v_param_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_932_, v_f_933_, v_param_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___boxed(lean_object* v_m_936_, lean_object* v_pu_937_, lean_object* v_inst_938_, lean_object* v_f_939_, lean_object* v_param_940_){
_start:
{
uint8_t v_pu_boxed_941_; lean_object* v_res_942_; 
v_pu_boxed_941_ = lean_unbox(v_pu_937_);
v_res_942_ = l_Lean_Compiler_LCNF_Param_forFVarM(v_m_936_, v_pu_boxed_941_, v_inst_938_, v_f_939_, v_param_940_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(uint8_t v_pu_943_, lean_object* v_m_944_, lean_object* v_inst_945_, lean_object* v_inst_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(v_pu_943_, v_inst_945_, v_inst_946_, v___y_947_, v___y_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0___boxed(lean_object* v_pu_950_, lean_object* v_m_951_, lean_object* v_inst_952_, lean_object* v_inst_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
uint8_t v_pu_boxed_956_; lean_object* v_res_957_; 
v_pu_boxed_956_ = lean_unbox(v_pu_950_);
v_res_957_ = l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(v_pu_boxed_956_, v_m_951_, v_inst_952_, v_inst_953_, v___y_954_, v___y_955_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__1(lean_object* v_m_958_, lean_object* v_inst_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_959_, v___y_960_, v___y_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam(uint8_t v_pu_964_){
_start:
{
lean_object* v___x_965_; lean_object* v___f_966_; lean_object* v___f_967_; lean_object* v___x_968_; 
v___x_965_ = lean_box(v_pu_964_);
v___f_966_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0___boxed), 6, 1);
lean_closure_set(v___f_966_, 0, v___x_965_);
v___f_967_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarParam___closed__0));
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v___f_966_);
lean_ctor_set(v___x_968_, 1, v___f_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___boxed(lean_object* v_pu_969_){
_start:
{
uint8_t v_pu_boxed_970_; lean_object* v_res_971_; 
v_pu_boxed_970_ = lean_unbox(v_pu_969_);
v_res_971_ = l_Lean_Compiler_LCNF_instTraverseFVarParam(v_pu_boxed_970_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0(lean_object* v_k_972_, lean_object* v_decl_973_, lean_object* v_toPure_974_, lean_object* v_decl_975_, lean_object* v_c_976_, lean_object* v_____do__lift_977_){
_start:
{
size_t v___x_978_; size_t v___x_979_; uint8_t v___x_980_; 
v___x_978_ = lean_ptr_addr(v_k_972_);
v___x_979_ = lean_ptr_addr(v_____do__lift_977_);
v___x_980_ = lean_usize_dec_eq(v___x_978_, v___x_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_982_; 
lean_dec_ref(v_c_976_);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v_decl_973_);
lean_ctor_set(v___x_981_, 1, v_____do__lift_977_);
v___x_982_ = lean_apply_2(v_toPure_974_, lean_box(0), v___x_981_);
return v___x_982_;
}
else
{
size_t v___x_983_; size_t v___x_984_; uint8_t v___x_985_; 
v___x_983_ = lean_ptr_addr(v_decl_975_);
v___x_984_ = lean_ptr_addr(v_decl_973_);
v___x_985_ = lean_usize_dec_eq(v___x_983_, v___x_984_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec_ref(v_c_976_);
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v_decl_973_);
lean_ctor_set(v___x_986_, 1, v_____do__lift_977_);
v___x_987_ = lean_apply_2(v_toPure_974_, lean_box(0), v___x_986_);
return v___x_987_;
}
else
{
lean_object* v___x_988_; 
lean_dec_ref(v_____do__lift_977_);
lean_dec_ref(v_decl_973_);
v___x_988_ = lean_apply_2(v_toPure_974_, lean_box(0), v_c_976_);
return v___x_988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed(lean_object* v_k_989_, lean_object* v_decl_990_, lean_object* v_toPure_991_, lean_object* v_decl_992_, lean_object* v_c_993_, lean_object* v_____do__lift_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0(v_k_989_, v_decl_990_, v_toPure_991_, v_decl_992_, v_c_993_, v_____do__lift_994_);
lean_dec_ref(v_decl_992_);
lean_dec_ref(v_k_989_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(lean_object* v_fvarId_996_, lean_object* v_____do__lift_997_, lean_object* v_i_998_, lean_object* v_____do__lift_999_, lean_object* v_toPure_1000_, lean_object* v_y_1001_, lean_object* v_k_1002_, lean_object* v_c_1003_, lean_object* v_____do__lift_1004_){
_start:
{
size_t v___x_1005_; size_t v___x_1006_; uint8_t v___x_1007_; 
v___x_1005_ = lean_ptr_addr(v_fvarId_996_);
v___x_1006_ = lean_ptr_addr(v_____do__lift_997_);
v___x_1007_ = lean_usize_dec_eq(v___x_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_dec_ref(v_c_1003_);
v___x_1008_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1008_, 0, v_____do__lift_997_);
lean_ctor_set(v___x_1008_, 1, v_i_998_);
lean_ctor_set(v___x_1008_, 2, v_____do__lift_999_);
lean_ctor_set(v___x_1008_, 3, v_____do__lift_1004_);
v___x_1009_ = lean_apply_2(v_toPure_1000_, lean_box(0), v___x_1008_);
return v___x_1009_;
}
else
{
uint8_t v___x_1010_; 
v___x_1010_ = lean_nat_dec_eq(v_i_998_, v_i_998_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec_ref(v_c_1003_);
v___x_1011_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1011_, 0, v_____do__lift_997_);
lean_ctor_set(v___x_1011_, 1, v_i_998_);
lean_ctor_set(v___x_1011_, 2, v_____do__lift_999_);
lean_ctor_set(v___x_1011_, 3, v_____do__lift_1004_);
v___x_1012_ = lean_apply_2(v_toPure_1000_, lean_box(0), v___x_1011_);
return v___x_1012_;
}
else
{
size_t v___x_1013_; size_t v___x_1014_; uint8_t v___x_1015_; 
v___x_1013_ = lean_ptr_addr(v_y_1001_);
v___x_1014_ = lean_ptr_addr(v_____do__lift_999_);
v___x_1015_ = lean_usize_dec_eq(v___x_1013_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec_ref(v_c_1003_);
v___x_1016_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1016_, 0, v_____do__lift_997_);
lean_ctor_set(v___x_1016_, 1, v_i_998_);
lean_ctor_set(v___x_1016_, 2, v_____do__lift_999_);
lean_ctor_set(v___x_1016_, 3, v_____do__lift_1004_);
v___x_1017_ = lean_apply_2(v_toPure_1000_, lean_box(0), v___x_1016_);
return v___x_1017_;
}
else
{
size_t v___x_1018_; size_t v___x_1019_; uint8_t v___x_1020_; 
v___x_1018_ = lean_ptr_addr(v_k_1002_);
v___x_1019_ = lean_ptr_addr(v_____do__lift_1004_);
v___x_1020_ = lean_usize_dec_eq(v___x_1018_, v___x_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec_ref(v_c_1003_);
v___x_1021_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1021_, 0, v_____do__lift_997_);
lean_ctor_set(v___x_1021_, 1, v_i_998_);
lean_ctor_set(v___x_1021_, 2, v_____do__lift_999_);
lean_ctor_set(v___x_1021_, 3, v_____do__lift_1004_);
v___x_1022_ = lean_apply_2(v_toPure_1000_, lean_box(0), v___x_1021_);
return v___x_1022_;
}
else
{
lean_object* v___x_1023_; 
lean_dec_ref(v_____do__lift_1004_);
lean_dec(v_____do__lift_999_);
lean_dec(v_i_998_);
lean_dec(v_____do__lift_997_);
v___x_1023_ = lean_apply_2(v_toPure_1000_, lean_box(0), v_c_1003_);
return v___x_1023_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed(lean_object* v_fvarId_1024_, lean_object* v_____do__lift_1025_, lean_object* v_i_1026_, lean_object* v_____do__lift_1027_, lean_object* v_toPure_1028_, lean_object* v_y_1029_, lean_object* v_k_1030_, lean_object* v_c_1031_, lean_object* v_____do__lift_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(v_fvarId_1024_, v_____do__lift_1025_, v_i_1026_, v_____do__lift_1027_, v_toPure_1028_, v_y_1029_, v_k_1030_, v_c_1031_, v_____do__lift_1032_);
lean_dec_ref(v_k_1030_);
lean_dec(v_y_1029_);
lean_dec(v_fvarId_1024_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(lean_object* v_fvarId_1034_, lean_object* v_toPure_1035_, lean_object* v_c_1036_, lean_object* v_____do__lift_1037_){
_start:
{
uint8_t v___x_1038_; 
v___x_1038_ = l_Lean_instBEqFVarId_beq(v_fvarId_1034_, v_____do__lift_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_dec_ref(v_c_1036_);
v___x_1039_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1039_, 0, v_____do__lift_1037_);
v___x_1040_ = lean_apply_2(v_toPure_1035_, lean_box(0), v___x_1039_);
return v___x_1040_;
}
else
{
lean_object* v___x_1041_; 
lean_dec(v_____do__lift_1037_);
v___x_1041_ = lean_apply_2(v_toPure_1035_, lean_box(0), v_c_1036_);
return v___x_1041_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed(lean_object* v_fvarId_1042_, lean_object* v_toPure_1043_, lean_object* v_c_1044_, lean_object* v_____do__lift_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(v_fvarId_1042_, v_toPure_1043_, v_c_1044_, v_____do__lift_1045_);
lean_dec(v_fvarId_1042_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27(lean_object* v_fvarId_1047_, lean_object* v_____do__lift_1048_, lean_object* v_cidx_1049_, lean_object* v_toPure_1050_, lean_object* v_k_1051_, lean_object* v_c_1052_, lean_object* v_____do__lift_1053_){
_start:
{
size_t v___x_1054_; size_t v___x_1055_; uint8_t v___x_1056_; 
v___x_1054_ = lean_ptr_addr(v_fvarId_1047_);
v___x_1055_ = lean_ptr_addr(v_____do__lift_1048_);
v___x_1056_ = lean_usize_dec_eq(v___x_1054_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_dec_ref(v_c_1052_);
v___x_1057_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1057_, 0, v_____do__lift_1048_);
lean_ctor_set(v___x_1057_, 1, v_cidx_1049_);
lean_ctor_set(v___x_1057_, 2, v_____do__lift_1053_);
v___x_1058_ = lean_apply_2(v_toPure_1050_, lean_box(0), v___x_1057_);
return v___x_1058_;
}
else
{
uint8_t v___x_1059_; 
v___x_1059_ = lean_nat_dec_eq(v_cidx_1049_, v_cidx_1049_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
lean_dec_ref(v_c_1052_);
v___x_1060_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1060_, 0, v_____do__lift_1048_);
lean_ctor_set(v___x_1060_, 1, v_cidx_1049_);
lean_ctor_set(v___x_1060_, 2, v_____do__lift_1053_);
v___x_1061_ = lean_apply_2(v_toPure_1050_, lean_box(0), v___x_1060_);
return v___x_1061_;
}
else
{
size_t v___x_1062_; size_t v___x_1063_; uint8_t v___x_1064_; 
v___x_1062_ = lean_ptr_addr(v_k_1051_);
v___x_1063_ = lean_ptr_addr(v_____do__lift_1053_);
v___x_1064_ = lean_usize_dec_eq(v___x_1062_, v___x_1063_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_dec_ref(v_c_1052_);
v___x_1065_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1065_, 0, v_____do__lift_1048_);
lean_ctor_set(v___x_1065_, 1, v_cidx_1049_);
lean_ctor_set(v___x_1065_, 2, v_____do__lift_1053_);
v___x_1066_ = lean_apply_2(v_toPure_1050_, lean_box(0), v___x_1065_);
return v___x_1066_;
}
else
{
lean_object* v___x_1067_; 
lean_dec_ref(v_____do__lift_1053_);
lean_dec(v_cidx_1049_);
lean_dec(v_____do__lift_1048_);
v___x_1067_ = lean_apply_2(v_toPure_1050_, lean_box(0), v_c_1052_);
return v___x_1067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27___boxed(lean_object* v_fvarId_1068_, lean_object* v_____do__lift_1069_, lean_object* v_cidx_1070_, lean_object* v_toPure_1071_, lean_object* v_k_1072_, lean_object* v_c_1073_, lean_object* v_____do__lift_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27(v_fvarId_1068_, v_____do__lift_1069_, v_cidx_1070_, v_toPure_1071_, v_k_1072_, v_c_1073_, v_____do__lift_1074_);
lean_dec_ref(v_k_1072_);
lean_dec(v_fvarId_1068_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(lean_object* v_fvarId_1076_, lean_object* v_____do__lift_1077_, lean_object* v_n_1078_, uint8_t v_check_1079_, uint8_t v_persistent_1080_, lean_object* v_toPure_1081_, lean_object* v_k_1082_, lean_object* v_c_1083_, lean_object* v_____do__lift_1084_){
_start:
{
size_t v___x_1085_; size_t v___x_1086_; uint8_t v___x_1087_; 
v___x_1085_ = lean_ptr_addr(v_fvarId_1076_);
v___x_1086_ = lean_ptr_addr(v_____do__lift_1077_);
v___x_1087_ = lean_usize_dec_eq(v___x_1085_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec_ref(v_c_1083_);
v___x_1088_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1088_, 0, v_____do__lift_1077_);
lean_ctor_set(v___x_1088_, 1, v_n_1078_);
lean_ctor_set(v___x_1088_, 2, v_____do__lift_1084_);
lean_ctor_set_uint8(v___x_1088_, sizeof(void*)*3, v_check_1079_);
lean_ctor_set_uint8(v___x_1088_, sizeof(void*)*3 + 1, v_persistent_1080_);
v___x_1089_ = lean_apply_2(v_toPure_1081_, lean_box(0), v___x_1088_);
return v___x_1089_;
}
else
{
uint8_t v___x_1090_; 
v___x_1090_ = lean_nat_dec_eq(v_n_1078_, v_n_1078_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_dec_ref(v_c_1083_);
v___x_1091_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1091_, 0, v_____do__lift_1077_);
lean_ctor_set(v___x_1091_, 1, v_n_1078_);
lean_ctor_set(v___x_1091_, 2, v_____do__lift_1084_);
lean_ctor_set_uint8(v___x_1091_, sizeof(void*)*3, v_check_1079_);
lean_ctor_set_uint8(v___x_1091_, sizeof(void*)*3 + 1, v_persistent_1080_);
v___x_1092_ = lean_apply_2(v_toPure_1081_, lean_box(0), v___x_1091_);
return v___x_1092_;
}
else
{
size_t v___x_1093_; size_t v___x_1094_; uint8_t v___x_1095_; 
v___x_1093_ = lean_ptr_addr(v_k_1082_);
v___x_1094_ = lean_ptr_addr(v_____do__lift_1084_);
v___x_1095_ = lean_usize_dec_eq(v___x_1093_, v___x_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec_ref(v_c_1083_);
v___x_1096_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1096_, 0, v_____do__lift_1077_);
lean_ctor_set(v___x_1096_, 1, v_n_1078_);
lean_ctor_set(v___x_1096_, 2, v_____do__lift_1084_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*3, v_check_1079_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*3 + 1, v_persistent_1080_);
v___x_1097_ = lean_apply_2(v_toPure_1081_, lean_box(0), v___x_1096_);
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; 
lean_dec_ref(v_____do__lift_1084_);
lean_dec(v_n_1078_);
lean_dec(v_____do__lift_1077_);
v___x_1098_ = lean_apply_2(v_toPure_1081_, lean_box(0), v_c_1083_);
return v___x_1098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29___boxed(lean_object* v_fvarId_1099_, lean_object* v_____do__lift_1100_, lean_object* v_n_1101_, lean_object* v_check_1102_, lean_object* v_persistent_1103_, lean_object* v_toPure_1104_, lean_object* v_k_1105_, lean_object* v_c_1106_, lean_object* v_____do__lift_1107_){
_start:
{
uint8_t v_check_1974__boxed_1108_; uint8_t v_persistent_1975__boxed_1109_; lean_object* v_res_1110_; 
v_check_1974__boxed_1108_ = lean_unbox(v_check_1102_);
v_persistent_1975__boxed_1109_ = lean_unbox(v_persistent_1103_);
v_res_1110_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(v_fvarId_1099_, v_____do__lift_1100_, v_n_1101_, v_check_1974__boxed_1108_, v_persistent_1975__boxed_1109_, v_toPure_1104_, v_k_1105_, v_c_1106_, v_____do__lift_1107_);
lean_dec_ref(v_k_1105_);
lean_dec(v_fvarId_1099_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(lean_object* v_fvarId_1111_, lean_object* v_____do__lift_1112_, lean_object* v_i_1113_, lean_object* v_offset_1114_, lean_object* v_____do__lift_1115_, lean_object* v_____do__lift_1116_, lean_object* v_toPure_1117_, lean_object* v_y_1118_, lean_object* v_ty_1119_, lean_object* v_k_1120_, lean_object* v_c_1121_, lean_object* v_____do__lift_1122_){
_start:
{
size_t v___x_1123_; size_t v___x_1124_; uint8_t v___x_1125_; 
v___x_1123_ = lean_ptr_addr(v_fvarId_1111_);
v___x_1124_ = lean_ptr_addr(v_____do__lift_1112_);
v___x_1125_ = lean_usize_dec_eq(v___x_1123_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec_ref(v_c_1121_);
v___x_1126_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1126_, 0, v_____do__lift_1112_);
lean_ctor_set(v___x_1126_, 1, v_i_1113_);
lean_ctor_set(v___x_1126_, 2, v_offset_1114_);
lean_ctor_set(v___x_1126_, 3, v_____do__lift_1115_);
lean_ctor_set(v___x_1126_, 4, v_____do__lift_1116_);
lean_ctor_set(v___x_1126_, 5, v_____do__lift_1122_);
v___x_1127_ = lean_apply_2(v_toPure_1117_, lean_box(0), v___x_1126_);
return v___x_1127_;
}
else
{
uint8_t v___x_1128_; 
v___x_1128_ = lean_nat_dec_eq(v_i_1113_, v_i_1113_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_dec_ref(v_c_1121_);
v___x_1129_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1129_, 0, v_____do__lift_1112_);
lean_ctor_set(v___x_1129_, 1, v_i_1113_);
lean_ctor_set(v___x_1129_, 2, v_offset_1114_);
lean_ctor_set(v___x_1129_, 3, v_____do__lift_1115_);
lean_ctor_set(v___x_1129_, 4, v_____do__lift_1116_);
lean_ctor_set(v___x_1129_, 5, v_____do__lift_1122_);
v___x_1130_ = lean_apply_2(v_toPure_1117_, lean_box(0), v___x_1129_);
return v___x_1130_;
}
else
{
uint8_t v___x_1131_; 
v___x_1131_ = lean_nat_dec_eq(v_offset_1114_, v_offset_1114_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_dec_ref(v_c_1121_);
v___x_1132_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1132_, 0, v_____do__lift_1112_);
lean_ctor_set(v___x_1132_, 1, v_i_1113_);
lean_ctor_set(v___x_1132_, 2, v_offset_1114_);
lean_ctor_set(v___x_1132_, 3, v_____do__lift_1115_);
lean_ctor_set(v___x_1132_, 4, v_____do__lift_1116_);
lean_ctor_set(v___x_1132_, 5, v_____do__lift_1122_);
v___x_1133_ = lean_apply_2(v_toPure_1117_, lean_box(0), v___x_1132_);
return v___x_1133_;
}
else
{
size_t v___x_1134_; size_t v___x_1135_; uint8_t v___x_1136_; 
v___x_1134_ = lean_ptr_addr(v_y_1118_);
v___x_1135_ = lean_ptr_addr(v_____do__lift_1115_);
v___x_1136_ = lean_usize_dec_eq(v___x_1134_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_dec_ref(v_c_1121_);
v___x_1137_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1137_, 0, v_____do__lift_1112_);
lean_ctor_set(v___x_1137_, 1, v_i_1113_);
lean_ctor_set(v___x_1137_, 2, v_offset_1114_);
lean_ctor_set(v___x_1137_, 3, v_____do__lift_1115_);
lean_ctor_set(v___x_1137_, 4, v_____do__lift_1116_);
lean_ctor_set(v___x_1137_, 5, v_____do__lift_1122_);
v___x_1138_ = lean_apply_2(v_toPure_1117_, lean_box(0), v___x_1137_);
return v___x_1138_;
}
else
{
size_t v___x_1139_; size_t v___x_1140_; uint8_t v___x_1141_; 
v___x_1139_ = lean_ptr_addr(v_ty_1119_);
v___x_1140_ = lean_ptr_addr(v_____do__lift_1116_);
v___x_1141_ = lean_usize_dec_eq(v___x_1139_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec_ref(v_c_1121_);
v___x_1142_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1142_, 0, v_____do__lift_1112_);
lean_ctor_set(v___x_1142_, 1, v_i_1113_);
lean_ctor_set(v___x_1142_, 2, v_offset_1114_);
lean_ctor_set(v___x_1142_, 3, v_____do__lift_1115_);
lean_ctor_set(v___x_1142_, 4, v_____do__lift_1116_);
lean_ctor_set(v___x_1142_, 5, v_____do__lift_1122_);
v___x_1143_ = lean_apply_2(v_toPure_1117_, lean_box(0), v___x_1142_);
return v___x_1143_;
}
else
{
size_t v___x_1144_; size_t v___x_1145_; uint8_t v___x_1146_; 
v___x_1144_ = lean_ptr_addr(v_k_1120_);
v___x_1145_ = lean_ptr_addr(v_____do__lift_1122_);
v___x_1146_ = lean_usize_dec_eq(v___x_1144_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_dec_ref(v_c_1121_);
v___x_1147_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1147_, 0, v_____do__lift_1112_);
lean_ctor_set(v___x_1147_, 1, v_i_1113_);
lean_ctor_set(v___x_1147_, 2, v_offset_1114_);
lean_ctor_set(v___x_1147_, 3, v_____do__lift_1115_);
lean_ctor_set(v___x_1147_, 4, v_____do__lift_1116_);
lean_ctor_set(v___x_1147_, 5, v_____do__lift_1122_);
v___x_1148_ = lean_apply_2(v_toPure_1117_, lean_box(0), v___x_1147_);
return v___x_1148_;
}
else
{
lean_object* v___x_1149_; 
lean_dec_ref(v_____do__lift_1122_);
lean_dec_ref(v_____do__lift_1116_);
lean_dec(v_____do__lift_1115_);
lean_dec(v_offset_1114_);
lean_dec(v_i_1113_);
lean_dec(v_____do__lift_1112_);
v___x_1149_ = lean_apply_2(v_toPure_1117_, lean_box(0), v_c_1121_);
return v___x_1149_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed(lean_object* v_fvarId_1150_, lean_object* v_____do__lift_1151_, lean_object* v_i_1152_, lean_object* v_offset_1153_, lean_object* v_____do__lift_1154_, lean_object* v_____do__lift_1155_, lean_object* v_toPure_1156_, lean_object* v_y_1157_, lean_object* v_ty_1158_, lean_object* v_k_1159_, lean_object* v_c_1160_, lean_object* v_____do__lift_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(v_fvarId_1150_, v_____do__lift_1151_, v_i_1152_, v_offset_1153_, v_____do__lift_1154_, v_____do__lift_1155_, v_toPure_1156_, v_y_1157_, v_ty_1158_, v_k_1159_, v_c_1160_, v_____do__lift_1161_);
lean_dec_ref(v_k_1159_);
lean_dec_ref(v_ty_1158_);
lean_dec(v_y_1157_);
lean_dec(v_fvarId_1150_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(uint8_t v_pu_1163_, lean_object* v_decl_1164_, lean_object* v_____do__lift_1165_, lean_object* v_params_1166_, lean_object* v_inst_1167_, lean_object* v_toBind_1168_, lean_object* v___f_1169_, lean_object* v_____do__lift_1170_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1171_ = lean_box(v_pu_1163_);
v___x_1172_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed), 10, 5);
lean_closure_set(v___x_1172_, 0, v___x_1171_);
lean_closure_set(v___x_1172_, 1, v_decl_1164_);
lean_closure_set(v___x_1172_, 2, v_____do__lift_1165_);
lean_closure_set(v___x_1172_, 3, v_params_1166_);
lean_closure_set(v___x_1172_, 4, v_____do__lift_1170_);
v___x_1173_ = lean_apply_2(v_inst_1167_, lean_box(0), v___x_1172_);
v___x_1174_ = lean_apply_4(v_toBind_1168_, lean_box(0), lean_box(0), v___x_1173_, v___f_1169_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed(lean_object* v_pu_1175_, lean_object* v_decl_1176_, lean_object* v_____do__lift_1177_, lean_object* v_params_1178_, lean_object* v_inst_1179_, lean_object* v_toBind_1180_, lean_object* v___f_1181_, lean_object* v_____do__lift_1182_){
_start:
{
uint8_t v_pu_boxed_1183_; lean_object* v_res_1184_; 
v_pu_boxed_1183_ = lean_unbox(v_pu_1175_);
v_res_1184_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(v_pu_boxed_1183_, v_decl_1176_, v_____do__lift_1177_, v_params_1178_, v_inst_1179_, v_toBind_1180_, v___f_1181_, v_____do__lift_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(lean_object* v_fvarId_1185_, lean_object* v_____do__lift_1186_, lean_object* v_toPure_1187_, lean_object* v_args_1188_, lean_object* v_c_1189_, lean_object* v_____do__lift_1190_){
_start:
{
uint8_t v___x_1191_; 
v___x_1191_ = l_Lean_instBEqFVarId_beq(v_fvarId_1185_, v_____do__lift_1186_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec_ref(v_c_1189_);
v___x_1192_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1192_, 0, v_____do__lift_1186_);
lean_ctor_set(v___x_1192_, 1, v_____do__lift_1190_);
v___x_1193_ = lean_apply_2(v_toPure_1187_, lean_box(0), v___x_1192_);
return v___x_1193_;
}
else
{
size_t v___x_1194_; size_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1194_ = lean_ptr_addr(v_args_1188_);
v___x_1195_ = lean_ptr_addr(v_____do__lift_1190_);
v___x_1196_ = lean_usize_dec_eq(v___x_1194_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_dec_ref(v_c_1189_);
v___x_1197_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1197_, 0, v_____do__lift_1186_);
lean_ctor_set(v___x_1197_, 1, v_____do__lift_1190_);
v___x_1198_ = lean_apply_2(v_toPure_1187_, lean_box(0), v___x_1197_);
return v___x_1198_;
}
else
{
lean_object* v___x_1199_; 
lean_dec_ref(v_____do__lift_1190_);
lean_dec(v_____do__lift_1186_);
v___x_1199_ = lean_apply_2(v_toPure_1187_, lean_box(0), v_c_1189_);
return v___x_1199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed(lean_object* v_fvarId_1200_, lean_object* v_____do__lift_1201_, lean_object* v_toPure_1202_, lean_object* v_args_1203_, lean_object* v_c_1204_, lean_object* v_____do__lift_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(v_fvarId_1200_, v_____do__lift_1201_, v_toPure_1202_, v_args_1203_, v_c_1204_, v_____do__lift_1205_);
lean_dec_ref(v_args_1203_);
lean_dec(v_fvarId_1200_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(lean_object* v_fvarId_1207_, lean_object* v_toPure_1208_, lean_object* v_args_1209_, lean_object* v_c_1210_, uint8_t v_pu_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_f_1214_, lean_object* v_toBind_1215_, lean_object* v_____do__lift_1216_){
_start:
{
lean_object* v___f_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; size_t v_sz_1220_; size_t v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_inc_ref(v_args_1209_);
v___f_1217_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed), 6, 5);
lean_closure_set(v___f_1217_, 0, v_fvarId_1207_);
lean_closure_set(v___f_1217_, 1, v_____do__lift_1216_);
lean_closure_set(v___f_1217_, 2, v_toPure_1208_);
lean_closure_set(v___f_1217_, 3, v_args_1209_);
lean_closure_set(v___f_1217_, 4, v_c_1210_);
v___x_1218_ = lean_box(v_pu_1211_);
lean_inc_ref(v_inst_1213_);
v___x_1219_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Arg_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_1219_, 0, lean_box(0));
lean_closure_set(v___x_1219_, 1, v___x_1218_);
lean_closure_set(v___x_1219_, 2, v_inst_1212_);
lean_closure_set(v___x_1219_, 3, v_inst_1213_);
lean_closure_set(v___x_1219_, 4, v_f_1214_);
v_sz_1220_ = lean_array_size(v_args_1209_);
v___x_1221_ = ((size_t)0ULL);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1213_, v___x_1219_, v_sz_1220_, v___x_1221_, v_args_1209_);
v___x_1223_ = lean_apply_4(v_toBind_1215_, lean_box(0), lean_box(0), v___x_1222_, v___f_1217_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed(lean_object* v_fvarId_1224_, lean_object* v_toPure_1225_, lean_object* v_args_1226_, lean_object* v_c_1227_, lean_object* v_pu_1228_, lean_object* v_inst_1229_, lean_object* v_inst_1230_, lean_object* v_f_1231_, lean_object* v_toBind_1232_, lean_object* v_____do__lift_1233_){
_start:
{
uint8_t v_pu_boxed_1234_; lean_object* v_res_1235_; 
v_pu_boxed_1234_ = lean_unbox(v_pu_1228_);
v_res_1235_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(v_fvarId_1224_, v_toPure_1225_, v_args_1226_, v_c_1227_, v_pu_boxed_1234_, v_inst_1229_, v_inst_1230_, v_f_1231_, v_toBind_1232_, v_____do__lift_1233_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(lean_object* v_typeName_1236_, lean_object* v_____do__lift_1237_, lean_object* v_____do__lift_1238_, lean_object* v_toPure_1239_, lean_object* v_alts_1240_, lean_object* v_resultType_1241_, lean_object* v_discr_1242_, lean_object* v_c_1243_, lean_object* v_____do__lift_1244_){
_start:
{
size_t v___x_1249_; size_t v___x_1250_; uint8_t v___x_1251_; 
v___x_1249_ = lean_ptr_addr(v_alts_1240_);
v___x_1250_ = lean_ptr_addr(v_____do__lift_1244_);
v___x_1251_ = lean_usize_dec_eq(v___x_1249_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_dec_ref(v_c_1243_);
goto v___jp_1245_;
}
else
{
size_t v___x_1252_; size_t v___x_1253_; uint8_t v___x_1254_; 
v___x_1252_ = lean_ptr_addr(v_resultType_1241_);
v___x_1253_ = lean_ptr_addr(v_____do__lift_1237_);
v___x_1254_ = lean_usize_dec_eq(v___x_1252_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_dec_ref(v_c_1243_);
goto v___jp_1245_;
}
else
{
uint8_t v___x_1255_; 
v___x_1255_ = l_Lean_instBEqFVarId_beq(v_discr_1242_, v_____do__lift_1238_);
if (v___x_1255_ == 0)
{
lean_dec_ref(v_c_1243_);
goto v___jp_1245_;
}
else
{
lean_object* v___x_1256_; 
lean_dec_ref(v_____do__lift_1244_);
lean_dec(v_____do__lift_1238_);
lean_dec_ref(v_____do__lift_1237_);
lean_dec(v_typeName_1236_);
v___x_1256_ = lean_apply_2(v_toPure_1239_, lean_box(0), v_c_1243_);
return v___x_1256_;
}
}
}
v___jp_1245_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1246_, 0, v_typeName_1236_);
lean_ctor_set(v___x_1246_, 1, v_____do__lift_1237_);
lean_ctor_set(v___x_1246_, 2, v_____do__lift_1238_);
lean_ctor_set(v___x_1246_, 3, v_____do__lift_1244_);
v___x_1247_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
v___x_1248_ = lean_apply_2(v_toPure_1239_, lean_box(0), v___x_1247_);
return v___x_1248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed(lean_object* v_typeName_1257_, lean_object* v_____do__lift_1258_, lean_object* v_____do__lift_1259_, lean_object* v_toPure_1260_, lean_object* v_alts_1261_, lean_object* v_resultType_1262_, lean_object* v_discr_1263_, lean_object* v_c_1264_, lean_object* v_____do__lift_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(v_typeName_1257_, v_____do__lift_1258_, v_____do__lift_1259_, v_toPure_1260_, v_alts_1261_, v_resultType_1262_, v_discr_1263_, v_c_1264_, v_____do__lift_1265_);
lean_dec(v_discr_1263_);
lean_dec_ref(v_resultType_1262_);
lean_dec_ref(v_alts_1261_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13(lean_object* v_typeName_1267_, lean_object* v_____do__lift_1268_, lean_object* v_toPure_1269_, lean_object* v_alts_1270_, lean_object* v_resultType_1271_, lean_object* v_discr_1272_, lean_object* v_c_1273_, lean_object* v_inst_1274_, lean_object* v___f_1275_, lean_object* v_toBind_1276_, lean_object* v_____do__lift_1277_){
_start:
{
lean_object* v___f_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_inc_ref(v_alts_1270_);
v___f_1278_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed), 9, 8);
lean_closure_set(v___f_1278_, 0, v_typeName_1267_);
lean_closure_set(v___f_1278_, 1, v_____do__lift_1268_);
lean_closure_set(v___f_1278_, 2, v_____do__lift_1277_);
lean_closure_set(v___f_1278_, 3, v_toPure_1269_);
lean_closure_set(v___f_1278_, 4, v_alts_1270_);
lean_closure_set(v___f_1278_, 5, v_resultType_1271_);
lean_closure_set(v___f_1278_, 6, v_discr_1272_);
lean_closure_set(v___f_1278_, 7, v_c_1273_);
v___x_1279_ = lean_unsigned_to_nat(0u);
v___x_1280_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_1274_, v___f_1275_, v___x_1279_, v_alts_1270_);
v___x_1281_ = lean_apply_4(v_toBind_1276_, lean_box(0), lean_box(0), v___x_1280_, v___f_1278_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14(lean_object* v_typeName_1282_, lean_object* v_toPure_1283_, lean_object* v_alts_1284_, lean_object* v_resultType_1285_, lean_object* v_discr_1286_, lean_object* v_c_1287_, lean_object* v_inst_1288_, lean_object* v___f_1289_, lean_object* v_toBind_1290_, lean_object* v_f_1291_, lean_object* v_____do__lift_1292_){
_start:
{
lean_object* v___f_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_inc(v_toBind_1290_);
lean_inc(v_discr_1286_);
v___f_1293_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13), 11, 10);
lean_closure_set(v___f_1293_, 0, v_typeName_1282_);
lean_closure_set(v___f_1293_, 1, v_____do__lift_1292_);
lean_closure_set(v___f_1293_, 2, v_toPure_1283_);
lean_closure_set(v___f_1293_, 3, v_alts_1284_);
lean_closure_set(v___f_1293_, 4, v_resultType_1285_);
lean_closure_set(v___f_1293_, 5, v_discr_1286_);
lean_closure_set(v___f_1293_, 6, v_c_1287_);
lean_closure_set(v___f_1293_, 7, v_inst_1288_);
lean_closure_set(v___f_1293_, 8, v___f_1289_);
lean_closure_set(v___f_1293_, 9, v_toBind_1290_);
v___x_1294_ = lean_apply_1(v_f_1291_, v_discr_1286_);
v___x_1295_ = lean_apply_4(v_toBind_1290_, lean_box(0), lean_box(0), v___x_1294_, v___f_1293_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(lean_object* v_fvarId_1296_, lean_object* v_____do__lift_1297_, lean_object* v_n_1298_, uint8_t v_check_1299_, uint8_t v_persistent_1300_, lean_object* v_objs_x3f_1301_, lean_object* v_toPure_1302_, lean_object* v_k_1303_, lean_object* v_c_1304_, lean_object* v_____do__lift_1305_){
_start:
{
size_t v___x_1306_; size_t v___x_1307_; uint8_t v___x_1308_; 
v___x_1306_ = lean_ptr_addr(v_fvarId_1296_);
v___x_1307_ = lean_ptr_addr(v_____do__lift_1297_);
v___x_1308_ = lean_usize_dec_eq(v___x_1306_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec_ref(v_c_1304_);
v___x_1309_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1309_, 0, v_____do__lift_1297_);
lean_ctor_set(v___x_1309_, 1, v_n_1298_);
lean_ctor_set(v___x_1309_, 2, v_objs_x3f_1301_);
lean_ctor_set(v___x_1309_, 3, v_____do__lift_1305_);
lean_ctor_set_uint8(v___x_1309_, sizeof(void*)*4, v_check_1299_);
lean_ctor_set_uint8(v___x_1309_, sizeof(void*)*4 + 1, v_persistent_1300_);
v___x_1310_ = lean_apply_2(v_toPure_1302_, lean_box(0), v___x_1309_);
return v___x_1310_;
}
else
{
uint8_t v___x_1311_; 
v___x_1311_ = lean_nat_dec_eq(v_n_1298_, v_n_1298_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_dec_ref(v_c_1304_);
v___x_1312_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1312_, 0, v_____do__lift_1297_);
lean_ctor_set(v___x_1312_, 1, v_n_1298_);
lean_ctor_set(v___x_1312_, 2, v_objs_x3f_1301_);
lean_ctor_set(v___x_1312_, 3, v_____do__lift_1305_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*4, v_check_1299_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*4 + 1, v_persistent_1300_);
v___x_1313_ = lean_apply_2(v_toPure_1302_, lean_box(0), v___x_1312_);
return v___x_1313_;
}
else
{
size_t v___x_1314_; size_t v___x_1315_; uint8_t v___x_1316_; 
v___x_1314_ = lean_ptr_addr(v_objs_x3f_1301_);
v___x_1315_ = lean_ptr_addr(v_objs_x3f_1301_);
v___x_1316_ = lean_usize_dec_eq(v___x_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_dec_ref(v_c_1304_);
v___x_1317_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1317_, 0, v_____do__lift_1297_);
lean_ctor_set(v___x_1317_, 1, v_n_1298_);
lean_ctor_set(v___x_1317_, 2, v_objs_x3f_1301_);
lean_ctor_set(v___x_1317_, 3, v_____do__lift_1305_);
lean_ctor_set_uint8(v___x_1317_, sizeof(void*)*4, v_check_1299_);
lean_ctor_set_uint8(v___x_1317_, sizeof(void*)*4 + 1, v_persistent_1300_);
v___x_1318_ = lean_apply_2(v_toPure_1302_, lean_box(0), v___x_1317_);
return v___x_1318_;
}
else
{
size_t v___x_1319_; size_t v___x_1320_; uint8_t v___x_1321_; 
v___x_1319_ = lean_ptr_addr(v_k_1303_);
v___x_1320_ = lean_ptr_addr(v_____do__lift_1305_);
v___x_1321_ = lean_usize_dec_eq(v___x_1319_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_dec_ref(v_c_1304_);
v___x_1322_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1322_, 0, v_____do__lift_1297_);
lean_ctor_set(v___x_1322_, 1, v_n_1298_);
lean_ctor_set(v___x_1322_, 2, v_objs_x3f_1301_);
lean_ctor_set(v___x_1322_, 3, v_____do__lift_1305_);
lean_ctor_set_uint8(v___x_1322_, sizeof(void*)*4, v_check_1299_);
lean_ctor_set_uint8(v___x_1322_, sizeof(void*)*4 + 1, v_persistent_1300_);
v___x_1323_ = lean_apply_2(v_toPure_1302_, lean_box(0), v___x_1322_);
return v___x_1323_;
}
else
{
lean_object* v___x_1324_; 
lean_dec_ref(v_____do__lift_1305_);
lean_dec(v_objs_x3f_1301_);
lean_dec(v_n_1298_);
lean_dec(v_____do__lift_1297_);
v___x_1324_ = lean_apply_2(v_toPure_1302_, lean_box(0), v_c_1304_);
return v___x_1324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed(lean_object* v_fvarId_1325_, lean_object* v_____do__lift_1326_, lean_object* v_n_1327_, lean_object* v_check_1328_, lean_object* v_persistent_1329_, lean_object* v_objs_x3f_1330_, lean_object* v_toPure_1331_, lean_object* v_k_1332_, lean_object* v_c_1333_, lean_object* v_____do__lift_1334_){
_start:
{
uint8_t v_check_2276__boxed_1335_; uint8_t v_persistent_2277__boxed_1336_; lean_object* v_res_1337_; 
v_check_2276__boxed_1335_ = lean_unbox(v_check_1328_);
v_persistent_2277__boxed_1336_ = lean_unbox(v_persistent_1329_);
v_res_1337_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(v_fvarId_1325_, v_____do__lift_1326_, v_n_1327_, v_check_2276__boxed_1335_, v_persistent_2277__boxed_1336_, v_objs_x3f_1330_, v_toPure_1331_, v_k_1332_, v_c_1333_, v_____do__lift_1334_);
lean_dec_ref(v_k_1332_);
lean_dec(v_fvarId_1325_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(lean_object* v_k_1338_, lean_object* v_decl_1339_, lean_object* v_toPure_1340_, lean_object* v_decl_1341_, lean_object* v_c_1342_, lean_object* v_____do__lift_1343_){
_start:
{
size_t v___x_1344_; size_t v___x_1345_; uint8_t v___x_1346_; 
v___x_1344_ = lean_ptr_addr(v_k_1338_);
v___x_1345_ = lean_ptr_addr(v_____do__lift_1343_);
v___x_1346_ = lean_usize_dec_eq(v___x_1344_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_dec_ref(v_c_1342_);
v___x_1347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1347_, 0, v_decl_1339_);
lean_ctor_set(v___x_1347_, 1, v_____do__lift_1343_);
v___x_1348_ = lean_apply_2(v_toPure_1340_, lean_box(0), v___x_1347_);
return v___x_1348_;
}
else
{
size_t v___x_1349_; size_t v___x_1350_; uint8_t v___x_1351_; 
v___x_1349_ = lean_ptr_addr(v_decl_1341_);
v___x_1350_ = lean_ptr_addr(v_decl_1339_);
v___x_1351_ = lean_usize_dec_eq(v___x_1349_, v___x_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_dec_ref(v_c_1342_);
v___x_1352_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_decl_1339_);
lean_ctor_set(v___x_1352_, 1, v_____do__lift_1343_);
v___x_1353_ = lean_apply_2(v_toPure_1340_, lean_box(0), v___x_1352_);
return v___x_1353_;
}
else
{
lean_object* v___x_1354_; 
lean_dec_ref(v_____do__lift_1343_);
lean_dec_ref(v_decl_1339_);
v___x_1354_ = lean_apply_2(v_toPure_1340_, lean_box(0), v_c_1342_);
return v___x_1354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed(lean_object* v_k_1355_, lean_object* v_decl_1356_, lean_object* v_toPure_1357_, lean_object* v_decl_1358_, lean_object* v_c_1359_, lean_object* v_____do__lift_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(v_k_1355_, v_decl_1356_, v_toPure_1357_, v_decl_1358_, v_c_1359_, v_____do__lift_1360_);
lean_dec_ref(v_decl_1358_);
lean_dec_ref(v_k_1355_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(lean_object* v_k_1362_, lean_object* v_decl_1363_, lean_object* v_toPure_1364_, lean_object* v_decl_1365_, lean_object* v_c_1366_, lean_object* v_____do__lift_1367_){
_start:
{
size_t v___x_1368_; size_t v___x_1369_; uint8_t v___x_1370_; 
v___x_1368_ = lean_ptr_addr(v_k_1362_);
v___x_1369_ = lean_ptr_addr(v_____do__lift_1367_);
v___x_1370_ = lean_usize_dec_eq(v___x_1368_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec_ref(v_c_1366_);
v___x_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1371_, 0, v_decl_1363_);
lean_ctor_set(v___x_1371_, 1, v_____do__lift_1367_);
v___x_1372_ = lean_apply_2(v_toPure_1364_, lean_box(0), v___x_1371_);
return v___x_1372_;
}
else
{
size_t v___x_1373_; size_t v___x_1374_; uint8_t v___x_1375_; 
v___x_1373_ = lean_ptr_addr(v_decl_1365_);
v___x_1374_ = lean_ptr_addr(v_decl_1363_);
v___x_1375_ = lean_usize_dec_eq(v___x_1373_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec_ref(v_c_1366_);
v___x_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1376_, 0, v_decl_1363_);
lean_ctor_set(v___x_1376_, 1, v_____do__lift_1367_);
v___x_1377_ = lean_apply_2(v_toPure_1364_, lean_box(0), v___x_1376_);
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; 
lean_dec_ref(v_____do__lift_1367_);
lean_dec_ref(v_decl_1363_);
v___x_1378_ = lean_apply_2(v_toPure_1364_, lean_box(0), v_c_1366_);
return v___x_1378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed(lean_object* v_k_1379_, lean_object* v_decl_1380_, lean_object* v_toPure_1381_, lean_object* v_decl_1382_, lean_object* v_c_1383_, lean_object* v_____do__lift_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(v_k_1379_, v_decl_1380_, v_toPure_1381_, v_decl_1382_, v_c_1383_, v_____do__lift_1384_);
lean_dec_ref(v_decl_1382_);
lean_dec_ref(v_k_1379_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(lean_object* v_fvarId_1386_, lean_object* v_____do__lift_1387_, lean_object* v_i_1388_, lean_object* v_____do__lift_1389_, lean_object* v_toPure_1390_, lean_object* v_y_1391_, lean_object* v_k_1392_, lean_object* v_c_1393_, lean_object* v_____do__lift_1394_){
_start:
{
size_t v___x_1395_; size_t v___x_1396_; uint8_t v___x_1397_; 
v___x_1395_ = lean_ptr_addr(v_fvarId_1386_);
v___x_1396_ = lean_ptr_addr(v_____do__lift_1387_);
v___x_1397_ = lean_usize_dec_eq(v___x_1395_, v___x_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_dec_ref(v_c_1393_);
v___x_1398_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1398_, 0, v_____do__lift_1387_);
lean_ctor_set(v___x_1398_, 1, v_i_1388_);
lean_ctor_set(v___x_1398_, 2, v_____do__lift_1389_);
lean_ctor_set(v___x_1398_, 3, v_____do__lift_1394_);
v___x_1399_ = lean_apply_2(v_toPure_1390_, lean_box(0), v___x_1398_);
return v___x_1399_;
}
else
{
uint8_t v___x_1400_; 
v___x_1400_ = lean_nat_dec_eq(v_i_1388_, v_i_1388_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_dec_ref(v_c_1393_);
v___x_1401_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1401_, 0, v_____do__lift_1387_);
lean_ctor_set(v___x_1401_, 1, v_i_1388_);
lean_ctor_set(v___x_1401_, 2, v_____do__lift_1389_);
lean_ctor_set(v___x_1401_, 3, v_____do__lift_1394_);
v___x_1402_ = lean_apply_2(v_toPure_1390_, lean_box(0), v___x_1401_);
return v___x_1402_;
}
else
{
size_t v___x_1403_; size_t v___x_1404_; uint8_t v___x_1405_; 
v___x_1403_ = lean_ptr_addr(v_y_1391_);
v___x_1404_ = lean_ptr_addr(v_____do__lift_1389_);
v___x_1405_ = lean_usize_dec_eq(v___x_1403_, v___x_1404_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_dec_ref(v_c_1393_);
v___x_1406_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1406_, 0, v_____do__lift_1387_);
lean_ctor_set(v___x_1406_, 1, v_i_1388_);
lean_ctor_set(v___x_1406_, 2, v_____do__lift_1389_);
lean_ctor_set(v___x_1406_, 3, v_____do__lift_1394_);
v___x_1407_ = lean_apply_2(v_toPure_1390_, lean_box(0), v___x_1406_);
return v___x_1407_;
}
else
{
size_t v___x_1408_; size_t v___x_1409_; uint8_t v___x_1410_; 
v___x_1408_ = lean_ptr_addr(v_k_1392_);
v___x_1409_ = lean_ptr_addr(v_____do__lift_1394_);
v___x_1410_ = lean_usize_dec_eq(v___x_1408_, v___x_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
lean_dec_ref(v_c_1393_);
v___x_1411_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1411_, 0, v_____do__lift_1387_);
lean_ctor_set(v___x_1411_, 1, v_i_1388_);
lean_ctor_set(v___x_1411_, 2, v_____do__lift_1389_);
lean_ctor_set(v___x_1411_, 3, v_____do__lift_1394_);
v___x_1412_ = lean_apply_2(v_toPure_1390_, lean_box(0), v___x_1411_);
return v___x_1412_;
}
else
{
lean_object* v___x_1413_; 
lean_dec_ref(v_____do__lift_1394_);
lean_dec(v_____do__lift_1389_);
lean_dec(v_i_1388_);
lean_dec(v_____do__lift_1387_);
v___x_1413_ = lean_apply_2(v_toPure_1390_, lean_box(0), v_c_1393_);
return v___x_1413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed(lean_object* v_fvarId_1414_, lean_object* v_____do__lift_1415_, lean_object* v_i_1416_, lean_object* v_____do__lift_1417_, lean_object* v_toPure_1418_, lean_object* v_y_1419_, lean_object* v_k_1420_, lean_object* v_c_1421_, lean_object* v_____do__lift_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(v_fvarId_1414_, v_____do__lift_1415_, v_i_1416_, v_____do__lift_1417_, v_toPure_1418_, v_y_1419_, v_k_1420_, v_c_1421_, v_____do__lift_1422_);
lean_dec_ref(v_k_1420_);
lean_dec(v_y_1419_);
lean_dec(v_fvarId_1414_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(lean_object* v_fvarId_1424_, lean_object* v_____do__lift_1425_, lean_object* v_toPure_1426_, lean_object* v_k_1427_, lean_object* v_c_1428_, lean_object* v_____do__lift_1429_){
_start:
{
size_t v___x_1430_; size_t v___x_1431_; uint8_t v___x_1432_; 
v___x_1430_ = lean_ptr_addr(v_fvarId_1424_);
v___x_1431_ = lean_ptr_addr(v_____do__lift_1425_);
v___x_1432_ = lean_usize_dec_eq(v___x_1430_, v___x_1431_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_dec_ref(v_c_1428_);
v___x_1433_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_1433_, 0, v_____do__lift_1425_);
lean_ctor_set(v___x_1433_, 1, v_____do__lift_1429_);
v___x_1434_ = lean_apply_2(v_toPure_1426_, lean_box(0), v___x_1433_);
return v___x_1434_;
}
else
{
size_t v___x_1435_; size_t v___x_1436_; uint8_t v___x_1437_; 
v___x_1435_ = lean_ptr_addr(v_k_1427_);
v___x_1436_ = lean_ptr_addr(v_____do__lift_1429_);
v___x_1437_ = lean_usize_dec_eq(v___x_1435_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_dec_ref(v_c_1428_);
v___x_1438_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_1438_, 0, v_____do__lift_1425_);
lean_ctor_set(v___x_1438_, 1, v_____do__lift_1429_);
v___x_1439_ = lean_apply_2(v_toPure_1426_, lean_box(0), v___x_1438_);
return v___x_1439_;
}
else
{
lean_object* v___x_1440_; 
lean_dec_ref(v_____do__lift_1429_);
lean_dec(v_____do__lift_1425_);
v___x_1440_ = lean_apply_2(v_toPure_1426_, lean_box(0), v_c_1428_);
return v___x_1440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed(lean_object* v_fvarId_1441_, lean_object* v_____do__lift_1442_, lean_object* v_toPure_1443_, lean_object* v_k_1444_, lean_object* v_c_1445_, lean_object* v_____do__lift_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(v_fvarId_1441_, v_____do__lift_1442_, v_toPure_1443_, v_k_1444_, v_c_1445_, v_____do__lift_1446_);
lean_dec_ref(v_k_1444_);
lean_dec(v_fvarId_1441_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(lean_object* v_type_1448_, lean_object* v_toPure_1449_, lean_object* v_c_1450_, lean_object* v_____do__lift_1451_){
_start:
{
size_t v___x_1452_; size_t v___x_1453_; uint8_t v___x_1454_; 
v___x_1452_ = lean_ptr_addr(v_type_1448_);
v___x_1453_ = lean_ptr_addr(v_____do__lift_1451_);
v___x_1454_ = lean_usize_dec_eq(v___x_1452_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_dec_ref(v_c_1450_);
v___x_1455_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1455_, 0, v_____do__lift_1451_);
v___x_1456_ = lean_apply_2(v_toPure_1449_, lean_box(0), v___x_1455_);
return v___x_1456_;
}
else
{
lean_object* v___x_1457_; 
lean_dec_ref(v_____do__lift_1451_);
v___x_1457_ = lean_apply_2(v_toPure_1449_, lean_box(0), v_c_1450_);
return v___x_1457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed(lean_object* v_type_1458_, lean_object* v_toPure_1459_, lean_object* v_c_1460_, lean_object* v_____do__lift_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(v_type_1458_, v_toPure_1459_, v_c_1460_, v_____do__lift_1461_);
lean_dec_ref(v_type_1458_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(lean_object* v_k_1463_, lean_object* v_toPure_1464_, lean_object* v_decl_1465_, lean_object* v_c_1466_, uint8_t v_pu_1467_, lean_object* v_inst_1468_, lean_object* v_inst_1469_, lean_object* v_f_1470_, lean_object* v_toBind_1471_, lean_object* v_decl_1472_){
_start:
{
lean_object* v___f_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_inc_ref(v_k_1463_);
v___f_1473_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1473_, 0, v_k_1463_);
lean_closure_set(v___f_1473_, 1, v_decl_1472_);
lean_closure_set(v___f_1473_, 2, v_toPure_1464_);
lean_closure_set(v___f_1473_, 3, v_decl_1465_);
lean_closure_set(v___f_1473_, 4, v_c_1466_);
v___x_1474_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1467_, v_inst_1468_, v_inst_1469_, v_f_1470_, v_k_1463_);
v___x_1475_ = lean_apply_4(v_toBind_1471_, lean_box(0), lean_box(0), v___x_1474_, v___f_1473_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed(lean_object* v_k_1476_, lean_object* v_toPure_1477_, lean_object* v_decl_1478_, lean_object* v_c_1479_, lean_object* v_pu_1480_, lean_object* v_inst_1481_, lean_object* v_inst_1482_, lean_object* v_f_1483_, lean_object* v_toBind_1484_, lean_object* v_decl_1485_){
_start:
{
uint8_t v_pu_boxed_1486_; lean_object* v_res_1487_; 
v_pu_boxed_1486_ = lean_unbox(v_pu_1480_);
v_res_1487_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(v_k_1476_, v_toPure_1477_, v_decl_1478_, v_c_1479_, v_pu_boxed_1486_, v_inst_1481_, v_inst_1482_, v_f_1483_, v_toBind_1484_, v_decl_1485_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(lean_object* v_k_1488_, lean_object* v_toPure_1489_, lean_object* v_decl_1490_, lean_object* v_c_1491_, uint8_t v_pu_1492_, lean_object* v_inst_1493_, lean_object* v_inst_1494_, lean_object* v_f_1495_, lean_object* v_toBind_1496_, lean_object* v_decl_1497_){
_start:
{
lean_object* v___f_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_inc_ref(v_k_1488_);
v___f_1498_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_1498_, 0, v_k_1488_);
lean_closure_set(v___f_1498_, 1, v_decl_1497_);
lean_closure_set(v___f_1498_, 2, v_toPure_1489_);
lean_closure_set(v___f_1498_, 3, v_decl_1490_);
lean_closure_set(v___f_1498_, 4, v_c_1491_);
v___x_1499_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1492_, v_inst_1493_, v_inst_1494_, v_f_1495_, v_k_1488_);
v___x_1500_ = lean_apply_4(v_toBind_1496_, lean_box(0), lean_box(0), v___x_1499_, v___f_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed(lean_object* v_k_1501_, lean_object* v_toPure_1502_, lean_object* v_decl_1503_, lean_object* v_c_1504_, lean_object* v_pu_1505_, lean_object* v_inst_1506_, lean_object* v_inst_1507_, lean_object* v_f_1508_, lean_object* v_toBind_1509_, lean_object* v_decl_1510_){
_start:
{
uint8_t v_pu_boxed_1511_; lean_object* v_res_1512_; 
v_pu_boxed_1511_ = lean_unbox(v_pu_1505_);
v_res_1512_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(v_k_1501_, v_toPure_1502_, v_decl_1503_, v_c_1504_, v_pu_boxed_1511_, v_inst_1506_, v_inst_1507_, v_f_1508_, v_toBind_1509_, v_decl_1510_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(uint8_t v_pu_1513_, lean_object* v_decl_1514_, lean_object* v_params_1515_, lean_object* v_inst_1516_, lean_object* v_toBind_1517_, lean_object* v___f_1518_, lean_object* v_inst_1519_, lean_object* v_f_1520_, lean_object* v_value_1521_, lean_object* v_____do__lift_1522_){
_start:
{
lean_object* v___x_1523_; lean_object* v___f_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1523_ = lean_box(v_pu_1513_);
lean_inc(v_toBind_1517_);
lean_inc(v_inst_1516_);
v___f_1524_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_1524_, 0, v___x_1523_);
lean_closure_set(v___f_1524_, 1, v_decl_1514_);
lean_closure_set(v___f_1524_, 2, v_____do__lift_1522_);
lean_closure_set(v___f_1524_, 3, v_params_1515_);
lean_closure_set(v___f_1524_, 4, v_inst_1516_);
lean_closure_set(v___f_1524_, 5, v_toBind_1517_);
lean_closure_set(v___f_1524_, 6, v___f_1518_);
v___x_1525_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1513_, v_inst_1516_, v_inst_1519_, v_f_1520_, v_value_1521_);
v___x_1526_ = lean_apply_4(v_toBind_1517_, lean_box(0), lean_box(0), v___x_1525_, v___f_1524_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed(lean_object* v_pu_1527_, lean_object* v_decl_1528_, lean_object* v_params_1529_, lean_object* v_inst_1530_, lean_object* v_toBind_1531_, lean_object* v___f_1532_, lean_object* v_inst_1533_, lean_object* v_f_1534_, lean_object* v_value_1535_, lean_object* v_____do__lift_1536_){
_start:
{
uint8_t v_pu_boxed_1537_; lean_object* v_res_1538_; 
v_pu_boxed_1537_ = lean_unbox(v_pu_1527_);
v_res_1538_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(v_pu_boxed_1537_, v_decl_1528_, v_params_1529_, v_inst_1530_, v_toBind_1531_, v___f_1532_, v_inst_1533_, v_f_1534_, v_value_1535_, v_____do__lift_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(uint8_t v_pu_1539_, lean_object* v_decl_1540_, lean_object* v_inst_1541_, lean_object* v_toBind_1542_, lean_object* v___f_1543_, lean_object* v_inst_1544_, lean_object* v_f_1545_, lean_object* v_value_1546_, lean_object* v_type_1547_, lean_object* v_params_1548_){
_start:
{
lean_object* v___x_1549_; lean_object* v___f_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1549_ = lean_box(v_pu_1539_);
lean_inc(v_f_1545_);
lean_inc_ref(v_inst_1544_);
lean_inc(v_toBind_1542_);
v___f_1550_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed), 10, 9);
lean_closure_set(v___f_1550_, 0, v___x_1549_);
lean_closure_set(v___f_1550_, 1, v_decl_1540_);
lean_closure_set(v___f_1550_, 2, v_params_1548_);
lean_closure_set(v___f_1550_, 3, v_inst_1541_);
lean_closure_set(v___f_1550_, 4, v_toBind_1542_);
lean_closure_set(v___f_1550_, 5, v___f_1543_);
lean_closure_set(v___f_1550_, 6, v_inst_1544_);
lean_closure_set(v___f_1550_, 7, v_f_1545_);
lean_closure_set(v___f_1550_, 8, v_value_1546_);
v___x_1551_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1544_, v_f_1545_, v_type_1547_);
v___x_1552_ = lean_apply_4(v_toBind_1542_, lean_box(0), lean_box(0), v___x_1551_, v___f_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed(lean_object* v_pu_1553_, lean_object* v_decl_1554_, lean_object* v_inst_1555_, lean_object* v_toBind_1556_, lean_object* v___f_1557_, lean_object* v_inst_1558_, lean_object* v_f_1559_, lean_object* v_value_1560_, lean_object* v_type_1561_, lean_object* v_params_1562_){
_start:
{
uint8_t v_pu_boxed_1563_; lean_object* v_res_1564_; 
v_pu_boxed_1563_ = lean_unbox(v_pu_1553_);
v_res_1564_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(v_pu_boxed_1563_, v_decl_1554_, v_inst_1555_, v_toBind_1556_, v___f_1557_, v_inst_1558_, v_f_1559_, v_value_1560_, v_type_1561_, v_params_1562_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(lean_object* v_k_1565_, lean_object* v_toPure_1566_, lean_object* v_decl_1567_, lean_object* v_c_1568_, uint8_t v_pu_1569_, lean_object* v_inst_1570_, lean_object* v_inst_1571_, lean_object* v_f_1572_, lean_object* v_toBind_1573_, lean_object* v_decl_1574_){
_start:
{
lean_object* v___f_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_inc_ref(v_k_1565_);
v___f_1575_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_1575_, 0, v_k_1565_);
lean_closure_set(v___f_1575_, 1, v_decl_1574_);
lean_closure_set(v___f_1575_, 2, v_toPure_1566_);
lean_closure_set(v___f_1575_, 3, v_decl_1567_);
lean_closure_set(v___f_1575_, 4, v_c_1568_);
v___x_1576_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1569_, v_inst_1570_, v_inst_1571_, v_f_1572_, v_k_1565_);
v___x_1577_ = lean_apply_4(v_toBind_1573_, lean_box(0), lean_box(0), v___x_1576_, v___f_1575_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed(lean_object* v_k_1578_, lean_object* v_toPure_1579_, lean_object* v_decl_1580_, lean_object* v_c_1581_, lean_object* v_pu_1582_, lean_object* v_inst_1583_, lean_object* v_inst_1584_, lean_object* v_f_1585_, lean_object* v_toBind_1586_, lean_object* v_decl_1587_){
_start:
{
uint8_t v_pu_boxed_1588_; lean_object* v_res_1589_; 
v_pu_boxed_1588_ = lean_unbox(v_pu_1582_);
v_res_1589_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(v_k_1578_, v_toPure_1579_, v_decl_1580_, v_c_1581_, v_pu_boxed_1588_, v_inst_1583_, v_inst_1584_, v_f_1585_, v_toBind_1586_, v_decl_1587_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed(lean_object* v_pu_1590_, lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_f_1593_, lean_object* v_x_1594_){
_start:
{
uint8_t v_pu_boxed_1595_; lean_object* v_res_1596_; 
v_pu_boxed_1595_ = lean_unbox(v_pu_1590_);
v_res_1596_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(v_pu_boxed_1595_, v_inst_1591_, v_inst_1592_, v_f_1593_, v_x_1594_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(lean_object* v_fvarId_1597_, lean_object* v_____do__lift_1598_, lean_object* v_i_1599_, lean_object* v_toPure_1600_, lean_object* v_y_1601_, lean_object* v_k_1602_, lean_object* v_c_1603_, uint8_t v_pu_1604_, lean_object* v_inst_1605_, lean_object* v_inst_1606_, lean_object* v_f_1607_, lean_object* v_toBind_1608_, lean_object* v_____do__lift_1609_){
_start:
{
lean_object* v___f_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_inc_ref(v_k_1602_);
v___f_1610_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed), 9, 8);
lean_closure_set(v___f_1610_, 0, v_fvarId_1597_);
lean_closure_set(v___f_1610_, 1, v_____do__lift_1598_);
lean_closure_set(v___f_1610_, 2, v_i_1599_);
lean_closure_set(v___f_1610_, 3, v_____do__lift_1609_);
lean_closure_set(v___f_1610_, 4, v_toPure_1600_);
lean_closure_set(v___f_1610_, 5, v_y_1601_);
lean_closure_set(v___f_1610_, 6, v_k_1602_);
lean_closure_set(v___f_1610_, 7, v_c_1603_);
v___x_1611_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1604_, v_inst_1605_, v_inst_1606_, v_f_1607_, v_k_1602_);
v___x_1612_ = lean_apply_4(v_toBind_1608_, lean_box(0), lean_box(0), v___x_1611_, v___f_1610_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed(lean_object* v_fvarId_1613_, lean_object* v_____do__lift_1614_, lean_object* v_i_1615_, lean_object* v_toPure_1616_, lean_object* v_y_1617_, lean_object* v_k_1618_, lean_object* v_c_1619_, lean_object* v_pu_1620_, lean_object* v_inst_1621_, lean_object* v_inst_1622_, lean_object* v_f_1623_, lean_object* v_toBind_1624_, lean_object* v_____do__lift_1625_){
_start:
{
uint8_t v_pu_boxed_1626_; lean_object* v_res_1627_; 
v_pu_boxed_1626_ = lean_unbox(v_pu_1620_);
v_res_1627_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(v_fvarId_1613_, v_____do__lift_1614_, v_i_1615_, v_toPure_1616_, v_y_1617_, v_k_1618_, v_c_1619_, v_pu_boxed_1626_, v_inst_1621_, v_inst_1622_, v_f_1623_, v_toBind_1624_, v_____do__lift_1625_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(lean_object* v_fvarId_1628_, lean_object* v_i_1629_, lean_object* v_toPure_1630_, lean_object* v_y_1631_, lean_object* v_k_1632_, lean_object* v_c_1633_, uint8_t v_pu_1634_, lean_object* v_inst_1635_, lean_object* v_inst_1636_, lean_object* v_f_1637_, lean_object* v_toBind_1638_, lean_object* v_____do__lift_1639_){
_start:
{
lean_object* v___x_1640_; lean_object* v___f_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1640_ = lean_box(v_pu_1634_);
lean_inc(v_toBind_1638_);
lean_inc(v_f_1637_);
lean_inc_ref(v_inst_1636_);
lean_inc(v_y_1631_);
v___f_1641_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed), 13, 12);
lean_closure_set(v___f_1641_, 0, v_fvarId_1628_);
lean_closure_set(v___f_1641_, 1, v_____do__lift_1639_);
lean_closure_set(v___f_1641_, 2, v_i_1629_);
lean_closure_set(v___f_1641_, 3, v_toPure_1630_);
lean_closure_set(v___f_1641_, 4, v_y_1631_);
lean_closure_set(v___f_1641_, 5, v_k_1632_);
lean_closure_set(v___f_1641_, 6, v_c_1633_);
lean_closure_set(v___f_1641_, 7, v___x_1640_);
lean_closure_set(v___f_1641_, 8, v_inst_1635_);
lean_closure_set(v___f_1641_, 9, v_inst_1636_);
lean_closure_set(v___f_1641_, 10, v_f_1637_);
lean_closure_set(v___f_1641_, 11, v_toBind_1638_);
v___x_1642_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_1634_, v_inst_1636_, v_f_1637_, v_y_1631_);
v___x_1643_ = lean_apply_4(v_toBind_1638_, lean_box(0), lean_box(0), v___x_1642_, v___f_1641_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed(lean_object* v_fvarId_1644_, lean_object* v_i_1645_, lean_object* v_toPure_1646_, lean_object* v_y_1647_, lean_object* v_k_1648_, lean_object* v_c_1649_, lean_object* v_pu_1650_, lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_f_1653_, lean_object* v_toBind_1654_, lean_object* v_____do__lift_1655_){
_start:
{
uint8_t v_pu_boxed_1656_; lean_object* v_res_1657_; 
v_pu_boxed_1656_ = lean_unbox(v_pu_1650_);
v_res_1657_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(v_fvarId_1644_, v_i_1645_, v_toPure_1646_, v_y_1647_, v_k_1648_, v_c_1649_, v_pu_boxed_1656_, v_inst_1651_, v_inst_1652_, v_f_1653_, v_toBind_1654_, v_____do__lift_1655_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(lean_object* v_fvarId_1658_, lean_object* v_____do__lift_1659_, lean_object* v_i_1660_, lean_object* v_toPure_1661_, lean_object* v_y_1662_, lean_object* v_k_1663_, lean_object* v_c_1664_, uint8_t v_pu_1665_, lean_object* v_inst_1666_, lean_object* v_inst_1667_, lean_object* v_f_1668_, lean_object* v_toBind_1669_, lean_object* v_____do__lift_1670_){
_start:
{
lean_object* v___f_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_inc_ref(v_k_1663_);
v___f_1671_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed), 9, 8);
lean_closure_set(v___f_1671_, 0, v_fvarId_1658_);
lean_closure_set(v___f_1671_, 1, v_____do__lift_1659_);
lean_closure_set(v___f_1671_, 2, v_i_1660_);
lean_closure_set(v___f_1671_, 3, v_____do__lift_1670_);
lean_closure_set(v___f_1671_, 4, v_toPure_1661_);
lean_closure_set(v___f_1671_, 5, v_y_1662_);
lean_closure_set(v___f_1671_, 6, v_k_1663_);
lean_closure_set(v___f_1671_, 7, v_c_1664_);
v___x_1672_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1665_, v_inst_1666_, v_inst_1667_, v_f_1668_, v_k_1663_);
v___x_1673_ = lean_apply_4(v_toBind_1669_, lean_box(0), lean_box(0), v___x_1672_, v___f_1671_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed(lean_object* v_fvarId_1674_, lean_object* v_____do__lift_1675_, lean_object* v_i_1676_, lean_object* v_toPure_1677_, lean_object* v_y_1678_, lean_object* v_k_1679_, lean_object* v_c_1680_, lean_object* v_pu_1681_, lean_object* v_inst_1682_, lean_object* v_inst_1683_, lean_object* v_f_1684_, lean_object* v_toBind_1685_, lean_object* v_____do__lift_1686_){
_start:
{
uint8_t v_pu_boxed_1687_; lean_object* v_res_1688_; 
v_pu_boxed_1687_ = lean_unbox(v_pu_1681_);
v_res_1688_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(v_fvarId_1674_, v_____do__lift_1675_, v_i_1676_, v_toPure_1677_, v_y_1678_, v_k_1679_, v_c_1680_, v_pu_boxed_1687_, v_inst_1682_, v_inst_1683_, v_f_1684_, v_toBind_1685_, v_____do__lift_1686_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(lean_object* v_fvarId_1689_, lean_object* v_i_1690_, lean_object* v_toPure_1691_, lean_object* v_y_1692_, lean_object* v_k_1693_, lean_object* v_c_1694_, uint8_t v_pu_1695_, lean_object* v_inst_1696_, lean_object* v_inst_1697_, lean_object* v_f_1698_, lean_object* v_toBind_1699_, lean_object* v_____do__lift_1700_){
_start:
{
lean_object* v___x_1701_; lean_object* v___f_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1701_ = lean_box(v_pu_1695_);
lean_inc(v_toBind_1699_);
lean_inc(v_f_1698_);
lean_inc(v_y_1692_);
v___f_1702_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed), 13, 12);
lean_closure_set(v___f_1702_, 0, v_fvarId_1689_);
lean_closure_set(v___f_1702_, 1, v_____do__lift_1700_);
lean_closure_set(v___f_1702_, 2, v_i_1690_);
lean_closure_set(v___f_1702_, 3, v_toPure_1691_);
lean_closure_set(v___f_1702_, 4, v_y_1692_);
lean_closure_set(v___f_1702_, 5, v_k_1693_);
lean_closure_set(v___f_1702_, 6, v_c_1694_);
lean_closure_set(v___f_1702_, 7, v___x_1701_);
lean_closure_set(v___f_1702_, 8, v_inst_1696_);
lean_closure_set(v___f_1702_, 9, v_inst_1697_);
lean_closure_set(v___f_1702_, 10, v_f_1698_);
lean_closure_set(v___f_1702_, 11, v_toBind_1699_);
v___x_1703_ = lean_apply_1(v_f_1698_, v_y_1692_);
v___x_1704_ = lean_apply_4(v_toBind_1699_, lean_box(0), lean_box(0), v___x_1703_, v___f_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed(lean_object* v_fvarId_1705_, lean_object* v_i_1706_, lean_object* v_toPure_1707_, lean_object* v_y_1708_, lean_object* v_k_1709_, lean_object* v_c_1710_, lean_object* v_pu_1711_, lean_object* v_inst_1712_, lean_object* v_inst_1713_, lean_object* v_f_1714_, lean_object* v_toBind_1715_, lean_object* v_____do__lift_1716_){
_start:
{
uint8_t v_pu_boxed_1717_; lean_object* v_res_1718_; 
v_pu_boxed_1717_ = lean_unbox(v_pu_1711_);
v_res_1718_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(v_fvarId_1705_, v_i_1706_, v_toPure_1707_, v_y_1708_, v_k_1709_, v_c_1710_, v_pu_boxed_1717_, v_inst_1712_, v_inst_1713_, v_f_1714_, v_toBind_1715_, v_____do__lift_1716_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(lean_object* v_fvarId_1719_, lean_object* v_____do__lift_1720_, lean_object* v_i_1721_, lean_object* v_offset_1722_, lean_object* v_____do__lift_1723_, lean_object* v_toPure_1724_, lean_object* v_y_1725_, lean_object* v_ty_1726_, lean_object* v_k_1727_, lean_object* v_c_1728_, uint8_t v_pu_1729_, lean_object* v_inst_1730_, lean_object* v_inst_1731_, lean_object* v_f_1732_, lean_object* v_toBind_1733_, lean_object* v_____do__lift_1734_){
_start:
{
lean_object* v___f_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_inc_ref(v_k_1727_);
v___f_1735_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed), 12, 11);
lean_closure_set(v___f_1735_, 0, v_fvarId_1719_);
lean_closure_set(v___f_1735_, 1, v_____do__lift_1720_);
lean_closure_set(v___f_1735_, 2, v_i_1721_);
lean_closure_set(v___f_1735_, 3, v_offset_1722_);
lean_closure_set(v___f_1735_, 4, v_____do__lift_1723_);
lean_closure_set(v___f_1735_, 5, v_____do__lift_1734_);
lean_closure_set(v___f_1735_, 6, v_toPure_1724_);
lean_closure_set(v___f_1735_, 7, v_y_1725_);
lean_closure_set(v___f_1735_, 8, v_ty_1726_);
lean_closure_set(v___f_1735_, 9, v_k_1727_);
lean_closure_set(v___f_1735_, 10, v_c_1728_);
v___x_1736_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1729_, v_inst_1730_, v_inst_1731_, v_f_1732_, v_k_1727_);
v___x_1737_ = lean_apply_4(v_toBind_1733_, lean_box(0), lean_box(0), v___x_1736_, v___f_1735_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed(lean_object* v_fvarId_1738_, lean_object* v_____do__lift_1739_, lean_object* v_i_1740_, lean_object* v_offset_1741_, lean_object* v_____do__lift_1742_, lean_object* v_toPure_1743_, lean_object* v_y_1744_, lean_object* v_ty_1745_, lean_object* v_k_1746_, lean_object* v_c_1747_, lean_object* v_pu_1748_, lean_object* v_inst_1749_, lean_object* v_inst_1750_, lean_object* v_f_1751_, lean_object* v_toBind_1752_, lean_object* v_____do__lift_1753_){
_start:
{
uint8_t v_pu_boxed_1754_; lean_object* v_res_1755_; 
v_pu_boxed_1754_ = lean_unbox(v_pu_1748_);
v_res_1755_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(v_fvarId_1738_, v_____do__lift_1739_, v_i_1740_, v_offset_1741_, v_____do__lift_1742_, v_toPure_1743_, v_y_1744_, v_ty_1745_, v_k_1746_, v_c_1747_, v_pu_boxed_1754_, v_inst_1749_, v_inst_1750_, v_f_1751_, v_toBind_1752_, v_____do__lift_1753_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(lean_object* v_fvarId_1756_, lean_object* v_____do__lift_1757_, lean_object* v_i_1758_, lean_object* v_offset_1759_, lean_object* v_toPure_1760_, lean_object* v_y_1761_, lean_object* v_ty_1762_, lean_object* v_k_1763_, lean_object* v_c_1764_, uint8_t v_pu_1765_, lean_object* v_inst_1766_, lean_object* v_inst_1767_, lean_object* v_f_1768_, lean_object* v_toBind_1769_, lean_object* v_____do__lift_1770_){
_start:
{
lean_object* v___x_1771_; lean_object* v___f_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1771_ = lean_box(v_pu_1765_);
lean_inc(v_toBind_1769_);
lean_inc(v_f_1768_);
lean_inc_ref(v_inst_1767_);
lean_inc_ref(v_ty_1762_);
v___f_1772_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed), 16, 15);
lean_closure_set(v___f_1772_, 0, v_fvarId_1756_);
lean_closure_set(v___f_1772_, 1, v_____do__lift_1757_);
lean_closure_set(v___f_1772_, 2, v_i_1758_);
lean_closure_set(v___f_1772_, 3, v_offset_1759_);
lean_closure_set(v___f_1772_, 4, v_____do__lift_1770_);
lean_closure_set(v___f_1772_, 5, v_toPure_1760_);
lean_closure_set(v___f_1772_, 6, v_y_1761_);
lean_closure_set(v___f_1772_, 7, v_ty_1762_);
lean_closure_set(v___f_1772_, 8, v_k_1763_);
lean_closure_set(v___f_1772_, 9, v_c_1764_);
lean_closure_set(v___f_1772_, 10, v___x_1771_);
lean_closure_set(v___f_1772_, 11, v_inst_1766_);
lean_closure_set(v___f_1772_, 12, v_inst_1767_);
lean_closure_set(v___f_1772_, 13, v_f_1768_);
lean_closure_set(v___f_1772_, 14, v_toBind_1769_);
v___x_1773_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1767_, v_f_1768_, v_ty_1762_);
v___x_1774_ = lean_apply_4(v_toBind_1769_, lean_box(0), lean_box(0), v___x_1773_, v___f_1772_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed(lean_object* v_fvarId_1775_, lean_object* v_____do__lift_1776_, lean_object* v_i_1777_, lean_object* v_offset_1778_, lean_object* v_toPure_1779_, lean_object* v_y_1780_, lean_object* v_ty_1781_, lean_object* v_k_1782_, lean_object* v_c_1783_, lean_object* v_pu_1784_, lean_object* v_inst_1785_, lean_object* v_inst_1786_, lean_object* v_f_1787_, lean_object* v_toBind_1788_, lean_object* v_____do__lift_1789_){
_start:
{
uint8_t v_pu_boxed_1790_; lean_object* v_res_1791_; 
v_pu_boxed_1790_ = lean_unbox(v_pu_1784_);
v_res_1791_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(v_fvarId_1775_, v_____do__lift_1776_, v_i_1777_, v_offset_1778_, v_toPure_1779_, v_y_1780_, v_ty_1781_, v_k_1782_, v_c_1783_, v_pu_boxed_1790_, v_inst_1785_, v_inst_1786_, v_f_1787_, v_toBind_1788_, v_____do__lift_1789_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(lean_object* v_fvarId_1792_, lean_object* v_i_1793_, lean_object* v_offset_1794_, lean_object* v_toPure_1795_, lean_object* v_y_1796_, lean_object* v_ty_1797_, lean_object* v_k_1798_, lean_object* v_c_1799_, uint8_t v_pu_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_f_1803_, lean_object* v_toBind_1804_, lean_object* v_____do__lift_1805_){
_start:
{
lean_object* v___x_1806_; lean_object* v___f_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1806_ = lean_box(v_pu_1800_);
lean_inc(v_toBind_1804_);
lean_inc(v_f_1803_);
lean_inc(v_y_1796_);
v___f_1807_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed), 15, 14);
lean_closure_set(v___f_1807_, 0, v_fvarId_1792_);
lean_closure_set(v___f_1807_, 1, v_____do__lift_1805_);
lean_closure_set(v___f_1807_, 2, v_i_1793_);
lean_closure_set(v___f_1807_, 3, v_offset_1794_);
lean_closure_set(v___f_1807_, 4, v_toPure_1795_);
lean_closure_set(v___f_1807_, 5, v_y_1796_);
lean_closure_set(v___f_1807_, 6, v_ty_1797_);
lean_closure_set(v___f_1807_, 7, v_k_1798_);
lean_closure_set(v___f_1807_, 8, v_c_1799_);
lean_closure_set(v___f_1807_, 9, v___x_1806_);
lean_closure_set(v___f_1807_, 10, v_inst_1801_);
lean_closure_set(v___f_1807_, 11, v_inst_1802_);
lean_closure_set(v___f_1807_, 12, v_f_1803_);
lean_closure_set(v___f_1807_, 13, v_toBind_1804_);
v___x_1808_ = lean_apply_1(v_f_1803_, v_y_1796_);
v___x_1809_ = lean_apply_4(v_toBind_1804_, lean_box(0), lean_box(0), v___x_1808_, v___f_1807_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed(lean_object* v_fvarId_1810_, lean_object* v_i_1811_, lean_object* v_offset_1812_, lean_object* v_toPure_1813_, lean_object* v_y_1814_, lean_object* v_ty_1815_, lean_object* v_k_1816_, lean_object* v_c_1817_, lean_object* v_pu_1818_, lean_object* v_inst_1819_, lean_object* v_inst_1820_, lean_object* v_f_1821_, lean_object* v_toBind_1822_, lean_object* v_____do__lift_1823_){
_start:
{
uint8_t v_pu_boxed_1824_; lean_object* v_res_1825_; 
v_pu_boxed_1824_ = lean_unbox(v_pu_1818_);
v_res_1825_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(v_fvarId_1810_, v_i_1811_, v_offset_1812_, v_toPure_1813_, v_y_1814_, v_ty_1815_, v_k_1816_, v_c_1817_, v_pu_boxed_1824_, v_inst_1819_, v_inst_1820_, v_f_1821_, v_toBind_1822_, v_____do__lift_1823_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(lean_object* v_fvarId_1826_, lean_object* v_cidx_1827_, lean_object* v_toPure_1828_, lean_object* v_k_1829_, lean_object* v_c_1830_, uint8_t v_pu_1831_, lean_object* v_inst_1832_, lean_object* v_inst_1833_, lean_object* v_f_1834_, lean_object* v_toBind_1835_, lean_object* v_____do__lift_1836_){
_start:
{
lean_object* v___f_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_inc_ref(v_k_1829_);
v___f_1837_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27___boxed), 7, 6);
lean_closure_set(v___f_1837_, 0, v_fvarId_1826_);
lean_closure_set(v___f_1837_, 1, v_____do__lift_1836_);
lean_closure_set(v___f_1837_, 2, v_cidx_1827_);
lean_closure_set(v___f_1837_, 3, v_toPure_1828_);
lean_closure_set(v___f_1837_, 4, v_k_1829_);
lean_closure_set(v___f_1837_, 5, v_c_1830_);
v___x_1838_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1831_, v_inst_1832_, v_inst_1833_, v_f_1834_, v_k_1829_);
v___x_1839_ = lean_apply_4(v_toBind_1835_, lean_box(0), lean_box(0), v___x_1838_, v___f_1837_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed(lean_object* v_fvarId_1840_, lean_object* v_cidx_1841_, lean_object* v_toPure_1842_, lean_object* v_k_1843_, lean_object* v_c_1844_, lean_object* v_pu_1845_, lean_object* v_inst_1846_, lean_object* v_inst_1847_, lean_object* v_f_1848_, lean_object* v_toBind_1849_, lean_object* v_____do__lift_1850_){
_start:
{
uint8_t v_pu_boxed_1851_; lean_object* v_res_1852_; 
v_pu_boxed_1851_ = lean_unbox(v_pu_1845_);
v_res_1852_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(v_fvarId_1840_, v_cidx_1841_, v_toPure_1842_, v_k_1843_, v_c_1844_, v_pu_boxed_1851_, v_inst_1846_, v_inst_1847_, v_f_1848_, v_toBind_1849_, v_____do__lift_1850_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(lean_object* v_fvarId_1853_, lean_object* v_n_1854_, uint8_t v_check_1855_, uint8_t v_persistent_1856_, lean_object* v_toPure_1857_, lean_object* v_k_1858_, lean_object* v_c_1859_, uint8_t v_pu_1860_, lean_object* v_inst_1861_, lean_object* v_inst_1862_, lean_object* v_f_1863_, lean_object* v_toBind_1864_, lean_object* v_____do__lift_1865_){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___f_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1866_ = lean_box(v_check_1855_);
v___x_1867_ = lean_box(v_persistent_1856_);
lean_inc_ref(v_k_1858_);
v___f_1868_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29___boxed), 9, 8);
lean_closure_set(v___f_1868_, 0, v_fvarId_1853_);
lean_closure_set(v___f_1868_, 1, v_____do__lift_1865_);
lean_closure_set(v___f_1868_, 2, v_n_1854_);
lean_closure_set(v___f_1868_, 3, v___x_1866_);
lean_closure_set(v___f_1868_, 4, v___x_1867_);
lean_closure_set(v___f_1868_, 5, v_toPure_1857_);
lean_closure_set(v___f_1868_, 6, v_k_1858_);
lean_closure_set(v___f_1868_, 7, v_c_1859_);
v___x_1869_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1860_, v_inst_1861_, v_inst_1862_, v_f_1863_, v_k_1858_);
v___x_1870_ = lean_apply_4(v_toBind_1864_, lean_box(0), lean_box(0), v___x_1869_, v___f_1868_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed(lean_object* v_fvarId_1871_, lean_object* v_n_1872_, lean_object* v_check_1873_, lean_object* v_persistent_1874_, lean_object* v_toPure_1875_, lean_object* v_k_1876_, lean_object* v_c_1877_, lean_object* v_pu_1878_, lean_object* v_inst_1879_, lean_object* v_inst_1880_, lean_object* v_f_1881_, lean_object* v_toBind_1882_, lean_object* v_____do__lift_1883_){
_start:
{
uint8_t v_check_2619__boxed_1884_; uint8_t v_persistent_2620__boxed_1885_; uint8_t v_pu_boxed_1886_; lean_object* v_res_1887_; 
v_check_2619__boxed_1884_ = lean_unbox(v_check_1873_);
v_persistent_2620__boxed_1885_ = lean_unbox(v_persistent_1874_);
v_pu_boxed_1886_ = lean_unbox(v_pu_1878_);
v_res_1887_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(v_fvarId_1871_, v_n_1872_, v_check_2619__boxed_1884_, v_persistent_2620__boxed_1885_, v_toPure_1875_, v_k_1876_, v_c_1877_, v_pu_boxed_1886_, v_inst_1879_, v_inst_1880_, v_f_1881_, v_toBind_1882_, v_____do__lift_1883_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(lean_object* v_fvarId_1888_, lean_object* v_n_1889_, uint8_t v_check_1890_, uint8_t v_persistent_1891_, lean_object* v_objs_x3f_1892_, lean_object* v_toPure_1893_, lean_object* v_k_1894_, lean_object* v_c_1895_, uint8_t v_pu_1896_, lean_object* v_inst_1897_, lean_object* v_inst_1898_, lean_object* v_f_1899_, lean_object* v_toBind_1900_, lean_object* v_____do__lift_1901_){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___f_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1902_ = lean_box(v_check_1890_);
v___x_1903_ = lean_box(v_persistent_1891_);
lean_inc_ref(v_k_1894_);
v___f_1904_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed), 10, 9);
lean_closure_set(v___f_1904_, 0, v_fvarId_1888_);
lean_closure_set(v___f_1904_, 1, v_____do__lift_1901_);
lean_closure_set(v___f_1904_, 2, v_n_1889_);
lean_closure_set(v___f_1904_, 3, v___x_1902_);
lean_closure_set(v___f_1904_, 4, v___x_1903_);
lean_closure_set(v___f_1904_, 5, v_objs_x3f_1892_);
lean_closure_set(v___f_1904_, 6, v_toPure_1893_);
lean_closure_set(v___f_1904_, 7, v_k_1894_);
lean_closure_set(v___f_1904_, 8, v_c_1895_);
v___x_1905_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1896_, v_inst_1897_, v_inst_1898_, v_f_1899_, v_k_1894_);
v___x_1906_ = lean_apply_4(v_toBind_1900_, lean_box(0), lean_box(0), v___x_1905_, v___f_1904_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed(lean_object* v_fvarId_1907_, lean_object* v_n_1908_, lean_object* v_check_1909_, lean_object* v_persistent_1910_, lean_object* v_objs_x3f_1911_, lean_object* v_toPure_1912_, lean_object* v_k_1913_, lean_object* v_c_1914_, lean_object* v_pu_1915_, lean_object* v_inst_1916_, lean_object* v_inst_1917_, lean_object* v_f_1918_, lean_object* v_toBind_1919_, lean_object* v_____do__lift_1920_){
_start:
{
uint8_t v_check_2630__boxed_1921_; uint8_t v_persistent_2631__boxed_1922_; uint8_t v_pu_boxed_1923_; lean_object* v_res_1924_; 
v_check_2630__boxed_1921_ = lean_unbox(v_check_1909_);
v_persistent_2631__boxed_1922_ = lean_unbox(v_persistent_1910_);
v_pu_boxed_1923_ = lean_unbox(v_pu_1915_);
v_res_1924_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(v_fvarId_1907_, v_n_1908_, v_check_2630__boxed_1921_, v_persistent_2631__boxed_1922_, v_objs_x3f_1911_, v_toPure_1912_, v_k_1913_, v_c_1914_, v_pu_boxed_1923_, v_inst_1916_, v_inst_1917_, v_f_1918_, v_toBind_1919_, v_____do__lift_1920_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(lean_object* v_fvarId_1925_, lean_object* v_toPure_1926_, lean_object* v_k_1927_, lean_object* v_c_1928_, uint8_t v_pu_1929_, lean_object* v_inst_1930_, lean_object* v_inst_1931_, lean_object* v_f_1932_, lean_object* v_toBind_1933_, lean_object* v_____do__lift_1934_){
_start:
{
lean_object* v___f_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_inc_ref(v_k_1927_);
v___f_1935_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed), 6, 5);
lean_closure_set(v___f_1935_, 0, v_fvarId_1925_);
lean_closure_set(v___f_1935_, 1, v_____do__lift_1934_);
lean_closure_set(v___f_1935_, 2, v_toPure_1926_);
lean_closure_set(v___f_1935_, 3, v_k_1927_);
lean_closure_set(v___f_1935_, 4, v_c_1928_);
v___x_1936_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1929_, v_inst_1930_, v_inst_1931_, v_f_1932_, v_k_1927_);
v___x_1937_ = lean_apply_4(v_toBind_1933_, lean_box(0), lean_box(0), v___x_1936_, v___f_1935_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed(lean_object* v_fvarId_1938_, lean_object* v_toPure_1939_, lean_object* v_k_1940_, lean_object* v_c_1941_, lean_object* v_pu_1942_, lean_object* v_inst_1943_, lean_object* v_inst_1944_, lean_object* v_f_1945_, lean_object* v_toBind_1946_, lean_object* v_____do__lift_1947_){
_start:
{
uint8_t v_pu_boxed_1948_; lean_object* v_res_1949_; 
v_pu_boxed_1948_ = lean_unbox(v_pu_1942_);
v_res_1949_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(v_fvarId_1938_, v_toPure_1939_, v_k_1940_, v_c_1941_, v_pu_boxed_1948_, v_inst_1943_, v_inst_1944_, v_f_1945_, v_toBind_1946_, v_____do__lift_1947_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(uint8_t v_pu_1950_, lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_f_1953_, lean_object* v_c_1954_){
_start:
{
switch(lean_obj_tag(v_c_1954_))
{
case 0:
{
lean_object* v_toApplicative_1955_; lean_object* v_toBind_1956_; lean_object* v_toPure_1957_; lean_object* v_decl_1958_; lean_object* v_k_1959_; lean_object* v___x_1960_; lean_object* v___f_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v_toApplicative_1955_ = lean_ctor_get(v_inst_1952_, 0);
v_toBind_1956_ = lean_ctor_get(v_inst_1952_, 1);
lean_inc_n(v_toBind_1956_, 2);
v_toPure_1957_ = lean_ctor_get(v_toApplicative_1955_, 1);
v_decl_1958_ = lean_ctor_get(v_c_1954_, 0);
lean_inc_ref_n(v_decl_1958_, 2);
v_k_1959_ = lean_ctor_get(v_c_1954_, 1);
lean_inc_ref(v_k_1959_);
v___x_1960_ = lean_box(v_pu_1950_);
lean_inc(v_f_1953_);
lean_inc_ref(v_inst_1952_);
lean_inc(v_inst_1951_);
lean_inc(v_toPure_1957_);
v___f_1961_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_1961_, 0, v_k_1959_);
lean_closure_set(v___f_1961_, 1, v_toPure_1957_);
lean_closure_set(v___f_1961_, 2, v_decl_1958_);
lean_closure_set(v___f_1961_, 3, v_c_1954_);
lean_closure_set(v___f_1961_, 4, v___x_1960_);
lean_closure_set(v___f_1961_, 5, v_inst_1951_);
lean_closure_set(v___f_1961_, 6, v_inst_1952_);
lean_closure_set(v___f_1961_, 7, v_f_1953_);
lean_closure_set(v___f_1961_, 8, v_toBind_1956_);
v___x_1962_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_1950_, v_inst_1951_, v_inst_1952_, v_f_1953_, v_decl_1958_);
v___x_1963_ = lean_apply_4(v_toBind_1956_, lean_box(0), lean_box(0), v___x_1962_, v___f_1961_);
return v___x_1963_;
}
case 1:
{
lean_object* v_toApplicative_1964_; lean_object* v_decl_1965_; lean_object* v_toBind_1966_; lean_object* v_toPure_1967_; lean_object* v_k_1968_; lean_object* v_params_1969_; lean_object* v_type_1970_; lean_object* v_value_1971_; lean_object* v___x_1972_; lean_object* v___f_1973_; lean_object* v___x_1974_; lean_object* v___f_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; size_t v_sz_1978_; size_t v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v_toApplicative_1964_ = lean_ctor_get(v_inst_1952_, 0);
v_decl_1965_ = lean_ctor_get(v_c_1954_, 0);
lean_inc_ref_n(v_decl_1965_, 2);
v_toBind_1966_ = lean_ctor_get(v_inst_1952_, 1);
lean_inc_n(v_toBind_1966_, 3);
v_toPure_1967_ = lean_ctor_get(v_toApplicative_1964_, 1);
v_k_1968_ = lean_ctor_get(v_c_1954_, 1);
lean_inc_ref(v_k_1968_);
v_params_1969_ = lean_ctor_get(v_decl_1965_, 2);
lean_inc_ref(v_params_1969_);
v_type_1970_ = lean_ctor_get(v_decl_1965_, 3);
lean_inc_ref(v_type_1970_);
v_value_1971_ = lean_ctor_get(v_decl_1965_, 4);
lean_inc_ref(v_value_1971_);
v___x_1972_ = lean_box(v_pu_1950_);
lean_inc_n(v_f_1953_, 2);
lean_inc_ref_n(v_inst_1952_, 3);
lean_inc_n(v_inst_1951_, 2);
lean_inc(v_toPure_1967_);
v___f_1973_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_1973_, 0, v_k_1968_);
lean_closure_set(v___f_1973_, 1, v_toPure_1967_);
lean_closure_set(v___f_1973_, 2, v_decl_1965_);
lean_closure_set(v___f_1973_, 3, v_c_1954_);
lean_closure_set(v___f_1973_, 4, v___x_1972_);
lean_closure_set(v___f_1973_, 5, v_inst_1951_);
lean_closure_set(v___f_1973_, 6, v_inst_1952_);
lean_closure_set(v___f_1973_, 7, v_f_1953_);
lean_closure_set(v___f_1973_, 8, v_toBind_1966_);
v___x_1974_ = lean_box(v_pu_1950_);
v___f_1975_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_1975_, 0, v___x_1974_);
lean_closure_set(v___f_1975_, 1, v_decl_1965_);
lean_closure_set(v___f_1975_, 2, v_inst_1951_);
lean_closure_set(v___f_1975_, 3, v_toBind_1966_);
lean_closure_set(v___f_1975_, 4, v___f_1973_);
lean_closure_set(v___f_1975_, 5, v_inst_1952_);
lean_closure_set(v___f_1975_, 6, v_f_1953_);
lean_closure_set(v___f_1975_, 7, v_value_1971_);
lean_closure_set(v___f_1975_, 8, v_type_1970_);
v___x_1976_ = lean_box(v_pu_1950_);
v___x_1977_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_1977_, 0, lean_box(0));
lean_closure_set(v___x_1977_, 1, v___x_1976_);
lean_closure_set(v___x_1977_, 2, v_inst_1951_);
lean_closure_set(v___x_1977_, 3, v_inst_1952_);
lean_closure_set(v___x_1977_, 4, v_f_1953_);
v_sz_1978_ = lean_array_size(v_params_1969_);
v___x_1979_ = ((size_t)0ULL);
v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1952_, v___x_1977_, v_sz_1978_, v___x_1979_, v_params_1969_);
v___x_1981_ = lean_apply_4(v_toBind_1966_, lean_box(0), lean_box(0), v___x_1980_, v___f_1975_);
return v___x_1981_;
}
case 2:
{
lean_object* v_toApplicative_1982_; lean_object* v_decl_1983_; lean_object* v_toBind_1984_; lean_object* v_toPure_1985_; lean_object* v_k_1986_; lean_object* v_params_1987_; lean_object* v_type_1988_; lean_object* v_value_1989_; lean_object* v___x_1990_; lean_object* v___f_1991_; lean_object* v___x_1992_; lean_object* v___f_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; size_t v_sz_1996_; size_t v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v_toApplicative_1982_ = lean_ctor_get(v_inst_1952_, 0);
v_decl_1983_ = lean_ctor_get(v_c_1954_, 0);
lean_inc_ref_n(v_decl_1983_, 2);
v_toBind_1984_ = lean_ctor_get(v_inst_1952_, 1);
lean_inc_n(v_toBind_1984_, 3);
v_toPure_1985_ = lean_ctor_get(v_toApplicative_1982_, 1);
v_k_1986_ = lean_ctor_get(v_c_1954_, 1);
lean_inc_ref(v_k_1986_);
v_params_1987_ = lean_ctor_get(v_decl_1983_, 2);
lean_inc_ref(v_params_1987_);
v_type_1988_ = lean_ctor_get(v_decl_1983_, 3);
lean_inc_ref(v_type_1988_);
v_value_1989_ = lean_ctor_get(v_decl_1983_, 4);
lean_inc_ref(v_value_1989_);
v___x_1990_ = lean_box(v_pu_1950_);
lean_inc_n(v_f_1953_, 2);
lean_inc_ref_n(v_inst_1952_, 3);
lean_inc_n(v_inst_1951_, 2);
lean_inc(v_toPure_1985_);
v___f_1991_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed), 10, 9);
lean_closure_set(v___f_1991_, 0, v_k_1986_);
lean_closure_set(v___f_1991_, 1, v_toPure_1985_);
lean_closure_set(v___f_1991_, 2, v_decl_1983_);
lean_closure_set(v___f_1991_, 3, v_c_1954_);
lean_closure_set(v___f_1991_, 4, v___x_1990_);
lean_closure_set(v___f_1991_, 5, v_inst_1951_);
lean_closure_set(v___f_1991_, 6, v_inst_1952_);
lean_closure_set(v___f_1991_, 7, v_f_1953_);
lean_closure_set(v___f_1991_, 8, v_toBind_1984_);
v___x_1992_ = lean_box(v_pu_1950_);
v___f_1993_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_1993_, 0, v___x_1992_);
lean_closure_set(v___f_1993_, 1, v_decl_1983_);
lean_closure_set(v___f_1993_, 2, v_inst_1951_);
lean_closure_set(v___f_1993_, 3, v_toBind_1984_);
lean_closure_set(v___f_1993_, 4, v___f_1991_);
lean_closure_set(v___f_1993_, 5, v_inst_1952_);
lean_closure_set(v___f_1993_, 6, v_f_1953_);
lean_closure_set(v___f_1993_, 7, v_value_1989_);
lean_closure_set(v___f_1993_, 8, v_type_1988_);
v___x_1994_ = lean_box(v_pu_1950_);
v___x_1995_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_1995_, 0, lean_box(0));
lean_closure_set(v___x_1995_, 1, v___x_1994_);
lean_closure_set(v___x_1995_, 2, v_inst_1951_);
lean_closure_set(v___x_1995_, 3, v_inst_1952_);
lean_closure_set(v___x_1995_, 4, v_f_1953_);
v_sz_1996_ = lean_array_size(v_params_1987_);
v___x_1997_ = ((size_t)0ULL);
v___x_1998_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1952_, v___x_1995_, v_sz_1996_, v___x_1997_, v_params_1987_);
v___x_1999_ = lean_apply_4(v_toBind_1984_, lean_box(0), lean_box(0), v___x_1998_, v___f_1993_);
return v___x_1999_;
}
case 3:
{
lean_object* v_toApplicative_2000_; lean_object* v_toBind_2001_; lean_object* v_toPure_2002_; lean_object* v_fvarId_2003_; lean_object* v_args_2004_; lean_object* v___x_2005_; lean_object* v___f_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v_toApplicative_2000_ = lean_ctor_get(v_inst_1952_, 0);
v_toBind_2001_ = lean_ctor_get(v_inst_1952_, 1);
lean_inc_n(v_toBind_2001_, 2);
v_toPure_2002_ = lean_ctor_get(v_toApplicative_2000_, 1);
lean_inc(v_toPure_2002_);
v_fvarId_2003_ = lean_ctor_get(v_c_1954_, 0);
lean_inc_n(v_fvarId_2003_, 2);
v_args_2004_ = lean_ctor_get(v_c_1954_, 1);
lean_inc_ref(v_args_2004_);
v___x_2005_ = lean_box(v_pu_1950_);
lean_inc(v_f_1953_);
v___f_2006_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_2006_, 0, v_fvarId_2003_);
lean_closure_set(v___f_2006_, 1, v_toPure_2002_);
lean_closure_set(v___f_2006_, 2, v_args_2004_);
lean_closure_set(v___f_2006_, 3, v_c_1954_);
lean_closure_set(v___f_2006_, 4, v___x_2005_);
lean_closure_set(v___f_2006_, 5, v_inst_1951_);
lean_closure_set(v___f_2006_, 6, v_inst_1952_);
lean_closure_set(v___f_2006_, 7, v_f_1953_);
lean_closure_set(v___f_2006_, 8, v_toBind_2001_);
v___x_2007_ = lean_apply_1(v_f_1953_, v_fvarId_2003_);
v___x_2008_ = lean_apply_4(v_toBind_2001_, lean_box(0), lean_box(0), v___x_2007_, v___f_2006_);
return v___x_2008_;
}
case 4:
{
lean_object* v_toApplicative_2009_; lean_object* v_cases_2010_; lean_object* v_toBind_2011_; lean_object* v_toPure_2012_; lean_object* v_typeName_2013_; lean_object* v_resultType_2014_; lean_object* v_discr_2015_; lean_object* v_alts_2016_; lean_object* v___x_2017_; lean_object* v___f_2018_; lean_object* v___f_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v_toApplicative_2009_ = lean_ctor_get(v_inst_1952_, 0);
v_cases_2010_ = lean_ctor_get(v_c_1954_, 0);
v_toBind_2011_ = lean_ctor_get(v_inst_1952_, 1);
lean_inc_n(v_toBind_2011_, 2);
v_toPure_2012_ = lean_ctor_get(v_toApplicative_2009_, 1);
v_typeName_2013_ = lean_ctor_get(v_cases_2010_, 0);
lean_inc(v_typeName_2013_);
v_resultType_2014_ = lean_ctor_get(v_cases_2010_, 1);
lean_inc_ref_n(v_resultType_2014_, 2);
v_discr_2015_ = lean_ctor_get(v_cases_2010_, 2);
lean_inc(v_discr_2015_);
v_alts_2016_ = lean_ctor_get(v_cases_2010_, 3);
lean_inc_ref(v_alts_2016_);
v___x_2017_ = lean_box(v_pu_1950_);
lean_inc_n(v_f_1953_, 2);
lean_inc_ref_n(v_inst_1952_, 2);
v___f_2018_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed), 5, 4);
lean_closure_set(v___f_2018_, 0, v___x_2017_);
lean_closure_set(v___f_2018_, 1, v_inst_1951_);
lean_closure_set(v___f_2018_, 2, v_inst_1952_);
lean_closure_set(v___f_2018_, 3, v_f_1953_);
lean_inc(v_toPure_2012_);
v___f_2019_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14), 11, 10);
lean_closure_set(v___f_2019_, 0, v_typeName_2013_);
lean_closure_set(v___f_2019_, 1, v_toPure_2012_);
lean_closure_set(v___f_2019_, 2, v_alts_2016_);
lean_closure_set(v___f_2019_, 3, v_resultType_2014_);
lean_closure_set(v___f_2019_, 4, v_discr_2015_);
lean_closure_set(v___f_2019_, 5, v_c_1954_);
lean_closure_set(v___f_2019_, 6, v_inst_1952_);
lean_closure_set(v___f_2019_, 7, v___f_2018_);
lean_closure_set(v___f_2019_, 8, v_toBind_2011_);
lean_closure_set(v___f_2019_, 9, v_f_1953_);
v___x_2020_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1952_, v_f_1953_, v_resultType_2014_);
v___x_2021_ = lean_apply_4(v_toBind_2011_, lean_box(0), lean_box(0), v___x_2020_, v___f_2019_);
return v___x_2021_;
}
case 5:
{
lean_object* v_toApplicative_2022_; lean_object* v_toBind_2023_; lean_object* v_toPure_2024_; lean_object* v_fvarId_2025_; lean_object* v___f_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v_toApplicative_2022_ = lean_ctor_get(v_inst_1952_, 0);
lean_inc_ref(v_toApplicative_2022_);
lean_dec(v_inst_1951_);
v_toBind_2023_ = lean_ctor_get(v_inst_1952_, 1);
lean_inc(v_toBind_2023_);
lean_dec_ref(v_inst_1952_);
v_toPure_2024_ = lean_ctor_get(v_toApplicative_2022_, 1);
lean_inc(v_toPure_2024_);
lean_dec_ref(v_toApplicative_2022_);
v_fvarId_2025_ = lean_ctor_get(v_c_1954_, 0);
lean_inc_n(v_fvarId_2025_, 2);
v___f_2026_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed), 4, 3);
lean_closure_set(v___f_2026_, 0, v_fvarId_2025_);
lean_closure_set(v___f_2026_, 1, v_toPure_2024_);
lean_closure_set(v___f_2026_, 2, v_c_1954_);
v___x_2027_ = lean_apply_1(v_f_1953_, v_fvarId_2025_);
v___x_2028_ = lean_apply_4(v_toBind_2023_, lean_box(0), lean_box(0), v___x_2027_, v___f_2026_);
return v___x_2028_;
}
case 6:
{
lean_object* v_toApplicative_2029_; lean_object* v_toBind_2030_; lean_object* v_toPure_2031_; lean_object* v_type_2032_; lean_object* v___f_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v_toApplicative_2029_ = lean_ctor_get(v_inst_1952_, 0);
lean_dec(v_inst_1951_);
v_toBind_2030_ = lean_ctor_get(v_inst_1952_, 1);
lean_inc(v_toBind_2030_);
v_toPure_2031_ = lean_ctor_get(v_toApplicative_2029_, 1);
v_type_2032_ = lean_ctor_get(v_c_1954_, 0);
lean_inc_ref_n(v_type_2032_, 2);
lean_inc(v_toPure_2031_);
v___f_2033_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed), 4, 3);
lean_closure_set(v___f_2033_, 0, v_type_2032_);
lean_closure_set(v___f_2033_, 1, v_toPure_2031_);
lean_closure_set(v___f_2033_, 2, v_c_1954_);
v___x_2034_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1952_, v_f_1953_, v_type_2032_);
v___x_2035_ = lean_apply_4(v_toBind_2030_, lean_box(0), lean_box(0), v___x_2034_, v___f_2033_);
return v___x_2035_;
}
case 7:
{
lean_object* v_toApplicative_2036_; lean_object* v_toBind_2037_; lean_object* v_toPure_2038_; lean_object* v_fvarId_2039_; lean_object* v_i_2040_; lean_object* v_y_2041_; lean_object* v_k_2042_; lean_object* v___x_2043_; lean_object* v___f_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v_toApplicative_2036_ = lean_ctor_get(v_inst_1952_, 0);
v_toBind_2037_ = lean_ctor_get(v_inst_1952_, 1);
lean_inc_n(v_toBind_2037_, 2);
v_toPure_2038_ = lean_ctor_get(v_toApplicative_2036_, 1);
lean_inc(v_toPure_2038_);
v_fvarId_2039_ = lean_ctor_get(v_c_1954_, 0);
lean_inc_n(v_fvarId_2039_, 2);
v_i_2040_ = lean_ctor_get(v_c_1954_, 1);
lean_inc(v_i_2040_);
v_y_2041_ = lean_ctor_get(v_c_1954_, 2);
lean_inc(v_y_2041_);
v_k_2042_ = lean_ctor_get(v_c_1954_, 3);
lean_inc_ref(v_k_2042_);
v___x_2043_ = lean_box(v_pu_1950_);
lean_inc(v_f_1953_);
v___f_2044_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed), 12, 11);
lean_closure_set(v___f_2044_, 0, v_fvarId_2039_);
lean_closure_set(v___f_2044_, 1, v_i_2040_);
lean_closure_set(v___f_2044_, 2, v_toPure_2038_);
lean_closure_set(v___f_2044_, 3, v_y_2041_);
lean_closure_set(v___f_2044_, 4, v_k_2042_);
lean_closure_set(v___f_2044_, 5, v_c_1954_);
lean_closure_set(v___f_2044_, 6, v___x_2043_);
lean_closure_set(v___f_2044_, 7, v_inst_1951_);
lean_closure_set(v___f_2044_, 8, v_inst_1952_);
lean_closure_set(v___f_2044_, 9, v_f_1953_);
lean_closure_set(v___f_2044_, 10, v_toBind_2037_);
v___x_2045_ = lean_apply_1(v_f_1953_, v_fvarId_2039_);
v___x_2046_ = lean_apply_4(v_toBind_2037_, lean_box(0), lean_box(0), v___x_2045_, v___f_2044_);
return v___x_2046_;
}
case 8:
{
lean_object* v_toApplicative_2047_; lean_object* v_toBind_2048_; lean_object* v_toPure_2049_; lean_object* v_fvarId_2050_; lean_object* v_i_2051_; lean_object* v_y_2052_; lean_object* v_k_2053_; lean_object* v___x_2054_; lean_object* v___f_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v_toApplicative_2047_ = lean_ctor_get(v_inst_1952_, 0);
v_toBind_2048_ = lean_ctor_get(v_inst_1952_, 1);
lean_inc_n(v_toBind_2048_, 2);
v_toPure_2049_ = lean_ctor_get(v_toApplicative_2047_, 1);
lean_inc(v_toPure_2049_);
v_fvarId_2050_ = lean_ctor_get(v_c_1954_, 0);
lean_inc_n(v_fvarId_2050_, 2);
v_i_2051_ = lean_ctor_get(v_c_1954_, 1);
lean_inc(v_i_2051_);
v_y_2052_ = lean_ctor_get(v_c_1954_, 2);
lean_inc(v_y_2052_);
v_k_2053_ = lean_ctor_get(v_c_1954_, 3);
lean_inc_ref(v_k_2053_);
v___x_2054_ = lean_box(v_pu_1950_);
lean_inc(v_f_1953_);
v___f_2055_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed), 12, 11);
lean_closure_set(v___f_2055_, 0, v_fvarId_2050_);
lean_closure_set(v___f_2055_, 1, v_i_2051_);
lean_closure_set(v___f_2055_, 2, v_toPure_2049_);
lean_closure_set(v___f_2055_, 3, v_y_2052_);
lean_closure_set(v___f_2055_, 4, v_k_2053_);
lean_closure_set(v___f_2055_, 5, v_c_1954_);
lean_closure_set(v___f_2055_, 6, v___x_2054_);
lean_closure_set(v___f_2055_, 7, v_inst_1951_);
lean_closure_set(v___f_2055_, 8, v_inst_1952_);
lean_closure_set(v___f_2055_, 9, v_f_1953_);
lean_closure_set(v___f_2055_, 10, v_toBind_2048_);
v___x_2056_ = lean_apply_1(v_f_1953_, v_fvarId_2050_);
v___x_2057_ = lean_apply_4(v_toBind_2048_, lean_box(0), lean_box(0), v___x_2056_, v___f_2055_);
return v___x_2057_;
}
case 9:
{
lean_object* v_toApplicative_2058_; lean_object* v_toBind_2059_; lean_object* v_toPure_2060_; lean_object* v_fvarId_2061_; lean_object* v_i_2062_; lean_object* v_offset_2063_; lean_object* v_y_2064_; lean_object* v_ty_2065_; lean_object* v_k_2066_; lean_object* v___x_2067_; lean_object* v___f_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v_toApplicative_2058_ = lean_ctor_get(v_inst_1952_, 0);
v_toBind_2059_ = lean_ctor_get(v_inst_1952_, 1);
lean_inc_n(v_toBind_2059_, 2);
v_toPure_2060_ = lean_ctor_get(v_toApplicative_2058_, 1);
lean_inc(v_toPure_2060_);
v_fvarId_2061_ = lean_ctor_get(v_c_1954_, 0);
lean_inc_n(v_fvarId_2061_, 2);
v_i_2062_ = lean_ctor_get(v_c_1954_, 1);
lean_inc(v_i_2062_);
v_offset_2063_ = lean_ctor_get(v_c_1954_, 2);
lean_inc(v_offset_2063_);
v_y_2064_ = lean_ctor_get(v_c_1954_, 3);
lean_inc(v_y_2064_);
v_ty_2065_ = lean_ctor_get(v_c_1954_, 4);
lean_inc_ref(v_ty_2065_);
v_k_2066_ = lean_ctor_get(v_c_1954_, 5);
lean_inc_ref(v_k_2066_);
v___x_2067_ = lean_box(v_pu_1950_);
lean_inc(v_f_1953_);
v___f_2068_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed), 14, 13);
lean_closure_set(v___f_2068_, 0, v_fvarId_2061_);
lean_closure_set(v___f_2068_, 1, v_i_2062_);
lean_closure_set(v___f_2068_, 2, v_offset_2063_);
lean_closure_set(v___f_2068_, 3, v_toPure_2060_);
lean_closure_set(v___f_2068_, 4, v_y_2064_);
lean_closure_set(v___f_2068_, 5, v_ty_2065_);
lean_closure_set(v___f_2068_, 6, v_k_2066_);
lean_closure_set(v___f_2068_, 7, v_c_1954_);
lean_closure_set(v___f_2068_, 8, v___x_2067_);
lean_closure_set(v___f_2068_, 9, v_inst_1951_);
lean_closure_set(v___f_2068_, 10, v_inst_1952_);
lean_closure_set(v___f_2068_, 11, v_f_1953_);
lean_closure_set(v___f_2068_, 12, v_toBind_2059_);
v___x_2069_ = lean_apply_1(v_f_1953_, v_fvarId_2061_);
v___x_2070_ = lean_apply_4(v_toBind_2059_, lean_box(0), lean_box(0), v___x_2069_, v___f_2068_);
return v___x_2070_;
}
case 10:
{
lean_object* v_toApplicative_2071_; lean_object* v_toBind_2072_; lean_object* v_toPure_2073_; lean_object* v_fvarId_2074_; lean_object* v_cidx_2075_; lean_object* v_k_2076_; lean_object* v___x_2077_; lean_object* v___f_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v_toApplicative_2071_ = lean_ctor_get(v_inst_1952_, 0);
v_toBind_2072_ = lean_ctor_get(v_inst_1952_, 1);
lean_inc_n(v_toBind_2072_, 2);
v_toPure_2073_ = lean_ctor_get(v_toApplicative_2071_, 1);
lean_inc(v_toPure_2073_);
v_fvarId_2074_ = lean_ctor_get(v_c_1954_, 0);
lean_inc_n(v_fvarId_2074_, 2);
v_cidx_2075_ = lean_ctor_get(v_c_1954_, 1);
lean_inc(v_cidx_2075_);
v_k_2076_ = lean_ctor_get(v_c_1954_, 2);
lean_inc_ref(v_k_2076_);
v___x_2077_ = lean_box(v_pu_1950_);
lean_inc(v_f_1953_);
v___f_2078_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed), 11, 10);
lean_closure_set(v___f_2078_, 0, v_fvarId_2074_);
lean_closure_set(v___f_2078_, 1, v_cidx_2075_);
lean_closure_set(v___f_2078_, 2, v_toPure_2073_);
lean_closure_set(v___f_2078_, 3, v_k_2076_);
lean_closure_set(v___f_2078_, 4, v_c_1954_);
lean_closure_set(v___f_2078_, 5, v___x_2077_);
lean_closure_set(v___f_2078_, 6, v_inst_1951_);
lean_closure_set(v___f_2078_, 7, v_inst_1952_);
lean_closure_set(v___f_2078_, 8, v_f_1953_);
lean_closure_set(v___f_2078_, 9, v_toBind_2072_);
v___x_2079_ = lean_apply_1(v_f_1953_, v_fvarId_2074_);
v___x_2080_ = lean_apply_4(v_toBind_2072_, lean_box(0), lean_box(0), v___x_2079_, v___f_2078_);
return v___x_2080_;
}
case 11:
{
lean_object* v_toApplicative_2081_; lean_object* v_toBind_2082_; lean_object* v_toPure_2083_; lean_object* v_fvarId_2084_; lean_object* v_n_2085_; uint8_t v_check_2086_; uint8_t v_persistent_2087_; lean_object* v_k_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___f_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_toApplicative_2081_ = lean_ctor_get(v_inst_1952_, 0);
v_toBind_2082_ = lean_ctor_get(v_inst_1952_, 1);
lean_inc_n(v_toBind_2082_, 2);
v_toPure_2083_ = lean_ctor_get(v_toApplicative_2081_, 1);
lean_inc(v_toPure_2083_);
v_fvarId_2084_ = lean_ctor_get(v_c_1954_, 0);
lean_inc_n(v_fvarId_2084_, 2);
v_n_2085_ = lean_ctor_get(v_c_1954_, 1);
lean_inc(v_n_2085_);
v_check_2086_ = lean_ctor_get_uint8(v_c_1954_, sizeof(void*)*3);
v_persistent_2087_ = lean_ctor_get_uint8(v_c_1954_, sizeof(void*)*3 + 1);
v_k_2088_ = lean_ctor_get(v_c_1954_, 2);
lean_inc_ref(v_k_2088_);
v___x_2089_ = lean_box(v_check_2086_);
v___x_2090_ = lean_box(v_persistent_2087_);
v___x_2091_ = lean_box(v_pu_1950_);
lean_inc(v_f_1953_);
v___f_2092_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed), 13, 12);
lean_closure_set(v___f_2092_, 0, v_fvarId_2084_);
lean_closure_set(v___f_2092_, 1, v_n_2085_);
lean_closure_set(v___f_2092_, 2, v___x_2089_);
lean_closure_set(v___f_2092_, 3, v___x_2090_);
lean_closure_set(v___f_2092_, 4, v_toPure_2083_);
lean_closure_set(v___f_2092_, 5, v_k_2088_);
lean_closure_set(v___f_2092_, 6, v_c_1954_);
lean_closure_set(v___f_2092_, 7, v___x_2091_);
lean_closure_set(v___f_2092_, 8, v_inst_1951_);
lean_closure_set(v___f_2092_, 9, v_inst_1952_);
lean_closure_set(v___f_2092_, 10, v_f_1953_);
lean_closure_set(v___f_2092_, 11, v_toBind_2082_);
v___x_2093_ = lean_apply_1(v_f_1953_, v_fvarId_2084_);
v___x_2094_ = lean_apply_4(v_toBind_2082_, lean_box(0), lean_box(0), v___x_2093_, v___f_2092_);
return v___x_2094_;
}
case 12:
{
lean_object* v_toApplicative_2095_; lean_object* v_toBind_2096_; lean_object* v_toPure_2097_; lean_object* v_fvarId_2098_; lean_object* v_n_2099_; uint8_t v_check_2100_; uint8_t v_persistent_2101_; lean_object* v_objs_x3f_2102_; lean_object* v_k_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___f_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v_toApplicative_2095_ = lean_ctor_get(v_inst_1952_, 0);
v_toBind_2096_ = lean_ctor_get(v_inst_1952_, 1);
lean_inc_n(v_toBind_2096_, 2);
v_toPure_2097_ = lean_ctor_get(v_toApplicative_2095_, 1);
lean_inc(v_toPure_2097_);
v_fvarId_2098_ = lean_ctor_get(v_c_1954_, 0);
lean_inc_n(v_fvarId_2098_, 2);
v_n_2099_ = lean_ctor_get(v_c_1954_, 1);
lean_inc(v_n_2099_);
v_check_2100_ = lean_ctor_get_uint8(v_c_1954_, sizeof(void*)*4);
v_persistent_2101_ = lean_ctor_get_uint8(v_c_1954_, sizeof(void*)*4 + 1);
v_objs_x3f_2102_ = lean_ctor_get(v_c_1954_, 2);
lean_inc(v_objs_x3f_2102_);
v_k_2103_ = lean_ctor_get(v_c_1954_, 3);
lean_inc_ref(v_k_2103_);
v___x_2104_ = lean_box(v_check_2100_);
v___x_2105_ = lean_box(v_persistent_2101_);
v___x_2106_ = lean_box(v_pu_1950_);
lean_inc(v_f_1953_);
v___f_2107_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed), 14, 13);
lean_closure_set(v___f_2107_, 0, v_fvarId_2098_);
lean_closure_set(v___f_2107_, 1, v_n_2099_);
lean_closure_set(v___f_2107_, 2, v___x_2104_);
lean_closure_set(v___f_2107_, 3, v___x_2105_);
lean_closure_set(v___f_2107_, 4, v_objs_x3f_2102_);
lean_closure_set(v___f_2107_, 5, v_toPure_2097_);
lean_closure_set(v___f_2107_, 6, v_k_2103_);
lean_closure_set(v___f_2107_, 7, v_c_1954_);
lean_closure_set(v___f_2107_, 8, v___x_2106_);
lean_closure_set(v___f_2107_, 9, v_inst_1951_);
lean_closure_set(v___f_2107_, 10, v_inst_1952_);
lean_closure_set(v___f_2107_, 11, v_f_1953_);
lean_closure_set(v___f_2107_, 12, v_toBind_2096_);
v___x_2108_ = lean_apply_1(v_f_1953_, v_fvarId_2098_);
v___x_2109_ = lean_apply_4(v_toBind_2096_, lean_box(0), lean_box(0), v___x_2108_, v___f_2107_);
return v___x_2109_;
}
default: 
{
lean_object* v_toApplicative_2110_; lean_object* v_toBind_2111_; lean_object* v_toPure_2112_; lean_object* v_fvarId_2113_; lean_object* v_k_2114_; lean_object* v___x_2115_; lean_object* v___f_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_toApplicative_2110_ = lean_ctor_get(v_inst_1952_, 0);
v_toBind_2111_ = lean_ctor_get(v_inst_1952_, 1);
lean_inc_n(v_toBind_2111_, 2);
v_toPure_2112_ = lean_ctor_get(v_toApplicative_2110_, 1);
lean_inc(v_toPure_2112_);
v_fvarId_2113_ = lean_ctor_get(v_c_1954_, 0);
lean_inc_n(v_fvarId_2113_, 2);
v_k_2114_ = lean_ctor_get(v_c_1954_, 1);
lean_inc_ref(v_k_2114_);
v___x_2115_ = lean_box(v_pu_1950_);
lean_inc(v_f_1953_);
v___f_2116_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed), 10, 9);
lean_closure_set(v___f_2116_, 0, v_fvarId_2113_);
lean_closure_set(v___f_2116_, 1, v_toPure_2112_);
lean_closure_set(v___f_2116_, 2, v_k_2114_);
lean_closure_set(v___f_2116_, 3, v_c_1954_);
lean_closure_set(v___f_2116_, 4, v___x_2115_);
lean_closure_set(v___f_2116_, 5, v_inst_1951_);
lean_closure_set(v___f_2116_, 6, v_inst_1952_);
lean_closure_set(v___f_2116_, 7, v_f_1953_);
lean_closure_set(v___f_2116_, 8, v_toBind_2111_);
v___x_2117_ = lean_apply_1(v_f_1953_, v_fvarId_2113_);
v___x_2118_ = lean_apply_4(v_toBind_2111_, lean_box(0), lean_box(0), v___x_2117_, v___f_2116_);
return v___x_2118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed(lean_object* v_pu_2119_, lean_object* v_inst_2120_, lean_object* v_inst_2121_, lean_object* v_f_2122_, lean_object* v_c_2123_){
_start:
{
uint8_t v_pu_boxed_2124_; lean_object* v_res_2125_; 
v_pu_boxed_2124_ = lean_unbox(v_pu_2119_);
v_res_2125_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_boxed_2124_, v_inst_2120_, v_inst_2121_, v_f_2122_, v_c_2123_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(uint8_t v_pu_2126_, lean_object* v_inst_2127_, lean_object* v_inst_2128_, lean_object* v_f_2129_, lean_object* v_x_2130_){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2131_ = lean_box(v_pu_2126_);
lean_inc_ref(v_inst_2128_);
v___x_2132_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed), 5, 4);
lean_closure_set(v___x_2132_, 0, v___x_2131_);
lean_closure_set(v___x_2132_, 1, v_inst_2127_);
lean_closure_set(v___x_2132_, 2, v_inst_2128_);
lean_closure_set(v___x_2132_, 3, v_f_2129_);
v___x_2133_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg(v_inst_2128_, v_x_2130_, v___x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM(lean_object* v_m_2134_, uint8_t v_pu_2135_, lean_object* v_inst_2136_, lean_object* v_inst_2137_, lean_object* v_f_2138_, lean_object* v_c_2139_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2135_, v_inst_2136_, v_inst_2137_, v_f_2138_, v_c_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___boxed(lean_object* v_m_2141_, lean_object* v_pu_2142_, lean_object* v_inst_2143_, lean_object* v_inst_2144_, lean_object* v_f_2145_, lean_object* v_c_2146_){
_start:
{
uint8_t v_pu_boxed_2147_; lean_object* v_res_2148_; 
v_pu_boxed_2147_ = lean_unbox(v_pu_2142_);
v_res_2148_ = l_Lean_Compiler_LCNF_Code_mapFVarM(v_m_2141_, v_pu_boxed_2147_, v_inst_2143_, v_inst_2144_, v_f_2145_, v_c_2146_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1(lean_object* v_inst_2149_, lean_object* v_f_2150_, lean_object* v_type_2151_, lean_object* v_toBind_2152_, lean_object* v___f_2153_, lean_object* v_____r_2154_){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2149_, v_f_2150_, v_type_2151_);
v___x_2156_ = lean_apply_4(v_toBind_2152_, lean_box(0), lean_box(0), v___x_2155_, v___f_2153_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12(lean_object* v_inst_2157_, lean_object* v_f_2158_, lean_object* v_ty_2159_, lean_object* v_toBind_2160_, lean_object* v___f_2161_, lean_object* v_____r_2162_){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2157_, v_f_2158_, v_ty_2159_);
v___x_2164_ = lean_apply_4(v_toBind_2160_, lean_box(0), lean_box(0), v___x_2163_, v___f_2161_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4(lean_object* v_toApplicative_2165_, lean_object* v_args_2166_, lean_object* v_inst_2167_, lean_object* v___f_2168_, lean_object* v_____r_2169_){
_start:
{
lean_object* v_toPure_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
v_toPure_2170_ = lean_ctor_get(v_toApplicative_2165_, 1);
lean_inc(v_toPure_2170_);
lean_dec_ref(v_toApplicative_2165_);
v___x_2171_ = lean_unsigned_to_nat(0u);
v___x_2172_ = lean_array_get_size(v_args_2166_);
v___x_2173_ = lean_box(0);
v___x_2174_ = lean_nat_dec_lt(v___x_2171_, v___x_2172_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; 
lean_dec(v___f_2168_);
lean_dec_ref(v_inst_2167_);
lean_dec_ref(v_args_2166_);
v___x_2175_ = lean_apply_2(v_toPure_2170_, lean_box(0), v___x_2173_);
return v___x_2175_;
}
else
{
size_t v___x_2176_; size_t v___x_2177_; lean_object* v___x_2178_; 
lean_dec(v_toPure_2170_);
v___x_2176_ = ((size_t)0ULL);
v___x_2177_ = lean_usize_of_nat(v___x_2172_);
v___x_2178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2167_, v___f_2168_, v_args_2166_, v___x_2176_, v___x_2177_, v___x_2173_);
return v___x_2178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3(lean_object* v_inst_2179_, lean_object* v_f_2180_, lean_object* v_x_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_2179_, v_f_2180_, v___y_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10(lean_object* v_inst_2184_, lean_object* v_f_2185_, lean_object* v_y_2186_, lean_object* v_toBind_2187_, lean_object* v___f_2188_, lean_object* v_____r_2189_){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2184_, v_f_2185_, v_y_2186_);
v___x_2191_ = lean_apply_4(v_toBind_2187_, lean_box(0), lean_box(0), v___x_2190_, v___f_2188_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11(lean_object* v_f_2192_, lean_object* v_y_2193_, lean_object* v_toBind_2194_, lean_object* v___f_2195_, lean_object* v_____r_2196_){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = lean_apply_1(v_f_2192_, v_y_2193_);
v___x_2198_ = lean_apply_4(v_toBind_2194_, lean_box(0), lean_box(0), v___x_2197_, v___f_2195_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7(lean_object* v_f_2199_, lean_object* v_discr_2200_, lean_object* v_toBind_2201_, lean_object* v___f_2202_, lean_object* v_____r_2203_){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = lean_apply_1(v_f_2199_, v_discr_2200_);
v___x_2205_ = lean_apply_4(v_toBind_2201_, lean_box(0), lean_box(0), v___x_2204_, v___f_2202_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6(lean_object* v_toApplicative_2206_, lean_object* v_alts_2207_, lean_object* v_inst_2208_, lean_object* v___f_2209_, lean_object* v_____r_2210_){
_start:
{
lean_object* v_toPure_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; 
v_toPure_2211_ = lean_ctor_get(v_toApplicative_2206_, 1);
lean_inc(v_toPure_2211_);
lean_dec_ref(v_toApplicative_2206_);
v___x_2212_ = lean_unsigned_to_nat(0u);
v___x_2213_ = lean_array_get_size(v_alts_2207_);
v___x_2214_ = lean_box(0);
v___x_2215_ = lean_nat_dec_lt(v___x_2212_, v___x_2213_);
if (v___x_2215_ == 0)
{
lean_object* v___x_2216_; 
lean_dec(v___f_2209_);
lean_dec_ref(v_inst_2208_);
lean_dec_ref(v_alts_2207_);
v___x_2216_ = lean_apply_2(v_toPure_2211_, lean_box(0), v___x_2214_);
return v___x_2216_;
}
else
{
size_t v___x_2217_; size_t v___x_2218_; lean_object* v___x_2219_; 
lean_dec(v_toPure_2211_);
v___x_2217_ = ((size_t)0ULL);
v___x_2218_ = lean_usize_of_nat(v___x_2213_);
v___x_2219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2208_, v___f_2209_, v_alts_2207_, v___x_2217_, v___x_2218_, v___x_2214_);
return v___x_2219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8(lean_object* v_inst_2220_, lean_object* v_f_2221_, lean_object* v_x_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2220_, v_f_2221_, v___y_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5(lean_object* v_inst_2225_, lean_object* v_f_2226_, lean_object* v_x_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg), 3, 2);
lean_closure_set(v___x_2229_, 0, v_inst_2225_);
lean_closure_set(v___x_2229_, 1, v_f_2226_);
v___x_2230_ = l_Lean_Compiler_LCNF_Alt_forCodeM___redArg(v___y_2228_, v___x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2(lean_object* v_inst_2231_, lean_object* v_f_2232_, lean_object* v_value_2233_, lean_object* v_toBind_2234_, lean_object* v___f_2235_, lean_object* v_____r_2236_){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2231_, v_f_2232_, v_value_2233_);
v___x_2238_ = lean_apply_4(v_toBind_2234_, lean_box(0), lean_box(0), v___x_2237_, v___f_2235_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg(lean_object* v_inst_2239_, lean_object* v_f_2240_, lean_object* v_c_2241_){
_start:
{
switch(lean_obj_tag(v_c_2241_))
{
case 0:
{
lean_object* v_toBind_2242_; lean_object* v_decl_2243_; lean_object* v_k_2244_; lean_object* v___f_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v_toBind_2242_ = lean_ctor_get(v_inst_2239_, 1);
lean_inc(v_toBind_2242_);
v_decl_2243_ = lean_ctor_get(v_c_2241_, 0);
lean_inc_ref(v_decl_2243_);
v_k_2244_ = lean_ctor_get(v_c_2241_, 1);
lean_inc_ref(v_k_2244_);
lean_dec_ref_known(v_c_2241_, 2);
lean_inc(v_f_2240_);
lean_inc_ref(v_inst_2239_);
v___f_2245_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2245_, 0, v_inst_2239_);
lean_closure_set(v___f_2245_, 1, v_f_2240_);
lean_closure_set(v___f_2245_, 2, v_k_2244_);
v___x_2246_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_2239_, v_f_2240_, v_decl_2243_);
v___x_2247_ = lean_apply_4(v_toBind_2242_, lean_box(0), lean_box(0), v___x_2246_, v___f_2245_);
return v___x_2247_;
}
case 3:
{
lean_object* v_toApplicative_2248_; lean_object* v_toBind_2249_; lean_object* v_fvarId_2250_; lean_object* v_args_2251_; lean_object* v___f_2252_; lean_object* v___f_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_toApplicative_2248_ = lean_ctor_get(v_inst_2239_, 0);
lean_inc_ref(v_toApplicative_2248_);
v_toBind_2249_ = lean_ctor_get(v_inst_2239_, 1);
lean_inc(v_toBind_2249_);
v_fvarId_2250_ = lean_ctor_get(v_c_2241_, 0);
lean_inc(v_fvarId_2250_);
v_args_2251_ = lean_ctor_get(v_c_2241_, 1);
lean_inc_ref(v_args_2251_);
lean_dec_ref_known(v_c_2241_, 2);
lean_inc(v_f_2240_);
lean_inc_ref(v_inst_2239_);
v___f_2252_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8), 4, 2);
lean_closure_set(v___f_2252_, 0, v_inst_2239_);
lean_closure_set(v___f_2252_, 1, v_f_2240_);
v___f_2253_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2253_, 0, v_toApplicative_2248_);
lean_closure_set(v___f_2253_, 1, v_args_2251_);
lean_closure_set(v___f_2253_, 2, v_inst_2239_);
lean_closure_set(v___f_2253_, 3, v___f_2252_);
v___x_2254_ = lean_apply_1(v_f_2240_, v_fvarId_2250_);
v___x_2255_ = lean_apply_4(v_toBind_2249_, lean_box(0), lean_box(0), v___x_2254_, v___f_2253_);
return v___x_2255_;
}
case 4:
{
lean_object* v_cases_2256_; lean_object* v_toApplicative_2257_; lean_object* v_toBind_2258_; lean_object* v_resultType_2259_; lean_object* v_discr_2260_; lean_object* v_alts_2261_; lean_object* v___f_2262_; lean_object* v___f_2263_; lean_object* v___f_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v_cases_2256_ = lean_ctor_get(v_c_2241_, 0);
lean_inc_ref(v_cases_2256_);
lean_dec_ref_known(v_c_2241_, 1);
v_toApplicative_2257_ = lean_ctor_get(v_inst_2239_, 0);
v_toBind_2258_ = lean_ctor_get(v_inst_2239_, 1);
lean_inc_n(v_toBind_2258_, 2);
v_resultType_2259_ = lean_ctor_get(v_cases_2256_, 1);
lean_inc_ref(v_resultType_2259_);
v_discr_2260_ = lean_ctor_get(v_cases_2256_, 2);
lean_inc(v_discr_2260_);
v_alts_2261_ = lean_ctor_get(v_cases_2256_, 3);
lean_inc_ref(v_alts_2261_);
lean_dec_ref(v_cases_2256_);
lean_inc_n(v_f_2240_, 2);
lean_inc_ref_n(v_inst_2239_, 2);
v___f_2262_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5), 4, 2);
lean_closure_set(v___f_2262_, 0, v_inst_2239_);
lean_closure_set(v___f_2262_, 1, v_f_2240_);
lean_inc_ref(v_toApplicative_2257_);
v___f_2263_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6), 5, 4);
lean_closure_set(v___f_2263_, 0, v_toApplicative_2257_);
lean_closure_set(v___f_2263_, 1, v_alts_2261_);
lean_closure_set(v___f_2263_, 2, v_inst_2239_);
lean_closure_set(v___f_2263_, 3, v___f_2262_);
v___f_2264_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7), 5, 4);
lean_closure_set(v___f_2264_, 0, v_f_2240_);
lean_closure_set(v___f_2264_, 1, v_discr_2260_);
lean_closure_set(v___f_2264_, 2, v_toBind_2258_);
lean_closure_set(v___f_2264_, 3, v___f_2263_);
v___x_2265_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2239_, v_f_2240_, v_resultType_2259_);
v___x_2266_ = lean_apply_4(v_toBind_2258_, lean_box(0), lean_box(0), v___x_2265_, v___f_2264_);
return v___x_2266_;
}
case 5:
{
lean_object* v_fvarId_2267_; lean_object* v___x_2268_; 
lean_dec_ref(v_inst_2239_);
v_fvarId_2267_ = lean_ctor_get(v_c_2241_, 0);
lean_inc(v_fvarId_2267_);
lean_dec_ref_known(v_c_2241_, 1);
v___x_2268_ = lean_apply_1(v_f_2240_, v_fvarId_2267_);
return v___x_2268_;
}
case 6:
{
lean_object* v_type_2269_; lean_object* v___x_2270_; 
v_type_2269_ = lean_ctor_get(v_c_2241_, 0);
lean_inc_ref(v_type_2269_);
lean_dec_ref_known(v_c_2241_, 1);
v___x_2270_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2239_, v_f_2240_, v_type_2269_);
return v___x_2270_;
}
case 7:
{
lean_object* v_toBind_2271_; lean_object* v_fvarId_2272_; lean_object* v_y_2273_; lean_object* v_k_2274_; lean_object* v___f_2275_; lean_object* v___f_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v_toBind_2271_ = lean_ctor_get(v_inst_2239_, 1);
lean_inc_n(v_toBind_2271_, 2);
v_fvarId_2272_ = lean_ctor_get(v_c_2241_, 0);
lean_inc(v_fvarId_2272_);
v_y_2273_ = lean_ctor_get(v_c_2241_, 2);
lean_inc(v_y_2273_);
v_k_2274_ = lean_ctor_get(v_c_2241_, 3);
lean_inc_ref(v_k_2274_);
lean_dec_ref_known(v_c_2241_, 4);
lean_inc_n(v_f_2240_, 2);
lean_inc_ref(v_inst_2239_);
v___f_2275_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2275_, 0, v_inst_2239_);
lean_closure_set(v___f_2275_, 1, v_f_2240_);
lean_closure_set(v___f_2275_, 2, v_k_2274_);
v___f_2276_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10), 6, 5);
lean_closure_set(v___f_2276_, 0, v_inst_2239_);
lean_closure_set(v___f_2276_, 1, v_f_2240_);
lean_closure_set(v___f_2276_, 2, v_y_2273_);
lean_closure_set(v___f_2276_, 3, v_toBind_2271_);
lean_closure_set(v___f_2276_, 4, v___f_2275_);
v___x_2277_ = lean_apply_1(v_f_2240_, v_fvarId_2272_);
v___x_2278_ = lean_apply_4(v_toBind_2271_, lean_box(0), lean_box(0), v___x_2277_, v___f_2276_);
return v___x_2278_;
}
case 8:
{
lean_object* v_toBind_2279_; lean_object* v_fvarId_2280_; lean_object* v_y_2281_; lean_object* v_k_2282_; lean_object* v___f_2283_; lean_object* v___f_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_toBind_2279_ = lean_ctor_get(v_inst_2239_, 1);
lean_inc_n(v_toBind_2279_, 2);
v_fvarId_2280_ = lean_ctor_get(v_c_2241_, 0);
lean_inc(v_fvarId_2280_);
v_y_2281_ = lean_ctor_get(v_c_2241_, 2);
lean_inc(v_y_2281_);
v_k_2282_ = lean_ctor_get(v_c_2241_, 3);
lean_inc_ref(v_k_2282_);
lean_dec_ref_known(v_c_2241_, 4);
lean_inc_n(v_f_2240_, 2);
v___f_2283_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2283_, 0, v_inst_2239_);
lean_closure_set(v___f_2283_, 1, v_f_2240_);
lean_closure_set(v___f_2283_, 2, v_k_2282_);
v___f_2284_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11), 5, 4);
lean_closure_set(v___f_2284_, 0, v_f_2240_);
lean_closure_set(v___f_2284_, 1, v_y_2281_);
lean_closure_set(v___f_2284_, 2, v_toBind_2279_);
lean_closure_set(v___f_2284_, 3, v___f_2283_);
v___x_2285_ = lean_apply_1(v_f_2240_, v_fvarId_2280_);
v___x_2286_ = lean_apply_4(v_toBind_2279_, lean_box(0), lean_box(0), v___x_2285_, v___f_2284_);
return v___x_2286_;
}
case 9:
{
lean_object* v_toBind_2287_; lean_object* v_fvarId_2288_; lean_object* v_y_2289_; lean_object* v_ty_2290_; lean_object* v_k_2291_; lean_object* v___f_2292_; lean_object* v___f_2293_; lean_object* v___f_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v_toBind_2287_ = lean_ctor_get(v_inst_2239_, 1);
lean_inc_n(v_toBind_2287_, 3);
v_fvarId_2288_ = lean_ctor_get(v_c_2241_, 0);
lean_inc(v_fvarId_2288_);
v_y_2289_ = lean_ctor_get(v_c_2241_, 3);
lean_inc(v_y_2289_);
v_ty_2290_ = lean_ctor_get(v_c_2241_, 4);
lean_inc_ref(v_ty_2290_);
v_k_2291_ = lean_ctor_get(v_c_2241_, 5);
lean_inc_ref(v_k_2291_);
lean_dec_ref_known(v_c_2241_, 6);
lean_inc_n(v_f_2240_, 3);
lean_inc_ref(v_inst_2239_);
v___f_2292_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2292_, 0, v_inst_2239_);
lean_closure_set(v___f_2292_, 1, v_f_2240_);
lean_closure_set(v___f_2292_, 2, v_k_2291_);
v___f_2293_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12), 6, 5);
lean_closure_set(v___f_2293_, 0, v_inst_2239_);
lean_closure_set(v___f_2293_, 1, v_f_2240_);
lean_closure_set(v___f_2293_, 2, v_ty_2290_);
lean_closure_set(v___f_2293_, 3, v_toBind_2287_);
lean_closure_set(v___f_2293_, 4, v___f_2292_);
v___f_2294_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11), 5, 4);
lean_closure_set(v___f_2294_, 0, v_f_2240_);
lean_closure_set(v___f_2294_, 1, v_y_2289_);
lean_closure_set(v___f_2294_, 2, v_toBind_2287_);
lean_closure_set(v___f_2294_, 3, v___f_2293_);
v___x_2295_ = lean_apply_1(v_f_2240_, v_fvarId_2288_);
v___x_2296_ = lean_apply_4(v_toBind_2287_, lean_box(0), lean_box(0), v___x_2295_, v___f_2294_);
return v___x_2296_;
}
case 10:
{
lean_object* v_toBind_2297_; lean_object* v_fvarId_2298_; lean_object* v_k_2299_; lean_object* v___f_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v_toBind_2297_ = lean_ctor_get(v_inst_2239_, 1);
lean_inc(v_toBind_2297_);
v_fvarId_2298_ = lean_ctor_get(v_c_2241_, 0);
lean_inc(v_fvarId_2298_);
v_k_2299_ = lean_ctor_get(v_c_2241_, 2);
lean_inc_ref(v_k_2299_);
lean_dec_ref_known(v_c_2241_, 3);
lean_inc(v_f_2240_);
v___f_2300_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2300_, 0, v_inst_2239_);
lean_closure_set(v___f_2300_, 1, v_f_2240_);
lean_closure_set(v___f_2300_, 2, v_k_2299_);
v___x_2301_ = lean_apply_1(v_f_2240_, v_fvarId_2298_);
v___x_2302_ = lean_apply_4(v_toBind_2297_, lean_box(0), lean_box(0), v___x_2301_, v___f_2300_);
return v___x_2302_;
}
case 11:
{
lean_object* v_toBind_2303_; lean_object* v_fvarId_2304_; lean_object* v_k_2305_; lean_object* v___f_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_toBind_2303_ = lean_ctor_get(v_inst_2239_, 1);
lean_inc(v_toBind_2303_);
v_fvarId_2304_ = lean_ctor_get(v_c_2241_, 0);
lean_inc(v_fvarId_2304_);
v_k_2305_ = lean_ctor_get(v_c_2241_, 2);
lean_inc_ref(v_k_2305_);
lean_dec_ref_known(v_c_2241_, 3);
lean_inc(v_f_2240_);
v___f_2306_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2306_, 0, v_inst_2239_);
lean_closure_set(v___f_2306_, 1, v_f_2240_);
lean_closure_set(v___f_2306_, 2, v_k_2305_);
v___x_2307_ = lean_apply_1(v_f_2240_, v_fvarId_2304_);
v___x_2308_ = lean_apply_4(v_toBind_2303_, lean_box(0), lean_box(0), v___x_2307_, v___f_2306_);
return v___x_2308_;
}
case 12:
{
lean_object* v_toBind_2309_; lean_object* v_fvarId_2310_; lean_object* v_k_2311_; lean_object* v___f_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_toBind_2309_ = lean_ctor_get(v_inst_2239_, 1);
lean_inc(v_toBind_2309_);
v_fvarId_2310_ = lean_ctor_get(v_c_2241_, 0);
lean_inc(v_fvarId_2310_);
v_k_2311_ = lean_ctor_get(v_c_2241_, 3);
lean_inc_ref(v_k_2311_);
lean_dec_ref_known(v_c_2241_, 4);
lean_inc(v_f_2240_);
v___f_2312_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2312_, 0, v_inst_2239_);
lean_closure_set(v___f_2312_, 1, v_f_2240_);
lean_closure_set(v___f_2312_, 2, v_k_2311_);
v___x_2313_ = lean_apply_1(v_f_2240_, v_fvarId_2310_);
v___x_2314_ = lean_apply_4(v_toBind_2309_, lean_box(0), lean_box(0), v___x_2313_, v___f_2312_);
return v___x_2314_;
}
case 13:
{
lean_object* v_toBind_2315_; lean_object* v_fvarId_2316_; lean_object* v_k_2317_; lean_object* v___f_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v_toBind_2315_ = lean_ctor_get(v_inst_2239_, 1);
lean_inc(v_toBind_2315_);
v_fvarId_2316_ = lean_ctor_get(v_c_2241_, 0);
lean_inc(v_fvarId_2316_);
v_k_2317_ = lean_ctor_get(v_c_2241_, 1);
lean_inc_ref(v_k_2317_);
lean_dec_ref_known(v_c_2241_, 2);
lean_inc(v_f_2240_);
v___f_2318_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2318_, 0, v_inst_2239_);
lean_closure_set(v___f_2318_, 1, v_f_2240_);
lean_closure_set(v___f_2318_, 2, v_k_2317_);
v___x_2319_ = lean_apply_1(v_f_2240_, v_fvarId_2316_);
v___x_2320_ = lean_apply_4(v_toBind_2315_, lean_box(0), lean_box(0), v___x_2319_, v___f_2318_);
return v___x_2320_;
}
default: 
{
lean_object* v_decl_2321_; lean_object* v_toApplicative_2322_; lean_object* v_toBind_2323_; lean_object* v_k_2324_; lean_object* v_params_2325_; lean_object* v_type_2326_; lean_object* v_value_2327_; lean_object* v_toPure_2328_; lean_object* v___f_2329_; lean_object* v___f_2330_; lean_object* v___f_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v_decl_2321_ = lean_ctor_get(v_c_2241_, 0);
lean_inc_ref(v_decl_2321_);
v_toApplicative_2322_ = lean_ctor_get(v_inst_2239_, 0);
v_toBind_2323_ = lean_ctor_get(v_inst_2239_, 1);
lean_inc_n(v_toBind_2323_, 3);
v_k_2324_ = lean_ctor_get(v_c_2241_, 1);
lean_inc_ref(v_k_2324_);
lean_dec_ref(v_c_2241_);
v_params_2325_ = lean_ctor_get(v_decl_2321_, 2);
lean_inc_ref(v_params_2325_);
v_type_2326_ = lean_ctor_get(v_decl_2321_, 3);
lean_inc_ref(v_type_2326_);
v_value_2327_ = lean_ctor_get(v_decl_2321_, 4);
lean_inc_ref(v_value_2327_);
lean_dec_ref(v_decl_2321_);
v_toPure_2328_ = lean_ctor_get(v_toApplicative_2322_, 1);
lean_inc_n(v_f_2240_, 3);
lean_inc_ref_n(v_inst_2239_, 3);
v___f_2329_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2329_, 0, v_inst_2239_);
lean_closure_set(v___f_2329_, 1, v_f_2240_);
lean_closure_set(v___f_2329_, 2, v_k_2324_);
v___f_2330_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2330_, 0, v_inst_2239_);
lean_closure_set(v___f_2330_, 1, v_f_2240_);
lean_closure_set(v___f_2330_, 2, v_value_2327_);
lean_closure_set(v___f_2330_, 3, v_toBind_2323_);
lean_closure_set(v___f_2330_, 4, v___f_2329_);
v___f_2331_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2331_, 0, v_inst_2239_);
lean_closure_set(v___f_2331_, 1, v_f_2240_);
lean_closure_set(v___f_2331_, 2, v_type_2326_);
lean_closure_set(v___f_2331_, 3, v_toBind_2323_);
lean_closure_set(v___f_2331_, 4, v___f_2330_);
v___x_2332_ = lean_unsigned_to_nat(0u);
v___x_2333_ = lean_array_get_size(v_params_2325_);
v___x_2334_ = lean_box(0);
v___x_2335_ = lean_nat_dec_lt(v___x_2332_, v___x_2333_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_inc(v_toPure_2328_);
lean_dec_ref(v_params_2325_);
lean_dec(v_f_2240_);
lean_dec_ref(v_inst_2239_);
v___x_2336_ = lean_apply_2(v_toPure_2328_, lean_box(0), v___x_2334_);
v___x_2337_ = lean_apply_4(v_toBind_2323_, lean_box(0), lean_box(0), v___x_2336_, v___f_2331_);
return v___x_2337_;
}
else
{
lean_object* v___f_2338_; size_t v___x_2339_; size_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
lean_inc_ref(v_inst_2239_);
v___f_2338_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2338_, 0, v_inst_2239_);
lean_closure_set(v___f_2338_, 1, v_f_2240_);
v___x_2339_ = ((size_t)0ULL);
v___x_2340_ = lean_usize_of_nat(v___x_2333_);
v___x_2341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2239_, v___f_2338_, v_params_2325_, v___x_2339_, v___x_2340_, v___x_2334_);
v___x_2342_ = lean_apply_4(v_toBind_2323_, lean_box(0), lean_box(0), v___x_2341_, v___f_2331_);
return v___x_2342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0(lean_object* v_inst_2343_, lean_object* v_f_2344_, lean_object* v_k_2345_, lean_object* v_____r_2346_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2343_, v_f_2344_, v_k_2345_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM(lean_object* v_m_2348_, uint8_t v_pu_2349_, lean_object* v_inst_2350_, lean_object* v_f_2351_, lean_object* v_c_2352_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2350_, v_f_2351_, v_c_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___boxed(lean_object* v_m_2354_, lean_object* v_pu_2355_, lean_object* v_inst_2356_, lean_object* v_f_2357_, lean_object* v_c_2358_){
_start:
{
uint8_t v_pu_boxed_2359_; lean_object* v_res_2360_; 
v_pu_boxed_2359_ = lean_unbox(v_pu_2355_);
v_res_2360_ = l_Lean_Compiler_LCNF_Code_forFVarM(v_m_2354_, v_pu_boxed_2359_, v_inst_2356_, v_f_2357_, v_c_2358_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(uint8_t v_pu_2361_, lean_object* v_m_2362_, lean_object* v_inst_2363_, lean_object* v_inst_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2361_, v_inst_2363_, v_inst_2364_, v___y_2365_, v___y_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed(lean_object* v_pu_2368_, lean_object* v_m_2369_, lean_object* v_inst_2370_, lean_object* v_inst_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
uint8_t v_pu_boxed_2374_; lean_object* v_res_2375_; 
v_pu_boxed_2374_ = lean_unbox(v_pu_2368_);
v_res_2375_ = l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(v_pu_boxed_2374_, v_m_2369_, v_inst_2370_, v_inst_2371_, v___y_2372_, v___y_2373_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__1(lean_object* v_m_2376_, lean_object* v_inst_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2377_, v___y_2378_, v___y_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode(uint8_t v_pu_2382_){
_start:
{
lean_object* v___x_2383_; lean_object* v___f_2384_; lean_object* v___f_2385_; lean_object* v___x_2386_; 
v___x_2383_ = lean_box(v_pu_2382_);
v___f_2384_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2384_, 0, v___x_2383_);
v___f_2385_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0));
v___x_2386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___f_2384_);
lean_ctor_set(v___x_2386_, 1, v___f_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___boxed(lean_object* v_pu_2387_){
_start:
{
uint8_t v_pu_boxed_2388_; lean_object* v_res_2389_; 
v_pu_boxed_2388_ = lean_unbox(v_pu_2387_);
v_res_2389_ = l_Lean_Compiler_LCNF_instTraverseFVarCode(v_pu_boxed_2388_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(uint8_t v_pu_2390_, lean_object* v_decl_2391_, lean_object* v_____do__lift_2392_, lean_object* v_params_2393_, lean_object* v_inst_2394_, lean_object* v_____do__lift_2395_){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2396_ = lean_box(v_pu_2390_);
v___x_2397_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed), 10, 5);
lean_closure_set(v___x_2397_, 0, v___x_2396_);
lean_closure_set(v___x_2397_, 1, v_decl_2391_);
lean_closure_set(v___x_2397_, 2, v_____do__lift_2392_);
lean_closure_set(v___x_2397_, 3, v_params_2393_);
lean_closure_set(v___x_2397_, 4, v_____do__lift_2395_);
v___x_2398_ = lean_apply_2(v_inst_2394_, lean_box(0), v___x_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_2399_, lean_object* v_decl_2400_, lean_object* v_____do__lift_2401_, lean_object* v_params_2402_, lean_object* v_inst_2403_, lean_object* v_____do__lift_2404_){
_start:
{
uint8_t v_pu_boxed_2405_; lean_object* v_res_2406_; 
v_pu_boxed_2405_ = lean_unbox(v_pu_2399_);
v_res_2406_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(v_pu_boxed_2405_, v_decl_2400_, v_____do__lift_2401_, v_params_2402_, v_inst_2403_, v_____do__lift_2404_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(uint8_t v_pu_2407_, lean_object* v_decl_2408_, lean_object* v_params_2409_, lean_object* v_inst_2410_, lean_object* v_inst_2411_, lean_object* v_f_2412_, lean_object* v_value_2413_, lean_object* v_toBind_2414_, lean_object* v_____do__lift_2415_){
_start:
{
lean_object* v___x_2416_; lean_object* v___f_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2416_ = lean_box(v_pu_2407_);
lean_inc(v_inst_2410_);
v___f_2417_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2417_, 0, v___x_2416_);
lean_closure_set(v___f_2417_, 1, v_decl_2408_);
lean_closure_set(v___f_2417_, 2, v_____do__lift_2415_);
lean_closure_set(v___f_2417_, 3, v_params_2409_);
lean_closure_set(v___f_2417_, 4, v_inst_2410_);
v___x_2418_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2407_, v_inst_2410_, v_inst_2411_, v_f_2412_, v_value_2413_);
v___x_2419_ = lean_apply_4(v_toBind_2414_, lean_box(0), lean_box(0), v___x_2418_, v___f_2417_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed(lean_object* v_pu_2420_, lean_object* v_decl_2421_, lean_object* v_params_2422_, lean_object* v_inst_2423_, lean_object* v_inst_2424_, lean_object* v_f_2425_, lean_object* v_value_2426_, lean_object* v_toBind_2427_, lean_object* v_____do__lift_2428_){
_start:
{
uint8_t v_pu_boxed_2429_; lean_object* v_res_2430_; 
v_pu_boxed_2429_ = lean_unbox(v_pu_2420_);
v_res_2430_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(v_pu_boxed_2429_, v_decl_2421_, v_params_2422_, v_inst_2423_, v_inst_2424_, v_f_2425_, v_value_2426_, v_toBind_2427_, v_____do__lift_2428_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(uint8_t v_pu_2431_, lean_object* v_decl_2432_, lean_object* v_inst_2433_, lean_object* v_inst_2434_, lean_object* v_f_2435_, lean_object* v_value_2436_, lean_object* v_toBind_2437_, lean_object* v_type_2438_, lean_object* v_params_2439_){
_start:
{
lean_object* v___x_2440_; lean_object* v___f_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2440_ = lean_box(v_pu_2431_);
lean_inc(v_toBind_2437_);
lean_inc(v_f_2435_);
lean_inc_ref(v_inst_2434_);
v___f_2441_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2441_, 0, v___x_2440_);
lean_closure_set(v___f_2441_, 1, v_decl_2432_);
lean_closure_set(v___f_2441_, 2, v_params_2439_);
lean_closure_set(v___f_2441_, 3, v_inst_2433_);
lean_closure_set(v___f_2441_, 4, v_inst_2434_);
lean_closure_set(v___f_2441_, 5, v_f_2435_);
lean_closure_set(v___f_2441_, 6, v_value_2436_);
lean_closure_set(v___f_2441_, 7, v_toBind_2437_);
v___x_2442_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2434_, v_f_2435_, v_type_2438_);
v___x_2443_ = lean_apply_4(v_toBind_2437_, lean_box(0), lean_box(0), v___x_2442_, v___f_2441_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed(lean_object* v_pu_2444_, lean_object* v_decl_2445_, lean_object* v_inst_2446_, lean_object* v_inst_2447_, lean_object* v_f_2448_, lean_object* v_value_2449_, lean_object* v_toBind_2450_, lean_object* v_type_2451_, lean_object* v_params_2452_){
_start:
{
uint8_t v_pu_boxed_2453_; lean_object* v_res_2454_; 
v_pu_boxed_2453_ = lean_unbox(v_pu_2444_);
v_res_2454_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(v_pu_boxed_2453_, v_decl_2445_, v_inst_2446_, v_inst_2447_, v_f_2448_, v_value_2449_, v_toBind_2450_, v_type_2451_, v_params_2452_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(uint8_t v_pu_2455_, lean_object* v_inst_2456_, lean_object* v_inst_2457_, lean_object* v_f_2458_, lean_object* v_decl_2459_){
_start:
{
lean_object* v_toBind_2460_; lean_object* v_params_2461_; lean_object* v_type_2462_; lean_object* v_value_2463_; lean_object* v___x_2464_; lean_object* v___f_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; size_t v_sz_2468_; size_t v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v_toBind_2460_ = lean_ctor_get(v_inst_2457_, 1);
lean_inc_n(v_toBind_2460_, 2);
v_params_2461_ = lean_ctor_get(v_decl_2459_, 2);
lean_inc_ref(v_params_2461_);
v_type_2462_ = lean_ctor_get(v_decl_2459_, 3);
lean_inc_ref(v_type_2462_);
v_value_2463_ = lean_ctor_get(v_decl_2459_, 4);
lean_inc_ref(v_value_2463_);
v___x_2464_ = lean_box(v_pu_2455_);
lean_inc(v_f_2458_);
lean_inc_ref_n(v_inst_2457_, 2);
lean_inc(v_inst_2456_);
v___f_2465_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2465_, 0, v___x_2464_);
lean_closure_set(v___f_2465_, 1, v_decl_2459_);
lean_closure_set(v___f_2465_, 2, v_inst_2456_);
lean_closure_set(v___f_2465_, 3, v_inst_2457_);
lean_closure_set(v___f_2465_, 4, v_f_2458_);
lean_closure_set(v___f_2465_, 5, v_value_2463_);
lean_closure_set(v___f_2465_, 6, v_toBind_2460_);
lean_closure_set(v___f_2465_, 7, v_type_2462_);
v___x_2466_ = lean_box(v_pu_2455_);
v___x_2467_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2467_, 0, lean_box(0));
lean_closure_set(v___x_2467_, 1, v___x_2466_);
lean_closure_set(v___x_2467_, 2, v_inst_2456_);
lean_closure_set(v___x_2467_, 3, v_inst_2457_);
lean_closure_set(v___x_2467_, 4, v_f_2458_);
v_sz_2468_ = lean_array_size(v_params_2461_);
v___x_2469_ = ((size_t)0ULL);
v___x_2470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2457_, v___x_2467_, v_sz_2468_, v___x_2469_, v_params_2461_);
v___x_2471_ = lean_apply_4(v_toBind_2460_, lean_box(0), lean_box(0), v___x_2470_, v___f_2465_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___boxed(lean_object* v_pu_2472_, lean_object* v_inst_2473_, lean_object* v_inst_2474_, lean_object* v_f_2475_, lean_object* v_decl_2476_){
_start:
{
uint8_t v_pu_boxed_2477_; lean_object* v_res_2478_; 
v_pu_boxed_2477_ = lean_unbox(v_pu_2472_);
v_res_2478_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_boxed_2477_, v_inst_2473_, v_inst_2474_, v_f_2475_, v_decl_2476_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM(lean_object* v_m_2479_, uint8_t v_pu_2480_, lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_f_2483_, lean_object* v_decl_2484_){
_start:
{
lean_object* v___x_2485_; 
v___x_2485_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2480_, v_inst_2481_, v_inst_2482_, v_f_2483_, v_decl_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___boxed(lean_object* v_m_2486_, lean_object* v_pu_2487_, lean_object* v_inst_2488_, lean_object* v_inst_2489_, lean_object* v_f_2490_, lean_object* v_decl_2491_){
_start:
{
uint8_t v_pu_boxed_2492_; lean_object* v_res_2493_; 
v_pu_boxed_2492_ = lean_unbox(v_pu_2487_);
v_res_2493_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM(v_m_2486_, v_pu_boxed_2492_, v_inst_2488_, v_inst_2489_, v_f_2490_, v_decl_2491_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0(lean_object* v_inst_2494_, lean_object* v_f_2495_, lean_object* v_value_2496_, lean_object* v_____r_2497_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2494_, v_f_2495_, v_value_2496_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1(lean_object* v_inst_2499_, lean_object* v_f_2500_, lean_object* v_type_2501_, lean_object* v_toBind_2502_, lean_object* v___f_2503_, lean_object* v_____r_2504_){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2499_, v_f_2500_, v_type_2501_);
v___x_2506_ = lean_apply_4(v_toBind_2502_, lean_box(0), lean_box(0), v___x_2505_, v___f_2503_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2(lean_object* v_inst_2507_, lean_object* v_f_2508_, lean_object* v_x_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_2507_, v_f_2508_, v___y_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(lean_object* v_inst_2512_, lean_object* v_f_2513_, lean_object* v_decl_2514_){
_start:
{
lean_object* v_toApplicative_2515_; lean_object* v_toBind_2516_; lean_object* v_params_2517_; lean_object* v_type_2518_; lean_object* v_value_2519_; lean_object* v_toPure_2520_; lean_object* v___f_2521_; lean_object* v___f_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
v_toApplicative_2515_ = lean_ctor_get(v_inst_2512_, 0);
v_toBind_2516_ = lean_ctor_get(v_inst_2512_, 1);
lean_inc_n(v_toBind_2516_, 2);
v_params_2517_ = lean_ctor_get(v_decl_2514_, 2);
lean_inc_ref(v_params_2517_);
v_type_2518_ = lean_ctor_get(v_decl_2514_, 3);
lean_inc_ref(v_type_2518_);
v_value_2519_ = lean_ctor_get(v_decl_2514_, 4);
lean_inc_ref(v_value_2519_);
lean_dec_ref(v_decl_2514_);
v_toPure_2520_ = lean_ctor_get(v_toApplicative_2515_, 1);
lean_inc_n(v_f_2513_, 2);
lean_inc_ref_n(v_inst_2512_, 2);
v___f_2521_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2521_, 0, v_inst_2512_);
lean_closure_set(v___f_2521_, 1, v_f_2513_);
lean_closure_set(v___f_2521_, 2, v_value_2519_);
v___f_2522_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2522_, 0, v_inst_2512_);
lean_closure_set(v___f_2522_, 1, v_f_2513_);
lean_closure_set(v___f_2522_, 2, v_type_2518_);
lean_closure_set(v___f_2522_, 3, v_toBind_2516_);
lean_closure_set(v___f_2522_, 4, v___f_2521_);
v___x_2523_ = lean_unsigned_to_nat(0u);
v___x_2524_ = lean_array_get_size(v_params_2517_);
v___x_2525_ = lean_box(0);
v___x_2526_ = lean_nat_dec_lt(v___x_2523_, v___x_2524_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
lean_inc(v_toPure_2520_);
lean_dec_ref(v_params_2517_);
lean_dec(v_f_2513_);
lean_dec_ref(v_inst_2512_);
v___x_2527_ = lean_apply_2(v_toPure_2520_, lean_box(0), v___x_2525_);
v___x_2528_ = lean_apply_4(v_toBind_2516_, lean_box(0), lean_box(0), v___x_2527_, v___f_2522_);
return v___x_2528_;
}
else
{
lean_object* v___f_2529_; size_t v___x_2530_; size_t v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
lean_inc_ref(v_inst_2512_);
v___f_2529_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_2529_, 0, v_inst_2512_);
lean_closure_set(v___f_2529_, 1, v_f_2513_);
v___x_2530_ = ((size_t)0ULL);
v___x_2531_ = lean_usize_of_nat(v___x_2524_);
v___x_2532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2512_, v___f_2529_, v_params_2517_, v___x_2530_, v___x_2531_, v___x_2525_);
v___x_2533_ = lean_apply_4(v_toBind_2516_, lean_box(0), lean_box(0), v___x_2532_, v___f_2522_);
return v___x_2533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM(lean_object* v_m_2534_, uint8_t v_pu_2535_, lean_object* v_inst_2536_, lean_object* v_f_2537_, lean_object* v_decl_2538_){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2536_, v_f_2537_, v_decl_2538_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___boxed(lean_object* v_m_2540_, lean_object* v_pu_2541_, lean_object* v_inst_2542_, lean_object* v_f_2543_, lean_object* v_decl_2544_){
_start:
{
uint8_t v_pu_boxed_2545_; lean_object* v_res_2546_; 
v_pu_boxed_2545_ = lean_unbox(v_pu_2541_);
v_res_2546_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM(v_m_2540_, v_pu_boxed_2545_, v_inst_2542_, v_f_2543_, v_decl_2544_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(uint8_t v_pu_2547_, lean_object* v_m_2548_, lean_object* v_inst_2549_, lean_object* v_inst_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2547_, v_inst_2549_, v_inst_2550_, v___y_2551_, v___y_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed(lean_object* v_pu_2554_, lean_object* v_m_2555_, lean_object* v_inst_2556_, lean_object* v_inst_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
uint8_t v_pu_boxed_2560_; lean_object* v_res_2561_; 
v_pu_boxed_2560_ = lean_unbox(v_pu_2554_);
v_res_2561_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(v_pu_boxed_2560_, v_m_2555_, v_inst_2556_, v_inst_2557_, v___y_2558_, v___y_2559_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__1(lean_object* v_m_2562_, lean_object* v_inst_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2563_, v___y_2564_, v___y_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(uint8_t v_pu_2568_){
_start:
{
lean_object* v___x_2569_; lean_object* v___f_2570_; lean_object* v___f_2571_; lean_object* v___x_2572_; 
v___x_2569_ = lean_box(v_pu_2568_);
v___f_2570_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2570_, 0, v___x_2569_);
v___f_2571_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0));
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___f_2570_);
lean_ctor_set(v___x_2572_, 1, v___f_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___boxed(lean_object* v_pu_2573_){
_start:
{
uint8_t v_pu_boxed_2574_; lean_object* v_res_2575_; 
v_pu_boxed_2574_ = lean_unbox(v_pu_2573_);
v_res_2575_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(v_pu_boxed_2574_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0(lean_object* v_toPure_2576_, lean_object* v_____do__lift_2577_){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2578_, 0, v_____do__lift_2577_);
v___x_2579_ = lean_apply_2(v_toPure_2576_, lean_box(0), v___x_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1(lean_object* v_toPure_2580_, lean_object* v_____do__lift_2581_){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2582_, 0, v_____do__lift_2581_);
v___x_2583_ = lean_apply_2(v_toPure_2580_, lean_box(0), v___x_2582_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2(lean_object* v_toPure_2584_, lean_object* v_____do__lift_2585_){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_____do__lift_2585_);
v___x_2587_ = lean_apply_2(v_toPure_2584_, lean_box(0), v___x_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3(lean_object* v_____do__lift_2588_, lean_object* v_i_2589_, lean_object* v_toPure_2590_, lean_object* v_____do__lift_2591_){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2592_, 0, v_____do__lift_2588_);
lean_ctor_set(v___x_2592_, 1, v_i_2589_);
lean_ctor_set(v___x_2592_, 2, v_____do__lift_2591_);
v___x_2593_ = lean_apply_2(v_toPure_2590_, lean_box(0), v___x_2592_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(lean_object* v_i_2594_, lean_object* v_toPure_2595_, uint8_t v_pu_2596_, lean_object* v_inst_2597_, lean_object* v_f_2598_, lean_object* v_y_2599_, lean_object* v_toBind_2600_, lean_object* v_____do__lift_2601_){
_start:
{
lean_object* v___f_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___f_2602_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3), 4, 3);
lean_closure_set(v___f_2602_, 0, v_____do__lift_2601_);
lean_closure_set(v___f_2602_, 1, v_i_2594_);
lean_closure_set(v___f_2602_, 2, v_toPure_2595_);
v___x_2603_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_2596_, v_inst_2597_, v_f_2598_, v_y_2599_);
v___x_2604_ = lean_apply_4(v_toBind_2600_, lean_box(0), lean_box(0), v___x_2603_, v___f_2602_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed(lean_object* v_i_2605_, lean_object* v_toPure_2606_, lean_object* v_pu_2607_, lean_object* v_inst_2608_, lean_object* v_f_2609_, lean_object* v_y_2610_, lean_object* v_toBind_2611_, lean_object* v_____do__lift_2612_){
_start:
{
uint8_t v_pu_boxed_2613_; lean_object* v_res_2614_; 
v_pu_boxed_2613_ = lean_unbox(v_pu_2607_);
v_res_2614_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(v_i_2605_, v_toPure_2606_, v_pu_boxed_2613_, v_inst_2608_, v_f_2609_, v_y_2610_, v_toBind_2611_, v_____do__lift_2612_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5(lean_object* v_____do__lift_2615_, lean_object* v_i_2616_, lean_object* v_toPure_2617_, lean_object* v_____do__lift_2618_){
_start:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2619_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_2619_, 0, v_____do__lift_2615_);
lean_ctor_set(v___x_2619_, 1, v_i_2616_);
lean_ctor_set(v___x_2619_, 2, v_____do__lift_2618_);
v___x_2620_ = lean_apply_2(v_toPure_2617_, lean_box(0), v___x_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6(lean_object* v_i_2621_, lean_object* v_toPure_2622_, lean_object* v_f_2623_, lean_object* v_y_2624_, lean_object* v_toBind_2625_, lean_object* v_____do__lift_2626_){
_start:
{
lean_object* v___f_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___f_2627_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5), 4, 3);
lean_closure_set(v___f_2627_, 0, v_____do__lift_2626_);
lean_closure_set(v___f_2627_, 1, v_i_2621_);
lean_closure_set(v___f_2627_, 2, v_toPure_2622_);
v___x_2628_ = lean_apply_1(v_f_2623_, v_y_2624_);
v___x_2629_ = lean_apply_4(v_toBind_2625_, lean_box(0), lean_box(0), v___x_2628_, v___f_2627_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7(lean_object* v_____do__lift_2630_, lean_object* v_i_2631_, lean_object* v_offset_2632_, lean_object* v_____do__lift_2633_, lean_object* v_toPure_2634_, lean_object* v_____do__lift_2635_){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v___x_2636_, 0, v_____do__lift_2630_);
lean_ctor_set(v___x_2636_, 1, v_i_2631_);
lean_ctor_set(v___x_2636_, 2, v_offset_2632_);
lean_ctor_set(v___x_2636_, 3, v_____do__lift_2633_);
lean_ctor_set(v___x_2636_, 4, v_____do__lift_2635_);
v___x_2637_ = lean_apply_2(v_toPure_2634_, lean_box(0), v___x_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8(lean_object* v_____do__lift_2638_, lean_object* v_i_2639_, lean_object* v_offset_2640_, lean_object* v_toPure_2641_, lean_object* v_inst_2642_, lean_object* v_f_2643_, lean_object* v_ty_2644_, lean_object* v_toBind_2645_, lean_object* v_____do__lift_2646_){
_start:
{
lean_object* v___f_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___f_2647_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7), 6, 5);
lean_closure_set(v___f_2647_, 0, v_____do__lift_2638_);
lean_closure_set(v___f_2647_, 1, v_i_2639_);
lean_closure_set(v___f_2647_, 2, v_offset_2640_);
lean_closure_set(v___f_2647_, 3, v_____do__lift_2646_);
lean_closure_set(v___f_2647_, 4, v_toPure_2641_);
v___x_2648_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2642_, v_f_2643_, v_ty_2644_);
v___x_2649_ = lean_apply_4(v_toBind_2645_, lean_box(0), lean_box(0), v___x_2648_, v___f_2647_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9(lean_object* v_i_2650_, lean_object* v_offset_2651_, lean_object* v_toPure_2652_, lean_object* v_inst_2653_, lean_object* v_f_2654_, lean_object* v_ty_2655_, lean_object* v_toBind_2656_, lean_object* v_y_2657_, lean_object* v_____do__lift_2658_){
_start:
{
lean_object* v___f_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
lean_inc(v_toBind_2656_);
lean_inc(v_f_2654_);
v___f_2659_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8), 9, 8);
lean_closure_set(v___f_2659_, 0, v_____do__lift_2658_);
lean_closure_set(v___f_2659_, 1, v_i_2650_);
lean_closure_set(v___f_2659_, 2, v_offset_2651_);
lean_closure_set(v___f_2659_, 3, v_toPure_2652_);
lean_closure_set(v___f_2659_, 4, v_inst_2653_);
lean_closure_set(v___f_2659_, 5, v_f_2654_);
lean_closure_set(v___f_2659_, 6, v_ty_2655_);
lean_closure_set(v___f_2659_, 7, v_toBind_2656_);
v___x_2660_ = lean_apply_1(v_f_2654_, v_y_2657_);
v___x_2661_ = lean_apply_4(v_toBind_2656_, lean_box(0), lean_box(0), v___x_2660_, v___f_2659_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10(lean_object* v_cidx_2662_, lean_object* v_toPure_2663_, lean_object* v_____do__lift_2664_){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2665_, 0, v_____do__lift_2664_);
lean_ctor_set(v___x_2665_, 1, v_cidx_2662_);
v___x_2666_ = lean_apply_2(v_toPure_2663_, lean_box(0), v___x_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(lean_object* v_n_2667_, uint8_t v_check_2668_, uint8_t v_persistent_2669_, lean_object* v_toPure_2670_, lean_object* v_____do__lift_2671_){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2672_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v___x_2672_, 0, v_____do__lift_2671_);
lean_ctor_set(v___x_2672_, 1, v_n_2667_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*2, v_check_2668_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*2 + 1, v_persistent_2669_);
v___x_2673_ = lean_apply_2(v_toPure_2670_, lean_box(0), v___x_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed(lean_object* v_n_2674_, lean_object* v_check_2675_, lean_object* v_persistent_2676_, lean_object* v_toPure_2677_, lean_object* v_____do__lift_2678_){
_start:
{
uint8_t v_check_933__boxed_2679_; uint8_t v_persistent_934__boxed_2680_; lean_object* v_res_2681_; 
v_check_933__boxed_2679_ = lean_unbox(v_check_2675_);
v_persistent_934__boxed_2680_ = lean_unbox(v_persistent_2676_);
v_res_2681_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(v_n_2674_, v_check_933__boxed_2679_, v_persistent_934__boxed_2680_, v_toPure_2677_, v_____do__lift_2678_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(lean_object* v_n_2682_, uint8_t v_check_2683_, uint8_t v_persistent_2684_, lean_object* v_objs_x3f_2685_, lean_object* v_toPure_2686_, lean_object* v_____do__lift_2687_){
_start:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = lean_alloc_ctor(8, 3, 2);
lean_ctor_set(v___x_2688_, 0, v_____do__lift_2687_);
lean_ctor_set(v___x_2688_, 1, v_n_2682_);
lean_ctor_set(v___x_2688_, 2, v_objs_x3f_2685_);
lean_ctor_set_uint8(v___x_2688_, sizeof(void*)*3, v_check_2683_);
lean_ctor_set_uint8(v___x_2688_, sizeof(void*)*3 + 1, v_persistent_2684_);
v___x_2689_ = lean_apply_2(v_toPure_2686_, lean_box(0), v___x_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed(lean_object* v_n_2690_, lean_object* v_check_2691_, lean_object* v_persistent_2692_, lean_object* v_objs_x3f_2693_, lean_object* v_toPure_2694_, lean_object* v_____do__lift_2695_){
_start:
{
uint8_t v_check_949__boxed_2696_; uint8_t v_persistent_950__boxed_2697_; lean_object* v_res_2698_; 
v_check_949__boxed_2696_ = lean_unbox(v_check_2691_);
v_persistent_950__boxed_2697_ = lean_unbox(v_persistent_2692_);
v_res_2698_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(v_n_2690_, v_check_949__boxed_2696_, v_persistent_950__boxed_2697_, v_objs_x3f_2693_, v_toPure_2694_, v_____do__lift_2695_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13(lean_object* v_toPure_2699_, lean_object* v_____do__lift_2700_){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2701_, 0, v_____do__lift_2700_);
v___x_2702_ = lean_apply_2(v_toPure_2699_, lean_box(0), v___x_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(uint8_t v_pu_2703_, lean_object* v_m_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_f_2707_, lean_object* v_decl_2708_){
_start:
{
switch(lean_obj_tag(v_decl_2708_))
{
case 0:
{
lean_object* v_toApplicative_2709_; lean_object* v_toBind_2710_; lean_object* v_toPure_2711_; lean_object* v_decl_2712_; lean_object* v___f_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_toApplicative_2709_ = lean_ctor_get(v_inst_2706_, 0);
v_toBind_2710_ = lean_ctor_get(v_inst_2706_, 1);
lean_inc(v_toBind_2710_);
v_toPure_2711_ = lean_ctor_get(v_toApplicative_2709_, 1);
v_decl_2712_ = lean_ctor_get(v_decl_2708_, 0);
lean_inc_ref(v_decl_2712_);
lean_dec_ref_known(v_decl_2708_, 1);
lean_inc(v_toPure_2711_);
v___f_2713_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0), 2, 1);
lean_closure_set(v___f_2713_, 0, v_toPure_2711_);
v___x_2714_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_2703_, v_inst_2705_, v_inst_2706_, v_f_2707_, v_decl_2712_);
v___x_2715_ = lean_apply_4(v_toBind_2710_, lean_box(0), lean_box(0), v___x_2714_, v___f_2713_);
return v___x_2715_;
}
case 1:
{
lean_object* v_toApplicative_2716_; lean_object* v_toBind_2717_; lean_object* v_toPure_2718_; lean_object* v_decl_2719_; lean_object* v___f_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v_toApplicative_2716_ = lean_ctor_get(v_inst_2706_, 0);
v_toBind_2717_ = lean_ctor_get(v_inst_2706_, 1);
lean_inc(v_toBind_2717_);
v_toPure_2718_ = lean_ctor_get(v_toApplicative_2716_, 1);
v_decl_2719_ = lean_ctor_get(v_decl_2708_, 0);
lean_inc_ref(v_decl_2719_);
lean_dec_ref_known(v_decl_2708_, 1);
lean_inc(v_toPure_2718_);
v___f_2720_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1), 2, 1);
lean_closure_set(v___f_2720_, 0, v_toPure_2718_);
v___x_2721_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2703_, v_inst_2705_, v_inst_2706_, v_f_2707_, v_decl_2719_);
v___x_2722_ = lean_apply_4(v_toBind_2717_, lean_box(0), lean_box(0), v___x_2721_, v___f_2720_);
return v___x_2722_;
}
case 2:
{
lean_object* v_toApplicative_2723_; lean_object* v_toBind_2724_; lean_object* v_toPure_2725_; lean_object* v_decl_2726_; lean_object* v___f_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v_toApplicative_2723_ = lean_ctor_get(v_inst_2706_, 0);
v_toBind_2724_ = lean_ctor_get(v_inst_2706_, 1);
lean_inc(v_toBind_2724_);
v_toPure_2725_ = lean_ctor_get(v_toApplicative_2723_, 1);
v_decl_2726_ = lean_ctor_get(v_decl_2708_, 0);
lean_inc_ref(v_decl_2726_);
lean_dec_ref_known(v_decl_2708_, 1);
lean_inc(v_toPure_2725_);
v___f_2727_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2), 2, 1);
lean_closure_set(v___f_2727_, 0, v_toPure_2725_);
v___x_2728_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2703_, v_inst_2705_, v_inst_2706_, v_f_2707_, v_decl_2726_);
v___x_2729_ = lean_apply_4(v_toBind_2724_, lean_box(0), lean_box(0), v___x_2728_, v___f_2727_);
return v___x_2729_;
}
case 3:
{
lean_object* v_toApplicative_2730_; lean_object* v_toBind_2731_; lean_object* v_toPure_2732_; lean_object* v_fvarId_2733_; lean_object* v_i_2734_; lean_object* v_y_2735_; lean_object* v___x_2736_; lean_object* v___f_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v_toApplicative_2730_ = lean_ctor_get(v_inst_2706_, 0);
lean_dec(v_inst_2705_);
v_toBind_2731_ = lean_ctor_get(v_inst_2706_, 1);
lean_inc_n(v_toBind_2731_, 2);
v_toPure_2732_ = lean_ctor_get(v_toApplicative_2730_, 1);
lean_inc(v_toPure_2732_);
v_fvarId_2733_ = lean_ctor_get(v_decl_2708_, 0);
lean_inc(v_fvarId_2733_);
v_i_2734_ = lean_ctor_get(v_decl_2708_, 1);
lean_inc(v_i_2734_);
v_y_2735_ = lean_ctor_get(v_decl_2708_, 2);
lean_inc(v_y_2735_);
lean_dec_ref_known(v_decl_2708_, 3);
v___x_2736_ = lean_box(v_pu_2703_);
lean_inc(v_f_2707_);
v___f_2737_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed), 8, 7);
lean_closure_set(v___f_2737_, 0, v_i_2734_);
lean_closure_set(v___f_2737_, 1, v_toPure_2732_);
lean_closure_set(v___f_2737_, 2, v___x_2736_);
lean_closure_set(v___f_2737_, 3, v_inst_2706_);
lean_closure_set(v___f_2737_, 4, v_f_2707_);
lean_closure_set(v___f_2737_, 5, v_y_2735_);
lean_closure_set(v___f_2737_, 6, v_toBind_2731_);
v___x_2738_ = lean_apply_1(v_f_2707_, v_fvarId_2733_);
v___x_2739_ = lean_apply_4(v_toBind_2731_, lean_box(0), lean_box(0), v___x_2738_, v___f_2737_);
return v___x_2739_;
}
case 4:
{
lean_object* v_toApplicative_2740_; lean_object* v_toBind_2741_; lean_object* v_toPure_2742_; lean_object* v_fvarId_2743_; lean_object* v_i_2744_; lean_object* v_y_2745_; lean_object* v___f_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v_toApplicative_2740_ = lean_ctor_get(v_inst_2706_, 0);
lean_inc_ref(v_toApplicative_2740_);
lean_dec(v_inst_2705_);
v_toBind_2741_ = lean_ctor_get(v_inst_2706_, 1);
lean_inc_n(v_toBind_2741_, 2);
lean_dec_ref(v_inst_2706_);
v_toPure_2742_ = lean_ctor_get(v_toApplicative_2740_, 1);
lean_inc(v_toPure_2742_);
lean_dec_ref(v_toApplicative_2740_);
v_fvarId_2743_ = lean_ctor_get(v_decl_2708_, 0);
lean_inc(v_fvarId_2743_);
v_i_2744_ = lean_ctor_get(v_decl_2708_, 1);
lean_inc(v_i_2744_);
v_y_2745_ = lean_ctor_get(v_decl_2708_, 2);
lean_inc(v_y_2745_);
lean_dec_ref_known(v_decl_2708_, 3);
lean_inc(v_f_2707_);
v___f_2746_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6), 6, 5);
lean_closure_set(v___f_2746_, 0, v_i_2744_);
lean_closure_set(v___f_2746_, 1, v_toPure_2742_);
lean_closure_set(v___f_2746_, 2, v_f_2707_);
lean_closure_set(v___f_2746_, 3, v_y_2745_);
lean_closure_set(v___f_2746_, 4, v_toBind_2741_);
v___x_2747_ = lean_apply_1(v_f_2707_, v_fvarId_2743_);
v___x_2748_ = lean_apply_4(v_toBind_2741_, lean_box(0), lean_box(0), v___x_2747_, v___f_2746_);
return v___x_2748_;
}
case 5:
{
lean_object* v_toApplicative_2749_; lean_object* v_toBind_2750_; lean_object* v_toPure_2751_; lean_object* v_fvarId_2752_; lean_object* v_i_2753_; lean_object* v_offset_2754_; lean_object* v_y_2755_; lean_object* v_ty_2756_; lean_object* v___f_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v_toApplicative_2749_ = lean_ctor_get(v_inst_2706_, 0);
lean_dec(v_inst_2705_);
v_toBind_2750_ = lean_ctor_get(v_inst_2706_, 1);
lean_inc_n(v_toBind_2750_, 2);
v_toPure_2751_ = lean_ctor_get(v_toApplicative_2749_, 1);
lean_inc(v_toPure_2751_);
v_fvarId_2752_ = lean_ctor_get(v_decl_2708_, 0);
lean_inc(v_fvarId_2752_);
v_i_2753_ = lean_ctor_get(v_decl_2708_, 1);
lean_inc(v_i_2753_);
v_offset_2754_ = lean_ctor_get(v_decl_2708_, 2);
lean_inc(v_offset_2754_);
v_y_2755_ = lean_ctor_get(v_decl_2708_, 3);
lean_inc(v_y_2755_);
v_ty_2756_ = lean_ctor_get(v_decl_2708_, 4);
lean_inc_ref(v_ty_2756_);
lean_dec_ref_known(v_decl_2708_, 5);
lean_inc(v_f_2707_);
v___f_2757_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9), 9, 8);
lean_closure_set(v___f_2757_, 0, v_i_2753_);
lean_closure_set(v___f_2757_, 1, v_offset_2754_);
lean_closure_set(v___f_2757_, 2, v_toPure_2751_);
lean_closure_set(v___f_2757_, 3, v_inst_2706_);
lean_closure_set(v___f_2757_, 4, v_f_2707_);
lean_closure_set(v___f_2757_, 5, v_ty_2756_);
lean_closure_set(v___f_2757_, 6, v_toBind_2750_);
lean_closure_set(v___f_2757_, 7, v_y_2755_);
v___x_2758_ = lean_apply_1(v_f_2707_, v_fvarId_2752_);
v___x_2759_ = lean_apply_4(v_toBind_2750_, lean_box(0), lean_box(0), v___x_2758_, v___f_2757_);
return v___x_2759_;
}
case 6:
{
lean_object* v_toApplicative_2760_; lean_object* v_toBind_2761_; lean_object* v_toPure_2762_; lean_object* v_fvarId_2763_; lean_object* v_cidx_2764_; lean_object* v___f_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_toApplicative_2760_ = lean_ctor_get(v_inst_2706_, 0);
lean_inc_ref(v_toApplicative_2760_);
lean_dec(v_inst_2705_);
v_toBind_2761_ = lean_ctor_get(v_inst_2706_, 1);
lean_inc(v_toBind_2761_);
lean_dec_ref(v_inst_2706_);
v_toPure_2762_ = lean_ctor_get(v_toApplicative_2760_, 1);
lean_inc(v_toPure_2762_);
lean_dec_ref(v_toApplicative_2760_);
v_fvarId_2763_ = lean_ctor_get(v_decl_2708_, 0);
lean_inc(v_fvarId_2763_);
v_cidx_2764_ = lean_ctor_get(v_decl_2708_, 1);
lean_inc(v_cidx_2764_);
lean_dec_ref_known(v_decl_2708_, 2);
v___f_2765_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10), 3, 2);
lean_closure_set(v___f_2765_, 0, v_cidx_2764_);
lean_closure_set(v___f_2765_, 1, v_toPure_2762_);
v___x_2766_ = lean_apply_1(v_f_2707_, v_fvarId_2763_);
v___x_2767_ = lean_apply_4(v_toBind_2761_, lean_box(0), lean_box(0), v___x_2766_, v___f_2765_);
return v___x_2767_;
}
case 7:
{
lean_object* v_toApplicative_2768_; lean_object* v_toBind_2769_; lean_object* v_toPure_2770_; lean_object* v_fvarId_2771_; lean_object* v_n_2772_; uint8_t v_check_2773_; uint8_t v_persistent_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___f_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v_toApplicative_2768_ = lean_ctor_get(v_inst_2706_, 0);
lean_inc_ref(v_toApplicative_2768_);
lean_dec(v_inst_2705_);
v_toBind_2769_ = lean_ctor_get(v_inst_2706_, 1);
lean_inc(v_toBind_2769_);
lean_dec_ref(v_inst_2706_);
v_toPure_2770_ = lean_ctor_get(v_toApplicative_2768_, 1);
lean_inc(v_toPure_2770_);
lean_dec_ref(v_toApplicative_2768_);
v_fvarId_2771_ = lean_ctor_get(v_decl_2708_, 0);
lean_inc(v_fvarId_2771_);
v_n_2772_ = lean_ctor_get(v_decl_2708_, 1);
lean_inc(v_n_2772_);
v_check_2773_ = lean_ctor_get_uint8(v_decl_2708_, sizeof(void*)*2);
v_persistent_2774_ = lean_ctor_get_uint8(v_decl_2708_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_decl_2708_, 2);
v___x_2775_ = lean_box(v_check_2773_);
v___x_2776_ = lean_box(v_persistent_2774_);
v___f_2777_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed), 5, 4);
lean_closure_set(v___f_2777_, 0, v_n_2772_);
lean_closure_set(v___f_2777_, 1, v___x_2775_);
lean_closure_set(v___f_2777_, 2, v___x_2776_);
lean_closure_set(v___f_2777_, 3, v_toPure_2770_);
v___x_2778_ = lean_apply_1(v_f_2707_, v_fvarId_2771_);
v___x_2779_ = lean_apply_4(v_toBind_2769_, lean_box(0), lean_box(0), v___x_2778_, v___f_2777_);
return v___x_2779_;
}
case 8:
{
lean_object* v_toApplicative_2780_; lean_object* v_toBind_2781_; lean_object* v_toPure_2782_; lean_object* v_fvarId_2783_; lean_object* v_n_2784_; uint8_t v_check_2785_; uint8_t v_persistent_2786_; lean_object* v_objs_x3f_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___f_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v_toApplicative_2780_ = lean_ctor_get(v_inst_2706_, 0);
lean_inc_ref(v_toApplicative_2780_);
lean_dec(v_inst_2705_);
v_toBind_2781_ = lean_ctor_get(v_inst_2706_, 1);
lean_inc(v_toBind_2781_);
lean_dec_ref(v_inst_2706_);
v_toPure_2782_ = lean_ctor_get(v_toApplicative_2780_, 1);
lean_inc(v_toPure_2782_);
lean_dec_ref(v_toApplicative_2780_);
v_fvarId_2783_ = lean_ctor_get(v_decl_2708_, 0);
lean_inc(v_fvarId_2783_);
v_n_2784_ = lean_ctor_get(v_decl_2708_, 1);
lean_inc(v_n_2784_);
v_check_2785_ = lean_ctor_get_uint8(v_decl_2708_, sizeof(void*)*3);
v_persistent_2786_ = lean_ctor_get_uint8(v_decl_2708_, sizeof(void*)*3 + 1);
v_objs_x3f_2787_ = lean_ctor_get(v_decl_2708_, 2);
lean_inc(v_objs_x3f_2787_);
lean_dec_ref_known(v_decl_2708_, 3);
v___x_2788_ = lean_box(v_check_2785_);
v___x_2789_ = lean_box(v_persistent_2786_);
v___f_2790_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed), 6, 5);
lean_closure_set(v___f_2790_, 0, v_n_2784_);
lean_closure_set(v___f_2790_, 1, v___x_2788_);
lean_closure_set(v___f_2790_, 2, v___x_2789_);
lean_closure_set(v___f_2790_, 3, v_objs_x3f_2787_);
lean_closure_set(v___f_2790_, 4, v_toPure_2782_);
v___x_2791_ = lean_apply_1(v_f_2707_, v_fvarId_2783_);
v___x_2792_ = lean_apply_4(v_toBind_2781_, lean_box(0), lean_box(0), v___x_2791_, v___f_2790_);
return v___x_2792_;
}
default: 
{
lean_object* v_toApplicative_2793_; lean_object* v_toBind_2794_; lean_object* v_toPure_2795_; lean_object* v_fvarId_2796_; lean_object* v___f_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_toApplicative_2793_ = lean_ctor_get(v_inst_2706_, 0);
lean_inc_ref(v_toApplicative_2793_);
lean_dec(v_inst_2705_);
v_toBind_2794_ = lean_ctor_get(v_inst_2706_, 1);
lean_inc(v_toBind_2794_);
lean_dec_ref(v_inst_2706_);
v_toPure_2795_ = lean_ctor_get(v_toApplicative_2793_, 1);
lean_inc(v_toPure_2795_);
lean_dec_ref(v_toApplicative_2793_);
v_fvarId_2796_ = lean_ctor_get(v_decl_2708_, 0);
lean_inc(v_fvarId_2796_);
lean_dec_ref_known(v_decl_2708_, 1);
v___f_2797_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13), 2, 1);
lean_closure_set(v___f_2797_, 0, v_toPure_2795_);
v___x_2798_ = lean_apply_1(v_f_2707_, v_fvarId_2796_);
v___x_2799_ = lean_apply_4(v_toBind_2794_, lean_box(0), lean_box(0), v___x_2798_, v___f_2797_);
return v___x_2799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed(lean_object* v_pu_2800_, lean_object* v_m_2801_, lean_object* v_inst_2802_, lean_object* v_inst_2803_, lean_object* v_f_2804_, lean_object* v_decl_2805_){
_start:
{
uint8_t v_pu_boxed_2806_; lean_object* v_res_2807_; 
v_pu_boxed_2806_ = lean_unbox(v_pu_2800_);
v_res_2807_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(v_pu_boxed_2806_, v_m_2801_, v_inst_2802_, v_inst_2803_, v_f_2804_, v_decl_2805_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15(lean_object* v_inst_2808_, lean_object* v_f_2809_, lean_object* v_y_2810_, lean_object* v_____r_2811_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2808_, v_f_2809_, v_y_2810_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16(lean_object* v_f_2813_, lean_object* v_y_2814_, lean_object* v_____r_2815_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = lean_apply_1(v_f_2813_, v_y_2814_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17(lean_object* v_inst_2817_, lean_object* v_f_2818_, lean_object* v_ty_2819_, lean_object* v_____r_2820_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2817_, v_f_2818_, v_ty_2819_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18(lean_object* v_f_2822_, lean_object* v_y_2823_, lean_object* v_toBind_2824_, lean_object* v___f_2825_, lean_object* v_____r_2826_){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = lean_apply_1(v_f_2822_, v_y_2823_);
v___x_2828_ = lean_apply_4(v_toBind_2824_, lean_box(0), lean_box(0), v___x_2827_, v___f_2825_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__19(lean_object* v_m_2829_, lean_object* v_inst_2830_, lean_object* v_f_2831_, lean_object* v_decl_2832_){
_start:
{
switch(lean_obj_tag(v_decl_2832_))
{
case 0:
{
lean_object* v_decl_2833_; lean_object* v___x_2834_; 
v_decl_2833_ = lean_ctor_get(v_decl_2832_, 0);
lean_inc_ref(v_decl_2833_);
lean_dec_ref_known(v_decl_2832_, 1);
v___x_2834_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_2830_, v_f_2831_, v_decl_2833_);
return v___x_2834_;
}
case 1:
{
lean_object* v_decl_2835_; lean_object* v___x_2836_; 
v_decl_2835_ = lean_ctor_get(v_decl_2832_, 0);
lean_inc_ref(v_decl_2835_);
lean_dec_ref_known(v_decl_2832_, 1);
v___x_2836_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2830_, v_f_2831_, v_decl_2835_);
return v___x_2836_;
}
case 2:
{
lean_object* v_decl_2837_; lean_object* v___x_2838_; 
v_decl_2837_ = lean_ctor_get(v_decl_2832_, 0);
lean_inc_ref(v_decl_2837_);
lean_dec_ref_known(v_decl_2832_, 1);
v___x_2838_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2830_, v_f_2831_, v_decl_2837_);
return v___x_2838_;
}
case 3:
{
lean_object* v_toBind_2839_; lean_object* v_fvarId_2840_; lean_object* v_y_2841_; lean_object* v___f_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v_toBind_2839_ = lean_ctor_get(v_inst_2830_, 1);
lean_inc(v_toBind_2839_);
v_fvarId_2840_ = lean_ctor_get(v_decl_2832_, 0);
lean_inc(v_fvarId_2840_);
v_y_2841_ = lean_ctor_get(v_decl_2832_, 2);
lean_inc(v_y_2841_);
lean_dec_ref_known(v_decl_2832_, 3);
lean_inc(v_f_2831_);
v___f_2842_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15), 4, 3);
lean_closure_set(v___f_2842_, 0, v_inst_2830_);
lean_closure_set(v___f_2842_, 1, v_f_2831_);
lean_closure_set(v___f_2842_, 2, v_y_2841_);
v___x_2843_ = lean_apply_1(v_f_2831_, v_fvarId_2840_);
v___x_2844_ = lean_apply_4(v_toBind_2839_, lean_box(0), lean_box(0), v___x_2843_, v___f_2842_);
return v___x_2844_;
}
case 4:
{
lean_object* v_toBind_2845_; lean_object* v_fvarId_2846_; lean_object* v_y_2847_; lean_object* v___f_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v_toBind_2845_ = lean_ctor_get(v_inst_2830_, 1);
lean_inc(v_toBind_2845_);
lean_dec_ref(v_inst_2830_);
v_fvarId_2846_ = lean_ctor_get(v_decl_2832_, 0);
lean_inc(v_fvarId_2846_);
v_y_2847_ = lean_ctor_get(v_decl_2832_, 2);
lean_inc(v_y_2847_);
lean_dec_ref_known(v_decl_2832_, 3);
lean_inc(v_f_2831_);
v___f_2848_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16), 3, 2);
lean_closure_set(v___f_2848_, 0, v_f_2831_);
lean_closure_set(v___f_2848_, 1, v_y_2847_);
v___x_2849_ = lean_apply_1(v_f_2831_, v_fvarId_2846_);
v___x_2850_ = lean_apply_4(v_toBind_2845_, lean_box(0), lean_box(0), v___x_2849_, v___f_2848_);
return v___x_2850_;
}
case 5:
{
lean_object* v_toBind_2851_; lean_object* v_fvarId_2852_; lean_object* v_y_2853_; lean_object* v_ty_2854_; lean_object* v___f_2855_; lean_object* v___f_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v_toBind_2851_ = lean_ctor_get(v_inst_2830_, 1);
lean_inc_n(v_toBind_2851_, 2);
v_fvarId_2852_ = lean_ctor_get(v_decl_2832_, 0);
lean_inc(v_fvarId_2852_);
v_y_2853_ = lean_ctor_get(v_decl_2832_, 3);
lean_inc(v_y_2853_);
v_ty_2854_ = lean_ctor_get(v_decl_2832_, 4);
lean_inc_ref(v_ty_2854_);
lean_dec_ref_known(v_decl_2832_, 5);
lean_inc_n(v_f_2831_, 2);
v___f_2855_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17), 4, 3);
lean_closure_set(v___f_2855_, 0, v_inst_2830_);
lean_closure_set(v___f_2855_, 1, v_f_2831_);
lean_closure_set(v___f_2855_, 2, v_ty_2854_);
v___f_2856_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18), 5, 4);
lean_closure_set(v___f_2856_, 0, v_f_2831_);
lean_closure_set(v___f_2856_, 1, v_y_2853_);
lean_closure_set(v___f_2856_, 2, v_toBind_2851_);
lean_closure_set(v___f_2856_, 3, v___f_2855_);
v___x_2857_ = lean_apply_1(v_f_2831_, v_fvarId_2852_);
v___x_2858_ = lean_apply_4(v_toBind_2851_, lean_box(0), lean_box(0), v___x_2857_, v___f_2856_);
return v___x_2858_;
}
default: 
{
lean_object* v_fvarId_2859_; lean_object* v___x_2860_; 
lean_dec_ref(v_inst_2830_);
v_fvarId_2859_ = lean_ctor_get(v_decl_2832_, 0);
lean_inc(v_fvarId_2859_);
lean_dec_ref(v_decl_2832_);
v___x_2860_ = lean_apply_1(v_f_2831_, v_fvarId_2859_);
return v___x_2860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(uint8_t v_pu_2862_){
_start:
{
lean_object* v___x_2863_; lean_object* v___f_2864_; lean_object* v___f_2865_; lean_object* v___x_2866_; 
v___x_2863_ = lean_box(v_pu_2862_);
v___f_2864_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed), 6, 1);
lean_closure_set(v___f_2864_, 0, v___x_2863_);
v___f_2865_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0));
v___x_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___f_2864_);
lean_ctor_set(v___x_2866_, 1, v___f_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___boxed(lean_object* v_pu_2867_){
_start:
{
uint8_t v_pu_boxed_2868_; lean_object* v_res_2869_; 
v_pu_boxed_2868_ = lean_unbox(v_pu_2867_);
v_res_2869_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(v_pu_boxed_2868_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0(lean_object* v_ctorName_2870_, lean_object* v_params_2871_, lean_object* v_toPure_2872_, lean_object* v_____do__lift_2873_){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2874_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2874_, 0, v_ctorName_2870_);
lean_ctor_set(v___x_2874_, 1, v_params_2871_);
lean_ctor_set(v___x_2874_, 2, v_____do__lift_2873_);
v___x_2875_ = lean_apply_2(v_toPure_2872_, lean_box(0), v___x_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(lean_object* v_ctorName_2876_, lean_object* v_toPure_2877_, uint8_t v_pu_2878_, lean_object* v_inst_2879_, lean_object* v_inst_2880_, lean_object* v_f_2881_, lean_object* v_code_2882_, lean_object* v_toBind_2883_, lean_object* v_params_2884_){
_start:
{
lean_object* v___f_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___f_2885_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0), 4, 3);
lean_closure_set(v___f_2885_, 0, v_ctorName_2876_);
lean_closure_set(v___f_2885_, 1, v_params_2884_);
lean_closure_set(v___f_2885_, 2, v_toPure_2877_);
v___x_2886_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2878_, v_inst_2879_, v_inst_2880_, v_f_2881_, v_code_2882_);
v___x_2887_ = lean_apply_4(v_toBind_2883_, lean_box(0), lean_box(0), v___x_2886_, v___f_2885_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed(lean_object* v_ctorName_2888_, lean_object* v_toPure_2889_, lean_object* v_pu_2890_, lean_object* v_inst_2891_, lean_object* v_inst_2892_, lean_object* v_f_2893_, lean_object* v_code_2894_, lean_object* v_toBind_2895_, lean_object* v_params_2896_){
_start:
{
uint8_t v_pu_boxed_2897_; lean_object* v_res_2898_; 
v_pu_boxed_2897_ = lean_unbox(v_pu_2890_);
v_res_2898_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(v_ctorName_2888_, v_toPure_2889_, v_pu_boxed_2897_, v_inst_2891_, v_inst_2892_, v_f_2893_, v_code_2894_, v_toBind_2895_, v_params_2896_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2(lean_object* v_info_2899_, lean_object* v_toPure_2900_, lean_object* v_____do__lift_2901_){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2902_, 0, v_info_2899_);
lean_ctor_set(v___x_2902_, 1, v_____do__lift_2901_);
v___x_2903_ = lean_apply_2(v_toPure_2900_, lean_box(0), v___x_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3(lean_object* v_toPure_2904_, lean_object* v_____do__lift_2905_){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2906_, 0, v_____do__lift_2905_);
v___x_2907_ = lean_apply_2(v_toPure_2904_, lean_box(0), v___x_2906_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(uint8_t v_pu_2908_, lean_object* v_m_2909_, lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_f_2912_, lean_object* v_alt_2913_){
_start:
{
switch(lean_obj_tag(v_alt_2913_))
{
case 0:
{
lean_object* v_toApplicative_2914_; lean_object* v_toBind_2915_; lean_object* v_toPure_2916_; lean_object* v_ctorName_2917_; lean_object* v_params_2918_; lean_object* v_code_2919_; lean_object* v___x_2920_; lean_object* v___f_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; size_t v_sz_2924_; size_t v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v_toApplicative_2914_ = lean_ctor_get(v_inst_2911_, 0);
v_toBind_2915_ = lean_ctor_get(v_inst_2911_, 1);
lean_inc_n(v_toBind_2915_, 2);
v_toPure_2916_ = lean_ctor_get(v_toApplicative_2914_, 1);
v_ctorName_2917_ = lean_ctor_get(v_alt_2913_, 0);
lean_inc(v_ctorName_2917_);
v_params_2918_ = lean_ctor_get(v_alt_2913_, 1);
lean_inc_ref(v_params_2918_);
v_code_2919_ = lean_ctor_get(v_alt_2913_, 2);
lean_inc_ref(v_code_2919_);
lean_dec_ref_known(v_alt_2913_, 3);
v___x_2920_ = lean_box(v_pu_2908_);
lean_inc(v_f_2912_);
lean_inc_ref_n(v_inst_2911_, 2);
lean_inc(v_inst_2910_);
lean_inc(v_toPure_2916_);
v___f_2921_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2921_, 0, v_ctorName_2917_);
lean_closure_set(v___f_2921_, 1, v_toPure_2916_);
lean_closure_set(v___f_2921_, 2, v___x_2920_);
lean_closure_set(v___f_2921_, 3, v_inst_2910_);
lean_closure_set(v___f_2921_, 4, v_inst_2911_);
lean_closure_set(v___f_2921_, 5, v_f_2912_);
lean_closure_set(v___f_2921_, 6, v_code_2919_);
lean_closure_set(v___f_2921_, 7, v_toBind_2915_);
v___x_2922_ = lean_box(v_pu_2908_);
v___x_2923_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2923_, 0, lean_box(0));
lean_closure_set(v___x_2923_, 1, v___x_2922_);
lean_closure_set(v___x_2923_, 2, v_inst_2910_);
lean_closure_set(v___x_2923_, 3, v_inst_2911_);
lean_closure_set(v___x_2923_, 4, v_f_2912_);
v_sz_2924_ = lean_array_size(v_params_2918_);
v___x_2925_ = ((size_t)0ULL);
v___x_2926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2911_, v___x_2923_, v_sz_2924_, v___x_2925_, v_params_2918_);
v___x_2927_ = lean_apply_4(v_toBind_2915_, lean_box(0), lean_box(0), v___x_2926_, v___f_2921_);
return v___x_2927_;
}
case 1:
{
lean_object* v_toApplicative_2928_; lean_object* v_toBind_2929_; lean_object* v_toPure_2930_; lean_object* v_info_2931_; lean_object* v_code_2932_; lean_object* v___f_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v_toApplicative_2928_ = lean_ctor_get(v_inst_2911_, 0);
v_toBind_2929_ = lean_ctor_get(v_inst_2911_, 1);
lean_inc(v_toBind_2929_);
v_toPure_2930_ = lean_ctor_get(v_toApplicative_2928_, 1);
v_info_2931_ = lean_ctor_get(v_alt_2913_, 0);
lean_inc_ref(v_info_2931_);
v_code_2932_ = lean_ctor_get(v_alt_2913_, 1);
lean_inc_ref(v_code_2932_);
lean_dec_ref_known(v_alt_2913_, 2);
lean_inc(v_toPure_2930_);
v___f_2933_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2), 3, 2);
lean_closure_set(v___f_2933_, 0, v_info_2931_);
lean_closure_set(v___f_2933_, 1, v_toPure_2930_);
v___x_2934_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2908_, v_inst_2910_, v_inst_2911_, v_f_2912_, v_code_2932_);
v___x_2935_ = lean_apply_4(v_toBind_2929_, lean_box(0), lean_box(0), v___x_2934_, v___f_2933_);
return v___x_2935_;
}
default: 
{
lean_object* v_toApplicative_2936_; lean_object* v_toBind_2937_; lean_object* v_toPure_2938_; lean_object* v_code_2939_; lean_object* v___f_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v_toApplicative_2936_ = lean_ctor_get(v_inst_2911_, 0);
v_toBind_2937_ = lean_ctor_get(v_inst_2911_, 1);
lean_inc(v_toBind_2937_);
v_toPure_2938_ = lean_ctor_get(v_toApplicative_2936_, 1);
v_code_2939_ = lean_ctor_get(v_alt_2913_, 0);
lean_inc_ref(v_code_2939_);
lean_dec_ref_known(v_alt_2913_, 1);
lean_inc(v_toPure_2938_);
v___f_2940_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3), 2, 1);
lean_closure_set(v___f_2940_, 0, v_toPure_2938_);
v___x_2941_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2908_, v_inst_2910_, v_inst_2911_, v_f_2912_, v_code_2939_);
v___x_2942_ = lean_apply_4(v_toBind_2937_, lean_box(0), lean_box(0), v___x_2941_, v___f_2940_);
return v___x_2942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed(lean_object* v_pu_2943_, lean_object* v_m_2944_, lean_object* v_inst_2945_, lean_object* v_inst_2946_, lean_object* v_f_2947_, lean_object* v_alt_2948_){
_start:
{
uint8_t v_pu_boxed_2949_; lean_object* v_res_2950_; 
v_pu_boxed_2949_ = lean_unbox(v_pu_2943_);
v_res_2950_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(v_pu_boxed_2949_, v_m_2944_, v_inst_2945_, v_inst_2946_, v_f_2947_, v_alt_2948_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5(lean_object* v_inst_2951_, lean_object* v_f_2952_, lean_object* v_code_2953_, lean_object* v_____r_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2951_, v_f_2952_, v_code_2953_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__7(lean_object* v_m_2956_, lean_object* v_inst_2957_, lean_object* v_f_2958_, lean_object* v_alt_2959_){
_start:
{
switch(lean_obj_tag(v_alt_2959_))
{
case 0:
{
lean_object* v_toApplicative_2960_; lean_object* v_toBind_2961_; lean_object* v_params_2962_; lean_object* v_code_2963_; lean_object* v_toPure_2964_; lean_object* v___f_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; uint8_t v___x_2969_; 
v_toApplicative_2960_ = lean_ctor_get(v_inst_2957_, 0);
v_toBind_2961_ = lean_ctor_get(v_inst_2957_, 1);
lean_inc(v_toBind_2961_);
v_params_2962_ = lean_ctor_get(v_alt_2959_, 1);
lean_inc_ref(v_params_2962_);
v_code_2963_ = lean_ctor_get(v_alt_2959_, 2);
lean_inc_ref(v_code_2963_);
lean_dec_ref_known(v_alt_2959_, 3);
v_toPure_2964_ = lean_ctor_get(v_toApplicative_2960_, 1);
lean_inc(v_f_2958_);
lean_inc_ref(v_inst_2957_);
v___f_2965_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5), 4, 3);
lean_closure_set(v___f_2965_, 0, v_inst_2957_);
lean_closure_set(v___f_2965_, 1, v_f_2958_);
lean_closure_set(v___f_2965_, 2, v_code_2963_);
v___x_2966_ = lean_unsigned_to_nat(0u);
v___x_2967_ = lean_array_get_size(v_params_2962_);
v___x_2968_ = lean_box(0);
v___x_2969_ = lean_nat_dec_lt(v___x_2966_, v___x_2967_);
if (v___x_2969_ == 0)
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
lean_inc(v_toPure_2964_);
lean_dec_ref(v_params_2962_);
lean_dec(v_f_2958_);
lean_dec_ref(v_inst_2957_);
v___x_2970_ = lean_apply_2(v_toPure_2964_, lean_box(0), v___x_2968_);
v___x_2971_ = lean_apply_4(v_toBind_2961_, lean_box(0), lean_box(0), v___x_2970_, v___f_2965_);
return v___x_2971_;
}
else
{
lean_object* v___f_2972_; size_t v___x_2973_; size_t v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
lean_inc_ref(v_inst_2957_);
v___f_2972_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_2972_, 0, v_inst_2957_);
lean_closure_set(v___f_2972_, 1, v_f_2958_);
v___x_2973_ = ((size_t)0ULL);
v___x_2974_ = lean_usize_of_nat(v___x_2967_);
v___x_2975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2957_, v___f_2972_, v_params_2962_, v___x_2973_, v___x_2974_, v___x_2968_);
v___x_2976_ = lean_apply_4(v_toBind_2961_, lean_box(0), lean_box(0), v___x_2975_, v___f_2965_);
return v___x_2976_;
}
}
case 1:
{
lean_object* v_code_2977_; lean_object* v___x_2978_; 
v_code_2977_ = lean_ctor_get(v_alt_2959_, 1);
lean_inc_ref(v_code_2977_);
lean_dec_ref_known(v_alt_2959_, 2);
v___x_2978_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2957_, v_f_2958_, v_code_2977_);
return v___x_2978_;
}
default: 
{
lean_object* v_code_2979_; lean_object* v___x_2980_; 
v_code_2979_ = lean_ctor_get(v_alt_2959_, 0);
lean_inc_ref(v_code_2979_);
lean_dec_ref_known(v_alt_2959_, 1);
v___x_2980_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2957_, v_f_2958_, v_code_2979_);
return v___x_2980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt(uint8_t v_pu_2982_){
_start:
{
lean_object* v___x_2983_; lean_object* v___f_2984_; lean_object* v___f_2985_; lean_object* v___x_2986_; 
v___x_2983_ = lean_box(v_pu_2982_);
v___f_2984_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed), 6, 1);
lean_closure_set(v___f_2984_, 0, v___x_2983_);
v___f_2985_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0));
v___x_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___f_2984_);
lean_ctor_set(v___x_2986_, 1, v___f_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___boxed(lean_object* v_pu_2987_){
_start:
{
uint8_t v_pu_boxed_2988_; lean_object* v_res_2989_; 
v_pu_boxed_2988_ = lean_unbox(v_pu_2987_);
v_res_2989_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt(v_pu_boxed_2988_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(lean_object* v_toPure_2992_, lean_object* v_____do__lift_2993_){
_start:
{
if (lean_obj_tag(v_____do__lift_2993_) == 0)
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_box(0);
v___x_2995_ = lean_apply_2(v_toPure_2992_, lean_box(0), v___x_2994_);
return v___x_2995_;
}
else
{
lean_object* v_val_2996_; uint8_t v___x_2997_; 
v_val_2996_ = lean_ctor_get(v_____do__lift_2993_, 0);
v___x_2997_ = lean_unbox(v_val_2996_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0));
v___x_2999_ = lean_apply_2(v_toPure_2992_, lean_box(0), v___x_2998_);
return v___x_2999_;
}
else
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = lean_box(0);
v___x_3001_ = lean_apply_2(v_toPure_2992_, lean_box(0), v___x_3000_);
return v___x_3001_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed(lean_object* v_toPure_3002_, lean_object* v_____do__lift_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(v_toPure_3002_, v_____do__lift_3003_);
lean_dec(v_____do__lift_3003_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(lean_object* v_toPure_3005_, uint8_t v_____do__lift_3006_){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3007_ = lean_box(v_____do__lift_3006_);
v___x_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
v___x_3009_ = lean_apply_2(v_toPure_3005_, lean_box(0), v___x_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed(lean_object* v_toPure_3010_, lean_object* v_____do__lift_3011_){
_start:
{
uint8_t v_____do__lift_371__boxed_3012_; lean_object* v_res_3013_; 
v_____do__lift_371__boxed_3012_ = lean_unbox(v_____do__lift_3011_);
v_res_3013_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(v_toPure_3010_, v_____do__lift_371__boxed_3012_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(lean_object* v_inst_3014_, lean_object* v_f_3015_, lean_object* v_fvar_3016_){
_start:
{
lean_object* v_toApplicative_3017_; lean_object* v_toBind_3018_; lean_object* v_toPure_3019_; lean_object* v___x_3020_; lean_object* v___f_3021_; lean_object* v___f_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_toApplicative_3017_ = lean_ctor_get(v_inst_3014_, 0);
lean_inc_ref(v_toApplicative_3017_);
v_toBind_3018_ = lean_ctor_get(v_inst_3014_, 1);
lean_inc_n(v_toBind_3018_, 2);
lean_dec_ref(v_inst_3014_);
v_toPure_3019_ = lean_ctor_get(v_toApplicative_3017_, 1);
lean_inc_n(v_toPure_3019_, 2);
lean_dec_ref(v_toApplicative_3017_);
v___x_3020_ = lean_apply_1(v_f_3015_, v_fvar_3016_);
v___f_3021_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3021_, 0, v_toPure_3019_);
v___f_3022_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3022_, 0, v_toPure_3019_);
v___x_3023_ = lean_apply_4(v_toBind_3018_, lean_box(0), lean_box(0), v___x_3020_, v___f_3022_);
v___x_3024_ = lean_apply_4(v_toBind_3018_, lean_box(0), lean_box(0), v___x_3023_, v___f_3021_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go(lean_object* v_m_3025_, lean_object* v_inst_3026_, lean_object* v_f_3027_, lean_object* v_fvar_3028_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(v_inst_3026_, v_f_3027_, v_fvar_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(lean_object* v_toPure_3030_, lean_object* v_____do__lift_3031_){
_start:
{
if (lean_obj_tag(v_____do__lift_3031_) == 0)
{
uint8_t v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3032_ = 1;
v___x_3033_ = lean_box(v___x_3032_);
v___x_3034_ = lean_apply_2(v_toPure_3030_, lean_box(0), v___x_3033_);
return v___x_3034_;
}
else
{
uint8_t v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3035_ = 0;
v___x_3036_ = lean_box(v___x_3035_);
v___x_3037_ = lean_apply_2(v_toPure_3030_, lean_box(0), v___x_3036_);
return v___x_3037_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed(lean_object* v_toPure_3038_, lean_object* v_____do__lift_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(v_toPure_3038_, v_____do__lift_3039_);
lean_dec(v_____do__lift_3039_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg(lean_object* v_inst_3041_, lean_object* v_inst_3042_, lean_object* v_f_3043_, lean_object* v_x_3044_){
_start:
{
lean_object* v_toApplicative_3045_; lean_object* v_toBind_3046_; lean_object* v_forFVarM_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3068_; 
v_toApplicative_3045_ = lean_ctor_get(v_inst_3041_, 0);
v_toBind_3046_ = lean_ctor_get(v_inst_3041_, 1);
lean_inc(v_toBind_3046_);
v_forFVarM_3047_ = lean_ctor_get(v_inst_3042_, 1);
v_isSharedCheck_3068_ = !lean_is_exclusive(v_inst_3042_);
if (v_isSharedCheck_3068_ == 0)
{
lean_object* v_unused_3069_; 
v_unused_3069_ = lean_ctor_get(v_inst_3042_, 0);
lean_dec(v_unused_3069_);
v___x_3049_ = v_inst_3042_;
v_isShared_3050_ = v_isSharedCheck_3068_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_forFVarM_3047_);
lean_dec(v_inst_3042_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3068_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___f_3051_; lean_object* v___f_3052_; lean_object* v___f_3053_; lean_object* v___f_3054_; lean_object* v___f_3055_; lean_object* v___x_3057_; 
lean_inc_ref_n(v_inst_3041_, 5);
v___f_3051_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3051_, 0, v_inst_3041_);
v___f_3052_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3052_, 0, v_inst_3041_);
v___f_3053_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3053_, 0, v_inst_3041_);
v___f_3054_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3054_, 0, v_inst_3041_);
v___f_3055_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3055_, 0, v_inst_3041_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 1, v___f_3052_);
lean_ctor_set(v___x_3049_, 0, v___f_3051_);
v___x_3057_ = v___x_3049_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___f_3051_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v___f_3052_);
v___x_3057_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v_toPure_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___f_3065_; lean_object* v___x_3066_; 
lean_inc_ref_n(v_inst_3041_, 2);
v___x_3058_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3058_, 0, lean_box(0));
lean_closure_set(v___x_3058_, 1, v_inst_3041_);
v___x_3059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3057_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
lean_ctor_set(v___x_3059_, 2, v___f_3053_);
lean_ctor_set(v___x_3059_, 3, v___f_3054_);
lean_ctor_set(v___x_3059_, 4, v___f_3055_);
v___x_3060_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3060_, 0, lean_box(0));
lean_closure_set(v___x_3060_, 1, v_inst_3041_);
v___x_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3059_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
v_toPure_3062_ = lean_ctor_get(v_toApplicative_3045_, 1);
lean_inc(v_toPure_3062_);
v___x_3063_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go), 4, 3);
lean_closure_set(v___x_3063_, 0, lean_box(0));
lean_closure_set(v___x_3063_, 1, v_inst_3041_);
lean_closure_set(v___x_3063_, 2, v_f_3043_);
v___x_3064_ = lean_apply_4(v_forFVarM_3047_, lean_box(0), v___x_3061_, v___x_3063_, v_x_3044_);
v___f_3065_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3065_, 0, v_toPure_3062_);
v___x_3066_ = lean_apply_4(v_toBind_3046_, lean_box(0), lean_box(0), v___x_3064_, v___f_3065_);
return v___x_3066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM(lean_object* v_m_3070_, lean_object* v_00_u03b1_3071_, lean_object* v_inst_3072_, lean_object* v_inst_3073_, lean_object* v_f_3074_, lean_object* v_x_3075_){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = l_Lean_Compiler_LCNF_anyFVarM___redArg(v_inst_3072_, v_inst_3073_, v_f_3074_, v_x_3075_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(lean_object* v_toPure_3077_, lean_object* v_____do__lift_3078_){
_start:
{
if (lean_obj_tag(v_____do__lift_3078_) == 0)
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = lean_box(0);
v___x_3080_ = lean_apply_2(v_toPure_3077_, lean_box(0), v___x_3079_);
return v___x_3080_;
}
else
{
lean_object* v_val_3081_; uint8_t v___x_3082_; 
v_val_3081_ = lean_ctor_get(v_____do__lift_3078_, 0);
v___x_3082_ = lean_unbox(v_val_3081_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = lean_box(0);
v___x_3084_ = lean_apply_2(v_toPure_3077_, lean_box(0), v___x_3083_);
return v___x_3084_;
}
else
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0));
v___x_3086_ = lean_apply_2(v_toPure_3077_, lean_box(0), v___x_3085_);
return v___x_3086_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed(lean_object* v_toPure_3087_, lean_object* v_____do__lift_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(v_toPure_3087_, v_____do__lift_3088_);
lean_dec(v_____do__lift_3088_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(lean_object* v_inst_3090_, lean_object* v_f_3091_, lean_object* v_fvar_3092_){
_start:
{
lean_object* v_toApplicative_3093_; lean_object* v_toBind_3094_; lean_object* v_toPure_3095_; lean_object* v___x_3096_; lean_object* v___f_3097_; lean_object* v___f_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v_toApplicative_3093_ = lean_ctor_get(v_inst_3090_, 0);
lean_inc_ref(v_toApplicative_3093_);
v_toBind_3094_ = lean_ctor_get(v_inst_3090_, 1);
lean_inc_n(v_toBind_3094_, 2);
lean_dec_ref(v_inst_3090_);
v_toPure_3095_ = lean_ctor_get(v_toApplicative_3093_, 1);
lean_inc_n(v_toPure_3095_, 2);
lean_dec_ref(v_toApplicative_3093_);
v___x_3096_ = lean_apply_1(v_f_3091_, v_fvar_3092_);
v___f_3097_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3097_, 0, v_toPure_3095_);
v___f_3098_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3098_, 0, v_toPure_3095_);
v___x_3099_ = lean_apply_4(v_toBind_3094_, lean_box(0), lean_box(0), v___x_3096_, v___f_3098_);
v___x_3100_ = lean_apply_4(v_toBind_3094_, lean_box(0), lean_box(0), v___x_3099_, v___f_3097_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go(lean_object* v_m_3101_, lean_object* v_inst_3102_, lean_object* v_f_3103_, lean_object* v_fvar_3104_){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(v_inst_3102_, v_f_3103_, v_fvar_3104_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(lean_object* v_toPure_3106_, lean_object* v_____do__lift_3107_){
_start:
{
if (lean_obj_tag(v_____do__lift_3107_) == 1)
{
uint8_t v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3108_ = 1;
v___x_3109_ = lean_box(v___x_3108_);
v___x_3110_ = lean_apply_2(v_toPure_3106_, lean_box(0), v___x_3109_);
return v___x_3110_;
}
else
{
uint8_t v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3111_ = 0;
v___x_3112_ = lean_box(v___x_3111_);
v___x_3113_ = lean_apply_2(v_toPure_3106_, lean_box(0), v___x_3112_);
return v___x_3113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed(lean_object* v_toPure_3114_, lean_object* v_____do__lift_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(v_toPure_3114_, v_____do__lift_3115_);
lean_dec(v_____do__lift_3115_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg(lean_object* v_inst_3117_, lean_object* v_inst_3118_, lean_object* v_f_3119_, lean_object* v_x_3120_){
_start:
{
lean_object* v_toApplicative_3121_; lean_object* v_toBind_3122_; lean_object* v_forFVarM_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3144_; 
v_toApplicative_3121_ = lean_ctor_get(v_inst_3117_, 0);
v_toBind_3122_ = lean_ctor_get(v_inst_3117_, 1);
lean_inc(v_toBind_3122_);
v_forFVarM_3123_ = lean_ctor_get(v_inst_3118_, 1);
v_isSharedCheck_3144_ = !lean_is_exclusive(v_inst_3118_);
if (v_isSharedCheck_3144_ == 0)
{
lean_object* v_unused_3145_; 
v_unused_3145_ = lean_ctor_get(v_inst_3118_, 0);
lean_dec(v_unused_3145_);
v___x_3125_ = v_inst_3118_;
v_isShared_3126_ = v_isSharedCheck_3144_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_forFVarM_3123_);
lean_dec(v_inst_3118_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3144_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___f_3127_; lean_object* v___f_3128_; lean_object* v___f_3129_; lean_object* v___f_3130_; lean_object* v___f_3131_; lean_object* v___x_3133_; 
lean_inc_ref_n(v_inst_3117_, 5);
v___f_3127_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3127_, 0, v_inst_3117_);
v___f_3128_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3128_, 0, v_inst_3117_);
v___f_3129_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3129_, 0, v_inst_3117_);
v___f_3130_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3130_, 0, v_inst_3117_);
v___f_3131_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3131_, 0, v_inst_3117_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 1, v___f_3128_);
lean_ctor_set(v___x_3125_, 0, v___f_3127_);
v___x_3133_ = v___x_3125_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___f_3127_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v___f_3128_);
v___x_3133_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v_toPure_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___f_3141_; lean_object* v___x_3142_; 
lean_inc_ref_n(v_inst_3117_, 2);
v___x_3134_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3134_, 0, lean_box(0));
lean_closure_set(v___x_3134_, 1, v_inst_3117_);
v___x_3135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3133_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
lean_ctor_set(v___x_3135_, 2, v___f_3129_);
lean_ctor_set(v___x_3135_, 3, v___f_3130_);
lean_ctor_set(v___x_3135_, 4, v___f_3131_);
v___x_3136_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3136_, 0, lean_box(0));
lean_closure_set(v___x_3136_, 1, v_inst_3117_);
v___x_3137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3135_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
v_toPure_3138_ = lean_ctor_get(v_toApplicative_3121_, 1);
lean_inc(v_toPure_3138_);
v___x_3139_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go), 4, 3);
lean_closure_set(v___x_3139_, 0, lean_box(0));
lean_closure_set(v___x_3139_, 1, v_inst_3117_);
lean_closure_set(v___x_3139_, 2, v_f_3119_);
v___x_3140_ = lean_apply_4(v_forFVarM_3123_, lean_box(0), v___x_3137_, v___x_3139_, v_x_3120_);
v___f_3141_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3141_, 0, v_toPure_3138_);
v___x_3142_ = lean_apply_4(v_toBind_3122_, lean_box(0), lean_box(0), v___x_3140_, v___f_3141_);
return v___x_3142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM(lean_object* v_m_3146_, lean_object* v_00_u03b1_3147_, lean_object* v_inst_3148_, lean_object* v_inst_3149_, lean_object* v_f_3150_, lean_object* v_x_3151_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lean_Compiler_LCNF_allFVarM___redArg(v_inst_3148_, v_inst_3149_, v_f_3150_, v_x_3151_);
return v___x_3152_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(lean_object* v_f_3153_, lean_object* v_x_3154_){
_start:
{
lean_object* v___x_3155_; uint8_t v___x_3156_; 
v___x_3155_ = lean_apply_1(v_f_3153_, v_x_3154_);
v___x_3156_ = lean_unbox(v___x_3155_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed(lean_object* v_f_3157_, lean_object* v_x_3158_){
_start:
{
uint8_t v_res_3159_; lean_object* v_r_3160_; 
v_res_3159_ = l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(v_f_3157_, v_x_3158_);
v_r_3160_ = lean_box(v_res_3159_);
return v_r_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg(lean_object* v_inst_3180_, lean_object* v_f_3181_, lean_object* v_x_3182_){
_start:
{
lean_object* v___f_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___f_3183_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3183_, 0, v_f_3181_);
v___x_3184_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9));
v___x_3185_ = l_Lean_Compiler_LCNF_anyFVarM___redArg(v___x_3184_, v_inst_3180_, v___f_3183_, v_x_3182_);
return v___x_3185_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar(lean_object* v_00_u03b1_3186_, lean_object* v_inst_3187_, lean_object* v_f_3188_, lean_object* v_x_3189_){
_start:
{
lean_object* v___x_3190_; uint8_t v___x_3191_; 
v___x_3190_ = l_Lean_Compiler_LCNF_anyFVar___redArg(v_inst_3187_, v_f_3188_, v_x_3189_);
v___x_3191_ = lean_unbox(v___x_3190_);
lean_dec(v___x_3190_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___boxed(lean_object* v_00_u03b1_3192_, lean_object* v_inst_3193_, lean_object* v_f_3194_, lean_object* v_x_3195_){
_start:
{
uint8_t v_res_3196_; lean_object* v_r_3197_; 
v_res_3196_ = l_Lean_Compiler_LCNF_anyFVar(v_00_u03b1_3192_, v_inst_3193_, v_f_3194_, v_x_3195_);
v_r_3197_ = lean_box(v_res_3196_);
return v_r_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___redArg(lean_object* v_inst_3198_, lean_object* v_f_3199_, lean_object* v_x_3200_){
_start:
{
lean_object* v___f_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___f_3201_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3201_, 0, v_f_3199_);
v___x_3202_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9));
v___x_3203_ = l_Lean_Compiler_LCNF_allFVarM___redArg(v___x_3202_, v_inst_3198_, v___f_3201_, v_x_3200_);
return v___x_3203_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar(lean_object* v_00_u03b1_3204_, lean_object* v_inst_3205_, lean_object* v_f_3206_, lean_object* v_x_3207_){
_start:
{
lean_object* v___x_3208_; uint8_t v___x_3209_; 
v___x_3208_ = l_Lean_Compiler_LCNF_allFVar___redArg(v_inst_3205_, v_f_3206_, v_x_3207_);
v___x_3209_ = lean_unbox(v___x_3208_);
lean_dec(v___x_3208_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___boxed(lean_object* v_00_u03b1_3210_, lean_object* v_inst_3211_, lean_object* v_f_3212_, lean_object* v_x_3213_){
_start:
{
uint8_t v_res_3214_; lean_object* v_r_3215_; 
v_res_3214_ = l_Lean_Compiler_LCNF_allFVar(v_00_u03b1_3210_, v_inst_3211_, v_f_3212_, v_x_3213_);
v_r_3215_ = lean_box(v_res_3214_);
return v_r_3215_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_FVarUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_FVarUtil(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_FVarUtil(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_FVarUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_FVarUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_FVarUtil(builtin);
}
#ifdef __cplusplus
}
#endif
