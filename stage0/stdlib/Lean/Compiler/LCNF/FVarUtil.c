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
uint8_t v_check_1973__boxed_1108_; uint8_t v_persistent_1974__boxed_1109_; lean_object* v_res_1110_; 
v_check_1973__boxed_1108_ = lean_unbox(v_check_1102_);
v_persistent_1974__boxed_1109_ = lean_unbox(v_persistent_1103_);
v_res_1110_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(v_fvarId_1099_, v_____do__lift_1100_, v_n_1101_, v_check_1973__boxed_1108_, v_persistent_1974__boxed_1109_, v_toPure_1104_, v_k_1105_, v_c_1106_, v_____do__lift_1107_);
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
size_t v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = lean_ptr_addr(v_objs_x3f_1301_);
v___x_1315_ = lean_usize_dec_eq(v___x_1314_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec_ref(v_c_1304_);
v___x_1316_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1316_, 0, v_____do__lift_1297_);
lean_ctor_set(v___x_1316_, 1, v_n_1298_);
lean_ctor_set(v___x_1316_, 2, v_objs_x3f_1301_);
lean_ctor_set(v___x_1316_, 3, v_____do__lift_1305_);
lean_ctor_set_uint8(v___x_1316_, sizeof(void*)*4, v_check_1299_);
lean_ctor_set_uint8(v___x_1316_, sizeof(void*)*4 + 1, v_persistent_1300_);
v___x_1317_ = lean_apply_2(v_toPure_1302_, lean_box(0), v___x_1316_);
return v___x_1317_;
}
else
{
size_t v___x_1318_; size_t v___x_1319_; uint8_t v___x_1320_; 
v___x_1318_ = lean_ptr_addr(v_k_1303_);
v___x_1319_ = lean_ptr_addr(v_____do__lift_1305_);
v___x_1320_ = lean_usize_dec_eq(v___x_1318_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec_ref(v_c_1304_);
v___x_1321_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1321_, 0, v_____do__lift_1297_);
lean_ctor_set(v___x_1321_, 1, v_n_1298_);
lean_ctor_set(v___x_1321_, 2, v_objs_x3f_1301_);
lean_ctor_set(v___x_1321_, 3, v_____do__lift_1305_);
lean_ctor_set_uint8(v___x_1321_, sizeof(void*)*4, v_check_1299_);
lean_ctor_set_uint8(v___x_1321_, sizeof(void*)*4 + 1, v_persistent_1300_);
v___x_1322_ = lean_apply_2(v_toPure_1302_, lean_box(0), v___x_1321_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; 
lean_dec_ref(v_____do__lift_1305_);
lean_dec(v_objs_x3f_1301_);
lean_dec(v_n_1298_);
lean_dec(v_____do__lift_1297_);
v___x_1323_ = lean_apply_2(v_toPure_1302_, lean_box(0), v_c_1304_);
return v___x_1323_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed(lean_object* v_fvarId_1324_, lean_object* v_____do__lift_1325_, lean_object* v_n_1326_, lean_object* v_check_1327_, lean_object* v_persistent_1328_, lean_object* v_objs_x3f_1329_, lean_object* v_toPure_1330_, lean_object* v_k_1331_, lean_object* v_c_1332_, lean_object* v_____do__lift_1333_){
_start:
{
uint8_t v_check_2275__boxed_1334_; uint8_t v_persistent_2276__boxed_1335_; lean_object* v_res_1336_; 
v_check_2275__boxed_1334_ = lean_unbox(v_check_1327_);
v_persistent_2276__boxed_1335_ = lean_unbox(v_persistent_1328_);
v_res_1336_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(v_fvarId_1324_, v_____do__lift_1325_, v_n_1326_, v_check_2275__boxed_1334_, v_persistent_2276__boxed_1335_, v_objs_x3f_1329_, v_toPure_1330_, v_k_1331_, v_c_1332_, v_____do__lift_1333_);
lean_dec_ref(v_k_1331_);
lean_dec(v_fvarId_1324_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(lean_object* v_k_1337_, lean_object* v_decl_1338_, lean_object* v_toPure_1339_, lean_object* v_decl_1340_, lean_object* v_c_1341_, lean_object* v_____do__lift_1342_){
_start:
{
size_t v___x_1343_; size_t v___x_1344_; uint8_t v___x_1345_; 
v___x_1343_ = lean_ptr_addr(v_k_1337_);
v___x_1344_ = lean_ptr_addr(v_____do__lift_1342_);
v___x_1345_ = lean_usize_dec_eq(v___x_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_dec_ref(v_c_1341_);
v___x_1346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1346_, 0, v_decl_1338_);
lean_ctor_set(v___x_1346_, 1, v_____do__lift_1342_);
v___x_1347_ = lean_apply_2(v_toPure_1339_, lean_box(0), v___x_1346_);
return v___x_1347_;
}
else
{
size_t v___x_1348_; size_t v___x_1349_; uint8_t v___x_1350_; 
v___x_1348_ = lean_ptr_addr(v_decl_1340_);
v___x_1349_ = lean_ptr_addr(v_decl_1338_);
v___x_1350_ = lean_usize_dec_eq(v___x_1348_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
lean_dec_ref(v_c_1341_);
v___x_1351_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1351_, 0, v_decl_1338_);
lean_ctor_set(v___x_1351_, 1, v_____do__lift_1342_);
v___x_1352_ = lean_apply_2(v_toPure_1339_, lean_box(0), v___x_1351_);
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; 
lean_dec_ref(v_____do__lift_1342_);
lean_dec_ref(v_decl_1338_);
v___x_1353_ = lean_apply_2(v_toPure_1339_, lean_box(0), v_c_1341_);
return v___x_1353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed(lean_object* v_k_1354_, lean_object* v_decl_1355_, lean_object* v_toPure_1356_, lean_object* v_decl_1357_, lean_object* v_c_1358_, lean_object* v_____do__lift_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(v_k_1354_, v_decl_1355_, v_toPure_1356_, v_decl_1357_, v_c_1358_, v_____do__lift_1359_);
lean_dec_ref(v_decl_1357_);
lean_dec_ref(v_k_1354_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(lean_object* v_k_1361_, lean_object* v_decl_1362_, lean_object* v_toPure_1363_, lean_object* v_decl_1364_, lean_object* v_c_1365_, lean_object* v_____do__lift_1366_){
_start:
{
size_t v___x_1367_; size_t v___x_1368_; uint8_t v___x_1369_; 
v___x_1367_ = lean_ptr_addr(v_k_1361_);
v___x_1368_ = lean_ptr_addr(v_____do__lift_1366_);
v___x_1369_ = lean_usize_dec_eq(v___x_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_dec_ref(v_c_1365_);
v___x_1370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1370_, 0, v_decl_1362_);
lean_ctor_set(v___x_1370_, 1, v_____do__lift_1366_);
v___x_1371_ = lean_apply_2(v_toPure_1363_, lean_box(0), v___x_1370_);
return v___x_1371_;
}
else
{
size_t v___x_1372_; size_t v___x_1373_; uint8_t v___x_1374_; 
v___x_1372_ = lean_ptr_addr(v_decl_1364_);
v___x_1373_ = lean_ptr_addr(v_decl_1362_);
v___x_1374_ = lean_usize_dec_eq(v___x_1372_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_dec_ref(v_c_1365_);
v___x_1375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1375_, 0, v_decl_1362_);
lean_ctor_set(v___x_1375_, 1, v_____do__lift_1366_);
v___x_1376_ = lean_apply_2(v_toPure_1363_, lean_box(0), v___x_1375_);
return v___x_1376_;
}
else
{
lean_object* v___x_1377_; 
lean_dec_ref(v_____do__lift_1366_);
lean_dec_ref(v_decl_1362_);
v___x_1377_ = lean_apply_2(v_toPure_1363_, lean_box(0), v_c_1365_);
return v___x_1377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed(lean_object* v_k_1378_, lean_object* v_decl_1379_, lean_object* v_toPure_1380_, lean_object* v_decl_1381_, lean_object* v_c_1382_, lean_object* v_____do__lift_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(v_k_1378_, v_decl_1379_, v_toPure_1380_, v_decl_1381_, v_c_1382_, v_____do__lift_1383_);
lean_dec_ref(v_decl_1381_);
lean_dec_ref(v_k_1378_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(lean_object* v_fvarId_1385_, lean_object* v_____do__lift_1386_, lean_object* v_i_1387_, lean_object* v_____do__lift_1388_, lean_object* v_toPure_1389_, lean_object* v_y_1390_, lean_object* v_k_1391_, lean_object* v_c_1392_, lean_object* v_____do__lift_1393_){
_start:
{
size_t v___x_1394_; size_t v___x_1395_; uint8_t v___x_1396_; 
v___x_1394_ = lean_ptr_addr(v_fvarId_1385_);
v___x_1395_ = lean_ptr_addr(v_____do__lift_1386_);
v___x_1396_ = lean_usize_dec_eq(v___x_1394_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_dec_ref(v_c_1392_);
v___x_1397_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1397_, 0, v_____do__lift_1386_);
lean_ctor_set(v___x_1397_, 1, v_i_1387_);
lean_ctor_set(v___x_1397_, 2, v_____do__lift_1388_);
lean_ctor_set(v___x_1397_, 3, v_____do__lift_1393_);
v___x_1398_ = lean_apply_2(v_toPure_1389_, lean_box(0), v___x_1397_);
return v___x_1398_;
}
else
{
uint8_t v___x_1399_; 
v___x_1399_ = lean_nat_dec_eq(v_i_1387_, v_i_1387_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_dec_ref(v_c_1392_);
v___x_1400_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1400_, 0, v_____do__lift_1386_);
lean_ctor_set(v___x_1400_, 1, v_i_1387_);
lean_ctor_set(v___x_1400_, 2, v_____do__lift_1388_);
lean_ctor_set(v___x_1400_, 3, v_____do__lift_1393_);
v___x_1401_ = lean_apply_2(v_toPure_1389_, lean_box(0), v___x_1400_);
return v___x_1401_;
}
else
{
size_t v___x_1402_; size_t v___x_1403_; uint8_t v___x_1404_; 
v___x_1402_ = lean_ptr_addr(v_y_1390_);
v___x_1403_ = lean_ptr_addr(v_____do__lift_1388_);
v___x_1404_ = lean_usize_dec_eq(v___x_1402_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
lean_dec_ref(v_c_1392_);
v___x_1405_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1405_, 0, v_____do__lift_1386_);
lean_ctor_set(v___x_1405_, 1, v_i_1387_);
lean_ctor_set(v___x_1405_, 2, v_____do__lift_1388_);
lean_ctor_set(v___x_1405_, 3, v_____do__lift_1393_);
v___x_1406_ = lean_apply_2(v_toPure_1389_, lean_box(0), v___x_1405_);
return v___x_1406_;
}
else
{
size_t v___x_1407_; size_t v___x_1408_; uint8_t v___x_1409_; 
v___x_1407_ = lean_ptr_addr(v_k_1391_);
v___x_1408_ = lean_ptr_addr(v_____do__lift_1393_);
v___x_1409_ = lean_usize_dec_eq(v___x_1407_, v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_dec_ref(v_c_1392_);
v___x_1410_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1410_, 0, v_____do__lift_1386_);
lean_ctor_set(v___x_1410_, 1, v_i_1387_);
lean_ctor_set(v___x_1410_, 2, v_____do__lift_1388_);
lean_ctor_set(v___x_1410_, 3, v_____do__lift_1393_);
v___x_1411_ = lean_apply_2(v_toPure_1389_, lean_box(0), v___x_1410_);
return v___x_1411_;
}
else
{
lean_object* v___x_1412_; 
lean_dec_ref(v_____do__lift_1393_);
lean_dec(v_____do__lift_1388_);
lean_dec(v_i_1387_);
lean_dec(v_____do__lift_1386_);
v___x_1412_ = lean_apply_2(v_toPure_1389_, lean_box(0), v_c_1392_);
return v___x_1412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed(lean_object* v_fvarId_1413_, lean_object* v_____do__lift_1414_, lean_object* v_i_1415_, lean_object* v_____do__lift_1416_, lean_object* v_toPure_1417_, lean_object* v_y_1418_, lean_object* v_k_1419_, lean_object* v_c_1420_, lean_object* v_____do__lift_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(v_fvarId_1413_, v_____do__lift_1414_, v_i_1415_, v_____do__lift_1416_, v_toPure_1417_, v_y_1418_, v_k_1419_, v_c_1420_, v_____do__lift_1421_);
lean_dec_ref(v_k_1419_);
lean_dec(v_y_1418_);
lean_dec(v_fvarId_1413_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(lean_object* v_fvarId_1423_, lean_object* v_____do__lift_1424_, lean_object* v_toPure_1425_, lean_object* v_k_1426_, lean_object* v_c_1427_, lean_object* v_____do__lift_1428_){
_start:
{
size_t v___x_1429_; size_t v___x_1430_; uint8_t v___x_1431_; 
v___x_1429_ = lean_ptr_addr(v_fvarId_1423_);
v___x_1430_ = lean_ptr_addr(v_____do__lift_1424_);
v___x_1431_ = lean_usize_dec_eq(v___x_1429_, v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec_ref(v_c_1427_);
v___x_1432_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_____do__lift_1424_);
lean_ctor_set(v___x_1432_, 1, v_____do__lift_1428_);
v___x_1433_ = lean_apply_2(v_toPure_1425_, lean_box(0), v___x_1432_);
return v___x_1433_;
}
else
{
size_t v___x_1434_; size_t v___x_1435_; uint8_t v___x_1436_; 
v___x_1434_ = lean_ptr_addr(v_k_1426_);
v___x_1435_ = lean_ptr_addr(v_____do__lift_1428_);
v___x_1436_ = lean_usize_dec_eq(v___x_1434_, v___x_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_dec_ref(v_c_1427_);
v___x_1437_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_1437_, 0, v_____do__lift_1424_);
lean_ctor_set(v___x_1437_, 1, v_____do__lift_1428_);
v___x_1438_ = lean_apply_2(v_toPure_1425_, lean_box(0), v___x_1437_);
return v___x_1438_;
}
else
{
lean_object* v___x_1439_; 
lean_dec_ref(v_____do__lift_1428_);
lean_dec(v_____do__lift_1424_);
v___x_1439_ = lean_apply_2(v_toPure_1425_, lean_box(0), v_c_1427_);
return v___x_1439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed(lean_object* v_fvarId_1440_, lean_object* v_____do__lift_1441_, lean_object* v_toPure_1442_, lean_object* v_k_1443_, lean_object* v_c_1444_, lean_object* v_____do__lift_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(v_fvarId_1440_, v_____do__lift_1441_, v_toPure_1442_, v_k_1443_, v_c_1444_, v_____do__lift_1445_);
lean_dec_ref(v_k_1443_);
lean_dec(v_fvarId_1440_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(lean_object* v_type_1447_, lean_object* v_toPure_1448_, lean_object* v_c_1449_, lean_object* v_____do__lift_1450_){
_start:
{
size_t v___x_1451_; size_t v___x_1452_; uint8_t v___x_1453_; 
v___x_1451_ = lean_ptr_addr(v_type_1447_);
v___x_1452_ = lean_ptr_addr(v_____do__lift_1450_);
v___x_1453_ = lean_usize_dec_eq(v___x_1451_, v___x_1452_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_dec_ref(v_c_1449_);
v___x_1454_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_____do__lift_1450_);
v___x_1455_ = lean_apply_2(v_toPure_1448_, lean_box(0), v___x_1454_);
return v___x_1455_;
}
else
{
lean_object* v___x_1456_; 
lean_dec_ref(v_____do__lift_1450_);
v___x_1456_ = lean_apply_2(v_toPure_1448_, lean_box(0), v_c_1449_);
return v___x_1456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed(lean_object* v_type_1457_, lean_object* v_toPure_1458_, lean_object* v_c_1459_, lean_object* v_____do__lift_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(v_type_1457_, v_toPure_1458_, v_c_1459_, v_____do__lift_1460_);
lean_dec_ref(v_type_1457_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(lean_object* v_k_1462_, lean_object* v_toPure_1463_, lean_object* v_decl_1464_, lean_object* v_c_1465_, uint8_t v_pu_1466_, lean_object* v_inst_1467_, lean_object* v_inst_1468_, lean_object* v_f_1469_, lean_object* v_toBind_1470_, lean_object* v_decl_1471_){
_start:
{
lean_object* v___f_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_inc_ref(v_k_1462_);
v___f_1472_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1472_, 0, v_k_1462_);
lean_closure_set(v___f_1472_, 1, v_decl_1471_);
lean_closure_set(v___f_1472_, 2, v_toPure_1463_);
lean_closure_set(v___f_1472_, 3, v_decl_1464_);
lean_closure_set(v___f_1472_, 4, v_c_1465_);
v___x_1473_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1466_, v_inst_1467_, v_inst_1468_, v_f_1469_, v_k_1462_);
v___x_1474_ = lean_apply_4(v_toBind_1470_, lean_box(0), lean_box(0), v___x_1473_, v___f_1472_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed(lean_object* v_k_1475_, lean_object* v_toPure_1476_, lean_object* v_decl_1477_, lean_object* v_c_1478_, lean_object* v_pu_1479_, lean_object* v_inst_1480_, lean_object* v_inst_1481_, lean_object* v_f_1482_, lean_object* v_toBind_1483_, lean_object* v_decl_1484_){
_start:
{
uint8_t v_pu_boxed_1485_; lean_object* v_res_1486_; 
v_pu_boxed_1485_ = lean_unbox(v_pu_1479_);
v_res_1486_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(v_k_1475_, v_toPure_1476_, v_decl_1477_, v_c_1478_, v_pu_boxed_1485_, v_inst_1480_, v_inst_1481_, v_f_1482_, v_toBind_1483_, v_decl_1484_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(lean_object* v_k_1487_, lean_object* v_toPure_1488_, lean_object* v_decl_1489_, lean_object* v_c_1490_, uint8_t v_pu_1491_, lean_object* v_inst_1492_, lean_object* v_inst_1493_, lean_object* v_f_1494_, lean_object* v_toBind_1495_, lean_object* v_decl_1496_){
_start:
{
lean_object* v___f_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_inc_ref(v_k_1487_);
v___f_1497_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_1497_, 0, v_k_1487_);
lean_closure_set(v___f_1497_, 1, v_decl_1496_);
lean_closure_set(v___f_1497_, 2, v_toPure_1488_);
lean_closure_set(v___f_1497_, 3, v_decl_1489_);
lean_closure_set(v___f_1497_, 4, v_c_1490_);
v___x_1498_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1491_, v_inst_1492_, v_inst_1493_, v_f_1494_, v_k_1487_);
v___x_1499_ = lean_apply_4(v_toBind_1495_, lean_box(0), lean_box(0), v___x_1498_, v___f_1497_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed(lean_object* v_k_1500_, lean_object* v_toPure_1501_, lean_object* v_decl_1502_, lean_object* v_c_1503_, lean_object* v_pu_1504_, lean_object* v_inst_1505_, lean_object* v_inst_1506_, lean_object* v_f_1507_, lean_object* v_toBind_1508_, lean_object* v_decl_1509_){
_start:
{
uint8_t v_pu_boxed_1510_; lean_object* v_res_1511_; 
v_pu_boxed_1510_ = lean_unbox(v_pu_1504_);
v_res_1511_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(v_k_1500_, v_toPure_1501_, v_decl_1502_, v_c_1503_, v_pu_boxed_1510_, v_inst_1505_, v_inst_1506_, v_f_1507_, v_toBind_1508_, v_decl_1509_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(uint8_t v_pu_1512_, lean_object* v_decl_1513_, lean_object* v_params_1514_, lean_object* v_inst_1515_, lean_object* v_toBind_1516_, lean_object* v___f_1517_, lean_object* v_inst_1518_, lean_object* v_f_1519_, lean_object* v_value_1520_, lean_object* v_____do__lift_1521_){
_start:
{
lean_object* v___x_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1522_ = lean_box(v_pu_1512_);
lean_inc(v_toBind_1516_);
lean_inc(v_inst_1515_);
v___f_1523_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_1523_, 0, v___x_1522_);
lean_closure_set(v___f_1523_, 1, v_decl_1513_);
lean_closure_set(v___f_1523_, 2, v_____do__lift_1521_);
lean_closure_set(v___f_1523_, 3, v_params_1514_);
lean_closure_set(v___f_1523_, 4, v_inst_1515_);
lean_closure_set(v___f_1523_, 5, v_toBind_1516_);
lean_closure_set(v___f_1523_, 6, v___f_1517_);
v___x_1524_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1512_, v_inst_1515_, v_inst_1518_, v_f_1519_, v_value_1520_);
v___x_1525_ = lean_apply_4(v_toBind_1516_, lean_box(0), lean_box(0), v___x_1524_, v___f_1523_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed(lean_object* v_pu_1526_, lean_object* v_decl_1527_, lean_object* v_params_1528_, lean_object* v_inst_1529_, lean_object* v_toBind_1530_, lean_object* v___f_1531_, lean_object* v_inst_1532_, lean_object* v_f_1533_, lean_object* v_value_1534_, lean_object* v_____do__lift_1535_){
_start:
{
uint8_t v_pu_boxed_1536_; lean_object* v_res_1537_; 
v_pu_boxed_1536_ = lean_unbox(v_pu_1526_);
v_res_1537_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(v_pu_boxed_1536_, v_decl_1527_, v_params_1528_, v_inst_1529_, v_toBind_1530_, v___f_1531_, v_inst_1532_, v_f_1533_, v_value_1534_, v_____do__lift_1535_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(uint8_t v_pu_1538_, lean_object* v_decl_1539_, lean_object* v_inst_1540_, lean_object* v_toBind_1541_, lean_object* v___f_1542_, lean_object* v_inst_1543_, lean_object* v_f_1544_, lean_object* v_value_1545_, lean_object* v_type_1546_, lean_object* v_params_1547_){
_start:
{
lean_object* v___x_1548_; lean_object* v___f_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1548_ = lean_box(v_pu_1538_);
lean_inc(v_f_1544_);
lean_inc_ref(v_inst_1543_);
lean_inc(v_toBind_1541_);
v___f_1549_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed), 10, 9);
lean_closure_set(v___f_1549_, 0, v___x_1548_);
lean_closure_set(v___f_1549_, 1, v_decl_1539_);
lean_closure_set(v___f_1549_, 2, v_params_1547_);
lean_closure_set(v___f_1549_, 3, v_inst_1540_);
lean_closure_set(v___f_1549_, 4, v_toBind_1541_);
lean_closure_set(v___f_1549_, 5, v___f_1542_);
lean_closure_set(v___f_1549_, 6, v_inst_1543_);
lean_closure_set(v___f_1549_, 7, v_f_1544_);
lean_closure_set(v___f_1549_, 8, v_value_1545_);
v___x_1550_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1543_, v_f_1544_, v_type_1546_);
v___x_1551_ = lean_apply_4(v_toBind_1541_, lean_box(0), lean_box(0), v___x_1550_, v___f_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed(lean_object* v_pu_1552_, lean_object* v_decl_1553_, lean_object* v_inst_1554_, lean_object* v_toBind_1555_, lean_object* v___f_1556_, lean_object* v_inst_1557_, lean_object* v_f_1558_, lean_object* v_value_1559_, lean_object* v_type_1560_, lean_object* v_params_1561_){
_start:
{
uint8_t v_pu_boxed_1562_; lean_object* v_res_1563_; 
v_pu_boxed_1562_ = lean_unbox(v_pu_1552_);
v_res_1563_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(v_pu_boxed_1562_, v_decl_1553_, v_inst_1554_, v_toBind_1555_, v___f_1556_, v_inst_1557_, v_f_1558_, v_value_1559_, v_type_1560_, v_params_1561_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(lean_object* v_k_1564_, lean_object* v_toPure_1565_, lean_object* v_decl_1566_, lean_object* v_c_1567_, uint8_t v_pu_1568_, lean_object* v_inst_1569_, lean_object* v_inst_1570_, lean_object* v_f_1571_, lean_object* v_toBind_1572_, lean_object* v_decl_1573_){
_start:
{
lean_object* v___f_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
lean_inc_ref(v_k_1564_);
v___f_1574_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_1574_, 0, v_k_1564_);
lean_closure_set(v___f_1574_, 1, v_decl_1573_);
lean_closure_set(v___f_1574_, 2, v_toPure_1565_);
lean_closure_set(v___f_1574_, 3, v_decl_1566_);
lean_closure_set(v___f_1574_, 4, v_c_1567_);
v___x_1575_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1568_, v_inst_1569_, v_inst_1570_, v_f_1571_, v_k_1564_);
v___x_1576_ = lean_apply_4(v_toBind_1572_, lean_box(0), lean_box(0), v___x_1575_, v___f_1574_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed(lean_object* v_k_1577_, lean_object* v_toPure_1578_, lean_object* v_decl_1579_, lean_object* v_c_1580_, lean_object* v_pu_1581_, lean_object* v_inst_1582_, lean_object* v_inst_1583_, lean_object* v_f_1584_, lean_object* v_toBind_1585_, lean_object* v_decl_1586_){
_start:
{
uint8_t v_pu_boxed_1587_; lean_object* v_res_1588_; 
v_pu_boxed_1587_ = lean_unbox(v_pu_1581_);
v_res_1588_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(v_k_1577_, v_toPure_1578_, v_decl_1579_, v_c_1580_, v_pu_boxed_1587_, v_inst_1582_, v_inst_1583_, v_f_1584_, v_toBind_1585_, v_decl_1586_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed(lean_object* v_pu_1589_, lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_f_1592_, lean_object* v_x_1593_){
_start:
{
uint8_t v_pu_boxed_1594_; lean_object* v_res_1595_; 
v_pu_boxed_1594_ = lean_unbox(v_pu_1589_);
v_res_1595_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(v_pu_boxed_1594_, v_inst_1590_, v_inst_1591_, v_f_1592_, v_x_1593_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(lean_object* v_fvarId_1596_, lean_object* v_____do__lift_1597_, lean_object* v_i_1598_, lean_object* v_toPure_1599_, lean_object* v_y_1600_, lean_object* v_k_1601_, lean_object* v_c_1602_, uint8_t v_pu_1603_, lean_object* v_inst_1604_, lean_object* v_inst_1605_, lean_object* v_f_1606_, lean_object* v_toBind_1607_, lean_object* v_____do__lift_1608_){
_start:
{
lean_object* v___f_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_inc_ref(v_k_1601_);
v___f_1609_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed), 9, 8);
lean_closure_set(v___f_1609_, 0, v_fvarId_1596_);
lean_closure_set(v___f_1609_, 1, v_____do__lift_1597_);
lean_closure_set(v___f_1609_, 2, v_i_1598_);
lean_closure_set(v___f_1609_, 3, v_____do__lift_1608_);
lean_closure_set(v___f_1609_, 4, v_toPure_1599_);
lean_closure_set(v___f_1609_, 5, v_y_1600_);
lean_closure_set(v___f_1609_, 6, v_k_1601_);
lean_closure_set(v___f_1609_, 7, v_c_1602_);
v___x_1610_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1603_, v_inst_1604_, v_inst_1605_, v_f_1606_, v_k_1601_);
v___x_1611_ = lean_apply_4(v_toBind_1607_, lean_box(0), lean_box(0), v___x_1610_, v___f_1609_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed(lean_object* v_fvarId_1612_, lean_object* v_____do__lift_1613_, lean_object* v_i_1614_, lean_object* v_toPure_1615_, lean_object* v_y_1616_, lean_object* v_k_1617_, lean_object* v_c_1618_, lean_object* v_pu_1619_, lean_object* v_inst_1620_, lean_object* v_inst_1621_, lean_object* v_f_1622_, lean_object* v_toBind_1623_, lean_object* v_____do__lift_1624_){
_start:
{
uint8_t v_pu_boxed_1625_; lean_object* v_res_1626_; 
v_pu_boxed_1625_ = lean_unbox(v_pu_1619_);
v_res_1626_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(v_fvarId_1612_, v_____do__lift_1613_, v_i_1614_, v_toPure_1615_, v_y_1616_, v_k_1617_, v_c_1618_, v_pu_boxed_1625_, v_inst_1620_, v_inst_1621_, v_f_1622_, v_toBind_1623_, v_____do__lift_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(lean_object* v_fvarId_1627_, lean_object* v_i_1628_, lean_object* v_toPure_1629_, lean_object* v_y_1630_, lean_object* v_k_1631_, lean_object* v_c_1632_, uint8_t v_pu_1633_, lean_object* v_inst_1634_, lean_object* v_inst_1635_, lean_object* v_f_1636_, lean_object* v_toBind_1637_, lean_object* v_____do__lift_1638_){
_start:
{
lean_object* v___x_1639_; lean_object* v___f_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1639_ = lean_box(v_pu_1633_);
lean_inc(v_toBind_1637_);
lean_inc(v_f_1636_);
lean_inc_ref(v_inst_1635_);
lean_inc(v_y_1630_);
v___f_1640_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed), 13, 12);
lean_closure_set(v___f_1640_, 0, v_fvarId_1627_);
lean_closure_set(v___f_1640_, 1, v_____do__lift_1638_);
lean_closure_set(v___f_1640_, 2, v_i_1628_);
lean_closure_set(v___f_1640_, 3, v_toPure_1629_);
lean_closure_set(v___f_1640_, 4, v_y_1630_);
lean_closure_set(v___f_1640_, 5, v_k_1631_);
lean_closure_set(v___f_1640_, 6, v_c_1632_);
lean_closure_set(v___f_1640_, 7, v___x_1639_);
lean_closure_set(v___f_1640_, 8, v_inst_1634_);
lean_closure_set(v___f_1640_, 9, v_inst_1635_);
lean_closure_set(v___f_1640_, 10, v_f_1636_);
lean_closure_set(v___f_1640_, 11, v_toBind_1637_);
v___x_1641_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_1633_, v_inst_1635_, v_f_1636_, v_y_1630_);
v___x_1642_ = lean_apply_4(v_toBind_1637_, lean_box(0), lean_box(0), v___x_1641_, v___f_1640_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed(lean_object* v_fvarId_1643_, lean_object* v_i_1644_, lean_object* v_toPure_1645_, lean_object* v_y_1646_, lean_object* v_k_1647_, lean_object* v_c_1648_, lean_object* v_pu_1649_, lean_object* v_inst_1650_, lean_object* v_inst_1651_, lean_object* v_f_1652_, lean_object* v_toBind_1653_, lean_object* v_____do__lift_1654_){
_start:
{
uint8_t v_pu_boxed_1655_; lean_object* v_res_1656_; 
v_pu_boxed_1655_ = lean_unbox(v_pu_1649_);
v_res_1656_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(v_fvarId_1643_, v_i_1644_, v_toPure_1645_, v_y_1646_, v_k_1647_, v_c_1648_, v_pu_boxed_1655_, v_inst_1650_, v_inst_1651_, v_f_1652_, v_toBind_1653_, v_____do__lift_1654_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(lean_object* v_fvarId_1657_, lean_object* v_____do__lift_1658_, lean_object* v_i_1659_, lean_object* v_toPure_1660_, lean_object* v_y_1661_, lean_object* v_k_1662_, lean_object* v_c_1663_, uint8_t v_pu_1664_, lean_object* v_inst_1665_, lean_object* v_inst_1666_, lean_object* v_f_1667_, lean_object* v_toBind_1668_, lean_object* v_____do__lift_1669_){
_start:
{
lean_object* v___f_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_inc_ref(v_k_1662_);
v___f_1670_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed), 9, 8);
lean_closure_set(v___f_1670_, 0, v_fvarId_1657_);
lean_closure_set(v___f_1670_, 1, v_____do__lift_1658_);
lean_closure_set(v___f_1670_, 2, v_i_1659_);
lean_closure_set(v___f_1670_, 3, v_____do__lift_1669_);
lean_closure_set(v___f_1670_, 4, v_toPure_1660_);
lean_closure_set(v___f_1670_, 5, v_y_1661_);
lean_closure_set(v___f_1670_, 6, v_k_1662_);
lean_closure_set(v___f_1670_, 7, v_c_1663_);
v___x_1671_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1664_, v_inst_1665_, v_inst_1666_, v_f_1667_, v_k_1662_);
v___x_1672_ = lean_apply_4(v_toBind_1668_, lean_box(0), lean_box(0), v___x_1671_, v___f_1670_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed(lean_object* v_fvarId_1673_, lean_object* v_____do__lift_1674_, lean_object* v_i_1675_, lean_object* v_toPure_1676_, lean_object* v_y_1677_, lean_object* v_k_1678_, lean_object* v_c_1679_, lean_object* v_pu_1680_, lean_object* v_inst_1681_, lean_object* v_inst_1682_, lean_object* v_f_1683_, lean_object* v_toBind_1684_, lean_object* v_____do__lift_1685_){
_start:
{
uint8_t v_pu_boxed_1686_; lean_object* v_res_1687_; 
v_pu_boxed_1686_ = lean_unbox(v_pu_1680_);
v_res_1687_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(v_fvarId_1673_, v_____do__lift_1674_, v_i_1675_, v_toPure_1676_, v_y_1677_, v_k_1678_, v_c_1679_, v_pu_boxed_1686_, v_inst_1681_, v_inst_1682_, v_f_1683_, v_toBind_1684_, v_____do__lift_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(lean_object* v_fvarId_1688_, lean_object* v_i_1689_, lean_object* v_toPure_1690_, lean_object* v_y_1691_, lean_object* v_k_1692_, lean_object* v_c_1693_, uint8_t v_pu_1694_, lean_object* v_inst_1695_, lean_object* v_inst_1696_, lean_object* v_f_1697_, lean_object* v_toBind_1698_, lean_object* v_____do__lift_1699_){
_start:
{
lean_object* v___x_1700_; lean_object* v___f_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1700_ = lean_box(v_pu_1694_);
lean_inc(v_toBind_1698_);
lean_inc(v_f_1697_);
lean_inc(v_y_1691_);
v___f_1701_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed), 13, 12);
lean_closure_set(v___f_1701_, 0, v_fvarId_1688_);
lean_closure_set(v___f_1701_, 1, v_____do__lift_1699_);
lean_closure_set(v___f_1701_, 2, v_i_1689_);
lean_closure_set(v___f_1701_, 3, v_toPure_1690_);
lean_closure_set(v___f_1701_, 4, v_y_1691_);
lean_closure_set(v___f_1701_, 5, v_k_1692_);
lean_closure_set(v___f_1701_, 6, v_c_1693_);
lean_closure_set(v___f_1701_, 7, v___x_1700_);
lean_closure_set(v___f_1701_, 8, v_inst_1695_);
lean_closure_set(v___f_1701_, 9, v_inst_1696_);
lean_closure_set(v___f_1701_, 10, v_f_1697_);
lean_closure_set(v___f_1701_, 11, v_toBind_1698_);
v___x_1702_ = lean_apply_1(v_f_1697_, v_y_1691_);
v___x_1703_ = lean_apply_4(v_toBind_1698_, lean_box(0), lean_box(0), v___x_1702_, v___f_1701_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed(lean_object* v_fvarId_1704_, lean_object* v_i_1705_, lean_object* v_toPure_1706_, lean_object* v_y_1707_, lean_object* v_k_1708_, lean_object* v_c_1709_, lean_object* v_pu_1710_, lean_object* v_inst_1711_, lean_object* v_inst_1712_, lean_object* v_f_1713_, lean_object* v_toBind_1714_, lean_object* v_____do__lift_1715_){
_start:
{
uint8_t v_pu_boxed_1716_; lean_object* v_res_1717_; 
v_pu_boxed_1716_ = lean_unbox(v_pu_1710_);
v_res_1717_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(v_fvarId_1704_, v_i_1705_, v_toPure_1706_, v_y_1707_, v_k_1708_, v_c_1709_, v_pu_boxed_1716_, v_inst_1711_, v_inst_1712_, v_f_1713_, v_toBind_1714_, v_____do__lift_1715_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(lean_object* v_fvarId_1718_, lean_object* v_____do__lift_1719_, lean_object* v_i_1720_, lean_object* v_offset_1721_, lean_object* v_____do__lift_1722_, lean_object* v_toPure_1723_, lean_object* v_y_1724_, lean_object* v_ty_1725_, lean_object* v_k_1726_, lean_object* v_c_1727_, uint8_t v_pu_1728_, lean_object* v_inst_1729_, lean_object* v_inst_1730_, lean_object* v_f_1731_, lean_object* v_toBind_1732_, lean_object* v_____do__lift_1733_){
_start:
{
lean_object* v___f_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
lean_inc_ref(v_k_1726_);
v___f_1734_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed), 12, 11);
lean_closure_set(v___f_1734_, 0, v_fvarId_1718_);
lean_closure_set(v___f_1734_, 1, v_____do__lift_1719_);
lean_closure_set(v___f_1734_, 2, v_i_1720_);
lean_closure_set(v___f_1734_, 3, v_offset_1721_);
lean_closure_set(v___f_1734_, 4, v_____do__lift_1722_);
lean_closure_set(v___f_1734_, 5, v_____do__lift_1733_);
lean_closure_set(v___f_1734_, 6, v_toPure_1723_);
lean_closure_set(v___f_1734_, 7, v_y_1724_);
lean_closure_set(v___f_1734_, 8, v_ty_1725_);
lean_closure_set(v___f_1734_, 9, v_k_1726_);
lean_closure_set(v___f_1734_, 10, v_c_1727_);
v___x_1735_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1728_, v_inst_1729_, v_inst_1730_, v_f_1731_, v_k_1726_);
v___x_1736_ = lean_apply_4(v_toBind_1732_, lean_box(0), lean_box(0), v___x_1735_, v___f_1734_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed(lean_object* v_fvarId_1737_, lean_object* v_____do__lift_1738_, lean_object* v_i_1739_, lean_object* v_offset_1740_, lean_object* v_____do__lift_1741_, lean_object* v_toPure_1742_, lean_object* v_y_1743_, lean_object* v_ty_1744_, lean_object* v_k_1745_, lean_object* v_c_1746_, lean_object* v_pu_1747_, lean_object* v_inst_1748_, lean_object* v_inst_1749_, lean_object* v_f_1750_, lean_object* v_toBind_1751_, lean_object* v_____do__lift_1752_){
_start:
{
uint8_t v_pu_boxed_1753_; lean_object* v_res_1754_; 
v_pu_boxed_1753_ = lean_unbox(v_pu_1747_);
v_res_1754_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(v_fvarId_1737_, v_____do__lift_1738_, v_i_1739_, v_offset_1740_, v_____do__lift_1741_, v_toPure_1742_, v_y_1743_, v_ty_1744_, v_k_1745_, v_c_1746_, v_pu_boxed_1753_, v_inst_1748_, v_inst_1749_, v_f_1750_, v_toBind_1751_, v_____do__lift_1752_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(lean_object* v_fvarId_1755_, lean_object* v_____do__lift_1756_, lean_object* v_i_1757_, lean_object* v_offset_1758_, lean_object* v_toPure_1759_, lean_object* v_y_1760_, lean_object* v_ty_1761_, lean_object* v_k_1762_, lean_object* v_c_1763_, uint8_t v_pu_1764_, lean_object* v_inst_1765_, lean_object* v_inst_1766_, lean_object* v_f_1767_, lean_object* v_toBind_1768_, lean_object* v_____do__lift_1769_){
_start:
{
lean_object* v___x_1770_; lean_object* v___f_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1770_ = lean_box(v_pu_1764_);
lean_inc(v_toBind_1768_);
lean_inc(v_f_1767_);
lean_inc_ref(v_inst_1766_);
lean_inc_ref(v_ty_1761_);
v___f_1771_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed), 16, 15);
lean_closure_set(v___f_1771_, 0, v_fvarId_1755_);
lean_closure_set(v___f_1771_, 1, v_____do__lift_1756_);
lean_closure_set(v___f_1771_, 2, v_i_1757_);
lean_closure_set(v___f_1771_, 3, v_offset_1758_);
lean_closure_set(v___f_1771_, 4, v_____do__lift_1769_);
lean_closure_set(v___f_1771_, 5, v_toPure_1759_);
lean_closure_set(v___f_1771_, 6, v_y_1760_);
lean_closure_set(v___f_1771_, 7, v_ty_1761_);
lean_closure_set(v___f_1771_, 8, v_k_1762_);
lean_closure_set(v___f_1771_, 9, v_c_1763_);
lean_closure_set(v___f_1771_, 10, v___x_1770_);
lean_closure_set(v___f_1771_, 11, v_inst_1765_);
lean_closure_set(v___f_1771_, 12, v_inst_1766_);
lean_closure_set(v___f_1771_, 13, v_f_1767_);
lean_closure_set(v___f_1771_, 14, v_toBind_1768_);
v___x_1772_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1766_, v_f_1767_, v_ty_1761_);
v___x_1773_ = lean_apply_4(v_toBind_1768_, lean_box(0), lean_box(0), v___x_1772_, v___f_1771_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed(lean_object* v_fvarId_1774_, lean_object* v_____do__lift_1775_, lean_object* v_i_1776_, lean_object* v_offset_1777_, lean_object* v_toPure_1778_, lean_object* v_y_1779_, lean_object* v_ty_1780_, lean_object* v_k_1781_, lean_object* v_c_1782_, lean_object* v_pu_1783_, lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v_f_1786_, lean_object* v_toBind_1787_, lean_object* v_____do__lift_1788_){
_start:
{
uint8_t v_pu_boxed_1789_; lean_object* v_res_1790_; 
v_pu_boxed_1789_ = lean_unbox(v_pu_1783_);
v_res_1790_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(v_fvarId_1774_, v_____do__lift_1775_, v_i_1776_, v_offset_1777_, v_toPure_1778_, v_y_1779_, v_ty_1780_, v_k_1781_, v_c_1782_, v_pu_boxed_1789_, v_inst_1784_, v_inst_1785_, v_f_1786_, v_toBind_1787_, v_____do__lift_1788_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(lean_object* v_fvarId_1791_, lean_object* v_i_1792_, lean_object* v_offset_1793_, lean_object* v_toPure_1794_, lean_object* v_y_1795_, lean_object* v_ty_1796_, lean_object* v_k_1797_, lean_object* v_c_1798_, uint8_t v_pu_1799_, lean_object* v_inst_1800_, lean_object* v_inst_1801_, lean_object* v_f_1802_, lean_object* v_toBind_1803_, lean_object* v_____do__lift_1804_){
_start:
{
lean_object* v___x_1805_; lean_object* v___f_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1805_ = lean_box(v_pu_1799_);
lean_inc(v_toBind_1803_);
lean_inc(v_f_1802_);
lean_inc(v_y_1795_);
v___f_1806_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed), 15, 14);
lean_closure_set(v___f_1806_, 0, v_fvarId_1791_);
lean_closure_set(v___f_1806_, 1, v_____do__lift_1804_);
lean_closure_set(v___f_1806_, 2, v_i_1792_);
lean_closure_set(v___f_1806_, 3, v_offset_1793_);
lean_closure_set(v___f_1806_, 4, v_toPure_1794_);
lean_closure_set(v___f_1806_, 5, v_y_1795_);
lean_closure_set(v___f_1806_, 6, v_ty_1796_);
lean_closure_set(v___f_1806_, 7, v_k_1797_);
lean_closure_set(v___f_1806_, 8, v_c_1798_);
lean_closure_set(v___f_1806_, 9, v___x_1805_);
lean_closure_set(v___f_1806_, 10, v_inst_1800_);
lean_closure_set(v___f_1806_, 11, v_inst_1801_);
lean_closure_set(v___f_1806_, 12, v_f_1802_);
lean_closure_set(v___f_1806_, 13, v_toBind_1803_);
v___x_1807_ = lean_apply_1(v_f_1802_, v_y_1795_);
v___x_1808_ = lean_apply_4(v_toBind_1803_, lean_box(0), lean_box(0), v___x_1807_, v___f_1806_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed(lean_object* v_fvarId_1809_, lean_object* v_i_1810_, lean_object* v_offset_1811_, lean_object* v_toPure_1812_, lean_object* v_y_1813_, lean_object* v_ty_1814_, lean_object* v_k_1815_, lean_object* v_c_1816_, lean_object* v_pu_1817_, lean_object* v_inst_1818_, lean_object* v_inst_1819_, lean_object* v_f_1820_, lean_object* v_toBind_1821_, lean_object* v_____do__lift_1822_){
_start:
{
uint8_t v_pu_boxed_1823_; lean_object* v_res_1824_; 
v_pu_boxed_1823_ = lean_unbox(v_pu_1817_);
v_res_1824_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(v_fvarId_1809_, v_i_1810_, v_offset_1811_, v_toPure_1812_, v_y_1813_, v_ty_1814_, v_k_1815_, v_c_1816_, v_pu_boxed_1823_, v_inst_1818_, v_inst_1819_, v_f_1820_, v_toBind_1821_, v_____do__lift_1822_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(lean_object* v_fvarId_1825_, lean_object* v_cidx_1826_, lean_object* v_toPure_1827_, lean_object* v_k_1828_, lean_object* v_c_1829_, uint8_t v_pu_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_f_1833_, lean_object* v_toBind_1834_, lean_object* v_____do__lift_1835_){
_start:
{
lean_object* v___f_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_inc_ref(v_k_1828_);
v___f_1836_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27___boxed), 7, 6);
lean_closure_set(v___f_1836_, 0, v_fvarId_1825_);
lean_closure_set(v___f_1836_, 1, v_____do__lift_1835_);
lean_closure_set(v___f_1836_, 2, v_cidx_1826_);
lean_closure_set(v___f_1836_, 3, v_toPure_1827_);
lean_closure_set(v___f_1836_, 4, v_k_1828_);
lean_closure_set(v___f_1836_, 5, v_c_1829_);
v___x_1837_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1830_, v_inst_1831_, v_inst_1832_, v_f_1833_, v_k_1828_);
v___x_1838_ = lean_apply_4(v_toBind_1834_, lean_box(0), lean_box(0), v___x_1837_, v___f_1836_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed(lean_object* v_fvarId_1839_, lean_object* v_cidx_1840_, lean_object* v_toPure_1841_, lean_object* v_k_1842_, lean_object* v_c_1843_, lean_object* v_pu_1844_, lean_object* v_inst_1845_, lean_object* v_inst_1846_, lean_object* v_f_1847_, lean_object* v_toBind_1848_, lean_object* v_____do__lift_1849_){
_start:
{
uint8_t v_pu_boxed_1850_; lean_object* v_res_1851_; 
v_pu_boxed_1850_ = lean_unbox(v_pu_1844_);
v_res_1851_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(v_fvarId_1839_, v_cidx_1840_, v_toPure_1841_, v_k_1842_, v_c_1843_, v_pu_boxed_1850_, v_inst_1845_, v_inst_1846_, v_f_1847_, v_toBind_1848_, v_____do__lift_1849_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(lean_object* v_fvarId_1852_, lean_object* v_n_1853_, uint8_t v_check_1854_, uint8_t v_persistent_1855_, lean_object* v_toPure_1856_, lean_object* v_k_1857_, lean_object* v_c_1858_, uint8_t v_pu_1859_, lean_object* v_inst_1860_, lean_object* v_inst_1861_, lean_object* v_f_1862_, lean_object* v_toBind_1863_, lean_object* v_____do__lift_1864_){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___f_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1865_ = lean_box(v_check_1854_);
v___x_1866_ = lean_box(v_persistent_1855_);
lean_inc_ref(v_k_1857_);
v___f_1867_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29___boxed), 9, 8);
lean_closure_set(v___f_1867_, 0, v_fvarId_1852_);
lean_closure_set(v___f_1867_, 1, v_____do__lift_1864_);
lean_closure_set(v___f_1867_, 2, v_n_1853_);
lean_closure_set(v___f_1867_, 3, v___x_1865_);
lean_closure_set(v___f_1867_, 4, v___x_1866_);
lean_closure_set(v___f_1867_, 5, v_toPure_1856_);
lean_closure_set(v___f_1867_, 6, v_k_1857_);
lean_closure_set(v___f_1867_, 7, v_c_1858_);
v___x_1868_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1859_, v_inst_1860_, v_inst_1861_, v_f_1862_, v_k_1857_);
v___x_1869_ = lean_apply_4(v_toBind_1863_, lean_box(0), lean_box(0), v___x_1868_, v___f_1867_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed(lean_object* v_fvarId_1870_, lean_object* v_n_1871_, lean_object* v_check_1872_, lean_object* v_persistent_1873_, lean_object* v_toPure_1874_, lean_object* v_k_1875_, lean_object* v_c_1876_, lean_object* v_pu_1877_, lean_object* v_inst_1878_, lean_object* v_inst_1879_, lean_object* v_f_1880_, lean_object* v_toBind_1881_, lean_object* v_____do__lift_1882_){
_start:
{
uint8_t v_check_2616__boxed_1883_; uint8_t v_persistent_2617__boxed_1884_; uint8_t v_pu_boxed_1885_; lean_object* v_res_1886_; 
v_check_2616__boxed_1883_ = lean_unbox(v_check_1872_);
v_persistent_2617__boxed_1884_ = lean_unbox(v_persistent_1873_);
v_pu_boxed_1885_ = lean_unbox(v_pu_1877_);
v_res_1886_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(v_fvarId_1870_, v_n_1871_, v_check_2616__boxed_1883_, v_persistent_2617__boxed_1884_, v_toPure_1874_, v_k_1875_, v_c_1876_, v_pu_boxed_1885_, v_inst_1878_, v_inst_1879_, v_f_1880_, v_toBind_1881_, v_____do__lift_1882_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(lean_object* v_fvarId_1887_, lean_object* v_n_1888_, uint8_t v_check_1889_, uint8_t v_persistent_1890_, lean_object* v_objs_x3f_1891_, lean_object* v_toPure_1892_, lean_object* v_k_1893_, lean_object* v_c_1894_, uint8_t v_pu_1895_, lean_object* v_inst_1896_, lean_object* v_inst_1897_, lean_object* v_f_1898_, lean_object* v_toBind_1899_, lean_object* v_____do__lift_1900_){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___f_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1901_ = lean_box(v_check_1889_);
v___x_1902_ = lean_box(v_persistent_1890_);
lean_inc_ref(v_k_1893_);
v___f_1903_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed), 10, 9);
lean_closure_set(v___f_1903_, 0, v_fvarId_1887_);
lean_closure_set(v___f_1903_, 1, v_____do__lift_1900_);
lean_closure_set(v___f_1903_, 2, v_n_1888_);
lean_closure_set(v___f_1903_, 3, v___x_1901_);
lean_closure_set(v___f_1903_, 4, v___x_1902_);
lean_closure_set(v___f_1903_, 5, v_objs_x3f_1891_);
lean_closure_set(v___f_1903_, 6, v_toPure_1892_);
lean_closure_set(v___f_1903_, 7, v_k_1893_);
lean_closure_set(v___f_1903_, 8, v_c_1894_);
v___x_1904_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1895_, v_inst_1896_, v_inst_1897_, v_f_1898_, v_k_1893_);
v___x_1905_ = lean_apply_4(v_toBind_1899_, lean_box(0), lean_box(0), v___x_1904_, v___f_1903_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed(lean_object* v_fvarId_1906_, lean_object* v_n_1907_, lean_object* v_check_1908_, lean_object* v_persistent_1909_, lean_object* v_objs_x3f_1910_, lean_object* v_toPure_1911_, lean_object* v_k_1912_, lean_object* v_c_1913_, lean_object* v_pu_1914_, lean_object* v_inst_1915_, lean_object* v_inst_1916_, lean_object* v_f_1917_, lean_object* v_toBind_1918_, lean_object* v_____do__lift_1919_){
_start:
{
uint8_t v_check_2627__boxed_1920_; uint8_t v_persistent_2628__boxed_1921_; uint8_t v_pu_boxed_1922_; lean_object* v_res_1923_; 
v_check_2627__boxed_1920_ = lean_unbox(v_check_1908_);
v_persistent_2628__boxed_1921_ = lean_unbox(v_persistent_1909_);
v_pu_boxed_1922_ = lean_unbox(v_pu_1914_);
v_res_1923_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(v_fvarId_1906_, v_n_1907_, v_check_2627__boxed_1920_, v_persistent_2628__boxed_1921_, v_objs_x3f_1910_, v_toPure_1911_, v_k_1912_, v_c_1913_, v_pu_boxed_1922_, v_inst_1915_, v_inst_1916_, v_f_1917_, v_toBind_1918_, v_____do__lift_1919_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(lean_object* v_fvarId_1924_, lean_object* v_toPure_1925_, lean_object* v_k_1926_, lean_object* v_c_1927_, uint8_t v_pu_1928_, lean_object* v_inst_1929_, lean_object* v_inst_1930_, lean_object* v_f_1931_, lean_object* v_toBind_1932_, lean_object* v_____do__lift_1933_){
_start:
{
lean_object* v___f_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
lean_inc_ref(v_k_1926_);
v___f_1934_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed), 6, 5);
lean_closure_set(v___f_1934_, 0, v_fvarId_1924_);
lean_closure_set(v___f_1934_, 1, v_____do__lift_1933_);
lean_closure_set(v___f_1934_, 2, v_toPure_1925_);
lean_closure_set(v___f_1934_, 3, v_k_1926_);
lean_closure_set(v___f_1934_, 4, v_c_1927_);
v___x_1935_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1928_, v_inst_1929_, v_inst_1930_, v_f_1931_, v_k_1926_);
v___x_1936_ = lean_apply_4(v_toBind_1932_, lean_box(0), lean_box(0), v___x_1935_, v___f_1934_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed(lean_object* v_fvarId_1937_, lean_object* v_toPure_1938_, lean_object* v_k_1939_, lean_object* v_c_1940_, lean_object* v_pu_1941_, lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_f_1944_, lean_object* v_toBind_1945_, lean_object* v_____do__lift_1946_){
_start:
{
uint8_t v_pu_boxed_1947_; lean_object* v_res_1948_; 
v_pu_boxed_1947_ = lean_unbox(v_pu_1941_);
v_res_1948_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(v_fvarId_1937_, v_toPure_1938_, v_k_1939_, v_c_1940_, v_pu_boxed_1947_, v_inst_1942_, v_inst_1943_, v_f_1944_, v_toBind_1945_, v_____do__lift_1946_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(uint8_t v_pu_1949_, lean_object* v_inst_1950_, lean_object* v_inst_1951_, lean_object* v_f_1952_, lean_object* v_c_1953_){
_start:
{
switch(lean_obj_tag(v_c_1953_))
{
case 0:
{
lean_object* v_toApplicative_1954_; lean_object* v_toBind_1955_; lean_object* v_toPure_1956_; lean_object* v_decl_1957_; lean_object* v_k_1958_; lean_object* v___x_1959_; lean_object* v___f_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v_toApplicative_1954_ = lean_ctor_get(v_inst_1951_, 0);
v_toBind_1955_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc_n(v_toBind_1955_, 2);
v_toPure_1956_ = lean_ctor_get(v_toApplicative_1954_, 1);
v_decl_1957_ = lean_ctor_get(v_c_1953_, 0);
lean_inc_ref_n(v_decl_1957_, 2);
v_k_1958_ = lean_ctor_get(v_c_1953_, 1);
lean_inc_ref(v_k_1958_);
v___x_1959_ = lean_box(v_pu_1949_);
lean_inc(v_f_1952_);
lean_inc_ref(v_inst_1951_);
lean_inc(v_inst_1950_);
lean_inc(v_toPure_1956_);
v___f_1960_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_1960_, 0, v_k_1958_);
lean_closure_set(v___f_1960_, 1, v_toPure_1956_);
lean_closure_set(v___f_1960_, 2, v_decl_1957_);
lean_closure_set(v___f_1960_, 3, v_c_1953_);
lean_closure_set(v___f_1960_, 4, v___x_1959_);
lean_closure_set(v___f_1960_, 5, v_inst_1950_);
lean_closure_set(v___f_1960_, 6, v_inst_1951_);
lean_closure_set(v___f_1960_, 7, v_f_1952_);
lean_closure_set(v___f_1960_, 8, v_toBind_1955_);
v___x_1961_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_1949_, v_inst_1950_, v_inst_1951_, v_f_1952_, v_decl_1957_);
v___x_1962_ = lean_apply_4(v_toBind_1955_, lean_box(0), lean_box(0), v___x_1961_, v___f_1960_);
return v___x_1962_;
}
case 1:
{
lean_object* v_toApplicative_1963_; lean_object* v_decl_1964_; lean_object* v_toBind_1965_; lean_object* v_toPure_1966_; lean_object* v_k_1967_; lean_object* v_params_1968_; lean_object* v_type_1969_; lean_object* v_value_1970_; lean_object* v___x_1971_; lean_object* v___f_1972_; lean_object* v___x_1973_; lean_object* v___f_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; size_t v_sz_1977_; size_t v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v_toApplicative_1963_ = lean_ctor_get(v_inst_1951_, 0);
v_decl_1964_ = lean_ctor_get(v_c_1953_, 0);
lean_inc_ref_n(v_decl_1964_, 2);
v_toBind_1965_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc_n(v_toBind_1965_, 3);
v_toPure_1966_ = lean_ctor_get(v_toApplicative_1963_, 1);
v_k_1967_ = lean_ctor_get(v_c_1953_, 1);
lean_inc_ref(v_k_1967_);
v_params_1968_ = lean_ctor_get(v_decl_1964_, 2);
lean_inc_ref(v_params_1968_);
v_type_1969_ = lean_ctor_get(v_decl_1964_, 3);
lean_inc_ref(v_type_1969_);
v_value_1970_ = lean_ctor_get(v_decl_1964_, 4);
lean_inc_ref(v_value_1970_);
v___x_1971_ = lean_box(v_pu_1949_);
lean_inc_n(v_f_1952_, 2);
lean_inc_ref_n(v_inst_1951_, 3);
lean_inc_n(v_inst_1950_, 2);
lean_inc(v_toPure_1966_);
v___f_1972_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_1972_, 0, v_k_1967_);
lean_closure_set(v___f_1972_, 1, v_toPure_1966_);
lean_closure_set(v___f_1972_, 2, v_decl_1964_);
lean_closure_set(v___f_1972_, 3, v_c_1953_);
lean_closure_set(v___f_1972_, 4, v___x_1971_);
lean_closure_set(v___f_1972_, 5, v_inst_1950_);
lean_closure_set(v___f_1972_, 6, v_inst_1951_);
lean_closure_set(v___f_1972_, 7, v_f_1952_);
lean_closure_set(v___f_1972_, 8, v_toBind_1965_);
v___x_1973_ = lean_box(v_pu_1949_);
v___f_1974_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_1974_, 0, v___x_1973_);
lean_closure_set(v___f_1974_, 1, v_decl_1964_);
lean_closure_set(v___f_1974_, 2, v_inst_1950_);
lean_closure_set(v___f_1974_, 3, v_toBind_1965_);
lean_closure_set(v___f_1974_, 4, v___f_1972_);
lean_closure_set(v___f_1974_, 5, v_inst_1951_);
lean_closure_set(v___f_1974_, 6, v_f_1952_);
lean_closure_set(v___f_1974_, 7, v_value_1970_);
lean_closure_set(v___f_1974_, 8, v_type_1969_);
v___x_1975_ = lean_box(v_pu_1949_);
v___x_1976_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_1976_, 0, lean_box(0));
lean_closure_set(v___x_1976_, 1, v___x_1975_);
lean_closure_set(v___x_1976_, 2, v_inst_1950_);
lean_closure_set(v___x_1976_, 3, v_inst_1951_);
lean_closure_set(v___x_1976_, 4, v_f_1952_);
v_sz_1977_ = lean_array_size(v_params_1968_);
v___x_1978_ = ((size_t)0ULL);
v___x_1979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1951_, v___x_1976_, v_sz_1977_, v___x_1978_, v_params_1968_);
v___x_1980_ = lean_apply_4(v_toBind_1965_, lean_box(0), lean_box(0), v___x_1979_, v___f_1974_);
return v___x_1980_;
}
case 2:
{
lean_object* v_toApplicative_1981_; lean_object* v_decl_1982_; lean_object* v_toBind_1983_; lean_object* v_toPure_1984_; lean_object* v_k_1985_; lean_object* v_params_1986_; lean_object* v_type_1987_; lean_object* v_value_1988_; lean_object* v___x_1989_; lean_object* v___f_1990_; lean_object* v___x_1991_; lean_object* v___f_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; size_t v_sz_1995_; size_t v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v_toApplicative_1981_ = lean_ctor_get(v_inst_1951_, 0);
v_decl_1982_ = lean_ctor_get(v_c_1953_, 0);
lean_inc_ref_n(v_decl_1982_, 2);
v_toBind_1983_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc_n(v_toBind_1983_, 3);
v_toPure_1984_ = lean_ctor_get(v_toApplicative_1981_, 1);
v_k_1985_ = lean_ctor_get(v_c_1953_, 1);
lean_inc_ref(v_k_1985_);
v_params_1986_ = lean_ctor_get(v_decl_1982_, 2);
lean_inc_ref(v_params_1986_);
v_type_1987_ = lean_ctor_get(v_decl_1982_, 3);
lean_inc_ref(v_type_1987_);
v_value_1988_ = lean_ctor_get(v_decl_1982_, 4);
lean_inc_ref(v_value_1988_);
v___x_1989_ = lean_box(v_pu_1949_);
lean_inc_n(v_f_1952_, 2);
lean_inc_ref_n(v_inst_1951_, 3);
lean_inc_n(v_inst_1950_, 2);
lean_inc(v_toPure_1984_);
v___f_1990_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed), 10, 9);
lean_closure_set(v___f_1990_, 0, v_k_1985_);
lean_closure_set(v___f_1990_, 1, v_toPure_1984_);
lean_closure_set(v___f_1990_, 2, v_decl_1982_);
lean_closure_set(v___f_1990_, 3, v_c_1953_);
lean_closure_set(v___f_1990_, 4, v___x_1989_);
lean_closure_set(v___f_1990_, 5, v_inst_1950_);
lean_closure_set(v___f_1990_, 6, v_inst_1951_);
lean_closure_set(v___f_1990_, 7, v_f_1952_);
lean_closure_set(v___f_1990_, 8, v_toBind_1983_);
v___x_1991_ = lean_box(v_pu_1949_);
v___f_1992_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_1992_, 0, v___x_1991_);
lean_closure_set(v___f_1992_, 1, v_decl_1982_);
lean_closure_set(v___f_1992_, 2, v_inst_1950_);
lean_closure_set(v___f_1992_, 3, v_toBind_1983_);
lean_closure_set(v___f_1992_, 4, v___f_1990_);
lean_closure_set(v___f_1992_, 5, v_inst_1951_);
lean_closure_set(v___f_1992_, 6, v_f_1952_);
lean_closure_set(v___f_1992_, 7, v_value_1988_);
lean_closure_set(v___f_1992_, 8, v_type_1987_);
v___x_1993_ = lean_box(v_pu_1949_);
v___x_1994_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_1994_, 0, lean_box(0));
lean_closure_set(v___x_1994_, 1, v___x_1993_);
lean_closure_set(v___x_1994_, 2, v_inst_1950_);
lean_closure_set(v___x_1994_, 3, v_inst_1951_);
lean_closure_set(v___x_1994_, 4, v_f_1952_);
v_sz_1995_ = lean_array_size(v_params_1986_);
v___x_1996_ = ((size_t)0ULL);
v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1951_, v___x_1994_, v_sz_1995_, v___x_1996_, v_params_1986_);
v___x_1998_ = lean_apply_4(v_toBind_1983_, lean_box(0), lean_box(0), v___x_1997_, v___f_1992_);
return v___x_1998_;
}
case 3:
{
lean_object* v_toApplicative_1999_; lean_object* v_toBind_2000_; lean_object* v_toPure_2001_; lean_object* v_fvarId_2002_; lean_object* v_args_2003_; lean_object* v___x_2004_; lean_object* v___f_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v_toApplicative_1999_ = lean_ctor_get(v_inst_1951_, 0);
v_toBind_2000_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc_n(v_toBind_2000_, 2);
v_toPure_2001_ = lean_ctor_get(v_toApplicative_1999_, 1);
lean_inc(v_toPure_2001_);
v_fvarId_2002_ = lean_ctor_get(v_c_1953_, 0);
lean_inc_n(v_fvarId_2002_, 2);
v_args_2003_ = lean_ctor_get(v_c_1953_, 1);
lean_inc_ref(v_args_2003_);
v___x_2004_ = lean_box(v_pu_1949_);
lean_inc(v_f_1952_);
v___f_2005_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_2005_, 0, v_fvarId_2002_);
lean_closure_set(v___f_2005_, 1, v_toPure_2001_);
lean_closure_set(v___f_2005_, 2, v_args_2003_);
lean_closure_set(v___f_2005_, 3, v_c_1953_);
lean_closure_set(v___f_2005_, 4, v___x_2004_);
lean_closure_set(v___f_2005_, 5, v_inst_1950_);
lean_closure_set(v___f_2005_, 6, v_inst_1951_);
lean_closure_set(v___f_2005_, 7, v_f_1952_);
lean_closure_set(v___f_2005_, 8, v_toBind_2000_);
v___x_2006_ = lean_apply_1(v_f_1952_, v_fvarId_2002_);
v___x_2007_ = lean_apply_4(v_toBind_2000_, lean_box(0), lean_box(0), v___x_2006_, v___f_2005_);
return v___x_2007_;
}
case 4:
{
lean_object* v_toApplicative_2008_; lean_object* v_cases_2009_; lean_object* v_toBind_2010_; lean_object* v_toPure_2011_; lean_object* v_typeName_2012_; lean_object* v_resultType_2013_; lean_object* v_discr_2014_; lean_object* v_alts_2015_; lean_object* v___x_2016_; lean_object* v___f_2017_; lean_object* v___f_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v_toApplicative_2008_ = lean_ctor_get(v_inst_1951_, 0);
v_cases_2009_ = lean_ctor_get(v_c_1953_, 0);
v_toBind_2010_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc_n(v_toBind_2010_, 2);
v_toPure_2011_ = lean_ctor_get(v_toApplicative_2008_, 1);
v_typeName_2012_ = lean_ctor_get(v_cases_2009_, 0);
lean_inc(v_typeName_2012_);
v_resultType_2013_ = lean_ctor_get(v_cases_2009_, 1);
lean_inc_ref_n(v_resultType_2013_, 2);
v_discr_2014_ = lean_ctor_get(v_cases_2009_, 2);
lean_inc(v_discr_2014_);
v_alts_2015_ = lean_ctor_get(v_cases_2009_, 3);
lean_inc_ref(v_alts_2015_);
v___x_2016_ = lean_box(v_pu_1949_);
lean_inc_n(v_f_1952_, 2);
lean_inc_ref_n(v_inst_1951_, 2);
v___f_2017_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed), 5, 4);
lean_closure_set(v___f_2017_, 0, v___x_2016_);
lean_closure_set(v___f_2017_, 1, v_inst_1950_);
lean_closure_set(v___f_2017_, 2, v_inst_1951_);
lean_closure_set(v___f_2017_, 3, v_f_1952_);
lean_inc(v_toPure_2011_);
v___f_2018_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14), 11, 10);
lean_closure_set(v___f_2018_, 0, v_typeName_2012_);
lean_closure_set(v___f_2018_, 1, v_toPure_2011_);
lean_closure_set(v___f_2018_, 2, v_alts_2015_);
lean_closure_set(v___f_2018_, 3, v_resultType_2013_);
lean_closure_set(v___f_2018_, 4, v_discr_2014_);
lean_closure_set(v___f_2018_, 5, v_c_1953_);
lean_closure_set(v___f_2018_, 6, v_inst_1951_);
lean_closure_set(v___f_2018_, 7, v___f_2017_);
lean_closure_set(v___f_2018_, 8, v_toBind_2010_);
lean_closure_set(v___f_2018_, 9, v_f_1952_);
v___x_2019_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1951_, v_f_1952_, v_resultType_2013_);
v___x_2020_ = lean_apply_4(v_toBind_2010_, lean_box(0), lean_box(0), v___x_2019_, v___f_2018_);
return v___x_2020_;
}
case 5:
{
lean_object* v_toApplicative_2021_; lean_object* v_toBind_2022_; lean_object* v_toPure_2023_; lean_object* v_fvarId_2024_; lean_object* v___f_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_toApplicative_2021_ = lean_ctor_get(v_inst_1951_, 0);
lean_inc_ref(v_toApplicative_2021_);
lean_dec(v_inst_1950_);
v_toBind_2022_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc(v_toBind_2022_);
lean_dec_ref(v_inst_1951_);
v_toPure_2023_ = lean_ctor_get(v_toApplicative_2021_, 1);
lean_inc(v_toPure_2023_);
lean_dec_ref(v_toApplicative_2021_);
v_fvarId_2024_ = lean_ctor_get(v_c_1953_, 0);
lean_inc_n(v_fvarId_2024_, 2);
v___f_2025_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed), 4, 3);
lean_closure_set(v___f_2025_, 0, v_fvarId_2024_);
lean_closure_set(v___f_2025_, 1, v_toPure_2023_);
lean_closure_set(v___f_2025_, 2, v_c_1953_);
v___x_2026_ = lean_apply_1(v_f_1952_, v_fvarId_2024_);
v___x_2027_ = lean_apply_4(v_toBind_2022_, lean_box(0), lean_box(0), v___x_2026_, v___f_2025_);
return v___x_2027_;
}
case 6:
{
lean_object* v_toApplicative_2028_; lean_object* v_toBind_2029_; lean_object* v_toPure_2030_; lean_object* v_type_2031_; lean_object* v___f_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_toApplicative_2028_ = lean_ctor_get(v_inst_1951_, 0);
lean_dec(v_inst_1950_);
v_toBind_2029_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc(v_toBind_2029_);
v_toPure_2030_ = lean_ctor_get(v_toApplicative_2028_, 1);
v_type_2031_ = lean_ctor_get(v_c_1953_, 0);
lean_inc_ref_n(v_type_2031_, 2);
lean_inc(v_toPure_2030_);
v___f_2032_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed), 4, 3);
lean_closure_set(v___f_2032_, 0, v_type_2031_);
lean_closure_set(v___f_2032_, 1, v_toPure_2030_);
lean_closure_set(v___f_2032_, 2, v_c_1953_);
v___x_2033_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1951_, v_f_1952_, v_type_2031_);
v___x_2034_ = lean_apply_4(v_toBind_2029_, lean_box(0), lean_box(0), v___x_2033_, v___f_2032_);
return v___x_2034_;
}
case 7:
{
lean_object* v_toApplicative_2035_; lean_object* v_toBind_2036_; lean_object* v_toPure_2037_; lean_object* v_fvarId_2038_; lean_object* v_i_2039_; lean_object* v_y_2040_; lean_object* v_k_2041_; lean_object* v___x_2042_; lean_object* v___f_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_toApplicative_2035_ = lean_ctor_get(v_inst_1951_, 0);
v_toBind_2036_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc_n(v_toBind_2036_, 2);
v_toPure_2037_ = lean_ctor_get(v_toApplicative_2035_, 1);
lean_inc(v_toPure_2037_);
v_fvarId_2038_ = lean_ctor_get(v_c_1953_, 0);
lean_inc_n(v_fvarId_2038_, 2);
v_i_2039_ = lean_ctor_get(v_c_1953_, 1);
lean_inc(v_i_2039_);
v_y_2040_ = lean_ctor_get(v_c_1953_, 2);
lean_inc(v_y_2040_);
v_k_2041_ = lean_ctor_get(v_c_1953_, 3);
lean_inc_ref(v_k_2041_);
v___x_2042_ = lean_box(v_pu_1949_);
lean_inc(v_f_1952_);
v___f_2043_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed), 12, 11);
lean_closure_set(v___f_2043_, 0, v_fvarId_2038_);
lean_closure_set(v___f_2043_, 1, v_i_2039_);
lean_closure_set(v___f_2043_, 2, v_toPure_2037_);
lean_closure_set(v___f_2043_, 3, v_y_2040_);
lean_closure_set(v___f_2043_, 4, v_k_2041_);
lean_closure_set(v___f_2043_, 5, v_c_1953_);
lean_closure_set(v___f_2043_, 6, v___x_2042_);
lean_closure_set(v___f_2043_, 7, v_inst_1950_);
lean_closure_set(v___f_2043_, 8, v_inst_1951_);
lean_closure_set(v___f_2043_, 9, v_f_1952_);
lean_closure_set(v___f_2043_, 10, v_toBind_2036_);
v___x_2044_ = lean_apply_1(v_f_1952_, v_fvarId_2038_);
v___x_2045_ = lean_apply_4(v_toBind_2036_, lean_box(0), lean_box(0), v___x_2044_, v___f_2043_);
return v___x_2045_;
}
case 8:
{
lean_object* v_toApplicative_2046_; lean_object* v_toBind_2047_; lean_object* v_toPure_2048_; lean_object* v_fvarId_2049_; lean_object* v_i_2050_; lean_object* v_y_2051_; lean_object* v_k_2052_; lean_object* v___x_2053_; lean_object* v___f_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v_toApplicative_2046_ = lean_ctor_get(v_inst_1951_, 0);
v_toBind_2047_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc_n(v_toBind_2047_, 2);
v_toPure_2048_ = lean_ctor_get(v_toApplicative_2046_, 1);
lean_inc(v_toPure_2048_);
v_fvarId_2049_ = lean_ctor_get(v_c_1953_, 0);
lean_inc_n(v_fvarId_2049_, 2);
v_i_2050_ = lean_ctor_get(v_c_1953_, 1);
lean_inc(v_i_2050_);
v_y_2051_ = lean_ctor_get(v_c_1953_, 2);
lean_inc(v_y_2051_);
v_k_2052_ = lean_ctor_get(v_c_1953_, 3);
lean_inc_ref(v_k_2052_);
v___x_2053_ = lean_box(v_pu_1949_);
lean_inc(v_f_1952_);
v___f_2054_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed), 12, 11);
lean_closure_set(v___f_2054_, 0, v_fvarId_2049_);
lean_closure_set(v___f_2054_, 1, v_i_2050_);
lean_closure_set(v___f_2054_, 2, v_toPure_2048_);
lean_closure_set(v___f_2054_, 3, v_y_2051_);
lean_closure_set(v___f_2054_, 4, v_k_2052_);
lean_closure_set(v___f_2054_, 5, v_c_1953_);
lean_closure_set(v___f_2054_, 6, v___x_2053_);
lean_closure_set(v___f_2054_, 7, v_inst_1950_);
lean_closure_set(v___f_2054_, 8, v_inst_1951_);
lean_closure_set(v___f_2054_, 9, v_f_1952_);
lean_closure_set(v___f_2054_, 10, v_toBind_2047_);
v___x_2055_ = lean_apply_1(v_f_1952_, v_fvarId_2049_);
v___x_2056_ = lean_apply_4(v_toBind_2047_, lean_box(0), lean_box(0), v___x_2055_, v___f_2054_);
return v___x_2056_;
}
case 9:
{
lean_object* v_toApplicative_2057_; lean_object* v_toBind_2058_; lean_object* v_toPure_2059_; lean_object* v_fvarId_2060_; lean_object* v_i_2061_; lean_object* v_offset_2062_; lean_object* v_y_2063_; lean_object* v_ty_2064_; lean_object* v_k_2065_; lean_object* v___x_2066_; lean_object* v___f_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v_toApplicative_2057_ = lean_ctor_get(v_inst_1951_, 0);
v_toBind_2058_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc_n(v_toBind_2058_, 2);
v_toPure_2059_ = lean_ctor_get(v_toApplicative_2057_, 1);
lean_inc(v_toPure_2059_);
v_fvarId_2060_ = lean_ctor_get(v_c_1953_, 0);
lean_inc_n(v_fvarId_2060_, 2);
v_i_2061_ = lean_ctor_get(v_c_1953_, 1);
lean_inc(v_i_2061_);
v_offset_2062_ = lean_ctor_get(v_c_1953_, 2);
lean_inc(v_offset_2062_);
v_y_2063_ = lean_ctor_get(v_c_1953_, 3);
lean_inc(v_y_2063_);
v_ty_2064_ = lean_ctor_get(v_c_1953_, 4);
lean_inc_ref(v_ty_2064_);
v_k_2065_ = lean_ctor_get(v_c_1953_, 5);
lean_inc_ref(v_k_2065_);
v___x_2066_ = lean_box(v_pu_1949_);
lean_inc(v_f_1952_);
v___f_2067_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed), 14, 13);
lean_closure_set(v___f_2067_, 0, v_fvarId_2060_);
lean_closure_set(v___f_2067_, 1, v_i_2061_);
lean_closure_set(v___f_2067_, 2, v_offset_2062_);
lean_closure_set(v___f_2067_, 3, v_toPure_2059_);
lean_closure_set(v___f_2067_, 4, v_y_2063_);
lean_closure_set(v___f_2067_, 5, v_ty_2064_);
lean_closure_set(v___f_2067_, 6, v_k_2065_);
lean_closure_set(v___f_2067_, 7, v_c_1953_);
lean_closure_set(v___f_2067_, 8, v___x_2066_);
lean_closure_set(v___f_2067_, 9, v_inst_1950_);
lean_closure_set(v___f_2067_, 10, v_inst_1951_);
lean_closure_set(v___f_2067_, 11, v_f_1952_);
lean_closure_set(v___f_2067_, 12, v_toBind_2058_);
v___x_2068_ = lean_apply_1(v_f_1952_, v_fvarId_2060_);
v___x_2069_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v___x_2068_, v___f_2067_);
return v___x_2069_;
}
case 10:
{
lean_object* v_toApplicative_2070_; lean_object* v_toBind_2071_; lean_object* v_toPure_2072_; lean_object* v_fvarId_2073_; lean_object* v_cidx_2074_; lean_object* v_k_2075_; lean_object* v___x_2076_; lean_object* v___f_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v_toApplicative_2070_ = lean_ctor_get(v_inst_1951_, 0);
v_toBind_2071_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc_n(v_toBind_2071_, 2);
v_toPure_2072_ = lean_ctor_get(v_toApplicative_2070_, 1);
lean_inc(v_toPure_2072_);
v_fvarId_2073_ = lean_ctor_get(v_c_1953_, 0);
lean_inc_n(v_fvarId_2073_, 2);
v_cidx_2074_ = lean_ctor_get(v_c_1953_, 1);
lean_inc(v_cidx_2074_);
v_k_2075_ = lean_ctor_get(v_c_1953_, 2);
lean_inc_ref(v_k_2075_);
v___x_2076_ = lean_box(v_pu_1949_);
lean_inc(v_f_1952_);
v___f_2077_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed), 11, 10);
lean_closure_set(v___f_2077_, 0, v_fvarId_2073_);
lean_closure_set(v___f_2077_, 1, v_cidx_2074_);
lean_closure_set(v___f_2077_, 2, v_toPure_2072_);
lean_closure_set(v___f_2077_, 3, v_k_2075_);
lean_closure_set(v___f_2077_, 4, v_c_1953_);
lean_closure_set(v___f_2077_, 5, v___x_2076_);
lean_closure_set(v___f_2077_, 6, v_inst_1950_);
lean_closure_set(v___f_2077_, 7, v_inst_1951_);
lean_closure_set(v___f_2077_, 8, v_f_1952_);
lean_closure_set(v___f_2077_, 9, v_toBind_2071_);
v___x_2078_ = lean_apply_1(v_f_1952_, v_fvarId_2073_);
v___x_2079_ = lean_apply_4(v_toBind_2071_, lean_box(0), lean_box(0), v___x_2078_, v___f_2077_);
return v___x_2079_;
}
case 11:
{
lean_object* v_toApplicative_2080_; lean_object* v_toBind_2081_; lean_object* v_toPure_2082_; lean_object* v_fvarId_2083_; lean_object* v_n_2084_; uint8_t v_check_2085_; uint8_t v_persistent_2086_; lean_object* v_k_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___f_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v_toApplicative_2080_ = lean_ctor_get(v_inst_1951_, 0);
v_toBind_2081_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc_n(v_toBind_2081_, 2);
v_toPure_2082_ = lean_ctor_get(v_toApplicative_2080_, 1);
lean_inc(v_toPure_2082_);
v_fvarId_2083_ = lean_ctor_get(v_c_1953_, 0);
lean_inc_n(v_fvarId_2083_, 2);
v_n_2084_ = lean_ctor_get(v_c_1953_, 1);
lean_inc(v_n_2084_);
v_check_2085_ = lean_ctor_get_uint8(v_c_1953_, sizeof(void*)*3);
v_persistent_2086_ = lean_ctor_get_uint8(v_c_1953_, sizeof(void*)*3 + 1);
v_k_2087_ = lean_ctor_get(v_c_1953_, 2);
lean_inc_ref(v_k_2087_);
v___x_2088_ = lean_box(v_check_2085_);
v___x_2089_ = lean_box(v_persistent_2086_);
v___x_2090_ = lean_box(v_pu_1949_);
lean_inc(v_f_1952_);
v___f_2091_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed), 13, 12);
lean_closure_set(v___f_2091_, 0, v_fvarId_2083_);
lean_closure_set(v___f_2091_, 1, v_n_2084_);
lean_closure_set(v___f_2091_, 2, v___x_2088_);
lean_closure_set(v___f_2091_, 3, v___x_2089_);
lean_closure_set(v___f_2091_, 4, v_toPure_2082_);
lean_closure_set(v___f_2091_, 5, v_k_2087_);
lean_closure_set(v___f_2091_, 6, v_c_1953_);
lean_closure_set(v___f_2091_, 7, v___x_2090_);
lean_closure_set(v___f_2091_, 8, v_inst_1950_);
lean_closure_set(v___f_2091_, 9, v_inst_1951_);
lean_closure_set(v___f_2091_, 10, v_f_1952_);
lean_closure_set(v___f_2091_, 11, v_toBind_2081_);
v___x_2092_ = lean_apply_1(v_f_1952_, v_fvarId_2083_);
v___x_2093_ = lean_apply_4(v_toBind_2081_, lean_box(0), lean_box(0), v___x_2092_, v___f_2091_);
return v___x_2093_;
}
case 12:
{
lean_object* v_toApplicative_2094_; lean_object* v_toBind_2095_; lean_object* v_toPure_2096_; lean_object* v_fvarId_2097_; lean_object* v_n_2098_; uint8_t v_check_2099_; uint8_t v_persistent_2100_; lean_object* v_objs_x3f_2101_; lean_object* v_k_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___f_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v_toApplicative_2094_ = lean_ctor_get(v_inst_1951_, 0);
v_toBind_2095_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc_n(v_toBind_2095_, 2);
v_toPure_2096_ = lean_ctor_get(v_toApplicative_2094_, 1);
lean_inc(v_toPure_2096_);
v_fvarId_2097_ = lean_ctor_get(v_c_1953_, 0);
lean_inc_n(v_fvarId_2097_, 2);
v_n_2098_ = lean_ctor_get(v_c_1953_, 1);
lean_inc(v_n_2098_);
v_check_2099_ = lean_ctor_get_uint8(v_c_1953_, sizeof(void*)*4);
v_persistent_2100_ = lean_ctor_get_uint8(v_c_1953_, sizeof(void*)*4 + 1);
v_objs_x3f_2101_ = lean_ctor_get(v_c_1953_, 2);
lean_inc(v_objs_x3f_2101_);
v_k_2102_ = lean_ctor_get(v_c_1953_, 3);
lean_inc_ref(v_k_2102_);
v___x_2103_ = lean_box(v_check_2099_);
v___x_2104_ = lean_box(v_persistent_2100_);
v___x_2105_ = lean_box(v_pu_1949_);
lean_inc(v_f_1952_);
v___f_2106_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed), 14, 13);
lean_closure_set(v___f_2106_, 0, v_fvarId_2097_);
lean_closure_set(v___f_2106_, 1, v_n_2098_);
lean_closure_set(v___f_2106_, 2, v___x_2103_);
lean_closure_set(v___f_2106_, 3, v___x_2104_);
lean_closure_set(v___f_2106_, 4, v_objs_x3f_2101_);
lean_closure_set(v___f_2106_, 5, v_toPure_2096_);
lean_closure_set(v___f_2106_, 6, v_k_2102_);
lean_closure_set(v___f_2106_, 7, v_c_1953_);
lean_closure_set(v___f_2106_, 8, v___x_2105_);
lean_closure_set(v___f_2106_, 9, v_inst_1950_);
lean_closure_set(v___f_2106_, 10, v_inst_1951_);
lean_closure_set(v___f_2106_, 11, v_f_1952_);
lean_closure_set(v___f_2106_, 12, v_toBind_2095_);
v___x_2107_ = lean_apply_1(v_f_1952_, v_fvarId_2097_);
v___x_2108_ = lean_apply_4(v_toBind_2095_, lean_box(0), lean_box(0), v___x_2107_, v___f_2106_);
return v___x_2108_;
}
default: 
{
lean_object* v_toApplicative_2109_; lean_object* v_toBind_2110_; lean_object* v_toPure_2111_; lean_object* v_fvarId_2112_; lean_object* v_k_2113_; lean_object* v___x_2114_; lean_object* v___f_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v_toApplicative_2109_ = lean_ctor_get(v_inst_1951_, 0);
v_toBind_2110_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc_n(v_toBind_2110_, 2);
v_toPure_2111_ = lean_ctor_get(v_toApplicative_2109_, 1);
lean_inc(v_toPure_2111_);
v_fvarId_2112_ = lean_ctor_get(v_c_1953_, 0);
lean_inc_n(v_fvarId_2112_, 2);
v_k_2113_ = lean_ctor_get(v_c_1953_, 1);
lean_inc_ref(v_k_2113_);
v___x_2114_ = lean_box(v_pu_1949_);
lean_inc(v_f_1952_);
v___f_2115_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed), 10, 9);
lean_closure_set(v___f_2115_, 0, v_fvarId_2112_);
lean_closure_set(v___f_2115_, 1, v_toPure_2111_);
lean_closure_set(v___f_2115_, 2, v_k_2113_);
lean_closure_set(v___f_2115_, 3, v_c_1953_);
lean_closure_set(v___f_2115_, 4, v___x_2114_);
lean_closure_set(v___f_2115_, 5, v_inst_1950_);
lean_closure_set(v___f_2115_, 6, v_inst_1951_);
lean_closure_set(v___f_2115_, 7, v_f_1952_);
lean_closure_set(v___f_2115_, 8, v_toBind_2110_);
v___x_2116_ = lean_apply_1(v_f_1952_, v_fvarId_2112_);
v___x_2117_ = lean_apply_4(v_toBind_2110_, lean_box(0), lean_box(0), v___x_2116_, v___f_2115_);
return v___x_2117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed(lean_object* v_pu_2118_, lean_object* v_inst_2119_, lean_object* v_inst_2120_, lean_object* v_f_2121_, lean_object* v_c_2122_){
_start:
{
uint8_t v_pu_boxed_2123_; lean_object* v_res_2124_; 
v_pu_boxed_2123_ = lean_unbox(v_pu_2118_);
v_res_2124_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_boxed_2123_, v_inst_2119_, v_inst_2120_, v_f_2121_, v_c_2122_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(uint8_t v_pu_2125_, lean_object* v_inst_2126_, lean_object* v_inst_2127_, lean_object* v_f_2128_, lean_object* v_x_2129_){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2130_ = lean_box(v_pu_2125_);
lean_inc_ref(v_inst_2127_);
v___x_2131_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed), 5, 4);
lean_closure_set(v___x_2131_, 0, v___x_2130_);
lean_closure_set(v___x_2131_, 1, v_inst_2126_);
lean_closure_set(v___x_2131_, 2, v_inst_2127_);
lean_closure_set(v___x_2131_, 3, v_f_2128_);
v___x_2132_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg(v_inst_2127_, v_x_2129_, v___x_2131_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM(lean_object* v_m_2133_, uint8_t v_pu_2134_, lean_object* v_inst_2135_, lean_object* v_inst_2136_, lean_object* v_f_2137_, lean_object* v_c_2138_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2134_, v_inst_2135_, v_inst_2136_, v_f_2137_, v_c_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___boxed(lean_object* v_m_2140_, lean_object* v_pu_2141_, lean_object* v_inst_2142_, lean_object* v_inst_2143_, lean_object* v_f_2144_, lean_object* v_c_2145_){
_start:
{
uint8_t v_pu_boxed_2146_; lean_object* v_res_2147_; 
v_pu_boxed_2146_ = lean_unbox(v_pu_2141_);
v_res_2147_ = l_Lean_Compiler_LCNF_Code_mapFVarM(v_m_2140_, v_pu_boxed_2146_, v_inst_2142_, v_inst_2143_, v_f_2144_, v_c_2145_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1(lean_object* v_inst_2148_, lean_object* v_f_2149_, lean_object* v_type_2150_, lean_object* v_toBind_2151_, lean_object* v___f_2152_, lean_object* v_____r_2153_){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2148_, v_f_2149_, v_type_2150_);
v___x_2155_ = lean_apply_4(v_toBind_2151_, lean_box(0), lean_box(0), v___x_2154_, v___f_2152_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12(lean_object* v_inst_2156_, lean_object* v_f_2157_, lean_object* v_ty_2158_, lean_object* v_toBind_2159_, lean_object* v___f_2160_, lean_object* v_____r_2161_){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2156_, v_f_2157_, v_ty_2158_);
v___x_2163_ = lean_apply_4(v_toBind_2159_, lean_box(0), lean_box(0), v___x_2162_, v___f_2160_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4(lean_object* v_toApplicative_2164_, lean_object* v_args_2165_, lean_object* v_inst_2166_, lean_object* v___f_2167_, lean_object* v_____r_2168_){
_start:
{
lean_object* v_toPure_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
v_toPure_2169_ = lean_ctor_get(v_toApplicative_2164_, 1);
lean_inc(v_toPure_2169_);
lean_dec_ref(v_toApplicative_2164_);
v___x_2170_ = lean_unsigned_to_nat(0u);
v___x_2171_ = lean_array_get_size(v_args_2165_);
v___x_2172_ = lean_box(0);
v___x_2173_ = lean_nat_dec_lt(v___x_2170_, v___x_2171_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; 
lean_dec(v___f_2167_);
lean_dec_ref(v_inst_2166_);
lean_dec_ref(v_args_2165_);
v___x_2174_ = lean_apply_2(v_toPure_2169_, lean_box(0), v___x_2172_);
return v___x_2174_;
}
else
{
size_t v___x_2175_; size_t v___x_2176_; lean_object* v___x_2177_; 
lean_dec(v_toPure_2169_);
v___x_2175_ = ((size_t)0ULL);
v___x_2176_ = lean_usize_of_nat(v___x_2171_);
v___x_2177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2166_, v___f_2167_, v_args_2165_, v___x_2175_, v___x_2176_, v___x_2172_);
return v___x_2177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3(lean_object* v_inst_2178_, lean_object* v_f_2179_, lean_object* v_x_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_2178_, v_f_2179_, v___y_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10(lean_object* v_inst_2183_, lean_object* v_f_2184_, lean_object* v_y_2185_, lean_object* v_toBind_2186_, lean_object* v___f_2187_, lean_object* v_____r_2188_){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2183_, v_f_2184_, v_y_2185_);
v___x_2190_ = lean_apply_4(v_toBind_2186_, lean_box(0), lean_box(0), v___x_2189_, v___f_2187_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11(lean_object* v_f_2191_, lean_object* v_y_2192_, lean_object* v_toBind_2193_, lean_object* v___f_2194_, lean_object* v_____r_2195_){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = lean_apply_1(v_f_2191_, v_y_2192_);
v___x_2197_ = lean_apply_4(v_toBind_2193_, lean_box(0), lean_box(0), v___x_2196_, v___f_2194_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7(lean_object* v_f_2198_, lean_object* v_discr_2199_, lean_object* v_toBind_2200_, lean_object* v___f_2201_, lean_object* v_____r_2202_){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = lean_apply_1(v_f_2198_, v_discr_2199_);
v___x_2204_ = lean_apply_4(v_toBind_2200_, lean_box(0), lean_box(0), v___x_2203_, v___f_2201_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6(lean_object* v_toApplicative_2205_, lean_object* v_alts_2206_, lean_object* v_inst_2207_, lean_object* v___f_2208_, lean_object* v_____r_2209_){
_start:
{
lean_object* v_toPure_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; 
v_toPure_2210_ = lean_ctor_get(v_toApplicative_2205_, 1);
lean_inc(v_toPure_2210_);
lean_dec_ref(v_toApplicative_2205_);
v___x_2211_ = lean_unsigned_to_nat(0u);
v___x_2212_ = lean_array_get_size(v_alts_2206_);
v___x_2213_ = lean_box(0);
v___x_2214_ = lean_nat_dec_lt(v___x_2211_, v___x_2212_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; 
lean_dec(v___f_2208_);
lean_dec_ref(v_inst_2207_);
lean_dec_ref(v_alts_2206_);
v___x_2215_ = lean_apply_2(v_toPure_2210_, lean_box(0), v___x_2213_);
return v___x_2215_;
}
else
{
size_t v___x_2216_; size_t v___x_2217_; lean_object* v___x_2218_; 
lean_dec(v_toPure_2210_);
v___x_2216_ = ((size_t)0ULL);
v___x_2217_ = lean_usize_of_nat(v___x_2212_);
v___x_2218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2207_, v___f_2208_, v_alts_2206_, v___x_2216_, v___x_2217_, v___x_2213_);
return v___x_2218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8(lean_object* v_inst_2219_, lean_object* v_f_2220_, lean_object* v_x_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2219_, v_f_2220_, v___y_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5(lean_object* v_inst_2224_, lean_object* v_f_2225_, lean_object* v_x_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg), 3, 2);
lean_closure_set(v___x_2228_, 0, v_inst_2224_);
lean_closure_set(v___x_2228_, 1, v_f_2225_);
v___x_2229_ = l_Lean_Compiler_LCNF_Alt_forCodeM___redArg(v___y_2227_, v___x_2228_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2(lean_object* v_inst_2230_, lean_object* v_f_2231_, lean_object* v_value_2232_, lean_object* v_toBind_2233_, lean_object* v___f_2234_, lean_object* v_____r_2235_){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2230_, v_f_2231_, v_value_2232_);
v___x_2237_ = lean_apply_4(v_toBind_2233_, lean_box(0), lean_box(0), v___x_2236_, v___f_2234_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg(lean_object* v_inst_2238_, lean_object* v_f_2239_, lean_object* v_c_2240_){
_start:
{
switch(lean_obj_tag(v_c_2240_))
{
case 0:
{
lean_object* v_toBind_2241_; lean_object* v_decl_2242_; lean_object* v_k_2243_; lean_object* v___f_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_toBind_2241_ = lean_ctor_get(v_inst_2238_, 1);
lean_inc(v_toBind_2241_);
v_decl_2242_ = lean_ctor_get(v_c_2240_, 0);
lean_inc_ref(v_decl_2242_);
v_k_2243_ = lean_ctor_get(v_c_2240_, 1);
lean_inc_ref(v_k_2243_);
lean_dec_ref_known(v_c_2240_, 2);
lean_inc(v_f_2239_);
lean_inc_ref(v_inst_2238_);
v___f_2244_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2244_, 0, v_inst_2238_);
lean_closure_set(v___f_2244_, 1, v_f_2239_);
lean_closure_set(v___f_2244_, 2, v_k_2243_);
v___x_2245_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_2238_, v_f_2239_, v_decl_2242_);
v___x_2246_ = lean_apply_4(v_toBind_2241_, lean_box(0), lean_box(0), v___x_2245_, v___f_2244_);
return v___x_2246_;
}
case 3:
{
lean_object* v_toApplicative_2247_; lean_object* v_toBind_2248_; lean_object* v_fvarId_2249_; lean_object* v_args_2250_; lean_object* v___f_2251_; lean_object* v___f_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v_toApplicative_2247_ = lean_ctor_get(v_inst_2238_, 0);
lean_inc_ref(v_toApplicative_2247_);
v_toBind_2248_ = lean_ctor_get(v_inst_2238_, 1);
lean_inc(v_toBind_2248_);
v_fvarId_2249_ = lean_ctor_get(v_c_2240_, 0);
lean_inc(v_fvarId_2249_);
v_args_2250_ = lean_ctor_get(v_c_2240_, 1);
lean_inc_ref(v_args_2250_);
lean_dec_ref_known(v_c_2240_, 2);
lean_inc(v_f_2239_);
lean_inc_ref(v_inst_2238_);
v___f_2251_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8), 4, 2);
lean_closure_set(v___f_2251_, 0, v_inst_2238_);
lean_closure_set(v___f_2251_, 1, v_f_2239_);
v___f_2252_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2252_, 0, v_toApplicative_2247_);
lean_closure_set(v___f_2252_, 1, v_args_2250_);
lean_closure_set(v___f_2252_, 2, v_inst_2238_);
lean_closure_set(v___f_2252_, 3, v___f_2251_);
v___x_2253_ = lean_apply_1(v_f_2239_, v_fvarId_2249_);
v___x_2254_ = lean_apply_4(v_toBind_2248_, lean_box(0), lean_box(0), v___x_2253_, v___f_2252_);
return v___x_2254_;
}
case 4:
{
lean_object* v_cases_2255_; lean_object* v_toApplicative_2256_; lean_object* v_toBind_2257_; lean_object* v_resultType_2258_; lean_object* v_discr_2259_; lean_object* v_alts_2260_; lean_object* v___f_2261_; lean_object* v___f_2262_; lean_object* v___f_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v_cases_2255_ = lean_ctor_get(v_c_2240_, 0);
lean_inc_ref(v_cases_2255_);
lean_dec_ref_known(v_c_2240_, 1);
v_toApplicative_2256_ = lean_ctor_get(v_inst_2238_, 0);
v_toBind_2257_ = lean_ctor_get(v_inst_2238_, 1);
lean_inc_n(v_toBind_2257_, 2);
v_resultType_2258_ = lean_ctor_get(v_cases_2255_, 1);
lean_inc_ref(v_resultType_2258_);
v_discr_2259_ = lean_ctor_get(v_cases_2255_, 2);
lean_inc(v_discr_2259_);
v_alts_2260_ = lean_ctor_get(v_cases_2255_, 3);
lean_inc_ref(v_alts_2260_);
lean_dec_ref(v_cases_2255_);
lean_inc_n(v_f_2239_, 2);
lean_inc_ref_n(v_inst_2238_, 2);
v___f_2261_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5), 4, 2);
lean_closure_set(v___f_2261_, 0, v_inst_2238_);
lean_closure_set(v___f_2261_, 1, v_f_2239_);
lean_inc_ref(v_toApplicative_2256_);
v___f_2262_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6), 5, 4);
lean_closure_set(v___f_2262_, 0, v_toApplicative_2256_);
lean_closure_set(v___f_2262_, 1, v_alts_2260_);
lean_closure_set(v___f_2262_, 2, v_inst_2238_);
lean_closure_set(v___f_2262_, 3, v___f_2261_);
v___f_2263_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7), 5, 4);
lean_closure_set(v___f_2263_, 0, v_f_2239_);
lean_closure_set(v___f_2263_, 1, v_discr_2259_);
lean_closure_set(v___f_2263_, 2, v_toBind_2257_);
lean_closure_set(v___f_2263_, 3, v___f_2262_);
v___x_2264_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2238_, v_f_2239_, v_resultType_2258_);
v___x_2265_ = lean_apply_4(v_toBind_2257_, lean_box(0), lean_box(0), v___x_2264_, v___f_2263_);
return v___x_2265_;
}
case 5:
{
lean_object* v_fvarId_2266_; lean_object* v___x_2267_; 
lean_dec_ref(v_inst_2238_);
v_fvarId_2266_ = lean_ctor_get(v_c_2240_, 0);
lean_inc(v_fvarId_2266_);
lean_dec_ref_known(v_c_2240_, 1);
v___x_2267_ = lean_apply_1(v_f_2239_, v_fvarId_2266_);
return v___x_2267_;
}
case 6:
{
lean_object* v_type_2268_; lean_object* v___x_2269_; 
v_type_2268_ = lean_ctor_get(v_c_2240_, 0);
lean_inc_ref(v_type_2268_);
lean_dec_ref_known(v_c_2240_, 1);
v___x_2269_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2238_, v_f_2239_, v_type_2268_);
return v___x_2269_;
}
case 7:
{
lean_object* v_toBind_2270_; lean_object* v_fvarId_2271_; lean_object* v_y_2272_; lean_object* v_k_2273_; lean_object* v___f_2274_; lean_object* v___f_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v_toBind_2270_ = lean_ctor_get(v_inst_2238_, 1);
lean_inc_n(v_toBind_2270_, 2);
v_fvarId_2271_ = lean_ctor_get(v_c_2240_, 0);
lean_inc(v_fvarId_2271_);
v_y_2272_ = lean_ctor_get(v_c_2240_, 2);
lean_inc(v_y_2272_);
v_k_2273_ = lean_ctor_get(v_c_2240_, 3);
lean_inc_ref(v_k_2273_);
lean_dec_ref_known(v_c_2240_, 4);
lean_inc_n(v_f_2239_, 2);
lean_inc_ref(v_inst_2238_);
v___f_2274_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2274_, 0, v_inst_2238_);
lean_closure_set(v___f_2274_, 1, v_f_2239_);
lean_closure_set(v___f_2274_, 2, v_k_2273_);
v___f_2275_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10), 6, 5);
lean_closure_set(v___f_2275_, 0, v_inst_2238_);
lean_closure_set(v___f_2275_, 1, v_f_2239_);
lean_closure_set(v___f_2275_, 2, v_y_2272_);
lean_closure_set(v___f_2275_, 3, v_toBind_2270_);
lean_closure_set(v___f_2275_, 4, v___f_2274_);
v___x_2276_ = lean_apply_1(v_f_2239_, v_fvarId_2271_);
v___x_2277_ = lean_apply_4(v_toBind_2270_, lean_box(0), lean_box(0), v___x_2276_, v___f_2275_);
return v___x_2277_;
}
case 8:
{
lean_object* v_toBind_2278_; lean_object* v_fvarId_2279_; lean_object* v_y_2280_; lean_object* v_k_2281_; lean_object* v___f_2282_; lean_object* v___f_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v_toBind_2278_ = lean_ctor_get(v_inst_2238_, 1);
lean_inc_n(v_toBind_2278_, 2);
v_fvarId_2279_ = lean_ctor_get(v_c_2240_, 0);
lean_inc(v_fvarId_2279_);
v_y_2280_ = lean_ctor_get(v_c_2240_, 2);
lean_inc(v_y_2280_);
v_k_2281_ = lean_ctor_get(v_c_2240_, 3);
lean_inc_ref(v_k_2281_);
lean_dec_ref_known(v_c_2240_, 4);
lean_inc_n(v_f_2239_, 2);
v___f_2282_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2282_, 0, v_inst_2238_);
lean_closure_set(v___f_2282_, 1, v_f_2239_);
lean_closure_set(v___f_2282_, 2, v_k_2281_);
v___f_2283_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11), 5, 4);
lean_closure_set(v___f_2283_, 0, v_f_2239_);
lean_closure_set(v___f_2283_, 1, v_y_2280_);
lean_closure_set(v___f_2283_, 2, v_toBind_2278_);
lean_closure_set(v___f_2283_, 3, v___f_2282_);
v___x_2284_ = lean_apply_1(v_f_2239_, v_fvarId_2279_);
v___x_2285_ = lean_apply_4(v_toBind_2278_, lean_box(0), lean_box(0), v___x_2284_, v___f_2283_);
return v___x_2285_;
}
case 9:
{
lean_object* v_toBind_2286_; lean_object* v_fvarId_2287_; lean_object* v_y_2288_; lean_object* v_ty_2289_; lean_object* v_k_2290_; lean_object* v___f_2291_; lean_object* v___f_2292_; lean_object* v___f_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v_toBind_2286_ = lean_ctor_get(v_inst_2238_, 1);
lean_inc_n(v_toBind_2286_, 3);
v_fvarId_2287_ = lean_ctor_get(v_c_2240_, 0);
lean_inc(v_fvarId_2287_);
v_y_2288_ = lean_ctor_get(v_c_2240_, 3);
lean_inc(v_y_2288_);
v_ty_2289_ = lean_ctor_get(v_c_2240_, 4);
lean_inc_ref(v_ty_2289_);
v_k_2290_ = lean_ctor_get(v_c_2240_, 5);
lean_inc_ref(v_k_2290_);
lean_dec_ref_known(v_c_2240_, 6);
lean_inc_n(v_f_2239_, 3);
lean_inc_ref(v_inst_2238_);
v___f_2291_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2291_, 0, v_inst_2238_);
lean_closure_set(v___f_2291_, 1, v_f_2239_);
lean_closure_set(v___f_2291_, 2, v_k_2290_);
v___f_2292_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12), 6, 5);
lean_closure_set(v___f_2292_, 0, v_inst_2238_);
lean_closure_set(v___f_2292_, 1, v_f_2239_);
lean_closure_set(v___f_2292_, 2, v_ty_2289_);
lean_closure_set(v___f_2292_, 3, v_toBind_2286_);
lean_closure_set(v___f_2292_, 4, v___f_2291_);
v___f_2293_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11), 5, 4);
lean_closure_set(v___f_2293_, 0, v_f_2239_);
lean_closure_set(v___f_2293_, 1, v_y_2288_);
lean_closure_set(v___f_2293_, 2, v_toBind_2286_);
lean_closure_set(v___f_2293_, 3, v___f_2292_);
v___x_2294_ = lean_apply_1(v_f_2239_, v_fvarId_2287_);
v___x_2295_ = lean_apply_4(v_toBind_2286_, lean_box(0), lean_box(0), v___x_2294_, v___f_2293_);
return v___x_2295_;
}
case 10:
{
lean_object* v_toBind_2296_; lean_object* v_fvarId_2297_; lean_object* v_k_2298_; lean_object* v___f_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v_toBind_2296_ = lean_ctor_get(v_inst_2238_, 1);
lean_inc(v_toBind_2296_);
v_fvarId_2297_ = lean_ctor_get(v_c_2240_, 0);
lean_inc(v_fvarId_2297_);
v_k_2298_ = lean_ctor_get(v_c_2240_, 2);
lean_inc_ref(v_k_2298_);
lean_dec_ref_known(v_c_2240_, 3);
lean_inc(v_f_2239_);
v___f_2299_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2299_, 0, v_inst_2238_);
lean_closure_set(v___f_2299_, 1, v_f_2239_);
lean_closure_set(v___f_2299_, 2, v_k_2298_);
v___x_2300_ = lean_apply_1(v_f_2239_, v_fvarId_2297_);
v___x_2301_ = lean_apply_4(v_toBind_2296_, lean_box(0), lean_box(0), v___x_2300_, v___f_2299_);
return v___x_2301_;
}
case 11:
{
lean_object* v_toBind_2302_; lean_object* v_fvarId_2303_; lean_object* v_k_2304_; lean_object* v___f_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v_toBind_2302_ = lean_ctor_get(v_inst_2238_, 1);
lean_inc(v_toBind_2302_);
v_fvarId_2303_ = lean_ctor_get(v_c_2240_, 0);
lean_inc(v_fvarId_2303_);
v_k_2304_ = lean_ctor_get(v_c_2240_, 2);
lean_inc_ref(v_k_2304_);
lean_dec_ref_known(v_c_2240_, 3);
lean_inc(v_f_2239_);
v___f_2305_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2305_, 0, v_inst_2238_);
lean_closure_set(v___f_2305_, 1, v_f_2239_);
lean_closure_set(v___f_2305_, 2, v_k_2304_);
v___x_2306_ = lean_apply_1(v_f_2239_, v_fvarId_2303_);
v___x_2307_ = lean_apply_4(v_toBind_2302_, lean_box(0), lean_box(0), v___x_2306_, v___f_2305_);
return v___x_2307_;
}
case 12:
{
lean_object* v_toBind_2308_; lean_object* v_fvarId_2309_; lean_object* v_k_2310_; lean_object* v___f_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v_toBind_2308_ = lean_ctor_get(v_inst_2238_, 1);
lean_inc(v_toBind_2308_);
v_fvarId_2309_ = lean_ctor_get(v_c_2240_, 0);
lean_inc(v_fvarId_2309_);
v_k_2310_ = lean_ctor_get(v_c_2240_, 3);
lean_inc_ref(v_k_2310_);
lean_dec_ref_known(v_c_2240_, 4);
lean_inc(v_f_2239_);
v___f_2311_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2311_, 0, v_inst_2238_);
lean_closure_set(v___f_2311_, 1, v_f_2239_);
lean_closure_set(v___f_2311_, 2, v_k_2310_);
v___x_2312_ = lean_apply_1(v_f_2239_, v_fvarId_2309_);
v___x_2313_ = lean_apply_4(v_toBind_2308_, lean_box(0), lean_box(0), v___x_2312_, v___f_2311_);
return v___x_2313_;
}
case 13:
{
lean_object* v_toBind_2314_; lean_object* v_fvarId_2315_; lean_object* v_k_2316_; lean_object* v___f_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v_toBind_2314_ = lean_ctor_get(v_inst_2238_, 1);
lean_inc(v_toBind_2314_);
v_fvarId_2315_ = lean_ctor_get(v_c_2240_, 0);
lean_inc(v_fvarId_2315_);
v_k_2316_ = lean_ctor_get(v_c_2240_, 1);
lean_inc_ref(v_k_2316_);
lean_dec_ref_known(v_c_2240_, 2);
lean_inc(v_f_2239_);
v___f_2317_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2317_, 0, v_inst_2238_);
lean_closure_set(v___f_2317_, 1, v_f_2239_);
lean_closure_set(v___f_2317_, 2, v_k_2316_);
v___x_2318_ = lean_apply_1(v_f_2239_, v_fvarId_2315_);
v___x_2319_ = lean_apply_4(v_toBind_2314_, lean_box(0), lean_box(0), v___x_2318_, v___f_2317_);
return v___x_2319_;
}
default: 
{
lean_object* v_decl_2320_; lean_object* v_toApplicative_2321_; lean_object* v_toBind_2322_; lean_object* v_k_2323_; lean_object* v_params_2324_; lean_object* v_type_2325_; lean_object* v_value_2326_; lean_object* v_toPure_2327_; lean_object* v___f_2328_; lean_object* v___f_2329_; lean_object* v___f_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v_decl_2320_ = lean_ctor_get(v_c_2240_, 0);
lean_inc_ref(v_decl_2320_);
v_toApplicative_2321_ = lean_ctor_get(v_inst_2238_, 0);
v_toBind_2322_ = lean_ctor_get(v_inst_2238_, 1);
lean_inc_n(v_toBind_2322_, 3);
v_k_2323_ = lean_ctor_get(v_c_2240_, 1);
lean_inc_ref(v_k_2323_);
lean_dec_ref(v_c_2240_);
v_params_2324_ = lean_ctor_get(v_decl_2320_, 2);
lean_inc_ref(v_params_2324_);
v_type_2325_ = lean_ctor_get(v_decl_2320_, 3);
lean_inc_ref(v_type_2325_);
v_value_2326_ = lean_ctor_get(v_decl_2320_, 4);
lean_inc_ref(v_value_2326_);
lean_dec_ref(v_decl_2320_);
v_toPure_2327_ = lean_ctor_get(v_toApplicative_2321_, 1);
lean_inc_n(v_f_2239_, 3);
lean_inc_ref_n(v_inst_2238_, 3);
v___f_2328_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2328_, 0, v_inst_2238_);
lean_closure_set(v___f_2328_, 1, v_f_2239_);
lean_closure_set(v___f_2328_, 2, v_k_2323_);
v___f_2329_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2329_, 0, v_inst_2238_);
lean_closure_set(v___f_2329_, 1, v_f_2239_);
lean_closure_set(v___f_2329_, 2, v_value_2326_);
lean_closure_set(v___f_2329_, 3, v_toBind_2322_);
lean_closure_set(v___f_2329_, 4, v___f_2328_);
v___f_2330_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2330_, 0, v_inst_2238_);
lean_closure_set(v___f_2330_, 1, v_f_2239_);
lean_closure_set(v___f_2330_, 2, v_type_2325_);
lean_closure_set(v___f_2330_, 3, v_toBind_2322_);
lean_closure_set(v___f_2330_, 4, v___f_2329_);
v___x_2331_ = lean_unsigned_to_nat(0u);
v___x_2332_ = lean_array_get_size(v_params_2324_);
v___x_2333_ = lean_box(0);
v___x_2334_ = lean_nat_dec_lt(v___x_2331_, v___x_2332_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_inc(v_toPure_2327_);
lean_dec_ref(v_params_2324_);
lean_dec(v_f_2239_);
lean_dec_ref(v_inst_2238_);
v___x_2335_ = lean_apply_2(v_toPure_2327_, lean_box(0), v___x_2333_);
v___x_2336_ = lean_apply_4(v_toBind_2322_, lean_box(0), lean_box(0), v___x_2335_, v___f_2330_);
return v___x_2336_;
}
else
{
lean_object* v___f_2337_; size_t v___x_2338_; size_t v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
lean_inc_ref(v_inst_2238_);
v___f_2337_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2337_, 0, v_inst_2238_);
lean_closure_set(v___f_2337_, 1, v_f_2239_);
v___x_2338_ = ((size_t)0ULL);
v___x_2339_ = lean_usize_of_nat(v___x_2332_);
v___x_2340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2238_, v___f_2337_, v_params_2324_, v___x_2338_, v___x_2339_, v___x_2333_);
v___x_2341_ = lean_apply_4(v_toBind_2322_, lean_box(0), lean_box(0), v___x_2340_, v___f_2330_);
return v___x_2341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0(lean_object* v_inst_2342_, lean_object* v_f_2343_, lean_object* v_k_2344_, lean_object* v_____r_2345_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2342_, v_f_2343_, v_k_2344_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM(lean_object* v_m_2347_, uint8_t v_pu_2348_, lean_object* v_inst_2349_, lean_object* v_f_2350_, lean_object* v_c_2351_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2349_, v_f_2350_, v_c_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___boxed(lean_object* v_m_2353_, lean_object* v_pu_2354_, lean_object* v_inst_2355_, lean_object* v_f_2356_, lean_object* v_c_2357_){
_start:
{
uint8_t v_pu_boxed_2358_; lean_object* v_res_2359_; 
v_pu_boxed_2358_ = lean_unbox(v_pu_2354_);
v_res_2359_ = l_Lean_Compiler_LCNF_Code_forFVarM(v_m_2353_, v_pu_boxed_2358_, v_inst_2355_, v_f_2356_, v_c_2357_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(uint8_t v_pu_2360_, lean_object* v_m_2361_, lean_object* v_inst_2362_, lean_object* v_inst_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2360_, v_inst_2362_, v_inst_2363_, v___y_2364_, v___y_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed(lean_object* v_pu_2367_, lean_object* v_m_2368_, lean_object* v_inst_2369_, lean_object* v_inst_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
uint8_t v_pu_boxed_2373_; lean_object* v_res_2374_; 
v_pu_boxed_2373_ = lean_unbox(v_pu_2367_);
v_res_2374_ = l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(v_pu_boxed_2373_, v_m_2368_, v_inst_2369_, v_inst_2370_, v___y_2371_, v___y_2372_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__1(lean_object* v_m_2375_, lean_object* v_inst_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2376_, v___y_2377_, v___y_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode(uint8_t v_pu_2381_){
_start:
{
lean_object* v___x_2382_; lean_object* v___f_2383_; lean_object* v___f_2384_; lean_object* v___x_2385_; 
v___x_2382_ = lean_box(v_pu_2381_);
v___f_2383_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2383_, 0, v___x_2382_);
v___f_2384_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0));
v___x_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___f_2383_);
lean_ctor_set(v___x_2385_, 1, v___f_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___boxed(lean_object* v_pu_2386_){
_start:
{
uint8_t v_pu_boxed_2387_; lean_object* v_res_2388_; 
v_pu_boxed_2387_ = lean_unbox(v_pu_2386_);
v_res_2388_ = l_Lean_Compiler_LCNF_instTraverseFVarCode(v_pu_boxed_2387_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(uint8_t v_pu_2389_, lean_object* v_decl_2390_, lean_object* v_____do__lift_2391_, lean_object* v_params_2392_, lean_object* v_inst_2393_, lean_object* v_____do__lift_2394_){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2395_ = lean_box(v_pu_2389_);
v___x_2396_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed), 10, 5);
lean_closure_set(v___x_2396_, 0, v___x_2395_);
lean_closure_set(v___x_2396_, 1, v_decl_2390_);
lean_closure_set(v___x_2396_, 2, v_____do__lift_2391_);
lean_closure_set(v___x_2396_, 3, v_params_2392_);
lean_closure_set(v___x_2396_, 4, v_____do__lift_2394_);
v___x_2397_ = lean_apply_2(v_inst_2393_, lean_box(0), v___x_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_2398_, lean_object* v_decl_2399_, lean_object* v_____do__lift_2400_, lean_object* v_params_2401_, lean_object* v_inst_2402_, lean_object* v_____do__lift_2403_){
_start:
{
uint8_t v_pu_boxed_2404_; lean_object* v_res_2405_; 
v_pu_boxed_2404_ = lean_unbox(v_pu_2398_);
v_res_2405_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(v_pu_boxed_2404_, v_decl_2399_, v_____do__lift_2400_, v_params_2401_, v_inst_2402_, v_____do__lift_2403_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(uint8_t v_pu_2406_, lean_object* v_decl_2407_, lean_object* v_params_2408_, lean_object* v_inst_2409_, lean_object* v_inst_2410_, lean_object* v_f_2411_, lean_object* v_value_2412_, lean_object* v_toBind_2413_, lean_object* v_____do__lift_2414_){
_start:
{
lean_object* v___x_2415_; lean_object* v___f_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2415_ = lean_box(v_pu_2406_);
lean_inc(v_inst_2409_);
v___f_2416_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2416_, 0, v___x_2415_);
lean_closure_set(v___f_2416_, 1, v_decl_2407_);
lean_closure_set(v___f_2416_, 2, v_____do__lift_2414_);
lean_closure_set(v___f_2416_, 3, v_params_2408_);
lean_closure_set(v___f_2416_, 4, v_inst_2409_);
v___x_2417_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2406_, v_inst_2409_, v_inst_2410_, v_f_2411_, v_value_2412_);
v___x_2418_ = lean_apply_4(v_toBind_2413_, lean_box(0), lean_box(0), v___x_2417_, v___f_2416_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed(lean_object* v_pu_2419_, lean_object* v_decl_2420_, lean_object* v_params_2421_, lean_object* v_inst_2422_, lean_object* v_inst_2423_, lean_object* v_f_2424_, lean_object* v_value_2425_, lean_object* v_toBind_2426_, lean_object* v_____do__lift_2427_){
_start:
{
uint8_t v_pu_boxed_2428_; lean_object* v_res_2429_; 
v_pu_boxed_2428_ = lean_unbox(v_pu_2419_);
v_res_2429_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(v_pu_boxed_2428_, v_decl_2420_, v_params_2421_, v_inst_2422_, v_inst_2423_, v_f_2424_, v_value_2425_, v_toBind_2426_, v_____do__lift_2427_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(uint8_t v_pu_2430_, lean_object* v_decl_2431_, lean_object* v_inst_2432_, lean_object* v_inst_2433_, lean_object* v_f_2434_, lean_object* v_value_2435_, lean_object* v_toBind_2436_, lean_object* v_type_2437_, lean_object* v_params_2438_){
_start:
{
lean_object* v___x_2439_; lean_object* v___f_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2439_ = lean_box(v_pu_2430_);
lean_inc(v_toBind_2436_);
lean_inc(v_f_2434_);
lean_inc_ref(v_inst_2433_);
v___f_2440_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2440_, 0, v___x_2439_);
lean_closure_set(v___f_2440_, 1, v_decl_2431_);
lean_closure_set(v___f_2440_, 2, v_params_2438_);
lean_closure_set(v___f_2440_, 3, v_inst_2432_);
lean_closure_set(v___f_2440_, 4, v_inst_2433_);
lean_closure_set(v___f_2440_, 5, v_f_2434_);
lean_closure_set(v___f_2440_, 6, v_value_2435_);
lean_closure_set(v___f_2440_, 7, v_toBind_2436_);
v___x_2441_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2433_, v_f_2434_, v_type_2437_);
v___x_2442_ = lean_apply_4(v_toBind_2436_, lean_box(0), lean_box(0), v___x_2441_, v___f_2440_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed(lean_object* v_pu_2443_, lean_object* v_decl_2444_, lean_object* v_inst_2445_, lean_object* v_inst_2446_, lean_object* v_f_2447_, lean_object* v_value_2448_, lean_object* v_toBind_2449_, lean_object* v_type_2450_, lean_object* v_params_2451_){
_start:
{
uint8_t v_pu_boxed_2452_; lean_object* v_res_2453_; 
v_pu_boxed_2452_ = lean_unbox(v_pu_2443_);
v_res_2453_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(v_pu_boxed_2452_, v_decl_2444_, v_inst_2445_, v_inst_2446_, v_f_2447_, v_value_2448_, v_toBind_2449_, v_type_2450_, v_params_2451_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(uint8_t v_pu_2454_, lean_object* v_inst_2455_, lean_object* v_inst_2456_, lean_object* v_f_2457_, lean_object* v_decl_2458_){
_start:
{
lean_object* v_toBind_2459_; lean_object* v_params_2460_; lean_object* v_type_2461_; lean_object* v_value_2462_; lean_object* v___x_2463_; lean_object* v___f_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; size_t v_sz_2467_; size_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v_toBind_2459_ = lean_ctor_get(v_inst_2456_, 1);
lean_inc_n(v_toBind_2459_, 2);
v_params_2460_ = lean_ctor_get(v_decl_2458_, 2);
lean_inc_ref(v_params_2460_);
v_type_2461_ = lean_ctor_get(v_decl_2458_, 3);
lean_inc_ref(v_type_2461_);
v_value_2462_ = lean_ctor_get(v_decl_2458_, 4);
lean_inc_ref(v_value_2462_);
v___x_2463_ = lean_box(v_pu_2454_);
lean_inc(v_f_2457_);
lean_inc_ref_n(v_inst_2456_, 2);
lean_inc(v_inst_2455_);
v___f_2464_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2464_, 0, v___x_2463_);
lean_closure_set(v___f_2464_, 1, v_decl_2458_);
lean_closure_set(v___f_2464_, 2, v_inst_2455_);
lean_closure_set(v___f_2464_, 3, v_inst_2456_);
lean_closure_set(v___f_2464_, 4, v_f_2457_);
lean_closure_set(v___f_2464_, 5, v_value_2462_);
lean_closure_set(v___f_2464_, 6, v_toBind_2459_);
lean_closure_set(v___f_2464_, 7, v_type_2461_);
v___x_2465_ = lean_box(v_pu_2454_);
v___x_2466_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2466_, 0, lean_box(0));
lean_closure_set(v___x_2466_, 1, v___x_2465_);
lean_closure_set(v___x_2466_, 2, v_inst_2455_);
lean_closure_set(v___x_2466_, 3, v_inst_2456_);
lean_closure_set(v___x_2466_, 4, v_f_2457_);
v_sz_2467_ = lean_array_size(v_params_2460_);
v___x_2468_ = ((size_t)0ULL);
v___x_2469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2456_, v___x_2466_, v_sz_2467_, v___x_2468_, v_params_2460_);
v___x_2470_ = lean_apply_4(v_toBind_2459_, lean_box(0), lean_box(0), v___x_2469_, v___f_2464_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___boxed(lean_object* v_pu_2471_, lean_object* v_inst_2472_, lean_object* v_inst_2473_, lean_object* v_f_2474_, lean_object* v_decl_2475_){
_start:
{
uint8_t v_pu_boxed_2476_; lean_object* v_res_2477_; 
v_pu_boxed_2476_ = lean_unbox(v_pu_2471_);
v_res_2477_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_boxed_2476_, v_inst_2472_, v_inst_2473_, v_f_2474_, v_decl_2475_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM(lean_object* v_m_2478_, uint8_t v_pu_2479_, lean_object* v_inst_2480_, lean_object* v_inst_2481_, lean_object* v_f_2482_, lean_object* v_decl_2483_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2479_, v_inst_2480_, v_inst_2481_, v_f_2482_, v_decl_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___boxed(lean_object* v_m_2485_, lean_object* v_pu_2486_, lean_object* v_inst_2487_, lean_object* v_inst_2488_, lean_object* v_f_2489_, lean_object* v_decl_2490_){
_start:
{
uint8_t v_pu_boxed_2491_; lean_object* v_res_2492_; 
v_pu_boxed_2491_ = lean_unbox(v_pu_2486_);
v_res_2492_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM(v_m_2485_, v_pu_boxed_2491_, v_inst_2487_, v_inst_2488_, v_f_2489_, v_decl_2490_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0(lean_object* v_inst_2493_, lean_object* v_f_2494_, lean_object* v_value_2495_, lean_object* v_____r_2496_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2493_, v_f_2494_, v_value_2495_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1(lean_object* v_inst_2498_, lean_object* v_f_2499_, lean_object* v_type_2500_, lean_object* v_toBind_2501_, lean_object* v___f_2502_, lean_object* v_____r_2503_){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2498_, v_f_2499_, v_type_2500_);
v___x_2505_ = lean_apply_4(v_toBind_2501_, lean_box(0), lean_box(0), v___x_2504_, v___f_2502_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2(lean_object* v_inst_2506_, lean_object* v_f_2507_, lean_object* v_x_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_2506_, v_f_2507_, v___y_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(lean_object* v_inst_2511_, lean_object* v_f_2512_, lean_object* v_decl_2513_){
_start:
{
lean_object* v_toApplicative_2514_; lean_object* v_toBind_2515_; lean_object* v_params_2516_; lean_object* v_type_2517_; lean_object* v_value_2518_; lean_object* v_toPure_2519_; lean_object* v___f_2520_; lean_object* v___f_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; 
v_toApplicative_2514_ = lean_ctor_get(v_inst_2511_, 0);
v_toBind_2515_ = lean_ctor_get(v_inst_2511_, 1);
lean_inc_n(v_toBind_2515_, 2);
v_params_2516_ = lean_ctor_get(v_decl_2513_, 2);
lean_inc_ref(v_params_2516_);
v_type_2517_ = lean_ctor_get(v_decl_2513_, 3);
lean_inc_ref(v_type_2517_);
v_value_2518_ = lean_ctor_get(v_decl_2513_, 4);
lean_inc_ref(v_value_2518_);
lean_dec_ref(v_decl_2513_);
v_toPure_2519_ = lean_ctor_get(v_toApplicative_2514_, 1);
lean_inc_n(v_f_2512_, 2);
lean_inc_ref_n(v_inst_2511_, 2);
v___f_2520_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2520_, 0, v_inst_2511_);
lean_closure_set(v___f_2520_, 1, v_f_2512_);
lean_closure_set(v___f_2520_, 2, v_value_2518_);
v___f_2521_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2521_, 0, v_inst_2511_);
lean_closure_set(v___f_2521_, 1, v_f_2512_);
lean_closure_set(v___f_2521_, 2, v_type_2517_);
lean_closure_set(v___f_2521_, 3, v_toBind_2515_);
lean_closure_set(v___f_2521_, 4, v___f_2520_);
v___x_2522_ = lean_unsigned_to_nat(0u);
v___x_2523_ = lean_array_get_size(v_params_2516_);
v___x_2524_ = lean_box(0);
v___x_2525_ = lean_nat_dec_lt(v___x_2522_, v___x_2523_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
lean_inc(v_toPure_2519_);
lean_dec_ref(v_params_2516_);
lean_dec(v_f_2512_);
lean_dec_ref(v_inst_2511_);
v___x_2526_ = lean_apply_2(v_toPure_2519_, lean_box(0), v___x_2524_);
v___x_2527_ = lean_apply_4(v_toBind_2515_, lean_box(0), lean_box(0), v___x_2526_, v___f_2521_);
return v___x_2527_;
}
else
{
lean_object* v___f_2528_; size_t v___x_2529_; size_t v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_inc_ref(v_inst_2511_);
v___f_2528_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_2528_, 0, v_inst_2511_);
lean_closure_set(v___f_2528_, 1, v_f_2512_);
v___x_2529_ = ((size_t)0ULL);
v___x_2530_ = lean_usize_of_nat(v___x_2523_);
v___x_2531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2511_, v___f_2528_, v_params_2516_, v___x_2529_, v___x_2530_, v___x_2524_);
v___x_2532_ = lean_apply_4(v_toBind_2515_, lean_box(0), lean_box(0), v___x_2531_, v___f_2521_);
return v___x_2532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM(lean_object* v_m_2533_, uint8_t v_pu_2534_, lean_object* v_inst_2535_, lean_object* v_f_2536_, lean_object* v_decl_2537_){
_start:
{
lean_object* v___x_2538_; 
v___x_2538_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2535_, v_f_2536_, v_decl_2537_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___boxed(lean_object* v_m_2539_, lean_object* v_pu_2540_, lean_object* v_inst_2541_, lean_object* v_f_2542_, lean_object* v_decl_2543_){
_start:
{
uint8_t v_pu_boxed_2544_; lean_object* v_res_2545_; 
v_pu_boxed_2544_ = lean_unbox(v_pu_2540_);
v_res_2545_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM(v_m_2539_, v_pu_boxed_2544_, v_inst_2541_, v_f_2542_, v_decl_2543_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(uint8_t v_pu_2546_, lean_object* v_m_2547_, lean_object* v_inst_2548_, lean_object* v_inst_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v___x_2552_; 
v___x_2552_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2546_, v_inst_2548_, v_inst_2549_, v___y_2550_, v___y_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed(lean_object* v_pu_2553_, lean_object* v_m_2554_, lean_object* v_inst_2555_, lean_object* v_inst_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
uint8_t v_pu_boxed_2559_; lean_object* v_res_2560_; 
v_pu_boxed_2559_ = lean_unbox(v_pu_2553_);
v_res_2560_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(v_pu_boxed_2559_, v_m_2554_, v_inst_2555_, v_inst_2556_, v___y_2557_, v___y_2558_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__1(lean_object* v_m_2561_, lean_object* v_inst_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2562_, v___y_2563_, v___y_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(uint8_t v_pu_2567_){
_start:
{
lean_object* v___x_2568_; lean_object* v___f_2569_; lean_object* v___f_2570_; lean_object* v___x_2571_; 
v___x_2568_ = lean_box(v_pu_2567_);
v___f_2569_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2569_, 0, v___x_2568_);
v___f_2570_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0));
v___x_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___f_2569_);
lean_ctor_set(v___x_2571_, 1, v___f_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___boxed(lean_object* v_pu_2572_){
_start:
{
uint8_t v_pu_boxed_2573_; lean_object* v_res_2574_; 
v_pu_boxed_2573_ = lean_unbox(v_pu_2572_);
v_res_2574_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(v_pu_boxed_2573_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0(lean_object* v_toPure_2575_, lean_object* v_____do__lift_2576_){
_start:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2577_, 0, v_____do__lift_2576_);
v___x_2578_ = lean_apply_2(v_toPure_2575_, lean_box(0), v___x_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1(lean_object* v_toPure_2579_, lean_object* v_____do__lift_2580_){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2581_, 0, v_____do__lift_2580_);
v___x_2582_ = lean_apply_2(v_toPure_2579_, lean_box(0), v___x_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2(lean_object* v_toPure_2583_, lean_object* v_____do__lift_2584_){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2585_, 0, v_____do__lift_2584_);
v___x_2586_ = lean_apply_2(v_toPure_2583_, lean_box(0), v___x_2585_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3(lean_object* v_____do__lift_2587_, lean_object* v_i_2588_, lean_object* v_toPure_2589_, lean_object* v_____do__lift_2590_){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2591_, 0, v_____do__lift_2587_);
lean_ctor_set(v___x_2591_, 1, v_i_2588_);
lean_ctor_set(v___x_2591_, 2, v_____do__lift_2590_);
v___x_2592_ = lean_apply_2(v_toPure_2589_, lean_box(0), v___x_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(lean_object* v_i_2593_, lean_object* v_toPure_2594_, uint8_t v_pu_2595_, lean_object* v_inst_2596_, lean_object* v_f_2597_, lean_object* v_y_2598_, lean_object* v_toBind_2599_, lean_object* v_____do__lift_2600_){
_start:
{
lean_object* v___f_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___f_2601_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3), 4, 3);
lean_closure_set(v___f_2601_, 0, v_____do__lift_2600_);
lean_closure_set(v___f_2601_, 1, v_i_2593_);
lean_closure_set(v___f_2601_, 2, v_toPure_2594_);
v___x_2602_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_2595_, v_inst_2596_, v_f_2597_, v_y_2598_);
v___x_2603_ = lean_apply_4(v_toBind_2599_, lean_box(0), lean_box(0), v___x_2602_, v___f_2601_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed(lean_object* v_i_2604_, lean_object* v_toPure_2605_, lean_object* v_pu_2606_, lean_object* v_inst_2607_, lean_object* v_f_2608_, lean_object* v_y_2609_, lean_object* v_toBind_2610_, lean_object* v_____do__lift_2611_){
_start:
{
uint8_t v_pu_boxed_2612_; lean_object* v_res_2613_; 
v_pu_boxed_2612_ = lean_unbox(v_pu_2606_);
v_res_2613_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(v_i_2604_, v_toPure_2605_, v_pu_boxed_2612_, v_inst_2607_, v_f_2608_, v_y_2609_, v_toBind_2610_, v_____do__lift_2611_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5(lean_object* v_____do__lift_2614_, lean_object* v_i_2615_, lean_object* v_toPure_2616_, lean_object* v_____do__lift_2617_){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_2618_, 0, v_____do__lift_2614_);
lean_ctor_set(v___x_2618_, 1, v_i_2615_);
lean_ctor_set(v___x_2618_, 2, v_____do__lift_2617_);
v___x_2619_ = lean_apply_2(v_toPure_2616_, lean_box(0), v___x_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6(lean_object* v_i_2620_, lean_object* v_toPure_2621_, lean_object* v_f_2622_, lean_object* v_y_2623_, lean_object* v_toBind_2624_, lean_object* v_____do__lift_2625_){
_start:
{
lean_object* v___f_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___f_2626_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5), 4, 3);
lean_closure_set(v___f_2626_, 0, v_____do__lift_2625_);
lean_closure_set(v___f_2626_, 1, v_i_2620_);
lean_closure_set(v___f_2626_, 2, v_toPure_2621_);
v___x_2627_ = lean_apply_1(v_f_2622_, v_y_2623_);
v___x_2628_ = lean_apply_4(v_toBind_2624_, lean_box(0), lean_box(0), v___x_2627_, v___f_2626_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7(lean_object* v_____do__lift_2629_, lean_object* v_i_2630_, lean_object* v_offset_2631_, lean_object* v_____do__lift_2632_, lean_object* v_toPure_2633_, lean_object* v_____do__lift_2634_){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v___x_2635_, 0, v_____do__lift_2629_);
lean_ctor_set(v___x_2635_, 1, v_i_2630_);
lean_ctor_set(v___x_2635_, 2, v_offset_2631_);
lean_ctor_set(v___x_2635_, 3, v_____do__lift_2632_);
lean_ctor_set(v___x_2635_, 4, v_____do__lift_2634_);
v___x_2636_ = lean_apply_2(v_toPure_2633_, lean_box(0), v___x_2635_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8(lean_object* v_____do__lift_2637_, lean_object* v_i_2638_, lean_object* v_offset_2639_, lean_object* v_toPure_2640_, lean_object* v_inst_2641_, lean_object* v_f_2642_, lean_object* v_ty_2643_, lean_object* v_toBind_2644_, lean_object* v_____do__lift_2645_){
_start:
{
lean_object* v___f_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___f_2646_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7), 6, 5);
lean_closure_set(v___f_2646_, 0, v_____do__lift_2637_);
lean_closure_set(v___f_2646_, 1, v_i_2638_);
lean_closure_set(v___f_2646_, 2, v_offset_2639_);
lean_closure_set(v___f_2646_, 3, v_____do__lift_2645_);
lean_closure_set(v___f_2646_, 4, v_toPure_2640_);
v___x_2647_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2641_, v_f_2642_, v_ty_2643_);
v___x_2648_ = lean_apply_4(v_toBind_2644_, lean_box(0), lean_box(0), v___x_2647_, v___f_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9(lean_object* v_i_2649_, lean_object* v_offset_2650_, lean_object* v_toPure_2651_, lean_object* v_inst_2652_, lean_object* v_f_2653_, lean_object* v_ty_2654_, lean_object* v_toBind_2655_, lean_object* v_y_2656_, lean_object* v_____do__lift_2657_){
_start:
{
lean_object* v___f_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
lean_inc(v_toBind_2655_);
lean_inc(v_f_2653_);
v___f_2658_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8), 9, 8);
lean_closure_set(v___f_2658_, 0, v_____do__lift_2657_);
lean_closure_set(v___f_2658_, 1, v_i_2649_);
lean_closure_set(v___f_2658_, 2, v_offset_2650_);
lean_closure_set(v___f_2658_, 3, v_toPure_2651_);
lean_closure_set(v___f_2658_, 4, v_inst_2652_);
lean_closure_set(v___f_2658_, 5, v_f_2653_);
lean_closure_set(v___f_2658_, 6, v_ty_2654_);
lean_closure_set(v___f_2658_, 7, v_toBind_2655_);
v___x_2659_ = lean_apply_1(v_f_2653_, v_y_2656_);
v___x_2660_ = lean_apply_4(v_toBind_2655_, lean_box(0), lean_box(0), v___x_2659_, v___f_2658_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10(lean_object* v_cidx_2661_, lean_object* v_toPure_2662_, lean_object* v_____do__lift_2663_){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2664_, 0, v_____do__lift_2663_);
lean_ctor_set(v___x_2664_, 1, v_cidx_2661_);
v___x_2665_ = lean_apply_2(v_toPure_2662_, lean_box(0), v___x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(lean_object* v_n_2666_, uint8_t v_check_2667_, uint8_t v_persistent_2668_, lean_object* v_toPure_2669_, lean_object* v_____do__lift_2670_){
_start:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v___x_2671_, 0, v_____do__lift_2670_);
lean_ctor_set(v___x_2671_, 1, v_n_2666_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*2, v_check_2667_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*2 + 1, v_persistent_2668_);
v___x_2672_ = lean_apply_2(v_toPure_2669_, lean_box(0), v___x_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed(lean_object* v_n_2673_, lean_object* v_check_2674_, lean_object* v_persistent_2675_, lean_object* v_toPure_2676_, lean_object* v_____do__lift_2677_){
_start:
{
uint8_t v_check_933__boxed_2678_; uint8_t v_persistent_934__boxed_2679_; lean_object* v_res_2680_; 
v_check_933__boxed_2678_ = lean_unbox(v_check_2674_);
v_persistent_934__boxed_2679_ = lean_unbox(v_persistent_2675_);
v_res_2680_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(v_n_2673_, v_check_933__boxed_2678_, v_persistent_934__boxed_2679_, v_toPure_2676_, v_____do__lift_2677_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(lean_object* v_n_2681_, uint8_t v_check_2682_, uint8_t v_persistent_2683_, lean_object* v_objs_x3f_2684_, lean_object* v_toPure_2685_, lean_object* v_____do__lift_2686_){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2687_ = lean_alloc_ctor(8, 3, 2);
lean_ctor_set(v___x_2687_, 0, v_____do__lift_2686_);
lean_ctor_set(v___x_2687_, 1, v_n_2681_);
lean_ctor_set(v___x_2687_, 2, v_objs_x3f_2684_);
lean_ctor_set_uint8(v___x_2687_, sizeof(void*)*3, v_check_2682_);
lean_ctor_set_uint8(v___x_2687_, sizeof(void*)*3 + 1, v_persistent_2683_);
v___x_2688_ = lean_apply_2(v_toPure_2685_, lean_box(0), v___x_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed(lean_object* v_n_2689_, lean_object* v_check_2690_, lean_object* v_persistent_2691_, lean_object* v_objs_x3f_2692_, lean_object* v_toPure_2693_, lean_object* v_____do__lift_2694_){
_start:
{
uint8_t v_check_949__boxed_2695_; uint8_t v_persistent_950__boxed_2696_; lean_object* v_res_2697_; 
v_check_949__boxed_2695_ = lean_unbox(v_check_2690_);
v_persistent_950__boxed_2696_ = lean_unbox(v_persistent_2691_);
v_res_2697_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(v_n_2689_, v_check_949__boxed_2695_, v_persistent_950__boxed_2696_, v_objs_x3f_2692_, v_toPure_2693_, v_____do__lift_2694_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13(lean_object* v_toPure_2698_, lean_object* v_____do__lift_2699_){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2700_, 0, v_____do__lift_2699_);
v___x_2701_ = lean_apply_2(v_toPure_2698_, lean_box(0), v___x_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(uint8_t v_pu_2702_, lean_object* v_m_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_f_2706_, lean_object* v_decl_2707_){
_start:
{
switch(lean_obj_tag(v_decl_2707_))
{
case 0:
{
lean_object* v_toApplicative_2708_; lean_object* v_toBind_2709_; lean_object* v_toPure_2710_; lean_object* v_decl_2711_; lean_object* v___f_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v_toApplicative_2708_ = lean_ctor_get(v_inst_2705_, 0);
v_toBind_2709_ = lean_ctor_get(v_inst_2705_, 1);
lean_inc(v_toBind_2709_);
v_toPure_2710_ = lean_ctor_get(v_toApplicative_2708_, 1);
v_decl_2711_ = lean_ctor_get(v_decl_2707_, 0);
lean_inc_ref(v_decl_2711_);
lean_dec_ref_known(v_decl_2707_, 1);
lean_inc(v_toPure_2710_);
v___f_2712_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0), 2, 1);
lean_closure_set(v___f_2712_, 0, v_toPure_2710_);
v___x_2713_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_2702_, v_inst_2704_, v_inst_2705_, v_f_2706_, v_decl_2711_);
v___x_2714_ = lean_apply_4(v_toBind_2709_, lean_box(0), lean_box(0), v___x_2713_, v___f_2712_);
return v___x_2714_;
}
case 1:
{
lean_object* v_toApplicative_2715_; lean_object* v_toBind_2716_; lean_object* v_toPure_2717_; lean_object* v_decl_2718_; lean_object* v___f_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v_toApplicative_2715_ = lean_ctor_get(v_inst_2705_, 0);
v_toBind_2716_ = lean_ctor_get(v_inst_2705_, 1);
lean_inc(v_toBind_2716_);
v_toPure_2717_ = lean_ctor_get(v_toApplicative_2715_, 1);
v_decl_2718_ = lean_ctor_get(v_decl_2707_, 0);
lean_inc_ref(v_decl_2718_);
lean_dec_ref_known(v_decl_2707_, 1);
lean_inc(v_toPure_2717_);
v___f_2719_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1), 2, 1);
lean_closure_set(v___f_2719_, 0, v_toPure_2717_);
v___x_2720_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2702_, v_inst_2704_, v_inst_2705_, v_f_2706_, v_decl_2718_);
v___x_2721_ = lean_apply_4(v_toBind_2716_, lean_box(0), lean_box(0), v___x_2720_, v___f_2719_);
return v___x_2721_;
}
case 2:
{
lean_object* v_toApplicative_2722_; lean_object* v_toBind_2723_; lean_object* v_toPure_2724_; lean_object* v_decl_2725_; lean_object* v___f_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v_toApplicative_2722_ = lean_ctor_get(v_inst_2705_, 0);
v_toBind_2723_ = lean_ctor_get(v_inst_2705_, 1);
lean_inc(v_toBind_2723_);
v_toPure_2724_ = lean_ctor_get(v_toApplicative_2722_, 1);
v_decl_2725_ = lean_ctor_get(v_decl_2707_, 0);
lean_inc_ref(v_decl_2725_);
lean_dec_ref_known(v_decl_2707_, 1);
lean_inc(v_toPure_2724_);
v___f_2726_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2), 2, 1);
lean_closure_set(v___f_2726_, 0, v_toPure_2724_);
v___x_2727_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2702_, v_inst_2704_, v_inst_2705_, v_f_2706_, v_decl_2725_);
v___x_2728_ = lean_apply_4(v_toBind_2723_, lean_box(0), lean_box(0), v___x_2727_, v___f_2726_);
return v___x_2728_;
}
case 3:
{
lean_object* v_toApplicative_2729_; lean_object* v_toBind_2730_; lean_object* v_toPure_2731_; lean_object* v_fvarId_2732_; lean_object* v_i_2733_; lean_object* v_y_2734_; lean_object* v___x_2735_; lean_object* v___f_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v_toApplicative_2729_ = lean_ctor_get(v_inst_2705_, 0);
lean_dec(v_inst_2704_);
v_toBind_2730_ = lean_ctor_get(v_inst_2705_, 1);
lean_inc_n(v_toBind_2730_, 2);
v_toPure_2731_ = lean_ctor_get(v_toApplicative_2729_, 1);
lean_inc(v_toPure_2731_);
v_fvarId_2732_ = lean_ctor_get(v_decl_2707_, 0);
lean_inc(v_fvarId_2732_);
v_i_2733_ = lean_ctor_get(v_decl_2707_, 1);
lean_inc(v_i_2733_);
v_y_2734_ = lean_ctor_get(v_decl_2707_, 2);
lean_inc(v_y_2734_);
lean_dec_ref_known(v_decl_2707_, 3);
v___x_2735_ = lean_box(v_pu_2702_);
lean_inc(v_f_2706_);
v___f_2736_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed), 8, 7);
lean_closure_set(v___f_2736_, 0, v_i_2733_);
lean_closure_set(v___f_2736_, 1, v_toPure_2731_);
lean_closure_set(v___f_2736_, 2, v___x_2735_);
lean_closure_set(v___f_2736_, 3, v_inst_2705_);
lean_closure_set(v___f_2736_, 4, v_f_2706_);
lean_closure_set(v___f_2736_, 5, v_y_2734_);
lean_closure_set(v___f_2736_, 6, v_toBind_2730_);
v___x_2737_ = lean_apply_1(v_f_2706_, v_fvarId_2732_);
v___x_2738_ = lean_apply_4(v_toBind_2730_, lean_box(0), lean_box(0), v___x_2737_, v___f_2736_);
return v___x_2738_;
}
case 4:
{
lean_object* v_toApplicative_2739_; lean_object* v_toBind_2740_; lean_object* v_toPure_2741_; lean_object* v_fvarId_2742_; lean_object* v_i_2743_; lean_object* v_y_2744_; lean_object* v___f_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v_toApplicative_2739_ = lean_ctor_get(v_inst_2705_, 0);
lean_inc_ref(v_toApplicative_2739_);
lean_dec(v_inst_2704_);
v_toBind_2740_ = lean_ctor_get(v_inst_2705_, 1);
lean_inc_n(v_toBind_2740_, 2);
lean_dec_ref(v_inst_2705_);
v_toPure_2741_ = lean_ctor_get(v_toApplicative_2739_, 1);
lean_inc(v_toPure_2741_);
lean_dec_ref(v_toApplicative_2739_);
v_fvarId_2742_ = lean_ctor_get(v_decl_2707_, 0);
lean_inc(v_fvarId_2742_);
v_i_2743_ = lean_ctor_get(v_decl_2707_, 1);
lean_inc(v_i_2743_);
v_y_2744_ = lean_ctor_get(v_decl_2707_, 2);
lean_inc(v_y_2744_);
lean_dec_ref_known(v_decl_2707_, 3);
lean_inc(v_f_2706_);
v___f_2745_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6), 6, 5);
lean_closure_set(v___f_2745_, 0, v_i_2743_);
lean_closure_set(v___f_2745_, 1, v_toPure_2741_);
lean_closure_set(v___f_2745_, 2, v_f_2706_);
lean_closure_set(v___f_2745_, 3, v_y_2744_);
lean_closure_set(v___f_2745_, 4, v_toBind_2740_);
v___x_2746_ = lean_apply_1(v_f_2706_, v_fvarId_2742_);
v___x_2747_ = lean_apply_4(v_toBind_2740_, lean_box(0), lean_box(0), v___x_2746_, v___f_2745_);
return v___x_2747_;
}
case 5:
{
lean_object* v_toApplicative_2748_; lean_object* v_toBind_2749_; lean_object* v_toPure_2750_; lean_object* v_fvarId_2751_; lean_object* v_i_2752_; lean_object* v_offset_2753_; lean_object* v_y_2754_; lean_object* v_ty_2755_; lean_object* v___f_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v_toApplicative_2748_ = lean_ctor_get(v_inst_2705_, 0);
lean_dec(v_inst_2704_);
v_toBind_2749_ = lean_ctor_get(v_inst_2705_, 1);
lean_inc_n(v_toBind_2749_, 2);
v_toPure_2750_ = lean_ctor_get(v_toApplicative_2748_, 1);
lean_inc(v_toPure_2750_);
v_fvarId_2751_ = lean_ctor_get(v_decl_2707_, 0);
lean_inc(v_fvarId_2751_);
v_i_2752_ = lean_ctor_get(v_decl_2707_, 1);
lean_inc(v_i_2752_);
v_offset_2753_ = lean_ctor_get(v_decl_2707_, 2);
lean_inc(v_offset_2753_);
v_y_2754_ = lean_ctor_get(v_decl_2707_, 3);
lean_inc(v_y_2754_);
v_ty_2755_ = lean_ctor_get(v_decl_2707_, 4);
lean_inc_ref(v_ty_2755_);
lean_dec_ref_known(v_decl_2707_, 5);
lean_inc(v_f_2706_);
v___f_2756_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9), 9, 8);
lean_closure_set(v___f_2756_, 0, v_i_2752_);
lean_closure_set(v___f_2756_, 1, v_offset_2753_);
lean_closure_set(v___f_2756_, 2, v_toPure_2750_);
lean_closure_set(v___f_2756_, 3, v_inst_2705_);
lean_closure_set(v___f_2756_, 4, v_f_2706_);
lean_closure_set(v___f_2756_, 5, v_ty_2755_);
lean_closure_set(v___f_2756_, 6, v_toBind_2749_);
lean_closure_set(v___f_2756_, 7, v_y_2754_);
v___x_2757_ = lean_apply_1(v_f_2706_, v_fvarId_2751_);
v___x_2758_ = lean_apply_4(v_toBind_2749_, lean_box(0), lean_box(0), v___x_2757_, v___f_2756_);
return v___x_2758_;
}
case 6:
{
lean_object* v_toApplicative_2759_; lean_object* v_toBind_2760_; lean_object* v_toPure_2761_; lean_object* v_fvarId_2762_; lean_object* v_cidx_2763_; lean_object* v___f_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v_toApplicative_2759_ = lean_ctor_get(v_inst_2705_, 0);
lean_inc_ref(v_toApplicative_2759_);
lean_dec(v_inst_2704_);
v_toBind_2760_ = lean_ctor_get(v_inst_2705_, 1);
lean_inc(v_toBind_2760_);
lean_dec_ref(v_inst_2705_);
v_toPure_2761_ = lean_ctor_get(v_toApplicative_2759_, 1);
lean_inc(v_toPure_2761_);
lean_dec_ref(v_toApplicative_2759_);
v_fvarId_2762_ = lean_ctor_get(v_decl_2707_, 0);
lean_inc(v_fvarId_2762_);
v_cidx_2763_ = lean_ctor_get(v_decl_2707_, 1);
lean_inc(v_cidx_2763_);
lean_dec_ref_known(v_decl_2707_, 2);
v___f_2764_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10), 3, 2);
lean_closure_set(v___f_2764_, 0, v_cidx_2763_);
lean_closure_set(v___f_2764_, 1, v_toPure_2761_);
v___x_2765_ = lean_apply_1(v_f_2706_, v_fvarId_2762_);
v___x_2766_ = lean_apply_4(v_toBind_2760_, lean_box(0), lean_box(0), v___x_2765_, v___f_2764_);
return v___x_2766_;
}
case 7:
{
lean_object* v_toApplicative_2767_; lean_object* v_toBind_2768_; lean_object* v_toPure_2769_; lean_object* v_fvarId_2770_; lean_object* v_n_2771_; uint8_t v_check_2772_; uint8_t v_persistent_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___f_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_toApplicative_2767_ = lean_ctor_get(v_inst_2705_, 0);
lean_inc_ref(v_toApplicative_2767_);
lean_dec(v_inst_2704_);
v_toBind_2768_ = lean_ctor_get(v_inst_2705_, 1);
lean_inc(v_toBind_2768_);
lean_dec_ref(v_inst_2705_);
v_toPure_2769_ = lean_ctor_get(v_toApplicative_2767_, 1);
lean_inc(v_toPure_2769_);
lean_dec_ref(v_toApplicative_2767_);
v_fvarId_2770_ = lean_ctor_get(v_decl_2707_, 0);
lean_inc(v_fvarId_2770_);
v_n_2771_ = lean_ctor_get(v_decl_2707_, 1);
lean_inc(v_n_2771_);
v_check_2772_ = lean_ctor_get_uint8(v_decl_2707_, sizeof(void*)*2);
v_persistent_2773_ = lean_ctor_get_uint8(v_decl_2707_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_decl_2707_, 2);
v___x_2774_ = lean_box(v_check_2772_);
v___x_2775_ = lean_box(v_persistent_2773_);
v___f_2776_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed), 5, 4);
lean_closure_set(v___f_2776_, 0, v_n_2771_);
lean_closure_set(v___f_2776_, 1, v___x_2774_);
lean_closure_set(v___f_2776_, 2, v___x_2775_);
lean_closure_set(v___f_2776_, 3, v_toPure_2769_);
v___x_2777_ = lean_apply_1(v_f_2706_, v_fvarId_2770_);
v___x_2778_ = lean_apply_4(v_toBind_2768_, lean_box(0), lean_box(0), v___x_2777_, v___f_2776_);
return v___x_2778_;
}
case 8:
{
lean_object* v_toApplicative_2779_; lean_object* v_toBind_2780_; lean_object* v_toPure_2781_; lean_object* v_fvarId_2782_; lean_object* v_n_2783_; uint8_t v_check_2784_; uint8_t v_persistent_2785_; lean_object* v_objs_x3f_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___f_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v_toApplicative_2779_ = lean_ctor_get(v_inst_2705_, 0);
lean_inc_ref(v_toApplicative_2779_);
lean_dec(v_inst_2704_);
v_toBind_2780_ = lean_ctor_get(v_inst_2705_, 1);
lean_inc(v_toBind_2780_);
lean_dec_ref(v_inst_2705_);
v_toPure_2781_ = lean_ctor_get(v_toApplicative_2779_, 1);
lean_inc(v_toPure_2781_);
lean_dec_ref(v_toApplicative_2779_);
v_fvarId_2782_ = lean_ctor_get(v_decl_2707_, 0);
lean_inc(v_fvarId_2782_);
v_n_2783_ = lean_ctor_get(v_decl_2707_, 1);
lean_inc(v_n_2783_);
v_check_2784_ = lean_ctor_get_uint8(v_decl_2707_, sizeof(void*)*3);
v_persistent_2785_ = lean_ctor_get_uint8(v_decl_2707_, sizeof(void*)*3 + 1);
v_objs_x3f_2786_ = lean_ctor_get(v_decl_2707_, 2);
lean_inc(v_objs_x3f_2786_);
lean_dec_ref_known(v_decl_2707_, 3);
v___x_2787_ = lean_box(v_check_2784_);
v___x_2788_ = lean_box(v_persistent_2785_);
v___f_2789_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed), 6, 5);
lean_closure_set(v___f_2789_, 0, v_n_2783_);
lean_closure_set(v___f_2789_, 1, v___x_2787_);
lean_closure_set(v___f_2789_, 2, v___x_2788_);
lean_closure_set(v___f_2789_, 3, v_objs_x3f_2786_);
lean_closure_set(v___f_2789_, 4, v_toPure_2781_);
v___x_2790_ = lean_apply_1(v_f_2706_, v_fvarId_2782_);
v___x_2791_ = lean_apply_4(v_toBind_2780_, lean_box(0), lean_box(0), v___x_2790_, v___f_2789_);
return v___x_2791_;
}
default: 
{
lean_object* v_toApplicative_2792_; lean_object* v_toBind_2793_; lean_object* v_toPure_2794_; lean_object* v_fvarId_2795_; lean_object* v___f_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_toApplicative_2792_ = lean_ctor_get(v_inst_2705_, 0);
lean_inc_ref(v_toApplicative_2792_);
lean_dec(v_inst_2704_);
v_toBind_2793_ = lean_ctor_get(v_inst_2705_, 1);
lean_inc(v_toBind_2793_);
lean_dec_ref(v_inst_2705_);
v_toPure_2794_ = lean_ctor_get(v_toApplicative_2792_, 1);
lean_inc(v_toPure_2794_);
lean_dec_ref(v_toApplicative_2792_);
v_fvarId_2795_ = lean_ctor_get(v_decl_2707_, 0);
lean_inc(v_fvarId_2795_);
lean_dec_ref_known(v_decl_2707_, 1);
v___f_2796_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13), 2, 1);
lean_closure_set(v___f_2796_, 0, v_toPure_2794_);
v___x_2797_ = lean_apply_1(v_f_2706_, v_fvarId_2795_);
v___x_2798_ = lean_apply_4(v_toBind_2793_, lean_box(0), lean_box(0), v___x_2797_, v___f_2796_);
return v___x_2798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed(lean_object* v_pu_2799_, lean_object* v_m_2800_, lean_object* v_inst_2801_, lean_object* v_inst_2802_, lean_object* v_f_2803_, lean_object* v_decl_2804_){
_start:
{
uint8_t v_pu_boxed_2805_; lean_object* v_res_2806_; 
v_pu_boxed_2805_ = lean_unbox(v_pu_2799_);
v_res_2806_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(v_pu_boxed_2805_, v_m_2800_, v_inst_2801_, v_inst_2802_, v_f_2803_, v_decl_2804_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15(lean_object* v_inst_2807_, lean_object* v_f_2808_, lean_object* v_y_2809_, lean_object* v_____r_2810_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2807_, v_f_2808_, v_y_2809_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16(lean_object* v_f_2812_, lean_object* v_y_2813_, lean_object* v_____r_2814_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = lean_apply_1(v_f_2812_, v_y_2813_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17(lean_object* v_inst_2816_, lean_object* v_f_2817_, lean_object* v_ty_2818_, lean_object* v_____r_2819_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2816_, v_f_2817_, v_ty_2818_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18(lean_object* v_f_2821_, lean_object* v_y_2822_, lean_object* v_toBind_2823_, lean_object* v___f_2824_, lean_object* v_____r_2825_){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = lean_apply_1(v_f_2821_, v_y_2822_);
v___x_2827_ = lean_apply_4(v_toBind_2823_, lean_box(0), lean_box(0), v___x_2826_, v___f_2824_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__19(lean_object* v_m_2828_, lean_object* v_inst_2829_, lean_object* v_f_2830_, lean_object* v_decl_2831_){
_start:
{
switch(lean_obj_tag(v_decl_2831_))
{
case 0:
{
lean_object* v_decl_2832_; lean_object* v___x_2833_; 
v_decl_2832_ = lean_ctor_get(v_decl_2831_, 0);
lean_inc_ref(v_decl_2832_);
lean_dec_ref_known(v_decl_2831_, 1);
v___x_2833_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_2829_, v_f_2830_, v_decl_2832_);
return v___x_2833_;
}
case 1:
{
lean_object* v_decl_2834_; lean_object* v___x_2835_; 
v_decl_2834_ = lean_ctor_get(v_decl_2831_, 0);
lean_inc_ref(v_decl_2834_);
lean_dec_ref_known(v_decl_2831_, 1);
v___x_2835_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2829_, v_f_2830_, v_decl_2834_);
return v___x_2835_;
}
case 2:
{
lean_object* v_decl_2836_; lean_object* v___x_2837_; 
v_decl_2836_ = lean_ctor_get(v_decl_2831_, 0);
lean_inc_ref(v_decl_2836_);
lean_dec_ref_known(v_decl_2831_, 1);
v___x_2837_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2829_, v_f_2830_, v_decl_2836_);
return v___x_2837_;
}
case 3:
{
lean_object* v_toBind_2838_; lean_object* v_fvarId_2839_; lean_object* v_y_2840_; lean_object* v___f_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v_toBind_2838_ = lean_ctor_get(v_inst_2829_, 1);
lean_inc(v_toBind_2838_);
v_fvarId_2839_ = lean_ctor_get(v_decl_2831_, 0);
lean_inc(v_fvarId_2839_);
v_y_2840_ = lean_ctor_get(v_decl_2831_, 2);
lean_inc(v_y_2840_);
lean_dec_ref_known(v_decl_2831_, 3);
lean_inc(v_f_2830_);
v___f_2841_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15), 4, 3);
lean_closure_set(v___f_2841_, 0, v_inst_2829_);
lean_closure_set(v___f_2841_, 1, v_f_2830_);
lean_closure_set(v___f_2841_, 2, v_y_2840_);
v___x_2842_ = lean_apply_1(v_f_2830_, v_fvarId_2839_);
v___x_2843_ = lean_apply_4(v_toBind_2838_, lean_box(0), lean_box(0), v___x_2842_, v___f_2841_);
return v___x_2843_;
}
case 4:
{
lean_object* v_toBind_2844_; lean_object* v_fvarId_2845_; lean_object* v_y_2846_; lean_object* v___f_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v_toBind_2844_ = lean_ctor_get(v_inst_2829_, 1);
lean_inc(v_toBind_2844_);
lean_dec_ref(v_inst_2829_);
v_fvarId_2845_ = lean_ctor_get(v_decl_2831_, 0);
lean_inc(v_fvarId_2845_);
v_y_2846_ = lean_ctor_get(v_decl_2831_, 2);
lean_inc(v_y_2846_);
lean_dec_ref_known(v_decl_2831_, 3);
lean_inc(v_f_2830_);
v___f_2847_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16), 3, 2);
lean_closure_set(v___f_2847_, 0, v_f_2830_);
lean_closure_set(v___f_2847_, 1, v_y_2846_);
v___x_2848_ = lean_apply_1(v_f_2830_, v_fvarId_2845_);
v___x_2849_ = lean_apply_4(v_toBind_2844_, lean_box(0), lean_box(0), v___x_2848_, v___f_2847_);
return v___x_2849_;
}
case 5:
{
lean_object* v_toBind_2850_; lean_object* v_fvarId_2851_; lean_object* v_y_2852_; lean_object* v_ty_2853_; lean_object* v___f_2854_; lean_object* v___f_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v_toBind_2850_ = lean_ctor_get(v_inst_2829_, 1);
lean_inc_n(v_toBind_2850_, 2);
v_fvarId_2851_ = lean_ctor_get(v_decl_2831_, 0);
lean_inc(v_fvarId_2851_);
v_y_2852_ = lean_ctor_get(v_decl_2831_, 3);
lean_inc(v_y_2852_);
v_ty_2853_ = lean_ctor_get(v_decl_2831_, 4);
lean_inc_ref(v_ty_2853_);
lean_dec_ref_known(v_decl_2831_, 5);
lean_inc_n(v_f_2830_, 2);
v___f_2854_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17), 4, 3);
lean_closure_set(v___f_2854_, 0, v_inst_2829_);
lean_closure_set(v___f_2854_, 1, v_f_2830_);
lean_closure_set(v___f_2854_, 2, v_ty_2853_);
v___f_2855_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18), 5, 4);
lean_closure_set(v___f_2855_, 0, v_f_2830_);
lean_closure_set(v___f_2855_, 1, v_y_2852_);
lean_closure_set(v___f_2855_, 2, v_toBind_2850_);
lean_closure_set(v___f_2855_, 3, v___f_2854_);
v___x_2856_ = lean_apply_1(v_f_2830_, v_fvarId_2851_);
v___x_2857_ = lean_apply_4(v_toBind_2850_, lean_box(0), lean_box(0), v___x_2856_, v___f_2855_);
return v___x_2857_;
}
default: 
{
lean_object* v_fvarId_2858_; lean_object* v___x_2859_; 
lean_dec_ref(v_inst_2829_);
v_fvarId_2858_ = lean_ctor_get(v_decl_2831_, 0);
lean_inc(v_fvarId_2858_);
lean_dec_ref(v_decl_2831_);
v___x_2859_ = lean_apply_1(v_f_2830_, v_fvarId_2858_);
return v___x_2859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(uint8_t v_pu_2861_){
_start:
{
lean_object* v___x_2862_; lean_object* v___f_2863_; lean_object* v___f_2864_; lean_object* v___x_2865_; 
v___x_2862_ = lean_box(v_pu_2861_);
v___f_2863_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed), 6, 1);
lean_closure_set(v___f_2863_, 0, v___x_2862_);
v___f_2864_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0));
v___x_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___f_2863_);
lean_ctor_set(v___x_2865_, 1, v___f_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___boxed(lean_object* v_pu_2866_){
_start:
{
uint8_t v_pu_boxed_2867_; lean_object* v_res_2868_; 
v_pu_boxed_2867_ = lean_unbox(v_pu_2866_);
v_res_2868_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(v_pu_boxed_2867_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0(lean_object* v_ctorName_2869_, lean_object* v_params_2870_, lean_object* v_toPure_2871_, lean_object* v_____do__lift_2872_){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2873_, 0, v_ctorName_2869_);
lean_ctor_set(v___x_2873_, 1, v_params_2870_);
lean_ctor_set(v___x_2873_, 2, v_____do__lift_2872_);
v___x_2874_ = lean_apply_2(v_toPure_2871_, lean_box(0), v___x_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(lean_object* v_ctorName_2875_, lean_object* v_toPure_2876_, uint8_t v_pu_2877_, lean_object* v_inst_2878_, lean_object* v_inst_2879_, lean_object* v_f_2880_, lean_object* v_code_2881_, lean_object* v_toBind_2882_, lean_object* v_params_2883_){
_start:
{
lean_object* v___f_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___f_2884_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0), 4, 3);
lean_closure_set(v___f_2884_, 0, v_ctorName_2875_);
lean_closure_set(v___f_2884_, 1, v_params_2883_);
lean_closure_set(v___f_2884_, 2, v_toPure_2876_);
v___x_2885_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2877_, v_inst_2878_, v_inst_2879_, v_f_2880_, v_code_2881_);
v___x_2886_ = lean_apply_4(v_toBind_2882_, lean_box(0), lean_box(0), v___x_2885_, v___f_2884_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed(lean_object* v_ctorName_2887_, lean_object* v_toPure_2888_, lean_object* v_pu_2889_, lean_object* v_inst_2890_, lean_object* v_inst_2891_, lean_object* v_f_2892_, lean_object* v_code_2893_, lean_object* v_toBind_2894_, lean_object* v_params_2895_){
_start:
{
uint8_t v_pu_boxed_2896_; lean_object* v_res_2897_; 
v_pu_boxed_2896_ = lean_unbox(v_pu_2889_);
v_res_2897_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(v_ctorName_2887_, v_toPure_2888_, v_pu_boxed_2896_, v_inst_2890_, v_inst_2891_, v_f_2892_, v_code_2893_, v_toBind_2894_, v_params_2895_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2(lean_object* v_info_2898_, lean_object* v_toPure_2899_, lean_object* v_____do__lift_2900_){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2901_, 0, v_info_2898_);
lean_ctor_set(v___x_2901_, 1, v_____do__lift_2900_);
v___x_2902_ = lean_apply_2(v_toPure_2899_, lean_box(0), v___x_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3(lean_object* v_toPure_2903_, lean_object* v_____do__lift_2904_){
_start:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2905_, 0, v_____do__lift_2904_);
v___x_2906_ = lean_apply_2(v_toPure_2903_, lean_box(0), v___x_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(uint8_t v_pu_2907_, lean_object* v_m_2908_, lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_f_2911_, lean_object* v_alt_2912_){
_start:
{
switch(lean_obj_tag(v_alt_2912_))
{
case 0:
{
lean_object* v_toApplicative_2913_; lean_object* v_toBind_2914_; lean_object* v_toPure_2915_; lean_object* v_ctorName_2916_; lean_object* v_params_2917_; lean_object* v_code_2918_; lean_object* v___x_2919_; lean_object* v___f_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; size_t v_sz_2923_; size_t v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v_toApplicative_2913_ = lean_ctor_get(v_inst_2910_, 0);
v_toBind_2914_ = lean_ctor_get(v_inst_2910_, 1);
lean_inc_n(v_toBind_2914_, 2);
v_toPure_2915_ = lean_ctor_get(v_toApplicative_2913_, 1);
v_ctorName_2916_ = lean_ctor_get(v_alt_2912_, 0);
lean_inc(v_ctorName_2916_);
v_params_2917_ = lean_ctor_get(v_alt_2912_, 1);
lean_inc_ref(v_params_2917_);
v_code_2918_ = lean_ctor_get(v_alt_2912_, 2);
lean_inc_ref(v_code_2918_);
lean_dec_ref_known(v_alt_2912_, 3);
v___x_2919_ = lean_box(v_pu_2907_);
lean_inc(v_f_2911_);
lean_inc_ref_n(v_inst_2910_, 2);
lean_inc(v_inst_2909_);
lean_inc(v_toPure_2915_);
v___f_2920_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2920_, 0, v_ctorName_2916_);
lean_closure_set(v___f_2920_, 1, v_toPure_2915_);
lean_closure_set(v___f_2920_, 2, v___x_2919_);
lean_closure_set(v___f_2920_, 3, v_inst_2909_);
lean_closure_set(v___f_2920_, 4, v_inst_2910_);
lean_closure_set(v___f_2920_, 5, v_f_2911_);
lean_closure_set(v___f_2920_, 6, v_code_2918_);
lean_closure_set(v___f_2920_, 7, v_toBind_2914_);
v___x_2921_ = lean_box(v_pu_2907_);
v___x_2922_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2922_, 0, lean_box(0));
lean_closure_set(v___x_2922_, 1, v___x_2921_);
lean_closure_set(v___x_2922_, 2, v_inst_2909_);
lean_closure_set(v___x_2922_, 3, v_inst_2910_);
lean_closure_set(v___x_2922_, 4, v_f_2911_);
v_sz_2923_ = lean_array_size(v_params_2917_);
v___x_2924_ = ((size_t)0ULL);
v___x_2925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2910_, v___x_2922_, v_sz_2923_, v___x_2924_, v_params_2917_);
v___x_2926_ = lean_apply_4(v_toBind_2914_, lean_box(0), lean_box(0), v___x_2925_, v___f_2920_);
return v___x_2926_;
}
case 1:
{
lean_object* v_toApplicative_2927_; lean_object* v_toBind_2928_; lean_object* v_toPure_2929_; lean_object* v_info_2930_; lean_object* v_code_2931_; lean_object* v___f_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v_toApplicative_2927_ = lean_ctor_get(v_inst_2910_, 0);
v_toBind_2928_ = lean_ctor_get(v_inst_2910_, 1);
lean_inc(v_toBind_2928_);
v_toPure_2929_ = lean_ctor_get(v_toApplicative_2927_, 1);
v_info_2930_ = lean_ctor_get(v_alt_2912_, 0);
lean_inc_ref(v_info_2930_);
v_code_2931_ = lean_ctor_get(v_alt_2912_, 1);
lean_inc_ref(v_code_2931_);
lean_dec_ref_known(v_alt_2912_, 2);
lean_inc(v_toPure_2929_);
v___f_2932_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2), 3, 2);
lean_closure_set(v___f_2932_, 0, v_info_2930_);
lean_closure_set(v___f_2932_, 1, v_toPure_2929_);
v___x_2933_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2907_, v_inst_2909_, v_inst_2910_, v_f_2911_, v_code_2931_);
v___x_2934_ = lean_apply_4(v_toBind_2928_, lean_box(0), lean_box(0), v___x_2933_, v___f_2932_);
return v___x_2934_;
}
default: 
{
lean_object* v_toApplicative_2935_; lean_object* v_toBind_2936_; lean_object* v_toPure_2937_; lean_object* v_code_2938_; lean_object* v___f_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v_toApplicative_2935_ = lean_ctor_get(v_inst_2910_, 0);
v_toBind_2936_ = lean_ctor_get(v_inst_2910_, 1);
lean_inc(v_toBind_2936_);
v_toPure_2937_ = lean_ctor_get(v_toApplicative_2935_, 1);
v_code_2938_ = lean_ctor_get(v_alt_2912_, 0);
lean_inc_ref(v_code_2938_);
lean_dec_ref_known(v_alt_2912_, 1);
lean_inc(v_toPure_2937_);
v___f_2939_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3), 2, 1);
lean_closure_set(v___f_2939_, 0, v_toPure_2937_);
v___x_2940_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2907_, v_inst_2909_, v_inst_2910_, v_f_2911_, v_code_2938_);
v___x_2941_ = lean_apply_4(v_toBind_2936_, lean_box(0), lean_box(0), v___x_2940_, v___f_2939_);
return v___x_2941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed(lean_object* v_pu_2942_, lean_object* v_m_2943_, lean_object* v_inst_2944_, lean_object* v_inst_2945_, lean_object* v_f_2946_, lean_object* v_alt_2947_){
_start:
{
uint8_t v_pu_boxed_2948_; lean_object* v_res_2949_; 
v_pu_boxed_2948_ = lean_unbox(v_pu_2942_);
v_res_2949_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(v_pu_boxed_2948_, v_m_2943_, v_inst_2944_, v_inst_2945_, v_f_2946_, v_alt_2947_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5(lean_object* v_inst_2950_, lean_object* v_f_2951_, lean_object* v_code_2952_, lean_object* v_____r_2953_){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2950_, v_f_2951_, v_code_2952_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__7(lean_object* v_m_2955_, lean_object* v_inst_2956_, lean_object* v_f_2957_, lean_object* v_alt_2958_){
_start:
{
switch(lean_obj_tag(v_alt_2958_))
{
case 0:
{
lean_object* v_toApplicative_2959_; lean_object* v_toBind_2960_; lean_object* v_params_2961_; lean_object* v_code_2962_; lean_object* v_toPure_2963_; lean_object* v___f_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; uint8_t v___x_2968_; 
v_toApplicative_2959_ = lean_ctor_get(v_inst_2956_, 0);
v_toBind_2960_ = lean_ctor_get(v_inst_2956_, 1);
lean_inc(v_toBind_2960_);
v_params_2961_ = lean_ctor_get(v_alt_2958_, 1);
lean_inc_ref(v_params_2961_);
v_code_2962_ = lean_ctor_get(v_alt_2958_, 2);
lean_inc_ref(v_code_2962_);
lean_dec_ref_known(v_alt_2958_, 3);
v_toPure_2963_ = lean_ctor_get(v_toApplicative_2959_, 1);
lean_inc(v_f_2957_);
lean_inc_ref(v_inst_2956_);
v___f_2964_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5), 4, 3);
lean_closure_set(v___f_2964_, 0, v_inst_2956_);
lean_closure_set(v___f_2964_, 1, v_f_2957_);
lean_closure_set(v___f_2964_, 2, v_code_2962_);
v___x_2965_ = lean_unsigned_to_nat(0u);
v___x_2966_ = lean_array_get_size(v_params_2961_);
v___x_2967_ = lean_box(0);
v___x_2968_ = lean_nat_dec_lt(v___x_2965_, v___x_2966_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
lean_inc(v_toPure_2963_);
lean_dec_ref(v_params_2961_);
lean_dec(v_f_2957_);
lean_dec_ref(v_inst_2956_);
v___x_2969_ = lean_apply_2(v_toPure_2963_, lean_box(0), v___x_2967_);
v___x_2970_ = lean_apply_4(v_toBind_2960_, lean_box(0), lean_box(0), v___x_2969_, v___f_2964_);
return v___x_2970_;
}
else
{
lean_object* v___f_2971_; size_t v___x_2972_; size_t v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
lean_inc_ref(v_inst_2956_);
v___f_2971_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_2971_, 0, v_inst_2956_);
lean_closure_set(v___f_2971_, 1, v_f_2957_);
v___x_2972_ = ((size_t)0ULL);
v___x_2973_ = lean_usize_of_nat(v___x_2966_);
v___x_2974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2956_, v___f_2971_, v_params_2961_, v___x_2972_, v___x_2973_, v___x_2967_);
v___x_2975_ = lean_apply_4(v_toBind_2960_, lean_box(0), lean_box(0), v___x_2974_, v___f_2964_);
return v___x_2975_;
}
}
case 1:
{
lean_object* v_code_2976_; lean_object* v___x_2977_; 
v_code_2976_ = lean_ctor_get(v_alt_2958_, 1);
lean_inc_ref(v_code_2976_);
lean_dec_ref_known(v_alt_2958_, 2);
v___x_2977_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2956_, v_f_2957_, v_code_2976_);
return v___x_2977_;
}
default: 
{
lean_object* v_code_2978_; lean_object* v___x_2979_; 
v_code_2978_ = lean_ctor_get(v_alt_2958_, 0);
lean_inc_ref(v_code_2978_);
lean_dec_ref_known(v_alt_2958_, 1);
v___x_2979_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2956_, v_f_2957_, v_code_2978_);
return v___x_2979_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt(uint8_t v_pu_2981_){
_start:
{
lean_object* v___x_2982_; lean_object* v___f_2983_; lean_object* v___f_2984_; lean_object* v___x_2985_; 
v___x_2982_ = lean_box(v_pu_2981_);
v___f_2983_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed), 6, 1);
lean_closure_set(v___f_2983_, 0, v___x_2982_);
v___f_2984_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0));
v___x_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___f_2983_);
lean_ctor_set(v___x_2985_, 1, v___f_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___boxed(lean_object* v_pu_2986_){
_start:
{
uint8_t v_pu_boxed_2987_; lean_object* v_res_2988_; 
v_pu_boxed_2987_ = lean_unbox(v_pu_2986_);
v_res_2988_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt(v_pu_boxed_2987_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(lean_object* v_toPure_2991_, lean_object* v_____do__lift_2992_){
_start:
{
if (lean_obj_tag(v_____do__lift_2992_) == 0)
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = lean_box(0);
v___x_2994_ = lean_apply_2(v_toPure_2991_, lean_box(0), v___x_2993_);
return v___x_2994_;
}
else
{
lean_object* v_val_2995_; uint8_t v___x_2996_; 
v_val_2995_ = lean_ctor_get(v_____do__lift_2992_, 0);
v___x_2996_ = lean_unbox(v_val_2995_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0));
v___x_2998_ = lean_apply_2(v_toPure_2991_, lean_box(0), v___x_2997_);
return v___x_2998_;
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = lean_box(0);
v___x_3000_ = lean_apply_2(v_toPure_2991_, lean_box(0), v___x_2999_);
return v___x_3000_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed(lean_object* v_toPure_3001_, lean_object* v_____do__lift_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(v_toPure_3001_, v_____do__lift_3002_);
lean_dec(v_____do__lift_3002_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(lean_object* v_toPure_3004_, uint8_t v_____do__lift_3005_){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3006_ = lean_box(v_____do__lift_3005_);
v___x_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
v___x_3008_ = lean_apply_2(v_toPure_3004_, lean_box(0), v___x_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed(lean_object* v_toPure_3009_, lean_object* v_____do__lift_3010_){
_start:
{
uint8_t v_____do__lift_371__boxed_3011_; lean_object* v_res_3012_; 
v_____do__lift_371__boxed_3011_ = lean_unbox(v_____do__lift_3010_);
v_res_3012_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(v_toPure_3009_, v_____do__lift_371__boxed_3011_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(lean_object* v_inst_3013_, lean_object* v_f_3014_, lean_object* v_fvar_3015_){
_start:
{
lean_object* v_toApplicative_3016_; lean_object* v_toBind_3017_; lean_object* v_toPure_3018_; lean_object* v___x_3019_; lean_object* v___f_3020_; lean_object* v___f_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v_toApplicative_3016_ = lean_ctor_get(v_inst_3013_, 0);
lean_inc_ref(v_toApplicative_3016_);
v_toBind_3017_ = lean_ctor_get(v_inst_3013_, 1);
lean_inc_n(v_toBind_3017_, 2);
lean_dec_ref(v_inst_3013_);
v_toPure_3018_ = lean_ctor_get(v_toApplicative_3016_, 1);
lean_inc_n(v_toPure_3018_, 2);
lean_dec_ref(v_toApplicative_3016_);
v___x_3019_ = lean_apply_1(v_f_3014_, v_fvar_3015_);
v___f_3020_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3020_, 0, v_toPure_3018_);
v___f_3021_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3021_, 0, v_toPure_3018_);
v___x_3022_ = lean_apply_4(v_toBind_3017_, lean_box(0), lean_box(0), v___x_3019_, v___f_3021_);
v___x_3023_ = lean_apply_4(v_toBind_3017_, lean_box(0), lean_box(0), v___x_3022_, v___f_3020_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go(lean_object* v_m_3024_, lean_object* v_inst_3025_, lean_object* v_f_3026_, lean_object* v_fvar_3027_){
_start:
{
lean_object* v___x_3028_; 
v___x_3028_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(v_inst_3025_, v_f_3026_, v_fvar_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(lean_object* v_toPure_3029_, lean_object* v_____do__lift_3030_){
_start:
{
if (lean_obj_tag(v_____do__lift_3030_) == 0)
{
uint8_t v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3031_ = 1;
v___x_3032_ = lean_box(v___x_3031_);
v___x_3033_ = lean_apply_2(v_toPure_3029_, lean_box(0), v___x_3032_);
return v___x_3033_;
}
else
{
uint8_t v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3034_ = 0;
v___x_3035_ = lean_box(v___x_3034_);
v___x_3036_ = lean_apply_2(v_toPure_3029_, lean_box(0), v___x_3035_);
return v___x_3036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed(lean_object* v_toPure_3037_, lean_object* v_____do__lift_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(v_toPure_3037_, v_____do__lift_3038_);
lean_dec(v_____do__lift_3038_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg(lean_object* v_inst_3040_, lean_object* v_inst_3041_, lean_object* v_f_3042_, lean_object* v_x_3043_){
_start:
{
lean_object* v_toApplicative_3044_; lean_object* v_toBind_3045_; lean_object* v_forFVarM_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3067_; 
v_toApplicative_3044_ = lean_ctor_get(v_inst_3040_, 0);
v_toBind_3045_ = lean_ctor_get(v_inst_3040_, 1);
lean_inc(v_toBind_3045_);
v_forFVarM_3046_ = lean_ctor_get(v_inst_3041_, 1);
v_isSharedCheck_3067_ = !lean_is_exclusive(v_inst_3041_);
if (v_isSharedCheck_3067_ == 0)
{
lean_object* v_unused_3068_; 
v_unused_3068_ = lean_ctor_get(v_inst_3041_, 0);
lean_dec(v_unused_3068_);
v___x_3048_ = v_inst_3041_;
v_isShared_3049_ = v_isSharedCheck_3067_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_forFVarM_3046_);
lean_dec(v_inst_3041_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3067_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___f_3050_; lean_object* v___f_3051_; lean_object* v___f_3052_; lean_object* v___f_3053_; lean_object* v___f_3054_; lean_object* v___x_3056_; 
lean_inc_ref_n(v_inst_3040_, 5);
v___f_3050_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3050_, 0, v_inst_3040_);
v___f_3051_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3051_, 0, v_inst_3040_);
v___f_3052_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3052_, 0, v_inst_3040_);
v___f_3053_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3053_, 0, v_inst_3040_);
v___f_3054_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3054_, 0, v_inst_3040_);
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 1, v___f_3051_);
lean_ctor_set(v___x_3048_, 0, v___f_3050_);
v___x_3056_ = v___x_3048_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___f_3050_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v___f_3051_);
v___x_3056_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v_toPure_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___f_3064_; lean_object* v___x_3065_; 
lean_inc_ref_n(v_inst_3040_, 2);
v___x_3057_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3057_, 0, lean_box(0));
lean_closure_set(v___x_3057_, 1, v_inst_3040_);
v___x_3058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3056_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
lean_ctor_set(v___x_3058_, 2, v___f_3052_);
lean_ctor_set(v___x_3058_, 3, v___f_3053_);
lean_ctor_set(v___x_3058_, 4, v___f_3054_);
v___x_3059_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3059_, 0, lean_box(0));
lean_closure_set(v___x_3059_, 1, v_inst_3040_);
v___x_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3058_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
v_toPure_3061_ = lean_ctor_get(v_toApplicative_3044_, 1);
lean_inc(v_toPure_3061_);
v___x_3062_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go), 4, 3);
lean_closure_set(v___x_3062_, 0, lean_box(0));
lean_closure_set(v___x_3062_, 1, v_inst_3040_);
lean_closure_set(v___x_3062_, 2, v_f_3042_);
v___x_3063_ = lean_apply_4(v_forFVarM_3046_, lean_box(0), v___x_3060_, v___x_3062_, v_x_3043_);
v___f_3064_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3064_, 0, v_toPure_3061_);
v___x_3065_ = lean_apply_4(v_toBind_3045_, lean_box(0), lean_box(0), v___x_3063_, v___f_3064_);
return v___x_3065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM(lean_object* v_m_3069_, lean_object* v_00_u03b1_3070_, lean_object* v_inst_3071_, lean_object* v_inst_3072_, lean_object* v_f_3073_, lean_object* v_x_3074_){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_Compiler_LCNF_anyFVarM___redArg(v_inst_3071_, v_inst_3072_, v_f_3073_, v_x_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(lean_object* v_toPure_3076_, lean_object* v_____do__lift_3077_){
_start:
{
if (lean_obj_tag(v_____do__lift_3077_) == 0)
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = lean_box(0);
v___x_3079_ = lean_apply_2(v_toPure_3076_, lean_box(0), v___x_3078_);
return v___x_3079_;
}
else
{
lean_object* v_val_3080_; uint8_t v___x_3081_; 
v_val_3080_ = lean_ctor_get(v_____do__lift_3077_, 0);
v___x_3081_ = lean_unbox(v_val_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = lean_box(0);
v___x_3083_ = lean_apply_2(v_toPure_3076_, lean_box(0), v___x_3082_);
return v___x_3083_;
}
else
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0));
v___x_3085_ = lean_apply_2(v_toPure_3076_, lean_box(0), v___x_3084_);
return v___x_3085_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed(lean_object* v_toPure_3086_, lean_object* v_____do__lift_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(v_toPure_3086_, v_____do__lift_3087_);
lean_dec(v_____do__lift_3087_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(lean_object* v_inst_3089_, lean_object* v_f_3090_, lean_object* v_fvar_3091_){
_start:
{
lean_object* v_toApplicative_3092_; lean_object* v_toBind_3093_; lean_object* v_toPure_3094_; lean_object* v___x_3095_; lean_object* v___f_3096_; lean_object* v___f_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v_toApplicative_3092_ = lean_ctor_get(v_inst_3089_, 0);
lean_inc_ref(v_toApplicative_3092_);
v_toBind_3093_ = lean_ctor_get(v_inst_3089_, 1);
lean_inc_n(v_toBind_3093_, 2);
lean_dec_ref(v_inst_3089_);
v_toPure_3094_ = lean_ctor_get(v_toApplicative_3092_, 1);
lean_inc_n(v_toPure_3094_, 2);
lean_dec_ref(v_toApplicative_3092_);
v___x_3095_ = lean_apply_1(v_f_3090_, v_fvar_3091_);
v___f_3096_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3096_, 0, v_toPure_3094_);
v___f_3097_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3097_, 0, v_toPure_3094_);
v___x_3098_ = lean_apply_4(v_toBind_3093_, lean_box(0), lean_box(0), v___x_3095_, v___f_3097_);
v___x_3099_ = lean_apply_4(v_toBind_3093_, lean_box(0), lean_box(0), v___x_3098_, v___f_3096_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go(lean_object* v_m_3100_, lean_object* v_inst_3101_, lean_object* v_f_3102_, lean_object* v_fvar_3103_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(v_inst_3101_, v_f_3102_, v_fvar_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(lean_object* v_toPure_3105_, lean_object* v_____do__lift_3106_){
_start:
{
if (lean_obj_tag(v_____do__lift_3106_) == 1)
{
uint8_t v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3107_ = 1;
v___x_3108_ = lean_box(v___x_3107_);
v___x_3109_ = lean_apply_2(v_toPure_3105_, lean_box(0), v___x_3108_);
return v___x_3109_;
}
else
{
uint8_t v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3110_ = 0;
v___x_3111_ = lean_box(v___x_3110_);
v___x_3112_ = lean_apply_2(v_toPure_3105_, lean_box(0), v___x_3111_);
return v___x_3112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed(lean_object* v_toPure_3113_, lean_object* v_____do__lift_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(v_toPure_3113_, v_____do__lift_3114_);
lean_dec(v_____do__lift_3114_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg(lean_object* v_inst_3116_, lean_object* v_inst_3117_, lean_object* v_f_3118_, lean_object* v_x_3119_){
_start:
{
lean_object* v_toApplicative_3120_; lean_object* v_toBind_3121_; lean_object* v_forFVarM_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3143_; 
v_toApplicative_3120_ = lean_ctor_get(v_inst_3116_, 0);
v_toBind_3121_ = lean_ctor_get(v_inst_3116_, 1);
lean_inc(v_toBind_3121_);
v_forFVarM_3122_ = lean_ctor_get(v_inst_3117_, 1);
v_isSharedCheck_3143_ = !lean_is_exclusive(v_inst_3117_);
if (v_isSharedCheck_3143_ == 0)
{
lean_object* v_unused_3144_; 
v_unused_3144_ = lean_ctor_get(v_inst_3117_, 0);
lean_dec(v_unused_3144_);
v___x_3124_ = v_inst_3117_;
v_isShared_3125_ = v_isSharedCheck_3143_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_forFVarM_3122_);
lean_dec(v_inst_3117_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3143_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___f_3126_; lean_object* v___f_3127_; lean_object* v___f_3128_; lean_object* v___f_3129_; lean_object* v___f_3130_; lean_object* v___x_3132_; 
lean_inc_ref_n(v_inst_3116_, 5);
v___f_3126_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3126_, 0, v_inst_3116_);
v___f_3127_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3127_, 0, v_inst_3116_);
v___f_3128_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3128_, 0, v_inst_3116_);
v___f_3129_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3129_, 0, v_inst_3116_);
v___f_3130_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3130_, 0, v_inst_3116_);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 1, v___f_3127_);
lean_ctor_set(v___x_3124_, 0, v___f_3126_);
v___x_3132_ = v___x_3124_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___f_3126_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v___f_3127_);
v___x_3132_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v_toPure_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___f_3140_; lean_object* v___x_3141_; 
lean_inc_ref_n(v_inst_3116_, 2);
v___x_3133_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3133_, 0, lean_box(0));
lean_closure_set(v___x_3133_, 1, v_inst_3116_);
v___x_3134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3132_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
lean_ctor_set(v___x_3134_, 2, v___f_3128_);
lean_ctor_set(v___x_3134_, 3, v___f_3129_);
lean_ctor_set(v___x_3134_, 4, v___f_3130_);
v___x_3135_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3135_, 0, lean_box(0));
lean_closure_set(v___x_3135_, 1, v_inst_3116_);
v___x_3136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3134_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v_toPure_3137_ = lean_ctor_get(v_toApplicative_3120_, 1);
lean_inc(v_toPure_3137_);
v___x_3138_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go), 4, 3);
lean_closure_set(v___x_3138_, 0, lean_box(0));
lean_closure_set(v___x_3138_, 1, v_inst_3116_);
lean_closure_set(v___x_3138_, 2, v_f_3118_);
v___x_3139_ = lean_apply_4(v_forFVarM_3122_, lean_box(0), v___x_3136_, v___x_3138_, v_x_3119_);
v___f_3140_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3140_, 0, v_toPure_3137_);
v___x_3141_ = lean_apply_4(v_toBind_3121_, lean_box(0), lean_box(0), v___x_3139_, v___f_3140_);
return v___x_3141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM(lean_object* v_m_3145_, lean_object* v_00_u03b1_3146_, lean_object* v_inst_3147_, lean_object* v_inst_3148_, lean_object* v_f_3149_, lean_object* v_x_3150_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l_Lean_Compiler_LCNF_allFVarM___redArg(v_inst_3147_, v_inst_3148_, v_f_3149_, v_x_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(lean_object* v_f_3152_, lean_object* v_x_3153_){
_start:
{
lean_object* v___x_3154_; uint8_t v___x_3155_; 
v___x_3154_ = lean_apply_1(v_f_3152_, v_x_3153_);
v___x_3155_ = lean_unbox(v___x_3154_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed(lean_object* v_f_3156_, lean_object* v_x_3157_){
_start:
{
uint8_t v_res_3158_; lean_object* v_r_3159_; 
v_res_3158_ = l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(v_f_3156_, v_x_3157_);
v_r_3159_ = lean_box(v_res_3158_);
return v_r_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg(lean_object* v_inst_3179_, lean_object* v_f_3180_, lean_object* v_x_3181_){
_start:
{
lean_object* v___f_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___f_3182_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3182_, 0, v_f_3180_);
v___x_3183_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9));
v___x_3184_ = l_Lean_Compiler_LCNF_anyFVarM___redArg(v___x_3183_, v_inst_3179_, v___f_3182_, v_x_3181_);
return v___x_3184_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar(lean_object* v_00_u03b1_3185_, lean_object* v_inst_3186_, lean_object* v_f_3187_, lean_object* v_x_3188_){
_start:
{
lean_object* v___x_3189_; uint8_t v___x_3190_; 
v___x_3189_ = l_Lean_Compiler_LCNF_anyFVar___redArg(v_inst_3186_, v_f_3187_, v_x_3188_);
v___x_3190_ = lean_unbox(v___x_3189_);
lean_dec(v___x_3189_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___boxed(lean_object* v_00_u03b1_3191_, lean_object* v_inst_3192_, lean_object* v_f_3193_, lean_object* v_x_3194_){
_start:
{
uint8_t v_res_3195_; lean_object* v_r_3196_; 
v_res_3195_ = l_Lean_Compiler_LCNF_anyFVar(v_00_u03b1_3191_, v_inst_3192_, v_f_3193_, v_x_3194_);
v_r_3196_ = lean_box(v_res_3195_);
return v_r_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___redArg(lean_object* v_inst_3197_, lean_object* v_f_3198_, lean_object* v_x_3199_){
_start:
{
lean_object* v___f_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___f_3200_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3200_, 0, v_f_3198_);
v___x_3201_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9));
v___x_3202_ = l_Lean_Compiler_LCNF_allFVarM___redArg(v___x_3201_, v_inst_3197_, v___f_3200_, v_x_3199_);
return v___x_3202_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar(lean_object* v_00_u03b1_3203_, lean_object* v_inst_3204_, lean_object* v_f_3205_, lean_object* v_x_3206_){
_start:
{
lean_object* v___x_3207_; uint8_t v___x_3208_; 
v___x_3207_ = l_Lean_Compiler_LCNF_allFVar___redArg(v_inst_3204_, v_f_3205_, v_x_3206_);
v___x_3208_ = lean_unbox(v___x_3207_);
lean_dec(v___x_3207_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___boxed(lean_object* v_00_u03b1_3209_, lean_object* v_inst_3210_, lean_object* v_f_3211_, lean_object* v_x_3212_){
_start:
{
uint8_t v_res_3213_; lean_object* v_r_3214_; 
v_res_3213_ = l_Lean_Compiler_LCNF_allFVar(v_00_u03b1_3209_, v_inst_3210_, v_f_3211_, v_x_3212_);
v_r_3214_ = lean_box(v_res_3213_);
return v_r_3214_;
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
