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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7___boxed(lean_object* v_e_456_, lean_object* v_____do__lift_457_, lean_object* v_toPure_458_, lean_object* v_____do__lift_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7(v_e_456_, v_____do__lift_457_, v_toPure_458_, v_____do__lift_459_);
lean_dec(v_e_456_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3(lean_object* v_e_461_, lean_object* v_toPure_462_, lean_object* v_args_463_, lean_object* v_inst_464_, lean_object* v___f_465_, lean_object* v_toBind_466_, lean_object* v_____do__lift_467_){
_start:
{
lean_object* v___f_468_; size_t v_sz_469_; size_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___f_468_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7___boxed), 4, 3);
lean_closure_set(v___f_468_, 0, v_e_461_);
lean_closure_set(v___f_468_, 1, v_____do__lift_467_);
lean_closure_set(v___f_468_, 2, v_toPure_462_);
v_sz_469_ = lean_array_size(v_args_463_);
v___x_470_ = ((size_t)0ULL);
v___x_471_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_464_, v___f_465_, v_sz_469_, v___x_470_, v_args_463_);
v___x_472_ = lean_apply_4(v_toBind_466_, lean_box(0), lean_box(0), v___x_471_, v___f_468_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8(lean_object* v_e_473_, lean_object* v_n_474_, lean_object* v_toPure_475_, lean_object* v_____do__lift_476_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp___redArg(v_e_473_, v_n_474_, v_____do__lift_476_);
v___x_478_ = lean_apply_2(v_toPure_475_, lean_box(0), v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(lean_object* v_e_479_, lean_object* v_____do__lift_480_, lean_object* v_i_481_, uint8_t v_updateHeader_482_, lean_object* v_toPure_483_, lean_object* v_____do__lift_484_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp___redArg(v_e_479_, v_____do__lift_480_, v_i_481_, v_updateHeader_482_, v_____do__lift_484_);
v___x_486_ = lean_apply_2(v_toPure_483_, lean_box(0), v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed(lean_object* v_e_487_, lean_object* v_____do__lift_488_, lean_object* v_i_489_, lean_object* v_updateHeader_490_, lean_object* v_toPure_491_, lean_object* v_____do__lift_492_){
_start:
{
uint8_t v_updateHeader_632__boxed_493_; lean_object* v_res_494_; 
v_updateHeader_632__boxed_493_ = lean_unbox(v_updateHeader_490_);
v_res_494_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(v_e_487_, v_____do__lift_488_, v_i_489_, v_updateHeader_632__boxed_493_, v_toPure_491_, v_____do__lift_492_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(lean_object* v_e_495_, lean_object* v_i_496_, uint8_t v_updateHeader_497_, lean_object* v_toPure_498_, lean_object* v_args_499_, lean_object* v_inst_500_, lean_object* v___f_501_, lean_object* v_toBind_502_, lean_object* v_____do__lift_503_){
_start:
{
lean_object* v___x_504_; lean_object* v___f_505_; size_t v_sz_506_; size_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_504_ = lean_box(v_updateHeader_497_);
v___f_505_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_505_, 0, v_e_495_);
lean_closure_set(v___f_505_, 1, v_____do__lift_503_);
lean_closure_set(v___f_505_, 2, v_i_496_);
lean_closure_set(v___f_505_, 3, v___x_504_);
lean_closure_set(v___f_505_, 4, v_toPure_498_);
v_sz_506_ = lean_array_size(v_args_499_);
v___x_507_ = ((size_t)0ULL);
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_500_, v___f_501_, v_sz_506_, v___x_507_, v_args_499_);
v___x_509_ = lean_apply_4(v_toBind_502_, lean_box(0), lean_box(0), v___x_508_, v___f_505_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed(lean_object* v_e_510_, lean_object* v_i_511_, lean_object* v_updateHeader_512_, lean_object* v_toPure_513_, lean_object* v_args_514_, lean_object* v_inst_515_, lean_object* v___f_516_, lean_object* v_toBind_517_, lean_object* v_____do__lift_518_){
_start:
{
uint8_t v_updateHeader_647__boxed_519_; lean_object* v_res_520_; 
v_updateHeader_647__boxed_519_ = lean_unbox(v_updateHeader_512_);
v_res_520_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(v_e_510_, v_i_511_, v_updateHeader_647__boxed_519_, v_toPure_513_, v_args_514_, v_inst_515_, v___f_516_, v_toBind_517_, v_____do__lift_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6(lean_object* v_e_521_, lean_object* v_ty_522_, lean_object* v_toPure_523_, lean_object* v_____do__lift_524_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp___redArg(v_e_521_, v_ty_522_, v_____do__lift_524_);
v___x_526_ = lean_apply_2(v_toPure_523_, lean_box(0), v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9(lean_object* v_e_527_, lean_object* v_toPure_528_, lean_object* v_____do__lift_529_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp___redArg(v_e_527_, v_____do__lift_529_);
v___x_531_ = lean_apply_2(v_toPure_528_, lean_box(0), v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10(lean_object* v_e_532_, lean_object* v_toPure_533_, lean_object* v_____do__lift_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp___redArg(v_e_532_, v_____do__lift_534_);
v___x_536_ = lean_apply_2(v_toPure_533_, lean_box(0), v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(uint8_t v_pu_537_, lean_object* v_inst_538_, lean_object* v_f_539_, lean_object* v_e_540_){
_start:
{
lean_object* v_toApplicative_541_; lean_object* v_toBind_542_; lean_object* v_toPure_543_; lean_object* v___x_544_; lean_object* v___f_545_; lean_object* v___f_546_; lean_object* v_args_548_; lean_object* v___x_553_; lean_object* v___f_554_; lean_object* v_fvarId_556_; 
v_toApplicative_541_ = lean_ctor_get(v_inst_538_, 0);
v_toBind_542_ = lean_ctor_get(v_inst_538_, 1);
lean_inc(v_toBind_542_);
v_toPure_543_ = lean_ctor_get(v_toApplicative_541_, 1);
v___x_544_ = lean_box(v_pu_537_);
lean_inc(v_f_539_);
lean_inc_ref(v_inst_538_);
v___f_545_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_545_, 0, v___x_544_);
lean_closure_set(v___f_545_, 1, v_inst_538_);
lean_closure_set(v___f_545_, 2, v_f_539_);
lean_inc_n(v_toPure_543_, 2);
lean_inc_n(v_e_540_, 2);
v___f_546_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1), 3, 2);
lean_closure_set(v___f_546_, 0, v_e_540_);
lean_closure_set(v___f_546_, 1, v_toPure_543_);
v___x_553_ = lean_box(v_pu_537_);
v___f_554_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_554_, 0, v___x_553_);
lean_closure_set(v___f_554_, 1, v_e_540_);
lean_closure_set(v___f_554_, 2, v_toPure_543_);
switch(lean_obj_tag(v_e_540_))
{
case 2:
{
lean_object* v_struct_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec_ref(v___f_546_);
lean_dec_ref(v___f_545_);
lean_dec_ref(v_inst_538_);
v_struct_559_ = lean_ctor_get(v_e_540_, 2);
lean_inc(v_struct_559_);
lean_dec_ref_known(v_e_540_, 3);
v___x_560_ = lean_apply_1(v_f_539_, v_struct_559_);
v___x_561_ = lean_apply_4(v_toBind_542_, lean_box(0), lean_box(0), v___x_560_, v___f_554_);
return v___x_561_;
}
case 3:
{
lean_object* v_args_562_; size_t v_sz_563_; size_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec_ref(v___f_554_);
lean_dec(v_f_539_);
v_args_562_ = lean_ctor_get(v_e_540_, 2);
lean_inc_ref(v_args_562_);
lean_dec_ref_known(v_e_540_, 3);
v_sz_563_ = lean_array_size(v_args_562_);
v___x_564_ = ((size_t)0ULL);
v___x_565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_538_, v___f_545_, v_sz_563_, v___x_564_, v_args_562_);
v___x_566_ = lean_apply_4(v_toBind_542_, lean_box(0), lean_box(0), v___x_565_, v___f_546_);
return v___x_566_;
}
case 4:
{
lean_object* v_fvarId_567_; lean_object* v_args_568_; lean_object* v___f_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
lean_inc(v_toPure_543_);
lean_dec_ref(v___f_554_);
lean_dec_ref(v___f_546_);
v_fvarId_567_ = lean_ctor_get(v_e_540_, 0);
lean_inc(v_fvarId_567_);
v_args_568_ = lean_ctor_get(v_e_540_, 1);
lean_inc_ref(v_args_568_);
lean_inc(v_toBind_542_);
v___f_569_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3), 7, 6);
lean_closure_set(v___f_569_, 0, v_e_540_);
lean_closure_set(v___f_569_, 1, v_toPure_543_);
lean_closure_set(v___f_569_, 2, v_args_568_);
lean_closure_set(v___f_569_, 3, v_inst_538_);
lean_closure_set(v___f_569_, 4, v___f_545_);
lean_closure_set(v___f_569_, 5, v_toBind_542_);
v___x_570_ = lean_apply_1(v_f_539_, v_fvarId_567_);
v___x_571_ = lean_apply_4(v_toBind_542_, lean_box(0), lean_box(0), v___x_570_, v___f_569_);
return v___x_571_;
}
case 5:
{
lean_object* v_args_572_; size_t v_sz_573_; size_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec_ref(v___f_554_);
lean_dec(v_f_539_);
v_args_572_ = lean_ctor_get(v_e_540_, 1);
lean_inc_ref(v_args_572_);
lean_dec_ref_known(v_e_540_, 2);
v_sz_573_ = lean_array_size(v_args_572_);
v___x_574_ = ((size_t)0ULL);
v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_538_, v___f_545_, v_sz_573_, v___x_574_, v_args_572_);
v___x_576_ = lean_apply_4(v_toBind_542_, lean_box(0), lean_box(0), v___x_575_, v___f_546_);
return v___x_576_;
}
case 6:
{
lean_object* v_var_577_; 
lean_dec_ref(v___f_546_);
lean_dec_ref(v___f_545_);
lean_dec_ref(v_inst_538_);
v_var_577_ = lean_ctor_get(v_e_540_, 1);
lean_inc(v_var_577_);
lean_dec_ref_known(v_e_540_, 2);
v_fvarId_556_ = v_var_577_;
goto v___jp_555_;
}
case 7:
{
lean_object* v_var_578_; 
lean_dec_ref(v___f_546_);
lean_dec_ref(v___f_545_);
lean_dec_ref(v_inst_538_);
v_var_578_ = lean_ctor_get(v_e_540_, 1);
lean_inc(v_var_578_);
lean_dec_ref_known(v_e_540_, 2);
v_fvarId_556_ = v_var_578_;
goto v___jp_555_;
}
case 8:
{
lean_object* v_var_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec_ref(v___f_546_);
lean_dec_ref(v___f_545_);
lean_dec_ref(v_inst_538_);
v_var_579_ = lean_ctor_get(v_e_540_, 2);
lean_inc(v_var_579_);
lean_dec_ref_known(v_e_540_, 3);
v___x_580_ = lean_apply_1(v_f_539_, v_var_579_);
v___x_581_ = lean_apply_4(v_toBind_542_, lean_box(0), lean_box(0), v___x_580_, v___f_554_);
return v___x_581_;
}
case 9:
{
lean_object* v_args_582_; 
lean_dec_ref(v___f_554_);
lean_dec(v_f_539_);
v_args_582_ = lean_ctor_get(v_e_540_, 1);
lean_inc_ref(v_args_582_);
lean_dec_ref_known(v_e_540_, 2);
v_args_548_ = v_args_582_;
goto v___jp_547_;
}
case 10:
{
lean_object* v_args_583_; 
lean_dec_ref(v___f_554_);
lean_dec(v_f_539_);
v_args_583_ = lean_ctor_get(v_e_540_, 1);
lean_inc_ref(v_args_583_);
lean_dec_ref_known(v_e_540_, 2);
v_args_548_ = v_args_583_;
goto v___jp_547_;
}
case 11:
{
lean_object* v_n_584_; lean_object* v_var_585_; lean_object* v___f_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
lean_inc(v_toPure_543_);
lean_dec_ref(v___f_554_);
lean_dec_ref(v___f_546_);
lean_dec_ref(v___f_545_);
lean_dec_ref(v_inst_538_);
v_n_584_ = lean_ctor_get(v_e_540_, 0);
lean_inc(v_n_584_);
v_var_585_ = lean_ctor_get(v_e_540_, 1);
lean_inc(v_var_585_);
v___f_586_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8), 4, 3);
lean_closure_set(v___f_586_, 0, v_e_540_);
lean_closure_set(v___f_586_, 1, v_n_584_);
lean_closure_set(v___f_586_, 2, v_toPure_543_);
v___x_587_ = lean_apply_1(v_f_539_, v_var_585_);
v___x_588_ = lean_apply_4(v_toBind_542_, lean_box(0), lean_box(0), v___x_587_, v___f_586_);
return v___x_588_;
}
case 12:
{
lean_object* v_var_589_; lean_object* v_i_590_; uint8_t v_updateHeader_591_; lean_object* v_args_592_; lean_object* v___x_593_; lean_object* v___f_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
lean_inc(v_toPure_543_);
lean_dec_ref(v___f_554_);
lean_dec_ref(v___f_546_);
v_var_589_ = lean_ctor_get(v_e_540_, 0);
lean_inc(v_var_589_);
v_i_590_ = lean_ctor_get(v_e_540_, 1);
lean_inc_ref(v_i_590_);
v_updateHeader_591_ = lean_ctor_get_uint8(v_e_540_, sizeof(void*)*3);
v_args_592_ = lean_ctor_get(v_e_540_, 2);
lean_inc_ref(v_args_592_);
v___x_593_ = lean_box(v_updateHeader_591_);
lean_inc(v_toBind_542_);
v___f_594_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_594_, 0, v_e_540_);
lean_closure_set(v___f_594_, 1, v_i_590_);
lean_closure_set(v___f_594_, 2, v___x_593_);
lean_closure_set(v___f_594_, 3, v_toPure_543_);
lean_closure_set(v___f_594_, 4, v_args_592_);
lean_closure_set(v___f_594_, 5, v_inst_538_);
lean_closure_set(v___f_594_, 6, v___f_545_);
lean_closure_set(v___f_594_, 7, v_toBind_542_);
v___x_595_ = lean_apply_1(v_f_539_, v_var_589_);
v___x_596_ = lean_apply_4(v_toBind_542_, lean_box(0), lean_box(0), v___x_595_, v___f_594_);
return v___x_596_;
}
case 13:
{
lean_object* v_ty_597_; lean_object* v_fvarId_598_; lean_object* v___f_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
lean_inc(v_toPure_543_);
lean_dec_ref(v___f_554_);
lean_dec_ref(v___f_546_);
lean_dec_ref(v___f_545_);
lean_dec_ref(v_inst_538_);
v_ty_597_ = lean_ctor_get(v_e_540_, 0);
lean_inc_ref(v_ty_597_);
v_fvarId_598_ = lean_ctor_get(v_e_540_, 1);
lean_inc(v_fvarId_598_);
v___f_599_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6), 4, 3);
lean_closure_set(v___f_599_, 0, v_e_540_);
lean_closure_set(v___f_599_, 1, v_ty_597_);
lean_closure_set(v___f_599_, 2, v_toPure_543_);
v___x_600_ = lean_apply_1(v_f_539_, v_fvarId_598_);
v___x_601_ = lean_apply_4(v_toBind_542_, lean_box(0), lean_box(0), v___x_600_, v___f_599_);
return v___x_601_;
}
case 14:
{
lean_object* v_fvarId_602_; lean_object* v___f_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
lean_inc(v_toPure_543_);
lean_dec_ref(v___f_554_);
lean_dec_ref(v___f_546_);
lean_dec_ref(v___f_545_);
lean_dec_ref(v_inst_538_);
v_fvarId_602_ = lean_ctor_get(v_e_540_, 0);
lean_inc(v_fvarId_602_);
v___f_603_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9), 3, 2);
lean_closure_set(v___f_603_, 0, v_e_540_);
lean_closure_set(v___f_603_, 1, v_toPure_543_);
v___x_604_ = lean_apply_1(v_f_539_, v_fvarId_602_);
v___x_605_ = lean_apply_4(v_toBind_542_, lean_box(0), lean_box(0), v___x_604_, v___f_603_);
return v___x_605_;
}
case 15:
{
lean_object* v_fvarId_606_; lean_object* v___f_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
lean_inc(v_toPure_543_);
lean_dec_ref(v___f_554_);
lean_dec_ref(v___f_546_);
lean_dec_ref(v___f_545_);
lean_dec_ref(v_inst_538_);
v_fvarId_606_ = lean_ctor_get(v_e_540_, 0);
lean_inc(v_fvarId_606_);
v___f_607_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10), 3, 2);
lean_closure_set(v___f_607_, 0, v_e_540_);
lean_closure_set(v___f_607_, 1, v_toPure_543_);
v___x_608_ = lean_apply_1(v_f_539_, v_fvarId_606_);
v___x_609_ = lean_apply_4(v_toBind_542_, lean_box(0), lean_box(0), v___x_608_, v___f_607_);
return v___x_609_;
}
default: 
{
lean_object* v___x_610_; 
lean_inc(v_toPure_543_);
lean_dec_ref(v___f_554_);
lean_dec_ref(v___f_546_);
lean_dec_ref(v___f_545_);
lean_dec(v_toBind_542_);
lean_dec(v_f_539_);
lean_dec_ref(v_inst_538_);
v___x_610_ = lean_apply_2(v_toPure_543_, lean_box(0), v_e_540_);
return v___x_610_;
}
}
v___jp_547_:
{
size_t v_sz_549_; size_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_sz_549_ = lean_array_size(v_args_548_);
v___x_550_ = ((size_t)0ULL);
v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_538_, v___f_545_, v_sz_549_, v___x_550_, v_args_548_);
v___x_552_ = lean_apply_4(v_toBind_542_, lean_box(0), lean_box(0), v___x_551_, v___f_546_);
return v___x_552_;
}
v___jp_555_:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_apply_1(v_f_539_, v_fvarId_556_);
v___x_558_ = lean_apply_4(v_toBind_542_, lean_box(0), lean_box(0), v___x_557_, v___f_554_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___boxed(lean_object* v_pu_611_, lean_object* v_inst_612_, lean_object* v_f_613_, lean_object* v_e_614_){
_start:
{
uint8_t v_pu_boxed_615_; lean_object* v_res_616_; 
v_pu_boxed_615_ = lean_unbox(v_pu_611_);
v_res_616_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_boxed_615_, v_inst_612_, v_f_613_, v_e_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM(lean_object* v_m_617_, uint8_t v_pu_618_, lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_f_621_, lean_object* v_e_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_618_, v_inst_620_, v_f_621_, v_e_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___boxed(lean_object* v_m_624_, lean_object* v_pu_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_f_628_, lean_object* v_e_629_){
_start:
{
uint8_t v_pu_boxed_630_; lean_object* v_res_631_; 
v_pu_boxed_630_ = lean_unbox(v_pu_625_);
v_res_631_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM(v_m_624_, v_pu_boxed_630_, v_inst_626_, v_inst_627_, v_f_628_, v_e_629_);
lean_dec(v_inst_626_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0(lean_object* v_inst_632_, lean_object* v_f_633_, lean_object* v_x_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_632_, v_f_633_, v___y_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3(lean_object* v_args_637_, lean_object* v_toPure_638_, lean_object* v_inst_639_, lean_object* v___f_640_, lean_object* v_____r_641_){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_array_get_size(v_args_637_);
v___x_644_ = lean_box(0);
v___x_645_ = lean_nat_dec_lt(v___x_642_, v___x_643_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
lean_dec(v___f_640_);
lean_dec_ref(v_inst_639_);
lean_dec_ref(v_args_637_);
v___x_646_ = lean_apply_2(v_toPure_638_, lean_box(0), v___x_644_);
return v___x_646_;
}
else
{
uint8_t v___x_647_; 
v___x_647_ = lean_nat_dec_le(v___x_643_, v___x_643_);
if (v___x_647_ == 0)
{
if (v___x_645_ == 0)
{
lean_object* v___x_648_; 
lean_dec(v___f_640_);
lean_dec_ref(v_inst_639_);
lean_dec_ref(v_args_637_);
v___x_648_ = lean_apply_2(v_toPure_638_, lean_box(0), v___x_644_);
return v___x_648_;
}
else
{
size_t v___x_649_; size_t v___x_650_; lean_object* v___x_651_; 
lean_dec(v_toPure_638_);
v___x_649_ = ((size_t)0ULL);
v___x_650_ = lean_usize_of_nat(v___x_643_);
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_639_, v___f_640_, v_args_637_, v___x_649_, v___x_650_, v___x_644_);
return v___x_651_;
}
}
else
{
size_t v___x_652_; size_t v___x_653_; lean_object* v___x_654_; 
lean_dec(v_toPure_638_);
v___x_652_ = ((size_t)0ULL);
v___x_653_ = lean_usize_of_nat(v___x_643_);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_639_, v___f_640_, v_args_637_, v___x_652_, v___x_653_, v___x_644_);
return v___x_654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(lean_object* v_inst_655_, lean_object* v_f_656_, lean_object* v_e_657_){
_start:
{
lean_object* v_toApplicative_658_; lean_object* v_toBind_659_; lean_object* v_toPure_660_; lean_object* v___f_661_; lean_object* v_args_663_; 
v_toApplicative_658_ = lean_ctor_get(v_inst_655_, 0);
v_toBind_659_ = lean_ctor_get(v_inst_655_, 1);
v_toPure_660_ = lean_ctor_get(v_toApplicative_658_, 1);
lean_inc(v_f_656_);
lean_inc_ref(v_inst_655_);
v___f_661_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_661_, 0, v_inst_655_);
lean_closure_set(v___f_661_, 1, v_f_656_);
switch(lean_obj_tag(v_e_657_))
{
case 2:
{
lean_object* v_struct_677_; lean_object* v___x_678_; 
lean_dec_ref(v___f_661_);
lean_dec_ref(v_inst_655_);
v_struct_677_ = lean_ctor_get(v_e_657_, 2);
lean_inc(v_struct_677_);
lean_dec_ref_known(v_e_657_, 3);
v___x_678_ = lean_apply_1(v_f_656_, v_struct_677_);
return v___x_678_;
}
case 3:
{
lean_object* v_args_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
lean_dec(v_f_656_);
v_args_679_ = lean_ctor_get(v_e_657_, 2);
lean_inc_ref(v_args_679_);
lean_dec_ref_known(v_e_657_, 3);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_array_get_size(v_args_679_);
v___x_682_ = lean_box(0);
v___x_683_ = lean_nat_dec_lt(v___x_680_, v___x_681_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
lean_inc(v_toPure_660_);
lean_dec_ref(v_args_679_);
lean_dec_ref(v___f_661_);
lean_dec_ref(v_inst_655_);
v___x_684_ = lean_apply_2(v_toPure_660_, lean_box(0), v___x_682_);
return v___x_684_;
}
else
{
uint8_t v___x_685_; 
v___x_685_ = lean_nat_dec_le(v___x_681_, v___x_681_);
if (v___x_685_ == 0)
{
if (v___x_683_ == 0)
{
lean_object* v___x_686_; 
lean_inc(v_toPure_660_);
lean_dec_ref(v_args_679_);
lean_dec_ref(v___f_661_);
lean_dec_ref(v_inst_655_);
v___x_686_ = lean_apply_2(v_toPure_660_, lean_box(0), v___x_682_);
return v___x_686_;
}
else
{
size_t v___x_687_; size_t v___x_688_; lean_object* v___x_689_; 
v___x_687_ = ((size_t)0ULL);
v___x_688_ = lean_usize_of_nat(v___x_681_);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_655_, v___f_661_, v_args_679_, v___x_687_, v___x_688_, v___x_682_);
return v___x_689_;
}
}
else
{
size_t v___x_690_; size_t v___x_691_; lean_object* v___x_692_; 
v___x_690_ = ((size_t)0ULL);
v___x_691_ = lean_usize_of_nat(v___x_681_);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_655_, v___f_661_, v_args_679_, v___x_690_, v___x_691_, v___x_682_);
return v___x_692_;
}
}
}
case 4:
{
lean_object* v_fvarId_693_; lean_object* v_args_694_; lean_object* v___f_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_inc(v_toPure_660_);
lean_inc(v_toBind_659_);
v_fvarId_693_ = lean_ctor_get(v_e_657_, 0);
lean_inc(v_fvarId_693_);
v_args_694_ = lean_ctor_get(v_e_657_, 1);
lean_inc_ref(v_args_694_);
lean_dec_ref_known(v_e_657_, 2);
v___f_695_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3), 5, 4);
lean_closure_set(v___f_695_, 0, v_args_694_);
lean_closure_set(v___f_695_, 1, v_toPure_660_);
lean_closure_set(v___f_695_, 2, v_inst_655_);
lean_closure_set(v___f_695_, 3, v___f_661_);
v___x_696_ = lean_apply_1(v_f_656_, v_fvarId_693_);
v___x_697_ = lean_apply_4(v_toBind_659_, lean_box(0), lean_box(0), v___x_696_, v___f_695_);
return v___x_697_;
}
case 5:
{
lean_object* v_args_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
lean_dec(v_f_656_);
v_args_698_ = lean_ctor_get(v_e_657_, 1);
lean_inc_ref(v_args_698_);
lean_dec_ref_known(v_e_657_, 2);
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = lean_array_get_size(v_args_698_);
v___x_701_ = lean_box(0);
v___x_702_ = lean_nat_dec_lt(v___x_699_, v___x_700_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; 
lean_inc(v_toPure_660_);
lean_dec_ref(v_args_698_);
lean_dec_ref(v___f_661_);
lean_dec_ref(v_inst_655_);
v___x_703_ = lean_apply_2(v_toPure_660_, lean_box(0), v___x_701_);
return v___x_703_;
}
else
{
uint8_t v___x_704_; 
v___x_704_ = lean_nat_dec_le(v___x_700_, v___x_700_);
if (v___x_704_ == 0)
{
if (v___x_702_ == 0)
{
lean_object* v___x_705_; 
lean_inc(v_toPure_660_);
lean_dec_ref(v_args_698_);
lean_dec_ref(v___f_661_);
lean_dec_ref(v_inst_655_);
v___x_705_ = lean_apply_2(v_toPure_660_, lean_box(0), v___x_701_);
return v___x_705_;
}
else
{
size_t v___x_706_; size_t v___x_707_; lean_object* v___x_708_; 
v___x_706_ = ((size_t)0ULL);
v___x_707_ = lean_usize_of_nat(v___x_700_);
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_655_, v___f_661_, v_args_698_, v___x_706_, v___x_707_, v___x_701_);
return v___x_708_;
}
}
else
{
size_t v___x_709_; size_t v___x_710_; lean_object* v___x_711_; 
v___x_709_ = ((size_t)0ULL);
v___x_710_ = lean_usize_of_nat(v___x_700_);
v___x_711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_655_, v___f_661_, v_args_698_, v___x_709_, v___x_710_, v___x_701_);
return v___x_711_;
}
}
}
case 6:
{
lean_object* v_var_712_; lean_object* v___x_713_; 
lean_dec_ref(v___f_661_);
lean_dec_ref(v_inst_655_);
v_var_712_ = lean_ctor_get(v_e_657_, 1);
lean_inc(v_var_712_);
lean_dec_ref_known(v_e_657_, 2);
v___x_713_ = lean_apply_1(v_f_656_, v_var_712_);
return v___x_713_;
}
case 7:
{
lean_object* v_var_714_; lean_object* v___x_715_; 
lean_dec_ref(v___f_661_);
lean_dec_ref(v_inst_655_);
v_var_714_ = lean_ctor_get(v_e_657_, 1);
lean_inc(v_var_714_);
lean_dec_ref_known(v_e_657_, 2);
v___x_715_ = lean_apply_1(v_f_656_, v_var_714_);
return v___x_715_;
}
case 8:
{
lean_object* v_var_716_; lean_object* v___x_717_; 
lean_dec_ref(v___f_661_);
lean_dec_ref(v_inst_655_);
v_var_716_ = lean_ctor_get(v_e_657_, 2);
lean_inc(v_var_716_);
lean_dec_ref_known(v_e_657_, 3);
v___x_717_ = lean_apply_1(v_f_656_, v_var_716_);
return v___x_717_;
}
case 9:
{
lean_object* v_args_718_; 
lean_dec(v_f_656_);
v_args_718_ = lean_ctor_get(v_e_657_, 1);
lean_inc_ref(v_args_718_);
lean_dec_ref_known(v_e_657_, 2);
v_args_663_ = v_args_718_;
goto v___jp_662_;
}
case 10:
{
lean_object* v_args_719_; 
lean_dec(v_f_656_);
v_args_719_ = lean_ctor_get(v_e_657_, 1);
lean_inc_ref(v_args_719_);
lean_dec_ref_known(v_e_657_, 2);
v_args_663_ = v_args_719_;
goto v___jp_662_;
}
case 11:
{
lean_object* v_var_720_; lean_object* v___x_721_; 
lean_dec_ref(v___f_661_);
lean_dec_ref(v_inst_655_);
v_var_720_ = lean_ctor_get(v_e_657_, 1);
lean_inc(v_var_720_);
lean_dec_ref_known(v_e_657_, 2);
v___x_721_ = lean_apply_1(v_f_656_, v_var_720_);
return v___x_721_;
}
case 12:
{
lean_object* v_var_722_; lean_object* v_args_723_; lean_object* v___f_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_inc(v_toPure_660_);
lean_inc(v_toBind_659_);
v_var_722_ = lean_ctor_get(v_e_657_, 0);
lean_inc(v_var_722_);
v_args_723_ = lean_ctor_get(v_e_657_, 2);
lean_inc_ref(v_args_723_);
lean_dec_ref_known(v_e_657_, 3);
v___f_724_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3), 5, 4);
lean_closure_set(v___f_724_, 0, v_args_723_);
lean_closure_set(v___f_724_, 1, v_toPure_660_);
lean_closure_set(v___f_724_, 2, v_inst_655_);
lean_closure_set(v___f_724_, 3, v___f_661_);
v___x_725_ = lean_apply_1(v_f_656_, v_var_722_);
v___x_726_ = lean_apply_4(v_toBind_659_, lean_box(0), lean_box(0), v___x_725_, v___f_724_);
return v___x_726_;
}
case 13:
{
lean_object* v_fvarId_727_; lean_object* v___x_728_; 
lean_dec_ref(v___f_661_);
lean_dec_ref(v_inst_655_);
v_fvarId_727_ = lean_ctor_get(v_e_657_, 1);
lean_inc(v_fvarId_727_);
lean_dec_ref_known(v_e_657_, 2);
v___x_728_ = lean_apply_1(v_f_656_, v_fvarId_727_);
return v___x_728_;
}
case 14:
{
lean_object* v_fvarId_729_; lean_object* v___x_730_; 
lean_dec_ref(v___f_661_);
lean_dec_ref(v_inst_655_);
v_fvarId_729_ = lean_ctor_get(v_e_657_, 0);
lean_inc(v_fvarId_729_);
lean_dec_ref_known(v_e_657_, 1);
v___x_730_ = lean_apply_1(v_f_656_, v_fvarId_729_);
return v___x_730_;
}
case 15:
{
lean_object* v_fvarId_731_; lean_object* v___x_732_; 
lean_dec_ref(v___f_661_);
lean_dec_ref(v_inst_655_);
v_fvarId_731_ = lean_ctor_get(v_e_657_, 0);
lean_inc(v_fvarId_731_);
lean_dec_ref_known(v_e_657_, 1);
v___x_732_ = lean_apply_1(v_f_656_, v_fvarId_731_);
return v___x_732_;
}
default: 
{
lean_object* v___x_733_; lean_object* v___x_734_; 
lean_inc(v_toPure_660_);
lean_dec_ref(v___f_661_);
lean_dec(v_e_657_);
lean_dec(v_f_656_);
lean_dec_ref(v_inst_655_);
v___x_733_ = lean_box(0);
v___x_734_ = lean_apply_2(v_toPure_660_, lean_box(0), v___x_733_);
return v___x_734_;
}
}
v___jp_662_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_array_get_size(v_args_663_);
v___x_666_ = lean_box(0);
v___x_667_ = lean_nat_dec_lt(v___x_664_, v___x_665_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
lean_inc(v_toPure_660_);
lean_dec_ref(v_args_663_);
lean_dec_ref(v___f_661_);
lean_dec_ref(v_inst_655_);
v___x_668_ = lean_apply_2(v_toPure_660_, lean_box(0), v___x_666_);
return v___x_668_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = lean_nat_dec_le(v___x_665_, v___x_665_);
if (v___x_669_ == 0)
{
if (v___x_667_ == 0)
{
lean_object* v___x_670_; 
lean_inc(v_toPure_660_);
lean_dec_ref(v_args_663_);
lean_dec_ref(v___f_661_);
lean_dec_ref(v_inst_655_);
v___x_670_ = lean_apply_2(v_toPure_660_, lean_box(0), v___x_666_);
return v___x_670_;
}
else
{
size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
v___x_671_ = ((size_t)0ULL);
v___x_672_ = lean_usize_of_nat(v___x_665_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_655_, v___f_661_, v_args_663_, v___x_671_, v___x_672_, v___x_666_);
return v___x_673_;
}
}
else
{
size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
v___x_674_ = ((size_t)0ULL);
v___x_675_ = lean_usize_of_nat(v___x_665_);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_655_, v___f_661_, v_args_663_, v___x_674_, v___x_675_, v___x_666_);
return v___x_676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM(lean_object* v_m_735_, uint8_t v_pu_736_, lean_object* v_inst_737_, lean_object* v_f_738_, lean_object* v_e_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_737_, v_f_738_, v_e_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___boxed(lean_object* v_m_741_, lean_object* v_pu_742_, lean_object* v_inst_743_, lean_object* v_f_744_, lean_object* v_e_745_){
_start:
{
uint8_t v_pu_boxed_746_; lean_object* v_res_747_; 
v_pu_boxed_746_ = lean_unbox(v_pu_742_);
v_res_747_ = l_Lean_Compiler_LCNF_LetValue_forFVarM(v_m_741_, v_pu_boxed_746_, v_inst_743_, v_f_744_, v_e_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(uint8_t v_pu_748_, lean_object* v_m_749_, lean_object* v_inst_750_, lean_object* v_inst_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_748_, v_inst_751_, v___y_752_, v___y_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0___boxed(lean_object* v_pu_755_, lean_object* v_m_756_, lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
uint8_t v_pu_boxed_761_; lean_object* v_res_762_; 
v_pu_boxed_761_ = lean_unbox(v_pu_755_);
v_res_762_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(v_pu_boxed_761_, v_m_756_, v_inst_757_, v_inst_758_, v___y_759_, v___y_760_);
lean_dec(v_inst_757_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__1(lean_object* v_m_763_, lean_object* v_inst_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_764_, v___y_765_, v___y_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue(uint8_t v_pu_769_){
_start:
{
lean_object* v___x_770_; lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___x_773_; 
v___x_770_ = lean_box(v_pu_769_);
v___f_771_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0___boxed), 6, 1);
lean_closure_set(v___f_771_, 0, v___x_770_);
v___f_772_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarLetValue___closed__0));
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v___f_771_);
lean_ctor_set(v___x_773_, 1, v___f_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___boxed(lean_object* v_pu_774_){
_start:
{
uint8_t v_pu_boxed_775_; lean_object* v_res_776_; 
v_pu_boxed_775_ = lean_unbox(v_pu_774_);
v_res_776_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue(v_pu_boxed_775_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(uint8_t v_pu_777_, lean_object* v_decl_778_, lean_object* v_____do__lift_779_, lean_object* v_inst_780_, lean_object* v_____do__lift_781_){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = lean_box(v_pu_777_);
v___x_783_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_783_, 0, v___x_782_);
lean_closure_set(v___x_783_, 1, v_decl_778_);
lean_closure_set(v___x_783_, 2, v_____do__lift_779_);
lean_closure_set(v___x_783_, 3, v_____do__lift_781_);
v___x_784_ = lean_apply_2(v_inst_780_, lean_box(0), v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_785_, lean_object* v_decl_786_, lean_object* v_____do__lift_787_, lean_object* v_inst_788_, lean_object* v_____do__lift_789_){
_start:
{
uint8_t v_pu_boxed_790_; lean_object* v_res_791_; 
v_pu_boxed_790_ = lean_unbox(v_pu_785_);
v_res_791_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(v_pu_boxed_790_, v_decl_786_, v_____do__lift_787_, v_inst_788_, v_____do__lift_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(uint8_t v_pu_792_, lean_object* v_decl_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_f_796_, lean_object* v_value_797_, lean_object* v_toBind_798_, lean_object* v_____do__lift_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___f_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_800_ = lean_box(v_pu_792_);
v___f_801_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_801_, 0, v___x_800_);
lean_closure_set(v___f_801_, 1, v_decl_793_);
lean_closure_set(v___f_801_, 2, v_____do__lift_799_);
lean_closure_set(v___f_801_, 3, v_inst_794_);
v___x_802_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_792_, v_inst_795_, v_f_796_, v_value_797_);
v___x_803_ = lean_apply_4(v_toBind_798_, lean_box(0), lean_box(0), v___x_802_, v___f_801_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1___boxed(lean_object* v_pu_804_, lean_object* v_decl_805_, lean_object* v_inst_806_, lean_object* v_inst_807_, lean_object* v_f_808_, lean_object* v_value_809_, lean_object* v_toBind_810_, lean_object* v_____do__lift_811_){
_start:
{
uint8_t v_pu_boxed_812_; lean_object* v_res_813_; 
v_pu_boxed_812_ = lean_unbox(v_pu_804_);
v_res_813_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(v_pu_boxed_812_, v_decl_805_, v_inst_806_, v_inst_807_, v_f_808_, v_value_809_, v_toBind_810_, v_____do__lift_811_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(uint8_t v_pu_814_, lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_f_817_, lean_object* v_decl_818_){
_start:
{
lean_object* v_toBind_819_; lean_object* v_type_820_; lean_object* v_value_821_; lean_object* v___x_822_; lean_object* v___f_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_toBind_819_ = lean_ctor_get(v_inst_816_, 1);
lean_inc_n(v_toBind_819_, 2);
v_type_820_ = lean_ctor_get(v_decl_818_, 2);
lean_inc_ref(v_type_820_);
v_value_821_ = lean_ctor_get(v_decl_818_, 3);
lean_inc(v_value_821_);
v___x_822_ = lean_box(v_pu_814_);
lean_inc(v_f_817_);
lean_inc_ref(v_inst_816_);
v___f_823_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_823_, 0, v___x_822_);
lean_closure_set(v___f_823_, 1, v_decl_818_);
lean_closure_set(v___f_823_, 2, v_inst_815_);
lean_closure_set(v___f_823_, 3, v_inst_816_);
lean_closure_set(v___f_823_, 4, v_f_817_);
lean_closure_set(v___f_823_, 5, v_value_821_);
lean_closure_set(v___f_823_, 6, v_toBind_819_);
v___x_824_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_816_, v_f_817_, v_type_820_);
v___x_825_ = lean_apply_4(v_toBind_819_, lean_box(0), lean_box(0), v___x_824_, v___f_823_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___boxed(lean_object* v_pu_826_, lean_object* v_inst_827_, lean_object* v_inst_828_, lean_object* v_f_829_, lean_object* v_decl_830_){
_start:
{
uint8_t v_pu_boxed_831_; lean_object* v_res_832_; 
v_pu_boxed_831_ = lean_unbox(v_pu_826_);
v_res_832_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_boxed_831_, v_inst_827_, v_inst_828_, v_f_829_, v_decl_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM(lean_object* v_m_833_, uint8_t v_pu_834_, lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_f_837_, lean_object* v_decl_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_834_, v_inst_835_, v_inst_836_, v_f_837_, v_decl_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___boxed(lean_object* v_m_840_, lean_object* v_pu_841_, lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_f_844_, lean_object* v_decl_845_){
_start:
{
uint8_t v_pu_boxed_846_; lean_object* v_res_847_; 
v_pu_boxed_846_ = lean_unbox(v_pu_841_);
v_res_847_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM(v_m_840_, v_pu_boxed_846_, v_inst_842_, v_inst_843_, v_f_844_, v_decl_845_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg___lam__0(lean_object* v_inst_848_, lean_object* v_f_849_, lean_object* v_value_850_, lean_object* v_____r_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_848_, v_f_849_, v_value_850_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(lean_object* v_inst_853_, lean_object* v_f_854_, lean_object* v_decl_855_){
_start:
{
lean_object* v_toBind_856_; lean_object* v_type_857_; lean_object* v_value_858_; lean_object* v___f_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_toBind_856_ = lean_ctor_get(v_inst_853_, 1);
lean_inc(v_toBind_856_);
v_type_857_ = lean_ctor_get(v_decl_855_, 2);
lean_inc_ref(v_type_857_);
v_value_858_ = lean_ctor_get(v_decl_855_, 3);
lean_inc(v_value_858_);
lean_dec_ref(v_decl_855_);
lean_inc(v_f_854_);
lean_inc_ref(v_inst_853_);
v___f_859_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_859_, 0, v_inst_853_);
lean_closure_set(v___f_859_, 1, v_f_854_);
lean_closure_set(v___f_859_, 2, v_value_858_);
v___x_860_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_853_, v_f_854_, v_type_857_);
v___x_861_ = lean_apply_4(v_toBind_856_, lean_box(0), lean_box(0), v___x_860_, v___f_859_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM(lean_object* v_m_862_, uint8_t v_pu_863_, lean_object* v_inst_864_, lean_object* v_f_865_, lean_object* v_decl_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_864_, v_f_865_, v_decl_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___boxed(lean_object* v_m_868_, lean_object* v_pu_869_, lean_object* v_inst_870_, lean_object* v_f_871_, lean_object* v_decl_872_){
_start:
{
uint8_t v_pu_boxed_873_; lean_object* v_res_874_; 
v_pu_boxed_873_ = lean_unbox(v_pu_869_);
v_res_874_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM(v_m_868_, v_pu_boxed_873_, v_inst_870_, v_f_871_, v_decl_872_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(uint8_t v_pu_875_, lean_object* v_m_876_, lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_875_, v_inst_877_, v_inst_878_, v___y_879_, v___y_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0___boxed(lean_object* v_pu_882_, lean_object* v_m_883_, lean_object* v_inst_884_, lean_object* v_inst_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
uint8_t v_pu_boxed_888_; lean_object* v_res_889_; 
v_pu_boxed_888_ = lean_unbox(v_pu_882_);
v_res_889_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(v_pu_boxed_888_, v_m_883_, v_inst_884_, v_inst_885_, v___y_886_, v___y_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__1(lean_object* v_m_890_, lean_object* v_inst_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_891_, v___y_892_, v___y_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(uint8_t v_pu_896_){
_start:
{
lean_object* v___x_897_; lean_object* v___f_898_; lean_object* v___f_899_; lean_object* v___x_900_; 
v___x_897_ = lean_box(v_pu_896_);
v___f_898_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0___boxed), 6, 1);
lean_closure_set(v___f_898_, 0, v___x_897_);
v___f_899_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___closed__0));
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v___f_898_);
lean_ctor_set(v___x_900_, 1, v___f_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___boxed(lean_object* v_pu_901_){
_start:
{
uint8_t v_pu_boxed_902_; lean_object* v_res_903_; 
v_pu_boxed_902_ = lean_unbox(v_pu_901_);
v_res_903_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(v_pu_boxed_902_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(uint8_t v_pu_904_, lean_object* v_param_905_, lean_object* v_inst_906_, lean_object* v_____do__lift_907_){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_908_ = lean_box(v_pu_904_);
v___x_909_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_909_, 0, v___x_908_);
lean_closure_set(v___x_909_, 1, v_param_905_);
lean_closure_set(v___x_909_, 2, v_____do__lift_907_);
v___x_910_ = lean_apply_2(v_inst_906_, lean_box(0), v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_911_, lean_object* v_param_912_, lean_object* v_inst_913_, lean_object* v_____do__lift_914_){
_start:
{
uint8_t v_pu_boxed_915_; lean_object* v_res_916_; 
v_pu_boxed_915_ = lean_unbox(v_pu_911_);
v_res_916_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(v_pu_boxed_915_, v_param_912_, v_inst_913_, v_____do__lift_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(uint8_t v_pu_917_, lean_object* v_inst_918_, lean_object* v_inst_919_, lean_object* v_f_920_, lean_object* v_param_921_){
_start:
{
lean_object* v_toBind_922_; lean_object* v_type_923_; lean_object* v___x_924_; lean_object* v___f_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_toBind_922_ = lean_ctor_get(v_inst_919_, 1);
lean_inc(v_toBind_922_);
v_type_923_ = lean_ctor_get(v_param_921_, 2);
lean_inc_ref(v_type_923_);
v___x_924_ = lean_box(v_pu_917_);
v___f_925_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_925_, 0, v___x_924_);
lean_closure_set(v___f_925_, 1, v_param_921_);
lean_closure_set(v___f_925_, 2, v_inst_918_);
v___x_926_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_919_, v_f_920_, v_type_923_);
v___x_927_ = lean_apply_4(v_toBind_922_, lean_box(0), lean_box(0), v___x_926_, v___f_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___boxed(lean_object* v_pu_928_, lean_object* v_inst_929_, lean_object* v_inst_930_, lean_object* v_f_931_, lean_object* v_param_932_){
_start:
{
uint8_t v_pu_boxed_933_; lean_object* v_res_934_; 
v_pu_boxed_933_ = lean_unbox(v_pu_928_);
v_res_934_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(v_pu_boxed_933_, v_inst_929_, v_inst_930_, v_f_931_, v_param_932_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM(lean_object* v_m_935_, uint8_t v_pu_936_, lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_f_939_, lean_object* v_param_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(v_pu_936_, v_inst_937_, v_inst_938_, v_f_939_, v_param_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___boxed(lean_object* v_m_942_, lean_object* v_pu_943_, lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_f_946_, lean_object* v_param_947_){
_start:
{
uint8_t v_pu_boxed_948_; lean_object* v_res_949_; 
v_pu_boxed_948_ = lean_unbox(v_pu_943_);
v_res_949_ = l_Lean_Compiler_LCNF_Param_mapFVarM(v_m_942_, v_pu_boxed_948_, v_inst_944_, v_inst_945_, v_f_946_, v_param_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___redArg(lean_object* v_inst_950_, lean_object* v_f_951_, lean_object* v_param_952_){
_start:
{
lean_object* v_type_953_; lean_object* v___x_954_; 
v_type_953_ = lean_ctor_get(v_param_952_, 2);
lean_inc_ref(v_type_953_);
lean_dec_ref(v_param_952_);
v___x_954_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_950_, v_f_951_, v_type_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM(lean_object* v_m_955_, uint8_t v_pu_956_, lean_object* v_inst_957_, lean_object* v_f_958_, lean_object* v_param_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_957_, v_f_958_, v_param_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___boxed(lean_object* v_m_961_, lean_object* v_pu_962_, lean_object* v_inst_963_, lean_object* v_f_964_, lean_object* v_param_965_){
_start:
{
uint8_t v_pu_boxed_966_; lean_object* v_res_967_; 
v_pu_boxed_966_ = lean_unbox(v_pu_962_);
v_res_967_ = l_Lean_Compiler_LCNF_Param_forFVarM(v_m_961_, v_pu_boxed_966_, v_inst_963_, v_f_964_, v_param_965_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(uint8_t v_pu_968_, lean_object* v_m_969_, lean_object* v_inst_970_, lean_object* v_inst_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(v_pu_968_, v_inst_970_, v_inst_971_, v___y_972_, v___y_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0___boxed(lean_object* v_pu_975_, lean_object* v_m_976_, lean_object* v_inst_977_, lean_object* v_inst_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
uint8_t v_pu_boxed_981_; lean_object* v_res_982_; 
v_pu_boxed_981_ = lean_unbox(v_pu_975_);
v_res_982_ = l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(v_pu_boxed_981_, v_m_976_, v_inst_977_, v_inst_978_, v___y_979_, v___y_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__1(lean_object* v_m_983_, lean_object* v_inst_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_984_, v___y_985_, v___y_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam(uint8_t v_pu_989_){
_start:
{
lean_object* v___x_990_; lean_object* v___f_991_; lean_object* v___f_992_; lean_object* v___x_993_; 
v___x_990_ = lean_box(v_pu_989_);
v___f_991_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0___boxed), 6, 1);
lean_closure_set(v___f_991_, 0, v___x_990_);
v___f_992_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarParam___closed__0));
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v___f_991_);
lean_ctor_set(v___x_993_, 1, v___f_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___boxed(lean_object* v_pu_994_){
_start:
{
uint8_t v_pu_boxed_995_; lean_object* v_res_996_; 
v_pu_boxed_995_ = lean_unbox(v_pu_994_);
v_res_996_ = l_Lean_Compiler_LCNF_instTraverseFVarParam(v_pu_boxed_995_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0(lean_object* v_k_997_, lean_object* v_decl_998_, lean_object* v_toPure_999_, lean_object* v_decl_1000_, lean_object* v_c_1001_, lean_object* v_____do__lift_1002_){
_start:
{
size_t v___x_1003_; size_t v___x_1004_; uint8_t v___x_1005_; 
v___x_1003_ = lean_ptr_addr(v_k_997_);
v___x_1004_ = lean_ptr_addr(v_____do__lift_1002_);
v___x_1005_ = lean_usize_dec_eq(v___x_1003_, v___x_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_dec_ref(v_c_1001_);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v_decl_998_);
lean_ctor_set(v___x_1006_, 1, v_____do__lift_1002_);
v___x_1007_ = lean_apply_2(v_toPure_999_, lean_box(0), v___x_1006_);
return v___x_1007_;
}
else
{
size_t v___x_1008_; size_t v___x_1009_; uint8_t v___x_1010_; 
v___x_1008_ = lean_ptr_addr(v_decl_1000_);
v___x_1009_ = lean_ptr_addr(v_decl_998_);
v___x_1010_ = lean_usize_dec_eq(v___x_1008_, v___x_1009_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec_ref(v_c_1001_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v_decl_998_);
lean_ctor_set(v___x_1011_, 1, v_____do__lift_1002_);
v___x_1012_ = lean_apply_2(v_toPure_999_, lean_box(0), v___x_1011_);
return v___x_1012_;
}
else
{
lean_object* v___x_1013_; 
lean_dec_ref(v_____do__lift_1002_);
lean_dec_ref(v_decl_998_);
v___x_1013_ = lean_apply_2(v_toPure_999_, lean_box(0), v_c_1001_);
return v___x_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed(lean_object* v_k_1014_, lean_object* v_decl_1015_, lean_object* v_toPure_1016_, lean_object* v_decl_1017_, lean_object* v_c_1018_, lean_object* v_____do__lift_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0(v_k_1014_, v_decl_1015_, v_toPure_1016_, v_decl_1017_, v_c_1018_, v_____do__lift_1019_);
lean_dec_ref(v_decl_1017_);
lean_dec_ref(v_k_1014_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(lean_object* v_fvarId_1021_, lean_object* v_____do__lift_1022_, lean_object* v_i_1023_, lean_object* v_____do__lift_1024_, lean_object* v_toPure_1025_, lean_object* v_y_1026_, lean_object* v_k_1027_, lean_object* v_c_1028_, lean_object* v_____do__lift_1029_){
_start:
{
size_t v___x_1030_; size_t v___x_1031_; uint8_t v___x_1032_; 
v___x_1030_ = lean_ptr_addr(v_fvarId_1021_);
v___x_1031_ = lean_ptr_addr(v_____do__lift_1022_);
v___x_1032_ = lean_usize_dec_eq(v___x_1030_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_dec_ref(v_c_1028_);
v___x_1033_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1033_, 0, v_____do__lift_1022_);
lean_ctor_set(v___x_1033_, 1, v_i_1023_);
lean_ctor_set(v___x_1033_, 2, v_____do__lift_1024_);
lean_ctor_set(v___x_1033_, 3, v_____do__lift_1029_);
v___x_1034_ = lean_apply_2(v_toPure_1025_, lean_box(0), v___x_1033_);
return v___x_1034_;
}
else
{
uint8_t v___x_1035_; 
v___x_1035_ = lean_nat_dec_eq(v_i_1023_, v_i_1023_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
lean_dec_ref(v_c_1028_);
v___x_1036_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1036_, 0, v_____do__lift_1022_);
lean_ctor_set(v___x_1036_, 1, v_i_1023_);
lean_ctor_set(v___x_1036_, 2, v_____do__lift_1024_);
lean_ctor_set(v___x_1036_, 3, v_____do__lift_1029_);
v___x_1037_ = lean_apply_2(v_toPure_1025_, lean_box(0), v___x_1036_);
return v___x_1037_;
}
else
{
size_t v___x_1038_; size_t v___x_1039_; uint8_t v___x_1040_; 
v___x_1038_ = lean_ptr_addr(v_y_1026_);
v___x_1039_ = lean_ptr_addr(v_____do__lift_1024_);
v___x_1040_ = lean_usize_dec_eq(v___x_1038_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_dec_ref(v_c_1028_);
v___x_1041_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1041_, 0, v_____do__lift_1022_);
lean_ctor_set(v___x_1041_, 1, v_i_1023_);
lean_ctor_set(v___x_1041_, 2, v_____do__lift_1024_);
lean_ctor_set(v___x_1041_, 3, v_____do__lift_1029_);
v___x_1042_ = lean_apply_2(v_toPure_1025_, lean_box(0), v___x_1041_);
return v___x_1042_;
}
else
{
size_t v___x_1043_; size_t v___x_1044_; uint8_t v___x_1045_; 
v___x_1043_ = lean_ptr_addr(v_k_1027_);
v___x_1044_ = lean_ptr_addr(v_____do__lift_1029_);
v___x_1045_ = lean_usize_dec_eq(v___x_1043_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec_ref(v_c_1028_);
v___x_1046_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1046_, 0, v_____do__lift_1022_);
lean_ctor_set(v___x_1046_, 1, v_i_1023_);
lean_ctor_set(v___x_1046_, 2, v_____do__lift_1024_);
lean_ctor_set(v___x_1046_, 3, v_____do__lift_1029_);
v___x_1047_ = lean_apply_2(v_toPure_1025_, lean_box(0), v___x_1046_);
return v___x_1047_;
}
else
{
lean_object* v___x_1048_; 
lean_dec_ref(v_____do__lift_1029_);
lean_dec(v_____do__lift_1024_);
lean_dec(v_i_1023_);
lean_dec(v_____do__lift_1022_);
v___x_1048_ = lean_apply_2(v_toPure_1025_, lean_box(0), v_c_1028_);
return v___x_1048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed(lean_object* v_fvarId_1049_, lean_object* v_____do__lift_1050_, lean_object* v_i_1051_, lean_object* v_____do__lift_1052_, lean_object* v_toPure_1053_, lean_object* v_y_1054_, lean_object* v_k_1055_, lean_object* v_c_1056_, lean_object* v_____do__lift_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(v_fvarId_1049_, v_____do__lift_1050_, v_i_1051_, v_____do__lift_1052_, v_toPure_1053_, v_y_1054_, v_k_1055_, v_c_1056_, v_____do__lift_1057_);
lean_dec_ref(v_k_1055_);
lean_dec(v_y_1054_);
lean_dec(v_fvarId_1049_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(lean_object* v_fvarId_1059_, lean_object* v_toPure_1060_, lean_object* v_c_1061_, lean_object* v_____do__lift_1062_){
_start:
{
uint8_t v___x_1063_; 
v___x_1063_ = l_Lean_instBEqFVarId_beq(v_fvarId_1059_, v_____do__lift_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_dec_ref(v_c_1061_);
v___x_1064_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1064_, 0, v_____do__lift_1062_);
v___x_1065_ = lean_apply_2(v_toPure_1060_, lean_box(0), v___x_1064_);
return v___x_1065_;
}
else
{
lean_object* v___x_1066_; 
lean_dec(v_____do__lift_1062_);
v___x_1066_ = lean_apply_2(v_toPure_1060_, lean_box(0), v_c_1061_);
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed(lean_object* v_fvarId_1067_, lean_object* v_toPure_1068_, lean_object* v_c_1069_, lean_object* v_____do__lift_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(v_fvarId_1067_, v_toPure_1068_, v_c_1069_, v_____do__lift_1070_);
lean_dec(v_fvarId_1067_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27(lean_object* v_fvarId_1072_, lean_object* v_____do__lift_1073_, lean_object* v_cidx_1074_, lean_object* v_toPure_1075_, lean_object* v_k_1076_, lean_object* v_c_1077_, lean_object* v_____do__lift_1078_){
_start:
{
size_t v___x_1079_; size_t v___x_1080_; uint8_t v___x_1081_; 
v___x_1079_ = lean_ptr_addr(v_fvarId_1072_);
v___x_1080_ = lean_ptr_addr(v_____do__lift_1073_);
v___x_1081_ = lean_usize_dec_eq(v___x_1079_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec_ref(v_c_1077_);
v___x_1082_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1082_, 0, v_____do__lift_1073_);
lean_ctor_set(v___x_1082_, 1, v_cidx_1074_);
lean_ctor_set(v___x_1082_, 2, v_____do__lift_1078_);
v___x_1083_ = lean_apply_2(v_toPure_1075_, lean_box(0), v___x_1082_);
return v___x_1083_;
}
else
{
uint8_t v___x_1084_; 
v___x_1084_ = lean_nat_dec_eq(v_cidx_1074_, v_cidx_1074_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_dec_ref(v_c_1077_);
v___x_1085_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1085_, 0, v_____do__lift_1073_);
lean_ctor_set(v___x_1085_, 1, v_cidx_1074_);
lean_ctor_set(v___x_1085_, 2, v_____do__lift_1078_);
v___x_1086_ = lean_apply_2(v_toPure_1075_, lean_box(0), v___x_1085_);
return v___x_1086_;
}
else
{
size_t v___x_1087_; size_t v___x_1088_; uint8_t v___x_1089_; 
v___x_1087_ = lean_ptr_addr(v_k_1076_);
v___x_1088_ = lean_ptr_addr(v_____do__lift_1078_);
v___x_1089_ = lean_usize_dec_eq(v___x_1087_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_dec_ref(v_c_1077_);
v___x_1090_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1090_, 0, v_____do__lift_1073_);
lean_ctor_set(v___x_1090_, 1, v_cidx_1074_);
lean_ctor_set(v___x_1090_, 2, v_____do__lift_1078_);
v___x_1091_ = lean_apply_2(v_toPure_1075_, lean_box(0), v___x_1090_);
return v___x_1091_;
}
else
{
lean_object* v___x_1092_; 
lean_dec_ref(v_____do__lift_1078_);
lean_dec(v_cidx_1074_);
lean_dec(v_____do__lift_1073_);
v___x_1092_ = lean_apply_2(v_toPure_1075_, lean_box(0), v_c_1077_);
return v___x_1092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27___boxed(lean_object* v_fvarId_1093_, lean_object* v_____do__lift_1094_, lean_object* v_cidx_1095_, lean_object* v_toPure_1096_, lean_object* v_k_1097_, lean_object* v_c_1098_, lean_object* v_____do__lift_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27(v_fvarId_1093_, v_____do__lift_1094_, v_cidx_1095_, v_toPure_1096_, v_k_1097_, v_c_1098_, v_____do__lift_1099_);
lean_dec_ref(v_k_1097_);
lean_dec(v_fvarId_1093_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(lean_object* v_fvarId_1101_, lean_object* v_____do__lift_1102_, lean_object* v_n_1103_, uint8_t v_check_1104_, uint8_t v_persistent_1105_, lean_object* v_toPure_1106_, lean_object* v_k_1107_, lean_object* v_c_1108_, lean_object* v_____do__lift_1109_){
_start:
{
size_t v___x_1110_; size_t v___x_1111_; uint8_t v___x_1112_; 
v___x_1110_ = lean_ptr_addr(v_fvarId_1101_);
v___x_1111_ = lean_ptr_addr(v_____do__lift_1102_);
v___x_1112_ = lean_usize_dec_eq(v___x_1110_, v___x_1111_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec_ref(v_c_1108_);
v___x_1113_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1113_, 0, v_____do__lift_1102_);
lean_ctor_set(v___x_1113_, 1, v_n_1103_);
lean_ctor_set(v___x_1113_, 2, v_____do__lift_1109_);
lean_ctor_set_uint8(v___x_1113_, sizeof(void*)*3, v_check_1104_);
lean_ctor_set_uint8(v___x_1113_, sizeof(void*)*3 + 1, v_persistent_1105_);
v___x_1114_ = lean_apply_2(v_toPure_1106_, lean_box(0), v___x_1113_);
return v___x_1114_;
}
else
{
uint8_t v___x_1115_; 
v___x_1115_ = lean_nat_dec_eq(v_n_1103_, v_n_1103_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec_ref(v_c_1108_);
v___x_1116_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1116_, 0, v_____do__lift_1102_);
lean_ctor_set(v___x_1116_, 1, v_n_1103_);
lean_ctor_set(v___x_1116_, 2, v_____do__lift_1109_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*3, v_check_1104_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*3 + 1, v_persistent_1105_);
v___x_1117_ = lean_apply_2(v_toPure_1106_, lean_box(0), v___x_1116_);
return v___x_1117_;
}
else
{
size_t v___x_1118_; size_t v___x_1119_; uint8_t v___x_1120_; 
v___x_1118_ = lean_ptr_addr(v_k_1107_);
v___x_1119_ = lean_ptr_addr(v_____do__lift_1109_);
v___x_1120_ = lean_usize_dec_eq(v___x_1118_, v___x_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_dec_ref(v_c_1108_);
v___x_1121_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1121_, 0, v_____do__lift_1102_);
lean_ctor_set(v___x_1121_, 1, v_n_1103_);
lean_ctor_set(v___x_1121_, 2, v_____do__lift_1109_);
lean_ctor_set_uint8(v___x_1121_, sizeof(void*)*3, v_check_1104_);
lean_ctor_set_uint8(v___x_1121_, sizeof(void*)*3 + 1, v_persistent_1105_);
v___x_1122_ = lean_apply_2(v_toPure_1106_, lean_box(0), v___x_1121_);
return v___x_1122_;
}
else
{
lean_object* v___x_1123_; 
lean_dec_ref(v_____do__lift_1109_);
lean_dec(v_n_1103_);
lean_dec(v_____do__lift_1102_);
v___x_1123_ = lean_apply_2(v_toPure_1106_, lean_box(0), v_c_1108_);
return v___x_1123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29___boxed(lean_object* v_fvarId_1124_, lean_object* v_____do__lift_1125_, lean_object* v_n_1126_, lean_object* v_check_1127_, lean_object* v_persistent_1128_, lean_object* v_toPure_1129_, lean_object* v_k_1130_, lean_object* v_c_1131_, lean_object* v_____do__lift_1132_){
_start:
{
uint8_t v_check_1973__boxed_1133_; uint8_t v_persistent_1974__boxed_1134_; lean_object* v_res_1135_; 
v_check_1973__boxed_1133_ = lean_unbox(v_check_1127_);
v_persistent_1974__boxed_1134_ = lean_unbox(v_persistent_1128_);
v_res_1135_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(v_fvarId_1124_, v_____do__lift_1125_, v_n_1126_, v_check_1973__boxed_1133_, v_persistent_1974__boxed_1134_, v_toPure_1129_, v_k_1130_, v_c_1131_, v_____do__lift_1132_);
lean_dec_ref(v_k_1130_);
lean_dec(v_fvarId_1124_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(lean_object* v_fvarId_1136_, lean_object* v_____do__lift_1137_, lean_object* v_i_1138_, lean_object* v_offset_1139_, lean_object* v_____do__lift_1140_, lean_object* v_____do__lift_1141_, lean_object* v_toPure_1142_, lean_object* v_y_1143_, lean_object* v_ty_1144_, lean_object* v_k_1145_, lean_object* v_c_1146_, lean_object* v_____do__lift_1147_){
_start:
{
size_t v___x_1148_; size_t v___x_1149_; uint8_t v___x_1150_; 
v___x_1148_ = lean_ptr_addr(v_fvarId_1136_);
v___x_1149_ = lean_ptr_addr(v_____do__lift_1137_);
v___x_1150_ = lean_usize_dec_eq(v___x_1148_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_dec_ref(v_c_1146_);
v___x_1151_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1151_, 0, v_____do__lift_1137_);
lean_ctor_set(v___x_1151_, 1, v_i_1138_);
lean_ctor_set(v___x_1151_, 2, v_offset_1139_);
lean_ctor_set(v___x_1151_, 3, v_____do__lift_1140_);
lean_ctor_set(v___x_1151_, 4, v_____do__lift_1141_);
lean_ctor_set(v___x_1151_, 5, v_____do__lift_1147_);
v___x_1152_ = lean_apply_2(v_toPure_1142_, lean_box(0), v___x_1151_);
return v___x_1152_;
}
else
{
uint8_t v___x_1153_; 
v___x_1153_ = lean_nat_dec_eq(v_i_1138_, v_i_1138_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec_ref(v_c_1146_);
v___x_1154_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1154_, 0, v_____do__lift_1137_);
lean_ctor_set(v___x_1154_, 1, v_i_1138_);
lean_ctor_set(v___x_1154_, 2, v_offset_1139_);
lean_ctor_set(v___x_1154_, 3, v_____do__lift_1140_);
lean_ctor_set(v___x_1154_, 4, v_____do__lift_1141_);
lean_ctor_set(v___x_1154_, 5, v_____do__lift_1147_);
v___x_1155_ = lean_apply_2(v_toPure_1142_, lean_box(0), v___x_1154_);
return v___x_1155_;
}
else
{
uint8_t v___x_1156_; 
v___x_1156_ = lean_nat_dec_eq(v_offset_1139_, v_offset_1139_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec_ref(v_c_1146_);
v___x_1157_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1157_, 0, v_____do__lift_1137_);
lean_ctor_set(v___x_1157_, 1, v_i_1138_);
lean_ctor_set(v___x_1157_, 2, v_offset_1139_);
lean_ctor_set(v___x_1157_, 3, v_____do__lift_1140_);
lean_ctor_set(v___x_1157_, 4, v_____do__lift_1141_);
lean_ctor_set(v___x_1157_, 5, v_____do__lift_1147_);
v___x_1158_ = lean_apply_2(v_toPure_1142_, lean_box(0), v___x_1157_);
return v___x_1158_;
}
else
{
size_t v___x_1159_; size_t v___x_1160_; uint8_t v___x_1161_; 
v___x_1159_ = lean_ptr_addr(v_y_1143_);
v___x_1160_ = lean_ptr_addr(v_____do__lift_1140_);
v___x_1161_ = lean_usize_dec_eq(v___x_1159_, v___x_1160_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_dec_ref(v_c_1146_);
v___x_1162_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1162_, 0, v_____do__lift_1137_);
lean_ctor_set(v___x_1162_, 1, v_i_1138_);
lean_ctor_set(v___x_1162_, 2, v_offset_1139_);
lean_ctor_set(v___x_1162_, 3, v_____do__lift_1140_);
lean_ctor_set(v___x_1162_, 4, v_____do__lift_1141_);
lean_ctor_set(v___x_1162_, 5, v_____do__lift_1147_);
v___x_1163_ = lean_apply_2(v_toPure_1142_, lean_box(0), v___x_1162_);
return v___x_1163_;
}
else
{
size_t v___x_1164_; size_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1164_ = lean_ptr_addr(v_ty_1144_);
v___x_1165_ = lean_ptr_addr(v_____do__lift_1141_);
v___x_1166_ = lean_usize_dec_eq(v___x_1164_, v___x_1165_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec_ref(v_c_1146_);
v___x_1167_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1167_, 0, v_____do__lift_1137_);
lean_ctor_set(v___x_1167_, 1, v_i_1138_);
lean_ctor_set(v___x_1167_, 2, v_offset_1139_);
lean_ctor_set(v___x_1167_, 3, v_____do__lift_1140_);
lean_ctor_set(v___x_1167_, 4, v_____do__lift_1141_);
lean_ctor_set(v___x_1167_, 5, v_____do__lift_1147_);
v___x_1168_ = lean_apply_2(v_toPure_1142_, lean_box(0), v___x_1167_);
return v___x_1168_;
}
else
{
size_t v___x_1169_; size_t v___x_1170_; uint8_t v___x_1171_; 
v___x_1169_ = lean_ptr_addr(v_k_1145_);
v___x_1170_ = lean_ptr_addr(v_____do__lift_1147_);
v___x_1171_ = lean_usize_dec_eq(v___x_1169_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_dec_ref(v_c_1146_);
v___x_1172_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1172_, 0, v_____do__lift_1137_);
lean_ctor_set(v___x_1172_, 1, v_i_1138_);
lean_ctor_set(v___x_1172_, 2, v_offset_1139_);
lean_ctor_set(v___x_1172_, 3, v_____do__lift_1140_);
lean_ctor_set(v___x_1172_, 4, v_____do__lift_1141_);
lean_ctor_set(v___x_1172_, 5, v_____do__lift_1147_);
v___x_1173_ = lean_apply_2(v_toPure_1142_, lean_box(0), v___x_1172_);
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; 
lean_dec_ref(v_____do__lift_1147_);
lean_dec_ref(v_____do__lift_1141_);
lean_dec(v_____do__lift_1140_);
lean_dec(v_offset_1139_);
lean_dec(v_i_1138_);
lean_dec(v_____do__lift_1137_);
v___x_1174_ = lean_apply_2(v_toPure_1142_, lean_box(0), v_c_1146_);
return v___x_1174_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed(lean_object* v_fvarId_1175_, lean_object* v_____do__lift_1176_, lean_object* v_i_1177_, lean_object* v_offset_1178_, lean_object* v_____do__lift_1179_, lean_object* v_____do__lift_1180_, lean_object* v_toPure_1181_, lean_object* v_y_1182_, lean_object* v_ty_1183_, lean_object* v_k_1184_, lean_object* v_c_1185_, lean_object* v_____do__lift_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(v_fvarId_1175_, v_____do__lift_1176_, v_i_1177_, v_offset_1178_, v_____do__lift_1179_, v_____do__lift_1180_, v_toPure_1181_, v_y_1182_, v_ty_1183_, v_k_1184_, v_c_1185_, v_____do__lift_1186_);
lean_dec_ref(v_k_1184_);
lean_dec_ref(v_ty_1183_);
lean_dec(v_y_1182_);
lean_dec(v_fvarId_1175_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(uint8_t v_pu_1188_, lean_object* v_decl_1189_, lean_object* v_____do__lift_1190_, lean_object* v_params_1191_, lean_object* v_inst_1192_, lean_object* v_toBind_1193_, lean_object* v___f_1194_, lean_object* v_____do__lift_1195_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1196_ = lean_box(v_pu_1188_);
v___x_1197_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed), 10, 5);
lean_closure_set(v___x_1197_, 0, v___x_1196_);
lean_closure_set(v___x_1197_, 1, v_decl_1189_);
lean_closure_set(v___x_1197_, 2, v_____do__lift_1190_);
lean_closure_set(v___x_1197_, 3, v_params_1191_);
lean_closure_set(v___x_1197_, 4, v_____do__lift_1195_);
v___x_1198_ = lean_apply_2(v_inst_1192_, lean_box(0), v___x_1197_);
v___x_1199_ = lean_apply_4(v_toBind_1193_, lean_box(0), lean_box(0), v___x_1198_, v___f_1194_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed(lean_object* v_pu_1200_, lean_object* v_decl_1201_, lean_object* v_____do__lift_1202_, lean_object* v_params_1203_, lean_object* v_inst_1204_, lean_object* v_toBind_1205_, lean_object* v___f_1206_, lean_object* v_____do__lift_1207_){
_start:
{
uint8_t v_pu_boxed_1208_; lean_object* v_res_1209_; 
v_pu_boxed_1208_ = lean_unbox(v_pu_1200_);
v_res_1209_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(v_pu_boxed_1208_, v_decl_1201_, v_____do__lift_1202_, v_params_1203_, v_inst_1204_, v_toBind_1205_, v___f_1206_, v_____do__lift_1207_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(lean_object* v_____do__lift_1210_, lean_object* v_toPure_1211_, lean_object* v_c_1212_, lean_object* v_fvarId_1213_, lean_object* v_args_1214_, lean_object* v_____do__lift_1215_){
_start:
{
uint8_t v___y_1217_; uint8_t v___x_1221_; 
v___x_1221_ = l_Lean_instBEqFVarId_beq(v_fvarId_1213_, v_____do__lift_1210_);
if (v___x_1221_ == 0)
{
v___y_1217_ = v___x_1221_;
goto v___jp_1216_;
}
else
{
size_t v___x_1222_; size_t v___x_1223_; uint8_t v___x_1224_; 
v___x_1222_ = lean_ptr_addr(v_args_1214_);
v___x_1223_ = lean_ptr_addr(v_____do__lift_1215_);
v___x_1224_ = lean_usize_dec_eq(v___x_1222_, v___x_1223_);
v___y_1217_ = v___x_1224_;
goto v___jp_1216_;
}
v___jp_1216_:
{
if (v___y_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec_ref(v_c_1212_);
v___x_1218_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1218_, 0, v_____do__lift_1210_);
lean_ctor_set(v___x_1218_, 1, v_____do__lift_1215_);
v___x_1219_ = lean_apply_2(v_toPure_1211_, lean_box(0), v___x_1218_);
return v___x_1219_;
}
else
{
lean_object* v___x_1220_; 
lean_dec_ref(v_____do__lift_1215_);
lean_dec(v_____do__lift_1210_);
v___x_1220_ = lean_apply_2(v_toPure_1211_, lean_box(0), v_c_1212_);
return v___x_1220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed(lean_object* v_____do__lift_1225_, lean_object* v_toPure_1226_, lean_object* v_c_1227_, lean_object* v_fvarId_1228_, lean_object* v_args_1229_, lean_object* v_____do__lift_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(v_____do__lift_1225_, v_toPure_1226_, v_c_1227_, v_fvarId_1228_, v_args_1229_, v_____do__lift_1230_);
lean_dec_ref(v_args_1229_);
lean_dec(v_fvarId_1228_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(lean_object* v_toPure_1232_, lean_object* v_c_1233_, lean_object* v_fvarId_1234_, lean_object* v_args_1235_, uint8_t v_pu_1236_, lean_object* v_inst_1237_, lean_object* v_inst_1238_, lean_object* v_f_1239_, lean_object* v_toBind_1240_, lean_object* v_____do__lift_1241_){
_start:
{
lean_object* v___f_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; size_t v_sz_1245_; size_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_inc_ref(v_args_1235_);
v___f_1242_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed), 6, 5);
lean_closure_set(v___f_1242_, 0, v_____do__lift_1241_);
lean_closure_set(v___f_1242_, 1, v_toPure_1232_);
lean_closure_set(v___f_1242_, 2, v_c_1233_);
lean_closure_set(v___f_1242_, 3, v_fvarId_1234_);
lean_closure_set(v___f_1242_, 4, v_args_1235_);
v___x_1243_ = lean_box(v_pu_1236_);
lean_inc_ref(v_inst_1238_);
v___x_1244_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Arg_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_1244_, 0, lean_box(0));
lean_closure_set(v___x_1244_, 1, v___x_1243_);
lean_closure_set(v___x_1244_, 2, v_inst_1237_);
lean_closure_set(v___x_1244_, 3, v_inst_1238_);
lean_closure_set(v___x_1244_, 4, v_f_1239_);
v_sz_1245_ = lean_array_size(v_args_1235_);
v___x_1246_ = ((size_t)0ULL);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1238_, v___x_1244_, v_sz_1245_, v___x_1246_, v_args_1235_);
v___x_1248_ = lean_apply_4(v_toBind_1240_, lean_box(0), lean_box(0), v___x_1247_, v___f_1242_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed(lean_object* v_toPure_1249_, lean_object* v_c_1250_, lean_object* v_fvarId_1251_, lean_object* v_args_1252_, lean_object* v_pu_1253_, lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v_f_1256_, lean_object* v_toBind_1257_, lean_object* v_____do__lift_1258_){
_start:
{
uint8_t v_pu_boxed_1259_; lean_object* v_res_1260_; 
v_pu_boxed_1259_ = lean_unbox(v_pu_1253_);
v_res_1260_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(v_toPure_1249_, v_c_1250_, v_fvarId_1251_, v_args_1252_, v_pu_boxed_1259_, v_inst_1254_, v_inst_1255_, v_f_1256_, v_toBind_1257_, v_____do__lift_1258_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(lean_object* v_typeName_1261_, lean_object* v_____do__lift_1262_, lean_object* v_____do__lift_1263_, lean_object* v_toPure_1264_, lean_object* v_alts_1265_, lean_object* v_resultType_1266_, lean_object* v_discr_1267_, lean_object* v_c_1268_, lean_object* v_____do__lift_1269_){
_start:
{
size_t v___x_1274_; size_t v___x_1275_; uint8_t v___x_1276_; 
v___x_1274_ = lean_ptr_addr(v_alts_1265_);
v___x_1275_ = lean_ptr_addr(v_____do__lift_1269_);
v___x_1276_ = lean_usize_dec_eq(v___x_1274_, v___x_1275_);
if (v___x_1276_ == 0)
{
lean_dec_ref(v_c_1268_);
goto v___jp_1270_;
}
else
{
size_t v___x_1277_; size_t v___x_1278_; uint8_t v___x_1279_; 
v___x_1277_ = lean_ptr_addr(v_resultType_1266_);
v___x_1278_ = lean_ptr_addr(v_____do__lift_1262_);
v___x_1279_ = lean_usize_dec_eq(v___x_1277_, v___x_1278_);
if (v___x_1279_ == 0)
{
lean_dec_ref(v_c_1268_);
goto v___jp_1270_;
}
else
{
uint8_t v___x_1280_; 
v___x_1280_ = l_Lean_instBEqFVarId_beq(v_discr_1267_, v_____do__lift_1263_);
if (v___x_1280_ == 0)
{
lean_dec_ref(v_c_1268_);
goto v___jp_1270_;
}
else
{
lean_object* v___x_1281_; 
lean_dec_ref(v_____do__lift_1269_);
lean_dec(v_____do__lift_1263_);
lean_dec_ref(v_____do__lift_1262_);
lean_dec(v_typeName_1261_);
v___x_1281_ = lean_apply_2(v_toPure_1264_, lean_box(0), v_c_1268_);
return v___x_1281_;
}
}
}
v___jp_1270_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1271_, 0, v_typeName_1261_);
lean_ctor_set(v___x_1271_, 1, v_____do__lift_1262_);
lean_ctor_set(v___x_1271_, 2, v_____do__lift_1263_);
lean_ctor_set(v___x_1271_, 3, v_____do__lift_1269_);
v___x_1272_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
v___x_1273_ = lean_apply_2(v_toPure_1264_, lean_box(0), v___x_1272_);
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed(lean_object* v_typeName_1282_, lean_object* v_____do__lift_1283_, lean_object* v_____do__lift_1284_, lean_object* v_toPure_1285_, lean_object* v_alts_1286_, lean_object* v_resultType_1287_, lean_object* v_discr_1288_, lean_object* v_c_1289_, lean_object* v_____do__lift_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(v_typeName_1282_, v_____do__lift_1283_, v_____do__lift_1284_, v_toPure_1285_, v_alts_1286_, v_resultType_1287_, v_discr_1288_, v_c_1289_, v_____do__lift_1290_);
lean_dec(v_discr_1288_);
lean_dec_ref(v_resultType_1287_);
lean_dec_ref(v_alts_1286_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13(lean_object* v_typeName_1292_, lean_object* v_____do__lift_1293_, lean_object* v_toPure_1294_, lean_object* v_alts_1295_, lean_object* v_resultType_1296_, lean_object* v_discr_1297_, lean_object* v_c_1298_, lean_object* v_inst_1299_, lean_object* v___f_1300_, lean_object* v_toBind_1301_, lean_object* v_____do__lift_1302_){
_start:
{
lean_object* v___f_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_inc_ref(v_alts_1295_);
v___f_1303_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed), 9, 8);
lean_closure_set(v___f_1303_, 0, v_typeName_1292_);
lean_closure_set(v___f_1303_, 1, v_____do__lift_1293_);
lean_closure_set(v___f_1303_, 2, v_____do__lift_1302_);
lean_closure_set(v___f_1303_, 3, v_toPure_1294_);
lean_closure_set(v___f_1303_, 4, v_alts_1295_);
lean_closure_set(v___f_1303_, 5, v_resultType_1296_);
lean_closure_set(v___f_1303_, 6, v_discr_1297_);
lean_closure_set(v___f_1303_, 7, v_c_1298_);
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_1299_, v___f_1300_, v___x_1304_, v_alts_1295_);
v___x_1306_ = lean_apply_4(v_toBind_1301_, lean_box(0), lean_box(0), v___x_1305_, v___f_1303_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14(lean_object* v_typeName_1307_, lean_object* v_toPure_1308_, lean_object* v_alts_1309_, lean_object* v_resultType_1310_, lean_object* v_discr_1311_, lean_object* v_c_1312_, lean_object* v_inst_1313_, lean_object* v___f_1314_, lean_object* v_toBind_1315_, lean_object* v_f_1316_, lean_object* v_____do__lift_1317_){
_start:
{
lean_object* v___f_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
lean_inc(v_toBind_1315_);
lean_inc(v_discr_1311_);
v___f_1318_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13), 11, 10);
lean_closure_set(v___f_1318_, 0, v_typeName_1307_);
lean_closure_set(v___f_1318_, 1, v_____do__lift_1317_);
lean_closure_set(v___f_1318_, 2, v_toPure_1308_);
lean_closure_set(v___f_1318_, 3, v_alts_1309_);
lean_closure_set(v___f_1318_, 4, v_resultType_1310_);
lean_closure_set(v___f_1318_, 5, v_discr_1311_);
lean_closure_set(v___f_1318_, 6, v_c_1312_);
lean_closure_set(v___f_1318_, 7, v_inst_1313_);
lean_closure_set(v___f_1318_, 8, v___f_1314_);
lean_closure_set(v___f_1318_, 9, v_toBind_1315_);
v___x_1319_ = lean_apply_1(v_f_1316_, v_discr_1311_);
v___x_1320_ = lean_apply_4(v_toBind_1315_, lean_box(0), lean_box(0), v___x_1319_, v___f_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(lean_object* v_fvarId_1321_, lean_object* v_____do__lift_1322_, lean_object* v_n_1323_, uint8_t v_check_1324_, uint8_t v_persistent_1325_, lean_object* v_objs_x3f_1326_, lean_object* v_toPure_1327_, lean_object* v_k_1328_, lean_object* v_c_1329_, lean_object* v_____do__lift_1330_){
_start:
{
size_t v___x_1331_; size_t v___x_1332_; uint8_t v___x_1333_; 
v___x_1331_ = lean_ptr_addr(v_fvarId_1321_);
v___x_1332_ = lean_ptr_addr(v_____do__lift_1322_);
v___x_1333_ = lean_usize_dec_eq(v___x_1331_, v___x_1332_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
lean_dec_ref(v_c_1329_);
v___x_1334_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1334_, 0, v_____do__lift_1322_);
lean_ctor_set(v___x_1334_, 1, v_n_1323_);
lean_ctor_set(v___x_1334_, 2, v_objs_x3f_1326_);
lean_ctor_set(v___x_1334_, 3, v_____do__lift_1330_);
lean_ctor_set_uint8(v___x_1334_, sizeof(void*)*4, v_check_1324_);
lean_ctor_set_uint8(v___x_1334_, sizeof(void*)*4 + 1, v_persistent_1325_);
v___x_1335_ = lean_apply_2(v_toPure_1327_, lean_box(0), v___x_1334_);
return v___x_1335_;
}
else
{
uint8_t v___x_1336_; 
v___x_1336_ = lean_nat_dec_eq(v_n_1323_, v_n_1323_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_dec_ref(v_c_1329_);
v___x_1337_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1337_, 0, v_____do__lift_1322_);
lean_ctor_set(v___x_1337_, 1, v_n_1323_);
lean_ctor_set(v___x_1337_, 2, v_objs_x3f_1326_);
lean_ctor_set(v___x_1337_, 3, v_____do__lift_1330_);
lean_ctor_set_uint8(v___x_1337_, sizeof(void*)*4, v_check_1324_);
lean_ctor_set_uint8(v___x_1337_, sizeof(void*)*4 + 1, v_persistent_1325_);
v___x_1338_ = lean_apply_2(v_toPure_1327_, lean_box(0), v___x_1337_);
return v___x_1338_;
}
else
{
size_t v___x_1339_; uint8_t v___x_1340_; 
v___x_1339_ = lean_ptr_addr(v_objs_x3f_1326_);
v___x_1340_ = lean_usize_dec_eq(v___x_1339_, v___x_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec_ref(v_c_1329_);
v___x_1341_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1341_, 0, v_____do__lift_1322_);
lean_ctor_set(v___x_1341_, 1, v_n_1323_);
lean_ctor_set(v___x_1341_, 2, v_objs_x3f_1326_);
lean_ctor_set(v___x_1341_, 3, v_____do__lift_1330_);
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*4, v_check_1324_);
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*4 + 1, v_persistent_1325_);
v___x_1342_ = lean_apply_2(v_toPure_1327_, lean_box(0), v___x_1341_);
return v___x_1342_;
}
else
{
size_t v___x_1343_; size_t v___x_1344_; uint8_t v___x_1345_; 
v___x_1343_ = lean_ptr_addr(v_k_1328_);
v___x_1344_ = lean_ptr_addr(v_____do__lift_1330_);
v___x_1345_ = lean_usize_dec_eq(v___x_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_dec_ref(v_c_1329_);
v___x_1346_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1346_, 0, v_____do__lift_1322_);
lean_ctor_set(v___x_1346_, 1, v_n_1323_);
lean_ctor_set(v___x_1346_, 2, v_objs_x3f_1326_);
lean_ctor_set(v___x_1346_, 3, v_____do__lift_1330_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*4, v_check_1324_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*4 + 1, v_persistent_1325_);
v___x_1347_ = lean_apply_2(v_toPure_1327_, lean_box(0), v___x_1346_);
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; 
lean_dec_ref(v_____do__lift_1330_);
lean_dec(v_objs_x3f_1326_);
lean_dec(v_n_1323_);
lean_dec(v_____do__lift_1322_);
v___x_1348_ = lean_apply_2(v_toPure_1327_, lean_box(0), v_c_1329_);
return v___x_1348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed(lean_object* v_fvarId_1349_, lean_object* v_____do__lift_1350_, lean_object* v_n_1351_, lean_object* v_check_1352_, lean_object* v_persistent_1353_, lean_object* v_objs_x3f_1354_, lean_object* v_toPure_1355_, lean_object* v_k_1356_, lean_object* v_c_1357_, lean_object* v_____do__lift_1358_){
_start:
{
uint8_t v_check_2275__boxed_1359_; uint8_t v_persistent_2276__boxed_1360_; lean_object* v_res_1361_; 
v_check_2275__boxed_1359_ = lean_unbox(v_check_1352_);
v_persistent_2276__boxed_1360_ = lean_unbox(v_persistent_1353_);
v_res_1361_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(v_fvarId_1349_, v_____do__lift_1350_, v_n_1351_, v_check_2275__boxed_1359_, v_persistent_2276__boxed_1360_, v_objs_x3f_1354_, v_toPure_1355_, v_k_1356_, v_c_1357_, v_____do__lift_1358_);
lean_dec_ref(v_k_1356_);
lean_dec(v_fvarId_1349_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(lean_object* v_k_1362_, lean_object* v_decl_1363_, lean_object* v_toPure_1364_, lean_object* v_decl_1365_, lean_object* v_c_1366_, lean_object* v_____do__lift_1367_){
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
v___x_1371_ = lean_alloc_ctor(2, 2, 0);
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
v___x_1376_ = lean_alloc_ctor(2, 2, 0);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed(lean_object* v_k_1379_, lean_object* v_decl_1380_, lean_object* v_toPure_1381_, lean_object* v_decl_1382_, lean_object* v_c_1383_, lean_object* v_____do__lift_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(v_k_1379_, v_decl_1380_, v_toPure_1381_, v_decl_1382_, v_c_1383_, v_____do__lift_1384_);
lean_dec_ref(v_decl_1382_);
lean_dec_ref(v_k_1379_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(lean_object* v_k_1386_, lean_object* v_decl_1387_, lean_object* v_toPure_1388_, lean_object* v_decl_1389_, lean_object* v_c_1390_, lean_object* v_____do__lift_1391_){
_start:
{
size_t v___x_1392_; size_t v___x_1393_; uint8_t v___x_1394_; 
v___x_1392_ = lean_ptr_addr(v_k_1386_);
v___x_1393_ = lean_ptr_addr(v_____do__lift_1391_);
v___x_1394_ = lean_usize_dec_eq(v___x_1392_, v___x_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec_ref(v_c_1390_);
v___x_1395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1395_, 0, v_decl_1387_);
lean_ctor_set(v___x_1395_, 1, v_____do__lift_1391_);
v___x_1396_ = lean_apply_2(v_toPure_1388_, lean_box(0), v___x_1395_);
return v___x_1396_;
}
else
{
size_t v___x_1397_; size_t v___x_1398_; uint8_t v___x_1399_; 
v___x_1397_ = lean_ptr_addr(v_decl_1389_);
v___x_1398_ = lean_ptr_addr(v_decl_1387_);
v___x_1399_ = lean_usize_dec_eq(v___x_1397_, v___x_1398_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_dec_ref(v_c_1390_);
v___x_1400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_decl_1387_);
lean_ctor_set(v___x_1400_, 1, v_____do__lift_1391_);
v___x_1401_ = lean_apply_2(v_toPure_1388_, lean_box(0), v___x_1400_);
return v___x_1401_;
}
else
{
lean_object* v___x_1402_; 
lean_dec_ref(v_____do__lift_1391_);
lean_dec_ref(v_decl_1387_);
v___x_1402_ = lean_apply_2(v_toPure_1388_, lean_box(0), v_c_1390_);
return v___x_1402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed(lean_object* v_k_1403_, lean_object* v_decl_1404_, lean_object* v_toPure_1405_, lean_object* v_decl_1406_, lean_object* v_c_1407_, lean_object* v_____do__lift_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(v_k_1403_, v_decl_1404_, v_toPure_1405_, v_decl_1406_, v_c_1407_, v_____do__lift_1408_);
lean_dec_ref(v_decl_1406_);
lean_dec_ref(v_k_1403_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(lean_object* v_fvarId_1410_, lean_object* v_____do__lift_1411_, lean_object* v_i_1412_, lean_object* v_____do__lift_1413_, lean_object* v_toPure_1414_, lean_object* v_y_1415_, lean_object* v_k_1416_, lean_object* v_c_1417_, lean_object* v_____do__lift_1418_){
_start:
{
size_t v___x_1419_; size_t v___x_1420_; uint8_t v___x_1421_; 
v___x_1419_ = lean_ptr_addr(v_fvarId_1410_);
v___x_1420_ = lean_ptr_addr(v_____do__lift_1411_);
v___x_1421_ = lean_usize_dec_eq(v___x_1419_, v___x_1420_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec_ref(v_c_1417_);
v___x_1422_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1422_, 0, v_____do__lift_1411_);
lean_ctor_set(v___x_1422_, 1, v_i_1412_);
lean_ctor_set(v___x_1422_, 2, v_____do__lift_1413_);
lean_ctor_set(v___x_1422_, 3, v_____do__lift_1418_);
v___x_1423_ = lean_apply_2(v_toPure_1414_, lean_box(0), v___x_1422_);
return v___x_1423_;
}
else
{
uint8_t v___x_1424_; 
v___x_1424_ = lean_nat_dec_eq(v_i_1412_, v_i_1412_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec_ref(v_c_1417_);
v___x_1425_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1425_, 0, v_____do__lift_1411_);
lean_ctor_set(v___x_1425_, 1, v_i_1412_);
lean_ctor_set(v___x_1425_, 2, v_____do__lift_1413_);
lean_ctor_set(v___x_1425_, 3, v_____do__lift_1418_);
v___x_1426_ = lean_apply_2(v_toPure_1414_, lean_box(0), v___x_1425_);
return v___x_1426_;
}
else
{
size_t v___x_1427_; size_t v___x_1428_; uint8_t v___x_1429_; 
v___x_1427_ = lean_ptr_addr(v_y_1415_);
v___x_1428_ = lean_ptr_addr(v_____do__lift_1413_);
v___x_1429_ = lean_usize_dec_eq(v___x_1427_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec_ref(v_c_1417_);
v___x_1430_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1430_, 0, v_____do__lift_1411_);
lean_ctor_set(v___x_1430_, 1, v_i_1412_);
lean_ctor_set(v___x_1430_, 2, v_____do__lift_1413_);
lean_ctor_set(v___x_1430_, 3, v_____do__lift_1418_);
v___x_1431_ = lean_apply_2(v_toPure_1414_, lean_box(0), v___x_1430_);
return v___x_1431_;
}
else
{
size_t v___x_1432_; size_t v___x_1433_; uint8_t v___x_1434_; 
v___x_1432_ = lean_ptr_addr(v_k_1416_);
v___x_1433_ = lean_ptr_addr(v_____do__lift_1418_);
v___x_1434_ = lean_usize_dec_eq(v___x_1432_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec_ref(v_c_1417_);
v___x_1435_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1435_, 0, v_____do__lift_1411_);
lean_ctor_set(v___x_1435_, 1, v_i_1412_);
lean_ctor_set(v___x_1435_, 2, v_____do__lift_1413_);
lean_ctor_set(v___x_1435_, 3, v_____do__lift_1418_);
v___x_1436_ = lean_apply_2(v_toPure_1414_, lean_box(0), v___x_1435_);
return v___x_1436_;
}
else
{
lean_object* v___x_1437_; 
lean_dec_ref(v_____do__lift_1418_);
lean_dec(v_____do__lift_1413_);
lean_dec(v_i_1412_);
lean_dec(v_____do__lift_1411_);
v___x_1437_ = lean_apply_2(v_toPure_1414_, lean_box(0), v_c_1417_);
return v___x_1437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed(lean_object* v_fvarId_1438_, lean_object* v_____do__lift_1439_, lean_object* v_i_1440_, lean_object* v_____do__lift_1441_, lean_object* v_toPure_1442_, lean_object* v_y_1443_, lean_object* v_k_1444_, lean_object* v_c_1445_, lean_object* v_____do__lift_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(v_fvarId_1438_, v_____do__lift_1439_, v_i_1440_, v_____do__lift_1441_, v_toPure_1442_, v_y_1443_, v_k_1444_, v_c_1445_, v_____do__lift_1446_);
lean_dec_ref(v_k_1444_);
lean_dec(v_y_1443_);
lean_dec(v_fvarId_1438_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(lean_object* v_fvarId_1448_, lean_object* v_____do__lift_1449_, lean_object* v_toPure_1450_, lean_object* v_k_1451_, lean_object* v_c_1452_, lean_object* v_____do__lift_1453_){
_start:
{
size_t v___x_1454_; size_t v___x_1455_; uint8_t v___x_1456_; 
v___x_1454_ = lean_ptr_addr(v_fvarId_1448_);
v___x_1455_ = lean_ptr_addr(v_____do__lift_1449_);
v___x_1456_ = lean_usize_dec_eq(v___x_1454_, v___x_1455_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec_ref(v_c_1452_);
v___x_1457_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_1457_, 0, v_____do__lift_1449_);
lean_ctor_set(v___x_1457_, 1, v_____do__lift_1453_);
v___x_1458_ = lean_apply_2(v_toPure_1450_, lean_box(0), v___x_1457_);
return v___x_1458_;
}
else
{
size_t v___x_1459_; size_t v___x_1460_; uint8_t v___x_1461_; 
v___x_1459_ = lean_ptr_addr(v_k_1451_);
v___x_1460_ = lean_ptr_addr(v_____do__lift_1453_);
v___x_1461_ = lean_usize_dec_eq(v___x_1459_, v___x_1460_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_dec_ref(v_c_1452_);
v___x_1462_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_1462_, 0, v_____do__lift_1449_);
lean_ctor_set(v___x_1462_, 1, v_____do__lift_1453_);
v___x_1463_ = lean_apply_2(v_toPure_1450_, lean_box(0), v___x_1462_);
return v___x_1463_;
}
else
{
lean_object* v___x_1464_; 
lean_dec_ref(v_____do__lift_1453_);
lean_dec(v_____do__lift_1449_);
v___x_1464_ = lean_apply_2(v_toPure_1450_, lean_box(0), v_c_1452_);
return v___x_1464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed(lean_object* v_fvarId_1465_, lean_object* v_____do__lift_1466_, lean_object* v_toPure_1467_, lean_object* v_k_1468_, lean_object* v_c_1469_, lean_object* v_____do__lift_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(v_fvarId_1465_, v_____do__lift_1466_, v_toPure_1467_, v_k_1468_, v_c_1469_, v_____do__lift_1470_);
lean_dec_ref(v_k_1468_);
lean_dec(v_fvarId_1465_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(lean_object* v_type_1472_, lean_object* v_toPure_1473_, lean_object* v_c_1474_, lean_object* v_____do__lift_1475_){
_start:
{
size_t v___x_1476_; size_t v___x_1477_; uint8_t v___x_1478_; 
v___x_1476_ = lean_ptr_addr(v_type_1472_);
v___x_1477_ = lean_ptr_addr(v_____do__lift_1475_);
v___x_1478_ = lean_usize_dec_eq(v___x_1476_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_dec_ref(v_c_1474_);
v___x_1479_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1479_, 0, v_____do__lift_1475_);
v___x_1480_ = lean_apply_2(v_toPure_1473_, lean_box(0), v___x_1479_);
return v___x_1480_;
}
else
{
lean_object* v___x_1481_; 
lean_dec_ref(v_____do__lift_1475_);
v___x_1481_ = lean_apply_2(v_toPure_1473_, lean_box(0), v_c_1474_);
return v___x_1481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed(lean_object* v_type_1482_, lean_object* v_toPure_1483_, lean_object* v_c_1484_, lean_object* v_____do__lift_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(v_type_1482_, v_toPure_1483_, v_c_1484_, v_____do__lift_1485_);
lean_dec_ref(v_type_1482_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(lean_object* v_k_1487_, lean_object* v_toPure_1488_, lean_object* v_decl_1489_, lean_object* v_c_1490_, uint8_t v_pu_1491_, lean_object* v_inst_1492_, lean_object* v_inst_1493_, lean_object* v_f_1494_, lean_object* v_toBind_1495_, lean_object* v_decl_1496_){
_start:
{
lean_object* v___f_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_inc_ref(v_k_1487_);
v___f_1497_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed), 6, 5);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed(lean_object* v_k_1500_, lean_object* v_toPure_1501_, lean_object* v_decl_1502_, lean_object* v_c_1503_, lean_object* v_pu_1504_, lean_object* v_inst_1505_, lean_object* v_inst_1506_, lean_object* v_f_1507_, lean_object* v_toBind_1508_, lean_object* v_decl_1509_){
_start:
{
uint8_t v_pu_boxed_1510_; lean_object* v_res_1511_; 
v_pu_boxed_1510_ = lean_unbox(v_pu_1504_);
v_res_1511_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(v_k_1500_, v_toPure_1501_, v_decl_1502_, v_c_1503_, v_pu_boxed_1510_, v_inst_1505_, v_inst_1506_, v_f_1507_, v_toBind_1508_, v_decl_1509_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(lean_object* v_k_1512_, lean_object* v_toPure_1513_, lean_object* v_decl_1514_, lean_object* v_c_1515_, uint8_t v_pu_1516_, lean_object* v_inst_1517_, lean_object* v_inst_1518_, lean_object* v_f_1519_, lean_object* v_toBind_1520_, lean_object* v_decl_1521_){
_start:
{
lean_object* v___f_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_inc_ref(v_k_1512_);
v___f_1522_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_1522_, 0, v_k_1512_);
lean_closure_set(v___f_1522_, 1, v_decl_1521_);
lean_closure_set(v___f_1522_, 2, v_toPure_1513_);
lean_closure_set(v___f_1522_, 3, v_decl_1514_);
lean_closure_set(v___f_1522_, 4, v_c_1515_);
v___x_1523_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1516_, v_inst_1517_, v_inst_1518_, v_f_1519_, v_k_1512_);
v___x_1524_ = lean_apply_4(v_toBind_1520_, lean_box(0), lean_box(0), v___x_1523_, v___f_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed(lean_object* v_k_1525_, lean_object* v_toPure_1526_, lean_object* v_decl_1527_, lean_object* v_c_1528_, lean_object* v_pu_1529_, lean_object* v_inst_1530_, lean_object* v_inst_1531_, lean_object* v_f_1532_, lean_object* v_toBind_1533_, lean_object* v_decl_1534_){
_start:
{
uint8_t v_pu_boxed_1535_; lean_object* v_res_1536_; 
v_pu_boxed_1535_ = lean_unbox(v_pu_1529_);
v_res_1536_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(v_k_1525_, v_toPure_1526_, v_decl_1527_, v_c_1528_, v_pu_boxed_1535_, v_inst_1530_, v_inst_1531_, v_f_1532_, v_toBind_1533_, v_decl_1534_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(uint8_t v_pu_1537_, lean_object* v_decl_1538_, lean_object* v_params_1539_, lean_object* v_inst_1540_, lean_object* v_toBind_1541_, lean_object* v___f_1542_, lean_object* v_inst_1543_, lean_object* v_f_1544_, lean_object* v_value_1545_, lean_object* v_____do__lift_1546_){
_start:
{
lean_object* v___x_1547_; lean_object* v___f_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1547_ = lean_box(v_pu_1537_);
lean_inc(v_toBind_1541_);
lean_inc(v_inst_1540_);
v___f_1548_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_1548_, 0, v___x_1547_);
lean_closure_set(v___f_1548_, 1, v_decl_1538_);
lean_closure_set(v___f_1548_, 2, v_____do__lift_1546_);
lean_closure_set(v___f_1548_, 3, v_params_1539_);
lean_closure_set(v___f_1548_, 4, v_inst_1540_);
lean_closure_set(v___f_1548_, 5, v_toBind_1541_);
lean_closure_set(v___f_1548_, 6, v___f_1542_);
v___x_1549_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1537_, v_inst_1540_, v_inst_1543_, v_f_1544_, v_value_1545_);
v___x_1550_ = lean_apply_4(v_toBind_1541_, lean_box(0), lean_box(0), v___x_1549_, v___f_1548_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed(lean_object* v_pu_1551_, lean_object* v_decl_1552_, lean_object* v_params_1553_, lean_object* v_inst_1554_, lean_object* v_toBind_1555_, lean_object* v___f_1556_, lean_object* v_inst_1557_, lean_object* v_f_1558_, lean_object* v_value_1559_, lean_object* v_____do__lift_1560_){
_start:
{
uint8_t v_pu_boxed_1561_; lean_object* v_res_1562_; 
v_pu_boxed_1561_ = lean_unbox(v_pu_1551_);
v_res_1562_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(v_pu_boxed_1561_, v_decl_1552_, v_params_1553_, v_inst_1554_, v_toBind_1555_, v___f_1556_, v_inst_1557_, v_f_1558_, v_value_1559_, v_____do__lift_1560_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(uint8_t v_pu_1563_, lean_object* v_decl_1564_, lean_object* v_inst_1565_, lean_object* v_toBind_1566_, lean_object* v___f_1567_, lean_object* v_inst_1568_, lean_object* v_f_1569_, lean_object* v_value_1570_, lean_object* v_type_1571_, lean_object* v_params_1572_){
_start:
{
lean_object* v___x_1573_; lean_object* v___f_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1573_ = lean_box(v_pu_1563_);
lean_inc(v_f_1569_);
lean_inc_ref(v_inst_1568_);
lean_inc(v_toBind_1566_);
v___f_1574_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed), 10, 9);
lean_closure_set(v___f_1574_, 0, v___x_1573_);
lean_closure_set(v___f_1574_, 1, v_decl_1564_);
lean_closure_set(v___f_1574_, 2, v_params_1572_);
lean_closure_set(v___f_1574_, 3, v_inst_1565_);
lean_closure_set(v___f_1574_, 4, v_toBind_1566_);
lean_closure_set(v___f_1574_, 5, v___f_1567_);
lean_closure_set(v___f_1574_, 6, v_inst_1568_);
lean_closure_set(v___f_1574_, 7, v_f_1569_);
lean_closure_set(v___f_1574_, 8, v_value_1570_);
v___x_1575_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1568_, v_f_1569_, v_type_1571_);
v___x_1576_ = lean_apply_4(v_toBind_1566_, lean_box(0), lean_box(0), v___x_1575_, v___f_1574_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed(lean_object* v_pu_1577_, lean_object* v_decl_1578_, lean_object* v_inst_1579_, lean_object* v_toBind_1580_, lean_object* v___f_1581_, lean_object* v_inst_1582_, lean_object* v_f_1583_, lean_object* v_value_1584_, lean_object* v_type_1585_, lean_object* v_params_1586_){
_start:
{
uint8_t v_pu_boxed_1587_; lean_object* v_res_1588_; 
v_pu_boxed_1587_ = lean_unbox(v_pu_1577_);
v_res_1588_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(v_pu_boxed_1587_, v_decl_1578_, v_inst_1579_, v_toBind_1580_, v___f_1581_, v_inst_1582_, v_f_1583_, v_value_1584_, v_type_1585_, v_params_1586_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(lean_object* v_k_1589_, lean_object* v_toPure_1590_, lean_object* v_decl_1591_, lean_object* v_c_1592_, uint8_t v_pu_1593_, lean_object* v_inst_1594_, lean_object* v_inst_1595_, lean_object* v_f_1596_, lean_object* v_toBind_1597_, lean_object* v_decl_1598_){
_start:
{
lean_object* v___f_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_inc_ref(v_k_1589_);
v___f_1599_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_1599_, 0, v_k_1589_);
lean_closure_set(v___f_1599_, 1, v_decl_1598_);
lean_closure_set(v___f_1599_, 2, v_toPure_1590_);
lean_closure_set(v___f_1599_, 3, v_decl_1591_);
lean_closure_set(v___f_1599_, 4, v_c_1592_);
v___x_1600_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1593_, v_inst_1594_, v_inst_1595_, v_f_1596_, v_k_1589_);
v___x_1601_ = lean_apply_4(v_toBind_1597_, lean_box(0), lean_box(0), v___x_1600_, v___f_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed(lean_object* v_k_1602_, lean_object* v_toPure_1603_, lean_object* v_decl_1604_, lean_object* v_c_1605_, lean_object* v_pu_1606_, lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v_f_1609_, lean_object* v_toBind_1610_, lean_object* v_decl_1611_){
_start:
{
uint8_t v_pu_boxed_1612_; lean_object* v_res_1613_; 
v_pu_boxed_1612_ = lean_unbox(v_pu_1606_);
v_res_1613_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(v_k_1602_, v_toPure_1603_, v_decl_1604_, v_c_1605_, v_pu_boxed_1612_, v_inst_1607_, v_inst_1608_, v_f_1609_, v_toBind_1610_, v_decl_1611_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed(lean_object* v_pu_1614_, lean_object* v_inst_1615_, lean_object* v_inst_1616_, lean_object* v_f_1617_, lean_object* v_x_1618_){
_start:
{
uint8_t v_pu_boxed_1619_; lean_object* v_res_1620_; 
v_pu_boxed_1619_ = lean_unbox(v_pu_1614_);
v_res_1620_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(v_pu_boxed_1619_, v_inst_1615_, v_inst_1616_, v_f_1617_, v_x_1618_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(lean_object* v_fvarId_1621_, lean_object* v_____do__lift_1622_, lean_object* v_i_1623_, lean_object* v_toPure_1624_, lean_object* v_y_1625_, lean_object* v_k_1626_, lean_object* v_c_1627_, uint8_t v_pu_1628_, lean_object* v_inst_1629_, lean_object* v_inst_1630_, lean_object* v_f_1631_, lean_object* v_toBind_1632_, lean_object* v_____do__lift_1633_){
_start:
{
lean_object* v___f_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_inc_ref(v_k_1626_);
v___f_1634_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed), 9, 8);
lean_closure_set(v___f_1634_, 0, v_fvarId_1621_);
lean_closure_set(v___f_1634_, 1, v_____do__lift_1622_);
lean_closure_set(v___f_1634_, 2, v_i_1623_);
lean_closure_set(v___f_1634_, 3, v_____do__lift_1633_);
lean_closure_set(v___f_1634_, 4, v_toPure_1624_);
lean_closure_set(v___f_1634_, 5, v_y_1625_);
lean_closure_set(v___f_1634_, 6, v_k_1626_);
lean_closure_set(v___f_1634_, 7, v_c_1627_);
v___x_1635_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1628_, v_inst_1629_, v_inst_1630_, v_f_1631_, v_k_1626_);
v___x_1636_ = lean_apply_4(v_toBind_1632_, lean_box(0), lean_box(0), v___x_1635_, v___f_1634_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed(lean_object* v_fvarId_1637_, lean_object* v_____do__lift_1638_, lean_object* v_i_1639_, lean_object* v_toPure_1640_, lean_object* v_y_1641_, lean_object* v_k_1642_, lean_object* v_c_1643_, lean_object* v_pu_1644_, lean_object* v_inst_1645_, lean_object* v_inst_1646_, lean_object* v_f_1647_, lean_object* v_toBind_1648_, lean_object* v_____do__lift_1649_){
_start:
{
uint8_t v_pu_boxed_1650_; lean_object* v_res_1651_; 
v_pu_boxed_1650_ = lean_unbox(v_pu_1644_);
v_res_1651_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(v_fvarId_1637_, v_____do__lift_1638_, v_i_1639_, v_toPure_1640_, v_y_1641_, v_k_1642_, v_c_1643_, v_pu_boxed_1650_, v_inst_1645_, v_inst_1646_, v_f_1647_, v_toBind_1648_, v_____do__lift_1649_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(lean_object* v_fvarId_1652_, lean_object* v_i_1653_, lean_object* v_toPure_1654_, lean_object* v_y_1655_, lean_object* v_k_1656_, lean_object* v_c_1657_, uint8_t v_pu_1658_, lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v_f_1661_, lean_object* v_toBind_1662_, lean_object* v_____do__lift_1663_){
_start:
{
lean_object* v___x_1664_; lean_object* v___f_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1664_ = lean_box(v_pu_1658_);
lean_inc(v_toBind_1662_);
lean_inc(v_f_1661_);
lean_inc_ref(v_inst_1660_);
lean_inc(v_y_1655_);
v___f_1665_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed), 13, 12);
lean_closure_set(v___f_1665_, 0, v_fvarId_1652_);
lean_closure_set(v___f_1665_, 1, v_____do__lift_1663_);
lean_closure_set(v___f_1665_, 2, v_i_1653_);
lean_closure_set(v___f_1665_, 3, v_toPure_1654_);
lean_closure_set(v___f_1665_, 4, v_y_1655_);
lean_closure_set(v___f_1665_, 5, v_k_1656_);
lean_closure_set(v___f_1665_, 6, v_c_1657_);
lean_closure_set(v___f_1665_, 7, v___x_1664_);
lean_closure_set(v___f_1665_, 8, v_inst_1659_);
lean_closure_set(v___f_1665_, 9, v_inst_1660_);
lean_closure_set(v___f_1665_, 10, v_f_1661_);
lean_closure_set(v___f_1665_, 11, v_toBind_1662_);
v___x_1666_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_1658_, v_inst_1660_, v_f_1661_, v_y_1655_);
v___x_1667_ = lean_apply_4(v_toBind_1662_, lean_box(0), lean_box(0), v___x_1666_, v___f_1665_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed(lean_object* v_fvarId_1668_, lean_object* v_i_1669_, lean_object* v_toPure_1670_, lean_object* v_y_1671_, lean_object* v_k_1672_, lean_object* v_c_1673_, lean_object* v_pu_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_f_1677_, lean_object* v_toBind_1678_, lean_object* v_____do__lift_1679_){
_start:
{
uint8_t v_pu_boxed_1680_; lean_object* v_res_1681_; 
v_pu_boxed_1680_ = lean_unbox(v_pu_1674_);
v_res_1681_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(v_fvarId_1668_, v_i_1669_, v_toPure_1670_, v_y_1671_, v_k_1672_, v_c_1673_, v_pu_boxed_1680_, v_inst_1675_, v_inst_1676_, v_f_1677_, v_toBind_1678_, v_____do__lift_1679_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(lean_object* v_fvarId_1682_, lean_object* v_____do__lift_1683_, lean_object* v_i_1684_, lean_object* v_toPure_1685_, lean_object* v_y_1686_, lean_object* v_k_1687_, lean_object* v_c_1688_, uint8_t v_pu_1689_, lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_f_1692_, lean_object* v_toBind_1693_, lean_object* v_____do__lift_1694_){
_start:
{
lean_object* v___f_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_inc_ref(v_k_1687_);
v___f_1695_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed), 9, 8);
lean_closure_set(v___f_1695_, 0, v_fvarId_1682_);
lean_closure_set(v___f_1695_, 1, v_____do__lift_1683_);
lean_closure_set(v___f_1695_, 2, v_i_1684_);
lean_closure_set(v___f_1695_, 3, v_____do__lift_1694_);
lean_closure_set(v___f_1695_, 4, v_toPure_1685_);
lean_closure_set(v___f_1695_, 5, v_y_1686_);
lean_closure_set(v___f_1695_, 6, v_k_1687_);
lean_closure_set(v___f_1695_, 7, v_c_1688_);
v___x_1696_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1689_, v_inst_1690_, v_inst_1691_, v_f_1692_, v_k_1687_);
v___x_1697_ = lean_apply_4(v_toBind_1693_, lean_box(0), lean_box(0), v___x_1696_, v___f_1695_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed(lean_object* v_fvarId_1698_, lean_object* v_____do__lift_1699_, lean_object* v_i_1700_, lean_object* v_toPure_1701_, lean_object* v_y_1702_, lean_object* v_k_1703_, lean_object* v_c_1704_, lean_object* v_pu_1705_, lean_object* v_inst_1706_, lean_object* v_inst_1707_, lean_object* v_f_1708_, lean_object* v_toBind_1709_, lean_object* v_____do__lift_1710_){
_start:
{
uint8_t v_pu_boxed_1711_; lean_object* v_res_1712_; 
v_pu_boxed_1711_ = lean_unbox(v_pu_1705_);
v_res_1712_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(v_fvarId_1698_, v_____do__lift_1699_, v_i_1700_, v_toPure_1701_, v_y_1702_, v_k_1703_, v_c_1704_, v_pu_boxed_1711_, v_inst_1706_, v_inst_1707_, v_f_1708_, v_toBind_1709_, v_____do__lift_1710_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(lean_object* v_fvarId_1713_, lean_object* v_i_1714_, lean_object* v_toPure_1715_, lean_object* v_y_1716_, lean_object* v_k_1717_, lean_object* v_c_1718_, uint8_t v_pu_1719_, lean_object* v_inst_1720_, lean_object* v_inst_1721_, lean_object* v_f_1722_, lean_object* v_toBind_1723_, lean_object* v_____do__lift_1724_){
_start:
{
lean_object* v___x_1725_; lean_object* v___f_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1725_ = lean_box(v_pu_1719_);
lean_inc(v_toBind_1723_);
lean_inc(v_f_1722_);
lean_inc(v_y_1716_);
v___f_1726_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed), 13, 12);
lean_closure_set(v___f_1726_, 0, v_fvarId_1713_);
lean_closure_set(v___f_1726_, 1, v_____do__lift_1724_);
lean_closure_set(v___f_1726_, 2, v_i_1714_);
lean_closure_set(v___f_1726_, 3, v_toPure_1715_);
lean_closure_set(v___f_1726_, 4, v_y_1716_);
lean_closure_set(v___f_1726_, 5, v_k_1717_);
lean_closure_set(v___f_1726_, 6, v_c_1718_);
lean_closure_set(v___f_1726_, 7, v___x_1725_);
lean_closure_set(v___f_1726_, 8, v_inst_1720_);
lean_closure_set(v___f_1726_, 9, v_inst_1721_);
lean_closure_set(v___f_1726_, 10, v_f_1722_);
lean_closure_set(v___f_1726_, 11, v_toBind_1723_);
v___x_1727_ = lean_apply_1(v_f_1722_, v_y_1716_);
v___x_1728_ = lean_apply_4(v_toBind_1723_, lean_box(0), lean_box(0), v___x_1727_, v___f_1726_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed(lean_object* v_fvarId_1729_, lean_object* v_i_1730_, lean_object* v_toPure_1731_, lean_object* v_y_1732_, lean_object* v_k_1733_, lean_object* v_c_1734_, lean_object* v_pu_1735_, lean_object* v_inst_1736_, lean_object* v_inst_1737_, lean_object* v_f_1738_, lean_object* v_toBind_1739_, lean_object* v_____do__lift_1740_){
_start:
{
uint8_t v_pu_boxed_1741_; lean_object* v_res_1742_; 
v_pu_boxed_1741_ = lean_unbox(v_pu_1735_);
v_res_1742_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(v_fvarId_1729_, v_i_1730_, v_toPure_1731_, v_y_1732_, v_k_1733_, v_c_1734_, v_pu_boxed_1741_, v_inst_1736_, v_inst_1737_, v_f_1738_, v_toBind_1739_, v_____do__lift_1740_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(lean_object* v_fvarId_1743_, lean_object* v_____do__lift_1744_, lean_object* v_i_1745_, lean_object* v_offset_1746_, lean_object* v_____do__lift_1747_, lean_object* v_toPure_1748_, lean_object* v_y_1749_, lean_object* v_ty_1750_, lean_object* v_k_1751_, lean_object* v_c_1752_, uint8_t v_pu_1753_, lean_object* v_inst_1754_, lean_object* v_inst_1755_, lean_object* v_f_1756_, lean_object* v_toBind_1757_, lean_object* v_____do__lift_1758_){
_start:
{
lean_object* v___f_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_inc_ref(v_k_1751_);
v___f_1759_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed), 12, 11);
lean_closure_set(v___f_1759_, 0, v_fvarId_1743_);
lean_closure_set(v___f_1759_, 1, v_____do__lift_1744_);
lean_closure_set(v___f_1759_, 2, v_i_1745_);
lean_closure_set(v___f_1759_, 3, v_offset_1746_);
lean_closure_set(v___f_1759_, 4, v_____do__lift_1747_);
lean_closure_set(v___f_1759_, 5, v_____do__lift_1758_);
lean_closure_set(v___f_1759_, 6, v_toPure_1748_);
lean_closure_set(v___f_1759_, 7, v_y_1749_);
lean_closure_set(v___f_1759_, 8, v_ty_1750_);
lean_closure_set(v___f_1759_, 9, v_k_1751_);
lean_closure_set(v___f_1759_, 10, v_c_1752_);
v___x_1760_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1753_, v_inst_1754_, v_inst_1755_, v_f_1756_, v_k_1751_);
v___x_1761_ = lean_apply_4(v_toBind_1757_, lean_box(0), lean_box(0), v___x_1760_, v___f_1759_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed(lean_object* v_fvarId_1762_, lean_object* v_____do__lift_1763_, lean_object* v_i_1764_, lean_object* v_offset_1765_, lean_object* v_____do__lift_1766_, lean_object* v_toPure_1767_, lean_object* v_y_1768_, lean_object* v_ty_1769_, lean_object* v_k_1770_, lean_object* v_c_1771_, lean_object* v_pu_1772_, lean_object* v_inst_1773_, lean_object* v_inst_1774_, lean_object* v_f_1775_, lean_object* v_toBind_1776_, lean_object* v_____do__lift_1777_){
_start:
{
uint8_t v_pu_boxed_1778_; lean_object* v_res_1779_; 
v_pu_boxed_1778_ = lean_unbox(v_pu_1772_);
v_res_1779_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(v_fvarId_1762_, v_____do__lift_1763_, v_i_1764_, v_offset_1765_, v_____do__lift_1766_, v_toPure_1767_, v_y_1768_, v_ty_1769_, v_k_1770_, v_c_1771_, v_pu_boxed_1778_, v_inst_1773_, v_inst_1774_, v_f_1775_, v_toBind_1776_, v_____do__lift_1777_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(lean_object* v_fvarId_1780_, lean_object* v_____do__lift_1781_, lean_object* v_i_1782_, lean_object* v_offset_1783_, lean_object* v_toPure_1784_, lean_object* v_y_1785_, lean_object* v_ty_1786_, lean_object* v_k_1787_, lean_object* v_c_1788_, uint8_t v_pu_1789_, lean_object* v_inst_1790_, lean_object* v_inst_1791_, lean_object* v_f_1792_, lean_object* v_toBind_1793_, lean_object* v_____do__lift_1794_){
_start:
{
lean_object* v___x_1795_; lean_object* v___f_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1795_ = lean_box(v_pu_1789_);
lean_inc(v_toBind_1793_);
lean_inc(v_f_1792_);
lean_inc_ref(v_inst_1791_);
lean_inc_ref(v_ty_1786_);
v___f_1796_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed), 16, 15);
lean_closure_set(v___f_1796_, 0, v_fvarId_1780_);
lean_closure_set(v___f_1796_, 1, v_____do__lift_1781_);
lean_closure_set(v___f_1796_, 2, v_i_1782_);
lean_closure_set(v___f_1796_, 3, v_offset_1783_);
lean_closure_set(v___f_1796_, 4, v_____do__lift_1794_);
lean_closure_set(v___f_1796_, 5, v_toPure_1784_);
lean_closure_set(v___f_1796_, 6, v_y_1785_);
lean_closure_set(v___f_1796_, 7, v_ty_1786_);
lean_closure_set(v___f_1796_, 8, v_k_1787_);
lean_closure_set(v___f_1796_, 9, v_c_1788_);
lean_closure_set(v___f_1796_, 10, v___x_1795_);
lean_closure_set(v___f_1796_, 11, v_inst_1790_);
lean_closure_set(v___f_1796_, 12, v_inst_1791_);
lean_closure_set(v___f_1796_, 13, v_f_1792_);
lean_closure_set(v___f_1796_, 14, v_toBind_1793_);
v___x_1797_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1791_, v_f_1792_, v_ty_1786_);
v___x_1798_ = lean_apply_4(v_toBind_1793_, lean_box(0), lean_box(0), v___x_1797_, v___f_1796_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed(lean_object* v_fvarId_1799_, lean_object* v_____do__lift_1800_, lean_object* v_i_1801_, lean_object* v_offset_1802_, lean_object* v_toPure_1803_, lean_object* v_y_1804_, lean_object* v_ty_1805_, lean_object* v_k_1806_, lean_object* v_c_1807_, lean_object* v_pu_1808_, lean_object* v_inst_1809_, lean_object* v_inst_1810_, lean_object* v_f_1811_, lean_object* v_toBind_1812_, lean_object* v_____do__lift_1813_){
_start:
{
uint8_t v_pu_boxed_1814_; lean_object* v_res_1815_; 
v_pu_boxed_1814_ = lean_unbox(v_pu_1808_);
v_res_1815_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(v_fvarId_1799_, v_____do__lift_1800_, v_i_1801_, v_offset_1802_, v_toPure_1803_, v_y_1804_, v_ty_1805_, v_k_1806_, v_c_1807_, v_pu_boxed_1814_, v_inst_1809_, v_inst_1810_, v_f_1811_, v_toBind_1812_, v_____do__lift_1813_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(lean_object* v_fvarId_1816_, lean_object* v_i_1817_, lean_object* v_offset_1818_, lean_object* v_toPure_1819_, lean_object* v_y_1820_, lean_object* v_ty_1821_, lean_object* v_k_1822_, lean_object* v_c_1823_, uint8_t v_pu_1824_, lean_object* v_inst_1825_, lean_object* v_inst_1826_, lean_object* v_f_1827_, lean_object* v_toBind_1828_, lean_object* v_____do__lift_1829_){
_start:
{
lean_object* v___x_1830_; lean_object* v___f_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1830_ = lean_box(v_pu_1824_);
lean_inc(v_toBind_1828_);
lean_inc(v_f_1827_);
lean_inc(v_y_1820_);
v___f_1831_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed), 15, 14);
lean_closure_set(v___f_1831_, 0, v_fvarId_1816_);
lean_closure_set(v___f_1831_, 1, v_____do__lift_1829_);
lean_closure_set(v___f_1831_, 2, v_i_1817_);
lean_closure_set(v___f_1831_, 3, v_offset_1818_);
lean_closure_set(v___f_1831_, 4, v_toPure_1819_);
lean_closure_set(v___f_1831_, 5, v_y_1820_);
lean_closure_set(v___f_1831_, 6, v_ty_1821_);
lean_closure_set(v___f_1831_, 7, v_k_1822_);
lean_closure_set(v___f_1831_, 8, v_c_1823_);
lean_closure_set(v___f_1831_, 9, v___x_1830_);
lean_closure_set(v___f_1831_, 10, v_inst_1825_);
lean_closure_set(v___f_1831_, 11, v_inst_1826_);
lean_closure_set(v___f_1831_, 12, v_f_1827_);
lean_closure_set(v___f_1831_, 13, v_toBind_1828_);
v___x_1832_ = lean_apply_1(v_f_1827_, v_y_1820_);
v___x_1833_ = lean_apply_4(v_toBind_1828_, lean_box(0), lean_box(0), v___x_1832_, v___f_1831_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed(lean_object* v_fvarId_1834_, lean_object* v_i_1835_, lean_object* v_offset_1836_, lean_object* v_toPure_1837_, lean_object* v_y_1838_, lean_object* v_ty_1839_, lean_object* v_k_1840_, lean_object* v_c_1841_, lean_object* v_pu_1842_, lean_object* v_inst_1843_, lean_object* v_inst_1844_, lean_object* v_f_1845_, lean_object* v_toBind_1846_, lean_object* v_____do__lift_1847_){
_start:
{
uint8_t v_pu_boxed_1848_; lean_object* v_res_1849_; 
v_pu_boxed_1848_ = lean_unbox(v_pu_1842_);
v_res_1849_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(v_fvarId_1834_, v_i_1835_, v_offset_1836_, v_toPure_1837_, v_y_1838_, v_ty_1839_, v_k_1840_, v_c_1841_, v_pu_boxed_1848_, v_inst_1843_, v_inst_1844_, v_f_1845_, v_toBind_1846_, v_____do__lift_1847_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(lean_object* v_fvarId_1850_, lean_object* v_cidx_1851_, lean_object* v_toPure_1852_, lean_object* v_k_1853_, lean_object* v_c_1854_, uint8_t v_pu_1855_, lean_object* v_inst_1856_, lean_object* v_inst_1857_, lean_object* v_f_1858_, lean_object* v_toBind_1859_, lean_object* v_____do__lift_1860_){
_start:
{
lean_object* v___f_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_inc_ref(v_k_1853_);
v___f_1861_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27___boxed), 7, 6);
lean_closure_set(v___f_1861_, 0, v_fvarId_1850_);
lean_closure_set(v___f_1861_, 1, v_____do__lift_1860_);
lean_closure_set(v___f_1861_, 2, v_cidx_1851_);
lean_closure_set(v___f_1861_, 3, v_toPure_1852_);
lean_closure_set(v___f_1861_, 4, v_k_1853_);
lean_closure_set(v___f_1861_, 5, v_c_1854_);
v___x_1862_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1855_, v_inst_1856_, v_inst_1857_, v_f_1858_, v_k_1853_);
v___x_1863_ = lean_apply_4(v_toBind_1859_, lean_box(0), lean_box(0), v___x_1862_, v___f_1861_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed(lean_object* v_fvarId_1864_, lean_object* v_cidx_1865_, lean_object* v_toPure_1866_, lean_object* v_k_1867_, lean_object* v_c_1868_, lean_object* v_pu_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_f_1872_, lean_object* v_toBind_1873_, lean_object* v_____do__lift_1874_){
_start:
{
uint8_t v_pu_boxed_1875_; lean_object* v_res_1876_; 
v_pu_boxed_1875_ = lean_unbox(v_pu_1869_);
v_res_1876_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(v_fvarId_1864_, v_cidx_1865_, v_toPure_1866_, v_k_1867_, v_c_1868_, v_pu_boxed_1875_, v_inst_1870_, v_inst_1871_, v_f_1872_, v_toBind_1873_, v_____do__lift_1874_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(lean_object* v_fvarId_1877_, lean_object* v_n_1878_, uint8_t v_check_1879_, uint8_t v_persistent_1880_, lean_object* v_toPure_1881_, lean_object* v_k_1882_, lean_object* v_c_1883_, uint8_t v_pu_1884_, lean_object* v_inst_1885_, lean_object* v_inst_1886_, lean_object* v_f_1887_, lean_object* v_toBind_1888_, lean_object* v_____do__lift_1889_){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___f_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1890_ = lean_box(v_check_1879_);
v___x_1891_ = lean_box(v_persistent_1880_);
lean_inc_ref(v_k_1882_);
v___f_1892_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29___boxed), 9, 8);
lean_closure_set(v___f_1892_, 0, v_fvarId_1877_);
lean_closure_set(v___f_1892_, 1, v_____do__lift_1889_);
lean_closure_set(v___f_1892_, 2, v_n_1878_);
lean_closure_set(v___f_1892_, 3, v___x_1890_);
lean_closure_set(v___f_1892_, 4, v___x_1891_);
lean_closure_set(v___f_1892_, 5, v_toPure_1881_);
lean_closure_set(v___f_1892_, 6, v_k_1882_);
lean_closure_set(v___f_1892_, 7, v_c_1883_);
v___x_1893_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1884_, v_inst_1885_, v_inst_1886_, v_f_1887_, v_k_1882_);
v___x_1894_ = lean_apply_4(v_toBind_1888_, lean_box(0), lean_box(0), v___x_1893_, v___f_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed(lean_object* v_fvarId_1895_, lean_object* v_n_1896_, lean_object* v_check_1897_, lean_object* v_persistent_1898_, lean_object* v_toPure_1899_, lean_object* v_k_1900_, lean_object* v_c_1901_, lean_object* v_pu_1902_, lean_object* v_inst_1903_, lean_object* v_inst_1904_, lean_object* v_f_1905_, lean_object* v_toBind_1906_, lean_object* v_____do__lift_1907_){
_start:
{
uint8_t v_check_2616__boxed_1908_; uint8_t v_persistent_2617__boxed_1909_; uint8_t v_pu_boxed_1910_; lean_object* v_res_1911_; 
v_check_2616__boxed_1908_ = lean_unbox(v_check_1897_);
v_persistent_2617__boxed_1909_ = lean_unbox(v_persistent_1898_);
v_pu_boxed_1910_ = lean_unbox(v_pu_1902_);
v_res_1911_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(v_fvarId_1895_, v_n_1896_, v_check_2616__boxed_1908_, v_persistent_2617__boxed_1909_, v_toPure_1899_, v_k_1900_, v_c_1901_, v_pu_boxed_1910_, v_inst_1903_, v_inst_1904_, v_f_1905_, v_toBind_1906_, v_____do__lift_1907_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(lean_object* v_fvarId_1912_, lean_object* v_n_1913_, uint8_t v_check_1914_, uint8_t v_persistent_1915_, lean_object* v_objs_x3f_1916_, lean_object* v_toPure_1917_, lean_object* v_k_1918_, lean_object* v_c_1919_, uint8_t v_pu_1920_, lean_object* v_inst_1921_, lean_object* v_inst_1922_, lean_object* v_f_1923_, lean_object* v_toBind_1924_, lean_object* v_____do__lift_1925_){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___f_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1926_ = lean_box(v_check_1914_);
v___x_1927_ = lean_box(v_persistent_1915_);
lean_inc_ref(v_k_1918_);
v___f_1928_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed), 10, 9);
lean_closure_set(v___f_1928_, 0, v_fvarId_1912_);
lean_closure_set(v___f_1928_, 1, v_____do__lift_1925_);
lean_closure_set(v___f_1928_, 2, v_n_1913_);
lean_closure_set(v___f_1928_, 3, v___x_1926_);
lean_closure_set(v___f_1928_, 4, v___x_1927_);
lean_closure_set(v___f_1928_, 5, v_objs_x3f_1916_);
lean_closure_set(v___f_1928_, 6, v_toPure_1917_);
lean_closure_set(v___f_1928_, 7, v_k_1918_);
lean_closure_set(v___f_1928_, 8, v_c_1919_);
v___x_1929_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1920_, v_inst_1921_, v_inst_1922_, v_f_1923_, v_k_1918_);
v___x_1930_ = lean_apply_4(v_toBind_1924_, lean_box(0), lean_box(0), v___x_1929_, v___f_1928_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed(lean_object* v_fvarId_1931_, lean_object* v_n_1932_, lean_object* v_check_1933_, lean_object* v_persistent_1934_, lean_object* v_objs_x3f_1935_, lean_object* v_toPure_1936_, lean_object* v_k_1937_, lean_object* v_c_1938_, lean_object* v_pu_1939_, lean_object* v_inst_1940_, lean_object* v_inst_1941_, lean_object* v_f_1942_, lean_object* v_toBind_1943_, lean_object* v_____do__lift_1944_){
_start:
{
uint8_t v_check_2627__boxed_1945_; uint8_t v_persistent_2628__boxed_1946_; uint8_t v_pu_boxed_1947_; lean_object* v_res_1948_; 
v_check_2627__boxed_1945_ = lean_unbox(v_check_1933_);
v_persistent_2628__boxed_1946_ = lean_unbox(v_persistent_1934_);
v_pu_boxed_1947_ = lean_unbox(v_pu_1939_);
v_res_1948_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(v_fvarId_1931_, v_n_1932_, v_check_2627__boxed_1945_, v_persistent_2628__boxed_1946_, v_objs_x3f_1935_, v_toPure_1936_, v_k_1937_, v_c_1938_, v_pu_boxed_1947_, v_inst_1940_, v_inst_1941_, v_f_1942_, v_toBind_1943_, v_____do__lift_1944_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(lean_object* v_fvarId_1949_, lean_object* v_toPure_1950_, lean_object* v_k_1951_, lean_object* v_c_1952_, uint8_t v_pu_1953_, lean_object* v_inst_1954_, lean_object* v_inst_1955_, lean_object* v_f_1956_, lean_object* v_toBind_1957_, lean_object* v_____do__lift_1958_){
_start:
{
lean_object* v___f_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
lean_inc_ref(v_k_1951_);
v___f_1959_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed), 6, 5);
lean_closure_set(v___f_1959_, 0, v_fvarId_1949_);
lean_closure_set(v___f_1959_, 1, v_____do__lift_1958_);
lean_closure_set(v___f_1959_, 2, v_toPure_1950_);
lean_closure_set(v___f_1959_, 3, v_k_1951_);
lean_closure_set(v___f_1959_, 4, v_c_1952_);
v___x_1960_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1953_, v_inst_1954_, v_inst_1955_, v_f_1956_, v_k_1951_);
v___x_1961_ = lean_apply_4(v_toBind_1957_, lean_box(0), lean_box(0), v___x_1960_, v___f_1959_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed(lean_object* v_fvarId_1962_, lean_object* v_toPure_1963_, lean_object* v_k_1964_, lean_object* v_c_1965_, lean_object* v_pu_1966_, lean_object* v_inst_1967_, lean_object* v_inst_1968_, lean_object* v_f_1969_, lean_object* v_toBind_1970_, lean_object* v_____do__lift_1971_){
_start:
{
uint8_t v_pu_boxed_1972_; lean_object* v_res_1973_; 
v_pu_boxed_1972_ = lean_unbox(v_pu_1966_);
v_res_1973_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(v_fvarId_1962_, v_toPure_1963_, v_k_1964_, v_c_1965_, v_pu_boxed_1972_, v_inst_1967_, v_inst_1968_, v_f_1969_, v_toBind_1970_, v_____do__lift_1971_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(uint8_t v_pu_1974_, lean_object* v_inst_1975_, lean_object* v_inst_1976_, lean_object* v_f_1977_, lean_object* v_c_1978_){
_start:
{
switch(lean_obj_tag(v_c_1978_))
{
case 0:
{
lean_object* v_toApplicative_1979_; lean_object* v_toBind_1980_; lean_object* v_toPure_1981_; lean_object* v_decl_1982_; lean_object* v_k_1983_; lean_object* v___x_1984_; lean_object* v___f_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v_toApplicative_1979_ = lean_ctor_get(v_inst_1976_, 0);
v_toBind_1980_ = lean_ctor_get(v_inst_1976_, 1);
lean_inc_n(v_toBind_1980_, 2);
v_toPure_1981_ = lean_ctor_get(v_toApplicative_1979_, 1);
v_decl_1982_ = lean_ctor_get(v_c_1978_, 0);
lean_inc_ref_n(v_decl_1982_, 2);
v_k_1983_ = lean_ctor_get(v_c_1978_, 1);
lean_inc_ref(v_k_1983_);
v___x_1984_ = lean_box(v_pu_1974_);
lean_inc(v_f_1977_);
lean_inc_ref(v_inst_1976_);
lean_inc(v_inst_1975_);
lean_inc(v_toPure_1981_);
v___f_1985_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_1985_, 0, v_k_1983_);
lean_closure_set(v___f_1985_, 1, v_toPure_1981_);
lean_closure_set(v___f_1985_, 2, v_decl_1982_);
lean_closure_set(v___f_1985_, 3, v_c_1978_);
lean_closure_set(v___f_1985_, 4, v___x_1984_);
lean_closure_set(v___f_1985_, 5, v_inst_1975_);
lean_closure_set(v___f_1985_, 6, v_inst_1976_);
lean_closure_set(v___f_1985_, 7, v_f_1977_);
lean_closure_set(v___f_1985_, 8, v_toBind_1980_);
v___x_1986_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_1974_, v_inst_1975_, v_inst_1976_, v_f_1977_, v_decl_1982_);
v___x_1987_ = lean_apply_4(v_toBind_1980_, lean_box(0), lean_box(0), v___x_1986_, v___f_1985_);
return v___x_1987_;
}
case 1:
{
lean_object* v_toApplicative_1988_; lean_object* v_decl_1989_; lean_object* v_toBind_1990_; lean_object* v_toPure_1991_; lean_object* v_k_1992_; lean_object* v_params_1993_; lean_object* v_type_1994_; lean_object* v_value_1995_; lean_object* v___x_1996_; lean_object* v___f_1997_; lean_object* v___x_1998_; lean_object* v___f_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; size_t v_sz_2002_; size_t v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v_toApplicative_1988_ = lean_ctor_get(v_inst_1976_, 0);
v_decl_1989_ = lean_ctor_get(v_c_1978_, 0);
lean_inc_ref_n(v_decl_1989_, 2);
v_toBind_1990_ = lean_ctor_get(v_inst_1976_, 1);
lean_inc_n(v_toBind_1990_, 3);
v_toPure_1991_ = lean_ctor_get(v_toApplicative_1988_, 1);
v_k_1992_ = lean_ctor_get(v_c_1978_, 1);
lean_inc_ref(v_k_1992_);
v_params_1993_ = lean_ctor_get(v_decl_1989_, 2);
lean_inc_ref(v_params_1993_);
v_type_1994_ = lean_ctor_get(v_decl_1989_, 3);
lean_inc_ref(v_type_1994_);
v_value_1995_ = lean_ctor_get(v_decl_1989_, 4);
lean_inc_ref(v_value_1995_);
v___x_1996_ = lean_box(v_pu_1974_);
lean_inc_n(v_f_1977_, 2);
lean_inc_ref_n(v_inst_1976_, 3);
lean_inc_n(v_inst_1975_, 2);
lean_inc(v_toPure_1991_);
v___f_1997_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_1997_, 0, v_k_1992_);
lean_closure_set(v___f_1997_, 1, v_toPure_1991_);
lean_closure_set(v___f_1997_, 2, v_decl_1989_);
lean_closure_set(v___f_1997_, 3, v_c_1978_);
lean_closure_set(v___f_1997_, 4, v___x_1996_);
lean_closure_set(v___f_1997_, 5, v_inst_1975_);
lean_closure_set(v___f_1997_, 6, v_inst_1976_);
lean_closure_set(v___f_1997_, 7, v_f_1977_);
lean_closure_set(v___f_1997_, 8, v_toBind_1990_);
v___x_1998_ = lean_box(v_pu_1974_);
v___f_1999_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_1999_, 0, v___x_1998_);
lean_closure_set(v___f_1999_, 1, v_decl_1989_);
lean_closure_set(v___f_1999_, 2, v_inst_1975_);
lean_closure_set(v___f_1999_, 3, v_toBind_1990_);
lean_closure_set(v___f_1999_, 4, v___f_1997_);
lean_closure_set(v___f_1999_, 5, v_inst_1976_);
lean_closure_set(v___f_1999_, 6, v_f_1977_);
lean_closure_set(v___f_1999_, 7, v_value_1995_);
lean_closure_set(v___f_1999_, 8, v_type_1994_);
v___x_2000_ = lean_box(v_pu_1974_);
v___x_2001_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2001_, 0, lean_box(0));
lean_closure_set(v___x_2001_, 1, v___x_2000_);
lean_closure_set(v___x_2001_, 2, v_inst_1975_);
lean_closure_set(v___x_2001_, 3, v_inst_1976_);
lean_closure_set(v___x_2001_, 4, v_f_1977_);
v_sz_2002_ = lean_array_size(v_params_1993_);
v___x_2003_ = ((size_t)0ULL);
v___x_2004_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1976_, v___x_2001_, v_sz_2002_, v___x_2003_, v_params_1993_);
v___x_2005_ = lean_apply_4(v_toBind_1990_, lean_box(0), lean_box(0), v___x_2004_, v___f_1999_);
return v___x_2005_;
}
case 2:
{
lean_object* v_toApplicative_2006_; lean_object* v_decl_2007_; lean_object* v_toBind_2008_; lean_object* v_toPure_2009_; lean_object* v_k_2010_; lean_object* v_params_2011_; lean_object* v_type_2012_; lean_object* v_value_2013_; lean_object* v___x_2014_; lean_object* v___f_2015_; lean_object* v___x_2016_; lean_object* v___f_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; size_t v_sz_2020_; size_t v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v_toApplicative_2006_ = lean_ctor_get(v_inst_1976_, 0);
v_decl_2007_ = lean_ctor_get(v_c_1978_, 0);
lean_inc_ref_n(v_decl_2007_, 2);
v_toBind_2008_ = lean_ctor_get(v_inst_1976_, 1);
lean_inc_n(v_toBind_2008_, 3);
v_toPure_2009_ = lean_ctor_get(v_toApplicative_2006_, 1);
v_k_2010_ = lean_ctor_get(v_c_1978_, 1);
lean_inc_ref(v_k_2010_);
v_params_2011_ = lean_ctor_get(v_decl_2007_, 2);
lean_inc_ref(v_params_2011_);
v_type_2012_ = lean_ctor_get(v_decl_2007_, 3);
lean_inc_ref(v_type_2012_);
v_value_2013_ = lean_ctor_get(v_decl_2007_, 4);
lean_inc_ref(v_value_2013_);
v___x_2014_ = lean_box(v_pu_1974_);
lean_inc_n(v_f_1977_, 2);
lean_inc_ref_n(v_inst_1976_, 3);
lean_inc_n(v_inst_1975_, 2);
lean_inc(v_toPure_2009_);
v___f_2015_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed), 10, 9);
lean_closure_set(v___f_2015_, 0, v_k_2010_);
lean_closure_set(v___f_2015_, 1, v_toPure_2009_);
lean_closure_set(v___f_2015_, 2, v_decl_2007_);
lean_closure_set(v___f_2015_, 3, v_c_1978_);
lean_closure_set(v___f_2015_, 4, v___x_2014_);
lean_closure_set(v___f_2015_, 5, v_inst_1975_);
lean_closure_set(v___f_2015_, 6, v_inst_1976_);
lean_closure_set(v___f_2015_, 7, v_f_1977_);
lean_closure_set(v___f_2015_, 8, v_toBind_2008_);
v___x_2016_ = lean_box(v_pu_1974_);
v___f_2017_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_2017_, 0, v___x_2016_);
lean_closure_set(v___f_2017_, 1, v_decl_2007_);
lean_closure_set(v___f_2017_, 2, v_inst_1975_);
lean_closure_set(v___f_2017_, 3, v_toBind_2008_);
lean_closure_set(v___f_2017_, 4, v___f_2015_);
lean_closure_set(v___f_2017_, 5, v_inst_1976_);
lean_closure_set(v___f_2017_, 6, v_f_1977_);
lean_closure_set(v___f_2017_, 7, v_value_2013_);
lean_closure_set(v___f_2017_, 8, v_type_2012_);
v___x_2018_ = lean_box(v_pu_1974_);
v___x_2019_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2019_, 0, lean_box(0));
lean_closure_set(v___x_2019_, 1, v___x_2018_);
lean_closure_set(v___x_2019_, 2, v_inst_1975_);
lean_closure_set(v___x_2019_, 3, v_inst_1976_);
lean_closure_set(v___x_2019_, 4, v_f_1977_);
v_sz_2020_ = lean_array_size(v_params_2011_);
v___x_2021_ = ((size_t)0ULL);
v___x_2022_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1976_, v___x_2019_, v_sz_2020_, v___x_2021_, v_params_2011_);
v___x_2023_ = lean_apply_4(v_toBind_2008_, lean_box(0), lean_box(0), v___x_2022_, v___f_2017_);
return v___x_2023_;
}
case 3:
{
lean_object* v_toApplicative_2024_; lean_object* v_toBind_2025_; lean_object* v_toPure_2026_; lean_object* v_fvarId_2027_; lean_object* v_args_2028_; lean_object* v___x_2029_; lean_object* v___f_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v_toApplicative_2024_ = lean_ctor_get(v_inst_1976_, 0);
v_toBind_2025_ = lean_ctor_get(v_inst_1976_, 1);
lean_inc_n(v_toBind_2025_, 2);
v_toPure_2026_ = lean_ctor_get(v_toApplicative_2024_, 1);
lean_inc(v_toPure_2026_);
v_fvarId_2027_ = lean_ctor_get(v_c_1978_, 0);
lean_inc_n(v_fvarId_2027_, 2);
v_args_2028_ = lean_ctor_get(v_c_1978_, 1);
lean_inc_ref(v_args_2028_);
v___x_2029_ = lean_box(v_pu_1974_);
lean_inc(v_f_1977_);
v___f_2030_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_2030_, 0, v_toPure_2026_);
lean_closure_set(v___f_2030_, 1, v_c_1978_);
lean_closure_set(v___f_2030_, 2, v_fvarId_2027_);
lean_closure_set(v___f_2030_, 3, v_args_2028_);
lean_closure_set(v___f_2030_, 4, v___x_2029_);
lean_closure_set(v___f_2030_, 5, v_inst_1975_);
lean_closure_set(v___f_2030_, 6, v_inst_1976_);
lean_closure_set(v___f_2030_, 7, v_f_1977_);
lean_closure_set(v___f_2030_, 8, v_toBind_2025_);
v___x_2031_ = lean_apply_1(v_f_1977_, v_fvarId_2027_);
v___x_2032_ = lean_apply_4(v_toBind_2025_, lean_box(0), lean_box(0), v___x_2031_, v___f_2030_);
return v___x_2032_;
}
case 4:
{
lean_object* v_toApplicative_2033_; lean_object* v_cases_2034_; lean_object* v_toBind_2035_; lean_object* v_toPure_2036_; lean_object* v_typeName_2037_; lean_object* v_resultType_2038_; lean_object* v_discr_2039_; lean_object* v_alts_2040_; lean_object* v___x_2041_; lean_object* v___f_2042_; lean_object* v___f_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_toApplicative_2033_ = lean_ctor_get(v_inst_1976_, 0);
v_cases_2034_ = lean_ctor_get(v_c_1978_, 0);
v_toBind_2035_ = lean_ctor_get(v_inst_1976_, 1);
lean_inc_n(v_toBind_2035_, 2);
v_toPure_2036_ = lean_ctor_get(v_toApplicative_2033_, 1);
v_typeName_2037_ = lean_ctor_get(v_cases_2034_, 0);
lean_inc(v_typeName_2037_);
v_resultType_2038_ = lean_ctor_get(v_cases_2034_, 1);
lean_inc_ref_n(v_resultType_2038_, 2);
v_discr_2039_ = lean_ctor_get(v_cases_2034_, 2);
lean_inc(v_discr_2039_);
v_alts_2040_ = lean_ctor_get(v_cases_2034_, 3);
lean_inc_ref(v_alts_2040_);
v___x_2041_ = lean_box(v_pu_1974_);
lean_inc_n(v_f_1977_, 2);
lean_inc_ref_n(v_inst_1976_, 2);
v___f_2042_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed), 5, 4);
lean_closure_set(v___f_2042_, 0, v___x_2041_);
lean_closure_set(v___f_2042_, 1, v_inst_1975_);
lean_closure_set(v___f_2042_, 2, v_inst_1976_);
lean_closure_set(v___f_2042_, 3, v_f_1977_);
lean_inc(v_toPure_2036_);
v___f_2043_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14), 11, 10);
lean_closure_set(v___f_2043_, 0, v_typeName_2037_);
lean_closure_set(v___f_2043_, 1, v_toPure_2036_);
lean_closure_set(v___f_2043_, 2, v_alts_2040_);
lean_closure_set(v___f_2043_, 3, v_resultType_2038_);
lean_closure_set(v___f_2043_, 4, v_discr_2039_);
lean_closure_set(v___f_2043_, 5, v_c_1978_);
lean_closure_set(v___f_2043_, 6, v_inst_1976_);
lean_closure_set(v___f_2043_, 7, v___f_2042_);
lean_closure_set(v___f_2043_, 8, v_toBind_2035_);
lean_closure_set(v___f_2043_, 9, v_f_1977_);
v___x_2044_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1976_, v_f_1977_, v_resultType_2038_);
v___x_2045_ = lean_apply_4(v_toBind_2035_, lean_box(0), lean_box(0), v___x_2044_, v___f_2043_);
return v___x_2045_;
}
case 5:
{
lean_object* v_toApplicative_2046_; lean_object* v_toBind_2047_; lean_object* v_toPure_2048_; lean_object* v_fvarId_2049_; lean_object* v___f_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v_toApplicative_2046_ = lean_ctor_get(v_inst_1976_, 0);
lean_inc_ref(v_toApplicative_2046_);
lean_dec(v_inst_1975_);
v_toBind_2047_ = lean_ctor_get(v_inst_1976_, 1);
lean_inc(v_toBind_2047_);
lean_dec_ref(v_inst_1976_);
v_toPure_2048_ = lean_ctor_get(v_toApplicative_2046_, 1);
lean_inc(v_toPure_2048_);
lean_dec_ref(v_toApplicative_2046_);
v_fvarId_2049_ = lean_ctor_get(v_c_1978_, 0);
lean_inc_n(v_fvarId_2049_, 2);
v___f_2050_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed), 4, 3);
lean_closure_set(v___f_2050_, 0, v_fvarId_2049_);
lean_closure_set(v___f_2050_, 1, v_toPure_2048_);
lean_closure_set(v___f_2050_, 2, v_c_1978_);
v___x_2051_ = lean_apply_1(v_f_1977_, v_fvarId_2049_);
v___x_2052_ = lean_apply_4(v_toBind_2047_, lean_box(0), lean_box(0), v___x_2051_, v___f_2050_);
return v___x_2052_;
}
case 6:
{
lean_object* v_toApplicative_2053_; lean_object* v_toBind_2054_; lean_object* v_toPure_2055_; lean_object* v_type_2056_; lean_object* v___f_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v_toApplicative_2053_ = lean_ctor_get(v_inst_1976_, 0);
lean_dec(v_inst_1975_);
v_toBind_2054_ = lean_ctor_get(v_inst_1976_, 1);
lean_inc(v_toBind_2054_);
v_toPure_2055_ = lean_ctor_get(v_toApplicative_2053_, 1);
v_type_2056_ = lean_ctor_get(v_c_1978_, 0);
lean_inc_ref_n(v_type_2056_, 2);
lean_inc(v_toPure_2055_);
v___f_2057_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed), 4, 3);
lean_closure_set(v___f_2057_, 0, v_type_2056_);
lean_closure_set(v___f_2057_, 1, v_toPure_2055_);
lean_closure_set(v___f_2057_, 2, v_c_1978_);
v___x_2058_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1976_, v_f_1977_, v_type_2056_);
v___x_2059_ = lean_apply_4(v_toBind_2054_, lean_box(0), lean_box(0), v___x_2058_, v___f_2057_);
return v___x_2059_;
}
case 7:
{
lean_object* v_toApplicative_2060_; lean_object* v_toBind_2061_; lean_object* v_toPure_2062_; lean_object* v_fvarId_2063_; lean_object* v_i_2064_; lean_object* v_y_2065_; lean_object* v_k_2066_; lean_object* v___x_2067_; lean_object* v___f_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v_toApplicative_2060_ = lean_ctor_get(v_inst_1976_, 0);
v_toBind_2061_ = lean_ctor_get(v_inst_1976_, 1);
lean_inc_n(v_toBind_2061_, 2);
v_toPure_2062_ = lean_ctor_get(v_toApplicative_2060_, 1);
lean_inc(v_toPure_2062_);
v_fvarId_2063_ = lean_ctor_get(v_c_1978_, 0);
lean_inc_n(v_fvarId_2063_, 2);
v_i_2064_ = lean_ctor_get(v_c_1978_, 1);
lean_inc(v_i_2064_);
v_y_2065_ = lean_ctor_get(v_c_1978_, 2);
lean_inc(v_y_2065_);
v_k_2066_ = lean_ctor_get(v_c_1978_, 3);
lean_inc_ref(v_k_2066_);
v___x_2067_ = lean_box(v_pu_1974_);
lean_inc(v_f_1977_);
v___f_2068_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed), 12, 11);
lean_closure_set(v___f_2068_, 0, v_fvarId_2063_);
lean_closure_set(v___f_2068_, 1, v_i_2064_);
lean_closure_set(v___f_2068_, 2, v_toPure_2062_);
lean_closure_set(v___f_2068_, 3, v_y_2065_);
lean_closure_set(v___f_2068_, 4, v_k_2066_);
lean_closure_set(v___f_2068_, 5, v_c_1978_);
lean_closure_set(v___f_2068_, 6, v___x_2067_);
lean_closure_set(v___f_2068_, 7, v_inst_1975_);
lean_closure_set(v___f_2068_, 8, v_inst_1976_);
lean_closure_set(v___f_2068_, 9, v_f_1977_);
lean_closure_set(v___f_2068_, 10, v_toBind_2061_);
v___x_2069_ = lean_apply_1(v_f_1977_, v_fvarId_2063_);
v___x_2070_ = lean_apply_4(v_toBind_2061_, lean_box(0), lean_box(0), v___x_2069_, v___f_2068_);
return v___x_2070_;
}
case 8:
{
lean_object* v_toApplicative_2071_; lean_object* v_toBind_2072_; lean_object* v_toPure_2073_; lean_object* v_fvarId_2074_; lean_object* v_i_2075_; lean_object* v_y_2076_; lean_object* v_k_2077_; lean_object* v___x_2078_; lean_object* v___f_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v_toApplicative_2071_ = lean_ctor_get(v_inst_1976_, 0);
v_toBind_2072_ = lean_ctor_get(v_inst_1976_, 1);
lean_inc_n(v_toBind_2072_, 2);
v_toPure_2073_ = lean_ctor_get(v_toApplicative_2071_, 1);
lean_inc(v_toPure_2073_);
v_fvarId_2074_ = lean_ctor_get(v_c_1978_, 0);
lean_inc_n(v_fvarId_2074_, 2);
v_i_2075_ = lean_ctor_get(v_c_1978_, 1);
lean_inc(v_i_2075_);
v_y_2076_ = lean_ctor_get(v_c_1978_, 2);
lean_inc(v_y_2076_);
v_k_2077_ = lean_ctor_get(v_c_1978_, 3);
lean_inc_ref(v_k_2077_);
v___x_2078_ = lean_box(v_pu_1974_);
lean_inc(v_f_1977_);
v___f_2079_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed), 12, 11);
lean_closure_set(v___f_2079_, 0, v_fvarId_2074_);
lean_closure_set(v___f_2079_, 1, v_i_2075_);
lean_closure_set(v___f_2079_, 2, v_toPure_2073_);
lean_closure_set(v___f_2079_, 3, v_y_2076_);
lean_closure_set(v___f_2079_, 4, v_k_2077_);
lean_closure_set(v___f_2079_, 5, v_c_1978_);
lean_closure_set(v___f_2079_, 6, v___x_2078_);
lean_closure_set(v___f_2079_, 7, v_inst_1975_);
lean_closure_set(v___f_2079_, 8, v_inst_1976_);
lean_closure_set(v___f_2079_, 9, v_f_1977_);
lean_closure_set(v___f_2079_, 10, v_toBind_2072_);
v___x_2080_ = lean_apply_1(v_f_1977_, v_fvarId_2074_);
v___x_2081_ = lean_apply_4(v_toBind_2072_, lean_box(0), lean_box(0), v___x_2080_, v___f_2079_);
return v___x_2081_;
}
case 9:
{
lean_object* v_toApplicative_2082_; lean_object* v_toBind_2083_; lean_object* v_toPure_2084_; lean_object* v_fvarId_2085_; lean_object* v_i_2086_; lean_object* v_offset_2087_; lean_object* v_y_2088_; lean_object* v_ty_2089_; lean_object* v_k_2090_; lean_object* v___x_2091_; lean_object* v___f_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_toApplicative_2082_ = lean_ctor_get(v_inst_1976_, 0);
v_toBind_2083_ = lean_ctor_get(v_inst_1976_, 1);
lean_inc_n(v_toBind_2083_, 2);
v_toPure_2084_ = lean_ctor_get(v_toApplicative_2082_, 1);
lean_inc(v_toPure_2084_);
v_fvarId_2085_ = lean_ctor_get(v_c_1978_, 0);
lean_inc_n(v_fvarId_2085_, 2);
v_i_2086_ = lean_ctor_get(v_c_1978_, 1);
lean_inc(v_i_2086_);
v_offset_2087_ = lean_ctor_get(v_c_1978_, 2);
lean_inc(v_offset_2087_);
v_y_2088_ = lean_ctor_get(v_c_1978_, 3);
lean_inc(v_y_2088_);
v_ty_2089_ = lean_ctor_get(v_c_1978_, 4);
lean_inc_ref(v_ty_2089_);
v_k_2090_ = lean_ctor_get(v_c_1978_, 5);
lean_inc_ref(v_k_2090_);
v___x_2091_ = lean_box(v_pu_1974_);
lean_inc(v_f_1977_);
v___f_2092_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed), 14, 13);
lean_closure_set(v___f_2092_, 0, v_fvarId_2085_);
lean_closure_set(v___f_2092_, 1, v_i_2086_);
lean_closure_set(v___f_2092_, 2, v_offset_2087_);
lean_closure_set(v___f_2092_, 3, v_toPure_2084_);
lean_closure_set(v___f_2092_, 4, v_y_2088_);
lean_closure_set(v___f_2092_, 5, v_ty_2089_);
lean_closure_set(v___f_2092_, 6, v_k_2090_);
lean_closure_set(v___f_2092_, 7, v_c_1978_);
lean_closure_set(v___f_2092_, 8, v___x_2091_);
lean_closure_set(v___f_2092_, 9, v_inst_1975_);
lean_closure_set(v___f_2092_, 10, v_inst_1976_);
lean_closure_set(v___f_2092_, 11, v_f_1977_);
lean_closure_set(v___f_2092_, 12, v_toBind_2083_);
v___x_2093_ = lean_apply_1(v_f_1977_, v_fvarId_2085_);
v___x_2094_ = lean_apply_4(v_toBind_2083_, lean_box(0), lean_box(0), v___x_2093_, v___f_2092_);
return v___x_2094_;
}
case 10:
{
lean_object* v_toApplicative_2095_; lean_object* v_toBind_2096_; lean_object* v_toPure_2097_; lean_object* v_fvarId_2098_; lean_object* v_cidx_2099_; lean_object* v_k_2100_; lean_object* v___x_2101_; lean_object* v___f_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v_toApplicative_2095_ = lean_ctor_get(v_inst_1976_, 0);
v_toBind_2096_ = lean_ctor_get(v_inst_1976_, 1);
lean_inc_n(v_toBind_2096_, 2);
v_toPure_2097_ = lean_ctor_get(v_toApplicative_2095_, 1);
lean_inc(v_toPure_2097_);
v_fvarId_2098_ = lean_ctor_get(v_c_1978_, 0);
lean_inc_n(v_fvarId_2098_, 2);
v_cidx_2099_ = lean_ctor_get(v_c_1978_, 1);
lean_inc(v_cidx_2099_);
v_k_2100_ = lean_ctor_get(v_c_1978_, 2);
lean_inc_ref(v_k_2100_);
v___x_2101_ = lean_box(v_pu_1974_);
lean_inc(v_f_1977_);
v___f_2102_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed), 11, 10);
lean_closure_set(v___f_2102_, 0, v_fvarId_2098_);
lean_closure_set(v___f_2102_, 1, v_cidx_2099_);
lean_closure_set(v___f_2102_, 2, v_toPure_2097_);
lean_closure_set(v___f_2102_, 3, v_k_2100_);
lean_closure_set(v___f_2102_, 4, v_c_1978_);
lean_closure_set(v___f_2102_, 5, v___x_2101_);
lean_closure_set(v___f_2102_, 6, v_inst_1975_);
lean_closure_set(v___f_2102_, 7, v_inst_1976_);
lean_closure_set(v___f_2102_, 8, v_f_1977_);
lean_closure_set(v___f_2102_, 9, v_toBind_2096_);
v___x_2103_ = lean_apply_1(v_f_1977_, v_fvarId_2098_);
v___x_2104_ = lean_apply_4(v_toBind_2096_, lean_box(0), lean_box(0), v___x_2103_, v___f_2102_);
return v___x_2104_;
}
case 11:
{
lean_object* v_toApplicative_2105_; lean_object* v_toBind_2106_; lean_object* v_toPure_2107_; lean_object* v_fvarId_2108_; lean_object* v_n_2109_; uint8_t v_check_2110_; uint8_t v_persistent_2111_; lean_object* v_k_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___f_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_toApplicative_2105_ = lean_ctor_get(v_inst_1976_, 0);
v_toBind_2106_ = lean_ctor_get(v_inst_1976_, 1);
lean_inc_n(v_toBind_2106_, 2);
v_toPure_2107_ = lean_ctor_get(v_toApplicative_2105_, 1);
lean_inc(v_toPure_2107_);
v_fvarId_2108_ = lean_ctor_get(v_c_1978_, 0);
lean_inc_n(v_fvarId_2108_, 2);
v_n_2109_ = lean_ctor_get(v_c_1978_, 1);
lean_inc(v_n_2109_);
v_check_2110_ = lean_ctor_get_uint8(v_c_1978_, sizeof(void*)*3);
v_persistent_2111_ = lean_ctor_get_uint8(v_c_1978_, sizeof(void*)*3 + 1);
v_k_2112_ = lean_ctor_get(v_c_1978_, 2);
lean_inc_ref(v_k_2112_);
v___x_2113_ = lean_box(v_check_2110_);
v___x_2114_ = lean_box(v_persistent_2111_);
v___x_2115_ = lean_box(v_pu_1974_);
lean_inc(v_f_1977_);
v___f_2116_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed), 13, 12);
lean_closure_set(v___f_2116_, 0, v_fvarId_2108_);
lean_closure_set(v___f_2116_, 1, v_n_2109_);
lean_closure_set(v___f_2116_, 2, v___x_2113_);
lean_closure_set(v___f_2116_, 3, v___x_2114_);
lean_closure_set(v___f_2116_, 4, v_toPure_2107_);
lean_closure_set(v___f_2116_, 5, v_k_2112_);
lean_closure_set(v___f_2116_, 6, v_c_1978_);
lean_closure_set(v___f_2116_, 7, v___x_2115_);
lean_closure_set(v___f_2116_, 8, v_inst_1975_);
lean_closure_set(v___f_2116_, 9, v_inst_1976_);
lean_closure_set(v___f_2116_, 10, v_f_1977_);
lean_closure_set(v___f_2116_, 11, v_toBind_2106_);
v___x_2117_ = lean_apply_1(v_f_1977_, v_fvarId_2108_);
v___x_2118_ = lean_apply_4(v_toBind_2106_, lean_box(0), lean_box(0), v___x_2117_, v___f_2116_);
return v___x_2118_;
}
case 12:
{
lean_object* v_toApplicative_2119_; lean_object* v_toBind_2120_; lean_object* v_toPure_2121_; lean_object* v_fvarId_2122_; lean_object* v_n_2123_; uint8_t v_check_2124_; uint8_t v_persistent_2125_; lean_object* v_objs_x3f_2126_; lean_object* v_k_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___f_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_toApplicative_2119_ = lean_ctor_get(v_inst_1976_, 0);
v_toBind_2120_ = lean_ctor_get(v_inst_1976_, 1);
lean_inc_n(v_toBind_2120_, 2);
v_toPure_2121_ = lean_ctor_get(v_toApplicative_2119_, 1);
lean_inc(v_toPure_2121_);
v_fvarId_2122_ = lean_ctor_get(v_c_1978_, 0);
lean_inc_n(v_fvarId_2122_, 2);
v_n_2123_ = lean_ctor_get(v_c_1978_, 1);
lean_inc(v_n_2123_);
v_check_2124_ = lean_ctor_get_uint8(v_c_1978_, sizeof(void*)*4);
v_persistent_2125_ = lean_ctor_get_uint8(v_c_1978_, sizeof(void*)*4 + 1);
v_objs_x3f_2126_ = lean_ctor_get(v_c_1978_, 2);
lean_inc(v_objs_x3f_2126_);
v_k_2127_ = lean_ctor_get(v_c_1978_, 3);
lean_inc_ref(v_k_2127_);
v___x_2128_ = lean_box(v_check_2124_);
v___x_2129_ = lean_box(v_persistent_2125_);
v___x_2130_ = lean_box(v_pu_1974_);
lean_inc(v_f_1977_);
v___f_2131_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed), 14, 13);
lean_closure_set(v___f_2131_, 0, v_fvarId_2122_);
lean_closure_set(v___f_2131_, 1, v_n_2123_);
lean_closure_set(v___f_2131_, 2, v___x_2128_);
lean_closure_set(v___f_2131_, 3, v___x_2129_);
lean_closure_set(v___f_2131_, 4, v_objs_x3f_2126_);
lean_closure_set(v___f_2131_, 5, v_toPure_2121_);
lean_closure_set(v___f_2131_, 6, v_k_2127_);
lean_closure_set(v___f_2131_, 7, v_c_1978_);
lean_closure_set(v___f_2131_, 8, v___x_2130_);
lean_closure_set(v___f_2131_, 9, v_inst_1975_);
lean_closure_set(v___f_2131_, 10, v_inst_1976_);
lean_closure_set(v___f_2131_, 11, v_f_1977_);
lean_closure_set(v___f_2131_, 12, v_toBind_2120_);
v___x_2132_ = lean_apply_1(v_f_1977_, v_fvarId_2122_);
v___x_2133_ = lean_apply_4(v_toBind_2120_, lean_box(0), lean_box(0), v___x_2132_, v___f_2131_);
return v___x_2133_;
}
default: 
{
lean_object* v_toApplicative_2134_; lean_object* v_toBind_2135_; lean_object* v_toPure_2136_; lean_object* v_fvarId_2137_; lean_object* v_k_2138_; lean_object* v___x_2139_; lean_object* v___f_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v_toApplicative_2134_ = lean_ctor_get(v_inst_1976_, 0);
v_toBind_2135_ = lean_ctor_get(v_inst_1976_, 1);
lean_inc_n(v_toBind_2135_, 2);
v_toPure_2136_ = lean_ctor_get(v_toApplicative_2134_, 1);
lean_inc(v_toPure_2136_);
v_fvarId_2137_ = lean_ctor_get(v_c_1978_, 0);
lean_inc_n(v_fvarId_2137_, 2);
v_k_2138_ = lean_ctor_get(v_c_1978_, 1);
lean_inc_ref(v_k_2138_);
v___x_2139_ = lean_box(v_pu_1974_);
lean_inc(v_f_1977_);
v___f_2140_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed), 10, 9);
lean_closure_set(v___f_2140_, 0, v_fvarId_2137_);
lean_closure_set(v___f_2140_, 1, v_toPure_2136_);
lean_closure_set(v___f_2140_, 2, v_k_2138_);
lean_closure_set(v___f_2140_, 3, v_c_1978_);
lean_closure_set(v___f_2140_, 4, v___x_2139_);
lean_closure_set(v___f_2140_, 5, v_inst_1975_);
lean_closure_set(v___f_2140_, 6, v_inst_1976_);
lean_closure_set(v___f_2140_, 7, v_f_1977_);
lean_closure_set(v___f_2140_, 8, v_toBind_2135_);
v___x_2141_ = lean_apply_1(v_f_1977_, v_fvarId_2137_);
v___x_2142_ = lean_apply_4(v_toBind_2135_, lean_box(0), lean_box(0), v___x_2141_, v___f_2140_);
return v___x_2142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed(lean_object* v_pu_2143_, lean_object* v_inst_2144_, lean_object* v_inst_2145_, lean_object* v_f_2146_, lean_object* v_c_2147_){
_start:
{
uint8_t v_pu_boxed_2148_; lean_object* v_res_2149_; 
v_pu_boxed_2148_ = lean_unbox(v_pu_2143_);
v_res_2149_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_boxed_2148_, v_inst_2144_, v_inst_2145_, v_f_2146_, v_c_2147_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(uint8_t v_pu_2150_, lean_object* v_inst_2151_, lean_object* v_inst_2152_, lean_object* v_f_2153_, lean_object* v_x_2154_){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = lean_box(v_pu_2150_);
lean_inc_ref(v_inst_2152_);
v___x_2156_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed), 5, 4);
lean_closure_set(v___x_2156_, 0, v___x_2155_);
lean_closure_set(v___x_2156_, 1, v_inst_2151_);
lean_closure_set(v___x_2156_, 2, v_inst_2152_);
lean_closure_set(v___x_2156_, 3, v_f_2153_);
v___x_2157_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg(v_inst_2152_, v_x_2154_, v___x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM(lean_object* v_m_2158_, uint8_t v_pu_2159_, lean_object* v_inst_2160_, lean_object* v_inst_2161_, lean_object* v_f_2162_, lean_object* v_c_2163_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2159_, v_inst_2160_, v_inst_2161_, v_f_2162_, v_c_2163_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___boxed(lean_object* v_m_2165_, lean_object* v_pu_2166_, lean_object* v_inst_2167_, lean_object* v_inst_2168_, lean_object* v_f_2169_, lean_object* v_c_2170_){
_start:
{
uint8_t v_pu_boxed_2171_; lean_object* v_res_2172_; 
v_pu_boxed_2171_ = lean_unbox(v_pu_2166_);
v_res_2172_ = l_Lean_Compiler_LCNF_Code_mapFVarM(v_m_2165_, v_pu_boxed_2171_, v_inst_2167_, v_inst_2168_, v_f_2169_, v_c_2170_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1(lean_object* v_inst_2173_, lean_object* v_f_2174_, lean_object* v_type_2175_, lean_object* v_toBind_2176_, lean_object* v___f_2177_, lean_object* v_____r_2178_){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2173_, v_f_2174_, v_type_2175_);
v___x_2180_ = lean_apply_4(v_toBind_2176_, lean_box(0), lean_box(0), v___x_2179_, v___f_2177_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12(lean_object* v_inst_2181_, lean_object* v_f_2182_, lean_object* v_ty_2183_, lean_object* v_toBind_2184_, lean_object* v___f_2185_, lean_object* v_____r_2186_){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2187_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2181_, v_f_2182_, v_ty_2183_);
v___x_2188_ = lean_apply_4(v_toBind_2184_, lean_box(0), lean_box(0), v___x_2187_, v___f_2185_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4(lean_object* v_toApplicative_2189_, lean_object* v_args_2190_, lean_object* v_inst_2191_, lean_object* v___f_2192_, lean_object* v_____r_2193_){
_start:
{
lean_object* v_toPure_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; 
v_toPure_2194_ = lean_ctor_get(v_toApplicative_2189_, 1);
lean_inc(v_toPure_2194_);
lean_dec_ref(v_toApplicative_2189_);
v___x_2195_ = lean_unsigned_to_nat(0u);
v___x_2196_ = lean_array_get_size(v_args_2190_);
v___x_2197_ = lean_box(0);
v___x_2198_ = lean_nat_dec_lt(v___x_2195_, v___x_2196_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; 
lean_dec(v___f_2192_);
lean_dec_ref(v_inst_2191_);
lean_dec_ref(v_args_2190_);
v___x_2199_ = lean_apply_2(v_toPure_2194_, lean_box(0), v___x_2197_);
return v___x_2199_;
}
else
{
uint8_t v___x_2200_; 
v___x_2200_ = lean_nat_dec_le(v___x_2196_, v___x_2196_);
if (v___x_2200_ == 0)
{
if (v___x_2198_ == 0)
{
lean_object* v___x_2201_; 
lean_dec(v___f_2192_);
lean_dec_ref(v_inst_2191_);
lean_dec_ref(v_args_2190_);
v___x_2201_ = lean_apply_2(v_toPure_2194_, lean_box(0), v___x_2197_);
return v___x_2201_;
}
else
{
size_t v___x_2202_; size_t v___x_2203_; lean_object* v___x_2204_; 
lean_dec(v_toPure_2194_);
v___x_2202_ = ((size_t)0ULL);
v___x_2203_ = lean_usize_of_nat(v___x_2196_);
v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2191_, v___f_2192_, v_args_2190_, v___x_2202_, v___x_2203_, v___x_2197_);
return v___x_2204_;
}
}
else
{
size_t v___x_2205_; size_t v___x_2206_; lean_object* v___x_2207_; 
lean_dec(v_toPure_2194_);
v___x_2205_ = ((size_t)0ULL);
v___x_2206_ = lean_usize_of_nat(v___x_2196_);
v___x_2207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2191_, v___f_2192_, v_args_2190_, v___x_2205_, v___x_2206_, v___x_2197_);
return v___x_2207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3(lean_object* v_inst_2208_, lean_object* v_f_2209_, lean_object* v_x_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_2208_, v_f_2209_, v___y_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10(lean_object* v_inst_2213_, lean_object* v_f_2214_, lean_object* v_y_2215_, lean_object* v_toBind_2216_, lean_object* v___f_2217_, lean_object* v_____r_2218_){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2213_, v_f_2214_, v_y_2215_);
v___x_2220_ = lean_apply_4(v_toBind_2216_, lean_box(0), lean_box(0), v___x_2219_, v___f_2217_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11(lean_object* v_f_2221_, lean_object* v_y_2222_, lean_object* v_toBind_2223_, lean_object* v___f_2224_, lean_object* v_____r_2225_){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_apply_1(v_f_2221_, v_y_2222_);
v___x_2227_ = lean_apply_4(v_toBind_2223_, lean_box(0), lean_box(0), v___x_2226_, v___f_2224_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7(lean_object* v_f_2228_, lean_object* v_discr_2229_, lean_object* v_toBind_2230_, lean_object* v___f_2231_, lean_object* v_____r_2232_){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_apply_1(v_f_2228_, v_discr_2229_);
v___x_2234_ = lean_apply_4(v_toBind_2230_, lean_box(0), lean_box(0), v___x_2233_, v___f_2231_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6(lean_object* v_toApplicative_2235_, lean_object* v_alts_2236_, lean_object* v_inst_2237_, lean_object* v___f_2238_, lean_object* v_____r_2239_){
_start:
{
lean_object* v_toPure_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; uint8_t v___x_2244_; 
v_toPure_2240_ = lean_ctor_get(v_toApplicative_2235_, 1);
lean_inc(v_toPure_2240_);
lean_dec_ref(v_toApplicative_2235_);
v___x_2241_ = lean_unsigned_to_nat(0u);
v___x_2242_ = lean_array_get_size(v_alts_2236_);
v___x_2243_ = lean_box(0);
v___x_2244_ = lean_nat_dec_lt(v___x_2241_, v___x_2242_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; 
lean_dec(v___f_2238_);
lean_dec_ref(v_inst_2237_);
lean_dec_ref(v_alts_2236_);
v___x_2245_ = lean_apply_2(v_toPure_2240_, lean_box(0), v___x_2243_);
return v___x_2245_;
}
else
{
uint8_t v___x_2246_; 
v___x_2246_ = lean_nat_dec_le(v___x_2242_, v___x_2242_);
if (v___x_2246_ == 0)
{
if (v___x_2244_ == 0)
{
lean_object* v___x_2247_; 
lean_dec(v___f_2238_);
lean_dec_ref(v_inst_2237_);
lean_dec_ref(v_alts_2236_);
v___x_2247_ = lean_apply_2(v_toPure_2240_, lean_box(0), v___x_2243_);
return v___x_2247_;
}
else
{
size_t v___x_2248_; size_t v___x_2249_; lean_object* v___x_2250_; 
lean_dec(v_toPure_2240_);
v___x_2248_ = ((size_t)0ULL);
v___x_2249_ = lean_usize_of_nat(v___x_2242_);
v___x_2250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2237_, v___f_2238_, v_alts_2236_, v___x_2248_, v___x_2249_, v___x_2243_);
return v___x_2250_;
}
}
else
{
size_t v___x_2251_; size_t v___x_2252_; lean_object* v___x_2253_; 
lean_dec(v_toPure_2240_);
v___x_2251_ = ((size_t)0ULL);
v___x_2252_ = lean_usize_of_nat(v___x_2242_);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2237_, v___f_2238_, v_alts_2236_, v___x_2251_, v___x_2252_, v___x_2243_);
return v___x_2253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8(lean_object* v_inst_2254_, lean_object* v_f_2255_, lean_object* v_x_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2254_, v_f_2255_, v___y_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5(lean_object* v_inst_2259_, lean_object* v_f_2260_, lean_object* v_x_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg), 3, 2);
lean_closure_set(v___x_2263_, 0, v_inst_2259_);
lean_closure_set(v___x_2263_, 1, v_f_2260_);
v___x_2264_ = l_Lean_Compiler_LCNF_Alt_forCodeM___redArg(v___y_2262_, v___x_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2(lean_object* v_inst_2265_, lean_object* v_f_2266_, lean_object* v_value_2267_, lean_object* v_toBind_2268_, lean_object* v___f_2269_, lean_object* v_____r_2270_){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2265_, v_f_2266_, v_value_2267_);
v___x_2272_ = lean_apply_4(v_toBind_2268_, lean_box(0), lean_box(0), v___x_2271_, v___f_2269_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg(lean_object* v_inst_2273_, lean_object* v_f_2274_, lean_object* v_c_2275_){
_start:
{
switch(lean_obj_tag(v_c_2275_))
{
case 0:
{
lean_object* v_toBind_2276_; lean_object* v_decl_2277_; lean_object* v_k_2278_; lean_object* v___f_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v_toBind_2276_ = lean_ctor_get(v_inst_2273_, 1);
lean_inc(v_toBind_2276_);
v_decl_2277_ = lean_ctor_get(v_c_2275_, 0);
lean_inc_ref(v_decl_2277_);
v_k_2278_ = lean_ctor_get(v_c_2275_, 1);
lean_inc_ref(v_k_2278_);
lean_dec_ref_known(v_c_2275_, 2);
lean_inc(v_f_2274_);
lean_inc_ref(v_inst_2273_);
v___f_2279_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2279_, 0, v_inst_2273_);
lean_closure_set(v___f_2279_, 1, v_f_2274_);
lean_closure_set(v___f_2279_, 2, v_k_2278_);
v___x_2280_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_2273_, v_f_2274_, v_decl_2277_);
v___x_2281_ = lean_apply_4(v_toBind_2276_, lean_box(0), lean_box(0), v___x_2280_, v___f_2279_);
return v___x_2281_;
}
case 3:
{
lean_object* v_toApplicative_2282_; lean_object* v_toBind_2283_; lean_object* v_fvarId_2284_; lean_object* v_args_2285_; lean_object* v___f_2286_; lean_object* v___f_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v_toApplicative_2282_ = lean_ctor_get(v_inst_2273_, 0);
lean_inc_ref(v_toApplicative_2282_);
v_toBind_2283_ = lean_ctor_get(v_inst_2273_, 1);
lean_inc(v_toBind_2283_);
v_fvarId_2284_ = lean_ctor_get(v_c_2275_, 0);
lean_inc(v_fvarId_2284_);
v_args_2285_ = lean_ctor_get(v_c_2275_, 1);
lean_inc_ref(v_args_2285_);
lean_dec_ref_known(v_c_2275_, 2);
lean_inc(v_f_2274_);
lean_inc_ref(v_inst_2273_);
v___f_2286_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8), 4, 2);
lean_closure_set(v___f_2286_, 0, v_inst_2273_);
lean_closure_set(v___f_2286_, 1, v_f_2274_);
v___f_2287_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2287_, 0, v_toApplicative_2282_);
lean_closure_set(v___f_2287_, 1, v_args_2285_);
lean_closure_set(v___f_2287_, 2, v_inst_2273_);
lean_closure_set(v___f_2287_, 3, v___f_2286_);
v___x_2288_ = lean_apply_1(v_f_2274_, v_fvarId_2284_);
v___x_2289_ = lean_apply_4(v_toBind_2283_, lean_box(0), lean_box(0), v___x_2288_, v___f_2287_);
return v___x_2289_;
}
case 4:
{
lean_object* v_cases_2290_; lean_object* v_toApplicative_2291_; lean_object* v_toBind_2292_; lean_object* v_resultType_2293_; lean_object* v_discr_2294_; lean_object* v_alts_2295_; lean_object* v___f_2296_; lean_object* v___f_2297_; lean_object* v___f_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v_cases_2290_ = lean_ctor_get(v_c_2275_, 0);
lean_inc_ref(v_cases_2290_);
lean_dec_ref_known(v_c_2275_, 1);
v_toApplicative_2291_ = lean_ctor_get(v_inst_2273_, 0);
v_toBind_2292_ = lean_ctor_get(v_inst_2273_, 1);
lean_inc_n(v_toBind_2292_, 2);
v_resultType_2293_ = lean_ctor_get(v_cases_2290_, 1);
lean_inc_ref(v_resultType_2293_);
v_discr_2294_ = lean_ctor_get(v_cases_2290_, 2);
lean_inc(v_discr_2294_);
v_alts_2295_ = lean_ctor_get(v_cases_2290_, 3);
lean_inc_ref(v_alts_2295_);
lean_dec_ref(v_cases_2290_);
lean_inc_n(v_f_2274_, 2);
lean_inc_ref_n(v_inst_2273_, 2);
v___f_2296_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5), 4, 2);
lean_closure_set(v___f_2296_, 0, v_inst_2273_);
lean_closure_set(v___f_2296_, 1, v_f_2274_);
lean_inc_ref(v_toApplicative_2291_);
v___f_2297_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6), 5, 4);
lean_closure_set(v___f_2297_, 0, v_toApplicative_2291_);
lean_closure_set(v___f_2297_, 1, v_alts_2295_);
lean_closure_set(v___f_2297_, 2, v_inst_2273_);
lean_closure_set(v___f_2297_, 3, v___f_2296_);
v___f_2298_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7), 5, 4);
lean_closure_set(v___f_2298_, 0, v_f_2274_);
lean_closure_set(v___f_2298_, 1, v_discr_2294_);
lean_closure_set(v___f_2298_, 2, v_toBind_2292_);
lean_closure_set(v___f_2298_, 3, v___f_2297_);
v___x_2299_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2273_, v_f_2274_, v_resultType_2293_);
v___x_2300_ = lean_apply_4(v_toBind_2292_, lean_box(0), lean_box(0), v___x_2299_, v___f_2298_);
return v___x_2300_;
}
case 5:
{
lean_object* v_fvarId_2301_; lean_object* v___x_2302_; 
lean_dec_ref(v_inst_2273_);
v_fvarId_2301_ = lean_ctor_get(v_c_2275_, 0);
lean_inc(v_fvarId_2301_);
lean_dec_ref_known(v_c_2275_, 1);
v___x_2302_ = lean_apply_1(v_f_2274_, v_fvarId_2301_);
return v___x_2302_;
}
case 6:
{
lean_object* v_type_2303_; lean_object* v___x_2304_; 
v_type_2303_ = lean_ctor_get(v_c_2275_, 0);
lean_inc_ref(v_type_2303_);
lean_dec_ref_known(v_c_2275_, 1);
v___x_2304_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2273_, v_f_2274_, v_type_2303_);
return v___x_2304_;
}
case 7:
{
lean_object* v_toBind_2305_; lean_object* v_fvarId_2306_; lean_object* v_y_2307_; lean_object* v_k_2308_; lean_object* v___f_2309_; lean_object* v___f_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v_toBind_2305_ = lean_ctor_get(v_inst_2273_, 1);
lean_inc_n(v_toBind_2305_, 2);
v_fvarId_2306_ = lean_ctor_get(v_c_2275_, 0);
lean_inc(v_fvarId_2306_);
v_y_2307_ = lean_ctor_get(v_c_2275_, 2);
lean_inc(v_y_2307_);
v_k_2308_ = lean_ctor_get(v_c_2275_, 3);
lean_inc_ref(v_k_2308_);
lean_dec_ref_known(v_c_2275_, 4);
lean_inc_n(v_f_2274_, 2);
lean_inc_ref(v_inst_2273_);
v___f_2309_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2309_, 0, v_inst_2273_);
lean_closure_set(v___f_2309_, 1, v_f_2274_);
lean_closure_set(v___f_2309_, 2, v_k_2308_);
v___f_2310_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10), 6, 5);
lean_closure_set(v___f_2310_, 0, v_inst_2273_);
lean_closure_set(v___f_2310_, 1, v_f_2274_);
lean_closure_set(v___f_2310_, 2, v_y_2307_);
lean_closure_set(v___f_2310_, 3, v_toBind_2305_);
lean_closure_set(v___f_2310_, 4, v___f_2309_);
v___x_2311_ = lean_apply_1(v_f_2274_, v_fvarId_2306_);
v___x_2312_ = lean_apply_4(v_toBind_2305_, lean_box(0), lean_box(0), v___x_2311_, v___f_2310_);
return v___x_2312_;
}
case 8:
{
lean_object* v_toBind_2313_; lean_object* v_fvarId_2314_; lean_object* v_y_2315_; lean_object* v_k_2316_; lean_object* v___f_2317_; lean_object* v___f_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v_toBind_2313_ = lean_ctor_get(v_inst_2273_, 1);
lean_inc_n(v_toBind_2313_, 2);
v_fvarId_2314_ = lean_ctor_get(v_c_2275_, 0);
lean_inc(v_fvarId_2314_);
v_y_2315_ = lean_ctor_get(v_c_2275_, 2);
lean_inc(v_y_2315_);
v_k_2316_ = lean_ctor_get(v_c_2275_, 3);
lean_inc_ref(v_k_2316_);
lean_dec_ref_known(v_c_2275_, 4);
lean_inc_n(v_f_2274_, 2);
v___f_2317_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2317_, 0, v_inst_2273_);
lean_closure_set(v___f_2317_, 1, v_f_2274_);
lean_closure_set(v___f_2317_, 2, v_k_2316_);
v___f_2318_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11), 5, 4);
lean_closure_set(v___f_2318_, 0, v_f_2274_);
lean_closure_set(v___f_2318_, 1, v_y_2315_);
lean_closure_set(v___f_2318_, 2, v_toBind_2313_);
lean_closure_set(v___f_2318_, 3, v___f_2317_);
v___x_2319_ = lean_apply_1(v_f_2274_, v_fvarId_2314_);
v___x_2320_ = lean_apply_4(v_toBind_2313_, lean_box(0), lean_box(0), v___x_2319_, v___f_2318_);
return v___x_2320_;
}
case 9:
{
lean_object* v_toBind_2321_; lean_object* v_fvarId_2322_; lean_object* v_y_2323_; lean_object* v_ty_2324_; lean_object* v_k_2325_; lean_object* v___f_2326_; lean_object* v___f_2327_; lean_object* v___f_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v_toBind_2321_ = lean_ctor_get(v_inst_2273_, 1);
lean_inc_n(v_toBind_2321_, 3);
v_fvarId_2322_ = lean_ctor_get(v_c_2275_, 0);
lean_inc(v_fvarId_2322_);
v_y_2323_ = lean_ctor_get(v_c_2275_, 3);
lean_inc(v_y_2323_);
v_ty_2324_ = lean_ctor_get(v_c_2275_, 4);
lean_inc_ref(v_ty_2324_);
v_k_2325_ = lean_ctor_get(v_c_2275_, 5);
lean_inc_ref(v_k_2325_);
lean_dec_ref_known(v_c_2275_, 6);
lean_inc_n(v_f_2274_, 3);
lean_inc_ref(v_inst_2273_);
v___f_2326_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2326_, 0, v_inst_2273_);
lean_closure_set(v___f_2326_, 1, v_f_2274_);
lean_closure_set(v___f_2326_, 2, v_k_2325_);
v___f_2327_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12), 6, 5);
lean_closure_set(v___f_2327_, 0, v_inst_2273_);
lean_closure_set(v___f_2327_, 1, v_f_2274_);
lean_closure_set(v___f_2327_, 2, v_ty_2324_);
lean_closure_set(v___f_2327_, 3, v_toBind_2321_);
lean_closure_set(v___f_2327_, 4, v___f_2326_);
v___f_2328_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11), 5, 4);
lean_closure_set(v___f_2328_, 0, v_f_2274_);
lean_closure_set(v___f_2328_, 1, v_y_2323_);
lean_closure_set(v___f_2328_, 2, v_toBind_2321_);
lean_closure_set(v___f_2328_, 3, v___f_2327_);
v___x_2329_ = lean_apply_1(v_f_2274_, v_fvarId_2322_);
v___x_2330_ = lean_apply_4(v_toBind_2321_, lean_box(0), lean_box(0), v___x_2329_, v___f_2328_);
return v___x_2330_;
}
case 10:
{
lean_object* v_toBind_2331_; lean_object* v_fvarId_2332_; lean_object* v_k_2333_; lean_object* v___f_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_toBind_2331_ = lean_ctor_get(v_inst_2273_, 1);
lean_inc(v_toBind_2331_);
v_fvarId_2332_ = lean_ctor_get(v_c_2275_, 0);
lean_inc(v_fvarId_2332_);
v_k_2333_ = lean_ctor_get(v_c_2275_, 2);
lean_inc_ref(v_k_2333_);
lean_dec_ref_known(v_c_2275_, 3);
lean_inc(v_f_2274_);
v___f_2334_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2334_, 0, v_inst_2273_);
lean_closure_set(v___f_2334_, 1, v_f_2274_);
lean_closure_set(v___f_2334_, 2, v_k_2333_);
v___x_2335_ = lean_apply_1(v_f_2274_, v_fvarId_2332_);
v___x_2336_ = lean_apply_4(v_toBind_2331_, lean_box(0), lean_box(0), v___x_2335_, v___f_2334_);
return v___x_2336_;
}
case 11:
{
lean_object* v_toBind_2337_; lean_object* v_fvarId_2338_; lean_object* v_k_2339_; lean_object* v___f_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_toBind_2337_ = lean_ctor_get(v_inst_2273_, 1);
lean_inc(v_toBind_2337_);
v_fvarId_2338_ = lean_ctor_get(v_c_2275_, 0);
lean_inc(v_fvarId_2338_);
v_k_2339_ = lean_ctor_get(v_c_2275_, 2);
lean_inc_ref(v_k_2339_);
lean_dec_ref_known(v_c_2275_, 3);
lean_inc(v_f_2274_);
v___f_2340_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2340_, 0, v_inst_2273_);
lean_closure_set(v___f_2340_, 1, v_f_2274_);
lean_closure_set(v___f_2340_, 2, v_k_2339_);
v___x_2341_ = lean_apply_1(v_f_2274_, v_fvarId_2338_);
v___x_2342_ = lean_apply_4(v_toBind_2337_, lean_box(0), lean_box(0), v___x_2341_, v___f_2340_);
return v___x_2342_;
}
case 12:
{
lean_object* v_toBind_2343_; lean_object* v_fvarId_2344_; lean_object* v_k_2345_; lean_object* v___f_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v_toBind_2343_ = lean_ctor_get(v_inst_2273_, 1);
lean_inc(v_toBind_2343_);
v_fvarId_2344_ = lean_ctor_get(v_c_2275_, 0);
lean_inc(v_fvarId_2344_);
v_k_2345_ = lean_ctor_get(v_c_2275_, 3);
lean_inc_ref(v_k_2345_);
lean_dec_ref_known(v_c_2275_, 4);
lean_inc(v_f_2274_);
v___f_2346_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2346_, 0, v_inst_2273_);
lean_closure_set(v___f_2346_, 1, v_f_2274_);
lean_closure_set(v___f_2346_, 2, v_k_2345_);
v___x_2347_ = lean_apply_1(v_f_2274_, v_fvarId_2344_);
v___x_2348_ = lean_apply_4(v_toBind_2343_, lean_box(0), lean_box(0), v___x_2347_, v___f_2346_);
return v___x_2348_;
}
case 13:
{
lean_object* v_toBind_2349_; lean_object* v_fvarId_2350_; lean_object* v_k_2351_; lean_object* v___f_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v_toBind_2349_ = lean_ctor_get(v_inst_2273_, 1);
lean_inc(v_toBind_2349_);
v_fvarId_2350_ = lean_ctor_get(v_c_2275_, 0);
lean_inc(v_fvarId_2350_);
v_k_2351_ = lean_ctor_get(v_c_2275_, 1);
lean_inc_ref(v_k_2351_);
lean_dec_ref_known(v_c_2275_, 2);
lean_inc(v_f_2274_);
v___f_2352_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2352_, 0, v_inst_2273_);
lean_closure_set(v___f_2352_, 1, v_f_2274_);
lean_closure_set(v___f_2352_, 2, v_k_2351_);
v___x_2353_ = lean_apply_1(v_f_2274_, v_fvarId_2350_);
v___x_2354_ = lean_apply_4(v_toBind_2349_, lean_box(0), lean_box(0), v___x_2353_, v___f_2352_);
return v___x_2354_;
}
default: 
{
lean_object* v_decl_2355_; lean_object* v_toApplicative_2356_; lean_object* v_toBind_2357_; lean_object* v_k_2358_; lean_object* v_params_2359_; lean_object* v_type_2360_; lean_object* v_value_2361_; lean_object* v_toPure_2362_; lean_object* v___f_2363_; lean_object* v___f_2364_; lean_object* v___f_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; uint8_t v___x_2369_; 
v_decl_2355_ = lean_ctor_get(v_c_2275_, 0);
lean_inc_ref(v_decl_2355_);
v_toApplicative_2356_ = lean_ctor_get(v_inst_2273_, 0);
v_toBind_2357_ = lean_ctor_get(v_inst_2273_, 1);
lean_inc_n(v_toBind_2357_, 3);
v_k_2358_ = lean_ctor_get(v_c_2275_, 1);
lean_inc_ref(v_k_2358_);
lean_dec_ref(v_c_2275_);
v_params_2359_ = lean_ctor_get(v_decl_2355_, 2);
lean_inc_ref(v_params_2359_);
v_type_2360_ = lean_ctor_get(v_decl_2355_, 3);
lean_inc_ref(v_type_2360_);
v_value_2361_ = lean_ctor_get(v_decl_2355_, 4);
lean_inc_ref(v_value_2361_);
lean_dec_ref(v_decl_2355_);
v_toPure_2362_ = lean_ctor_get(v_toApplicative_2356_, 1);
lean_inc_n(v_f_2274_, 3);
lean_inc_ref_n(v_inst_2273_, 3);
v___f_2363_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2363_, 0, v_inst_2273_);
lean_closure_set(v___f_2363_, 1, v_f_2274_);
lean_closure_set(v___f_2363_, 2, v_k_2358_);
v___f_2364_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2364_, 0, v_inst_2273_);
lean_closure_set(v___f_2364_, 1, v_f_2274_);
lean_closure_set(v___f_2364_, 2, v_value_2361_);
lean_closure_set(v___f_2364_, 3, v_toBind_2357_);
lean_closure_set(v___f_2364_, 4, v___f_2363_);
v___f_2365_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2365_, 0, v_inst_2273_);
lean_closure_set(v___f_2365_, 1, v_f_2274_);
lean_closure_set(v___f_2365_, 2, v_type_2360_);
lean_closure_set(v___f_2365_, 3, v_toBind_2357_);
lean_closure_set(v___f_2365_, 4, v___f_2364_);
v___x_2366_ = lean_unsigned_to_nat(0u);
v___x_2367_ = lean_array_get_size(v_params_2359_);
v___x_2368_ = lean_box(0);
v___x_2369_ = lean_nat_dec_lt(v___x_2366_, v___x_2367_);
if (v___x_2369_ == 0)
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
lean_inc(v_toPure_2362_);
lean_dec_ref(v_params_2359_);
lean_dec(v_f_2274_);
lean_dec_ref(v_inst_2273_);
v___x_2370_ = lean_apply_2(v_toPure_2362_, lean_box(0), v___x_2368_);
v___x_2371_ = lean_apply_4(v_toBind_2357_, lean_box(0), lean_box(0), v___x_2370_, v___f_2365_);
return v___x_2371_;
}
else
{
lean_object* v___f_2372_; uint8_t v___x_2373_; 
lean_inc_ref(v_inst_2273_);
v___f_2372_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2372_, 0, v_inst_2273_);
lean_closure_set(v___f_2372_, 1, v_f_2274_);
v___x_2373_ = lean_nat_dec_le(v___x_2367_, v___x_2367_);
if (v___x_2373_ == 0)
{
if (v___x_2369_ == 0)
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
lean_inc(v_toPure_2362_);
lean_dec_ref(v___f_2372_);
lean_dec_ref(v_params_2359_);
lean_dec_ref(v_inst_2273_);
v___x_2374_ = lean_apply_2(v_toPure_2362_, lean_box(0), v___x_2368_);
v___x_2375_ = lean_apply_4(v_toBind_2357_, lean_box(0), lean_box(0), v___x_2374_, v___f_2365_);
return v___x_2375_;
}
else
{
size_t v___x_2376_; size_t v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2376_ = ((size_t)0ULL);
v___x_2377_ = lean_usize_of_nat(v___x_2367_);
v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2273_, v___f_2372_, v_params_2359_, v___x_2376_, v___x_2377_, v___x_2368_);
v___x_2379_ = lean_apply_4(v_toBind_2357_, lean_box(0), lean_box(0), v___x_2378_, v___f_2365_);
return v___x_2379_;
}
}
else
{
size_t v___x_2380_; size_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2380_ = ((size_t)0ULL);
v___x_2381_ = lean_usize_of_nat(v___x_2367_);
v___x_2382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2273_, v___f_2372_, v_params_2359_, v___x_2380_, v___x_2381_, v___x_2368_);
v___x_2383_ = lean_apply_4(v_toBind_2357_, lean_box(0), lean_box(0), v___x_2382_, v___f_2365_);
return v___x_2383_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0(lean_object* v_inst_2384_, lean_object* v_f_2385_, lean_object* v_k_2386_, lean_object* v_____r_2387_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2384_, v_f_2385_, v_k_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM(lean_object* v_m_2389_, uint8_t v_pu_2390_, lean_object* v_inst_2391_, lean_object* v_f_2392_, lean_object* v_c_2393_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2391_, v_f_2392_, v_c_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___boxed(lean_object* v_m_2395_, lean_object* v_pu_2396_, lean_object* v_inst_2397_, lean_object* v_f_2398_, lean_object* v_c_2399_){
_start:
{
uint8_t v_pu_boxed_2400_; lean_object* v_res_2401_; 
v_pu_boxed_2400_ = lean_unbox(v_pu_2396_);
v_res_2401_ = l_Lean_Compiler_LCNF_Code_forFVarM(v_m_2395_, v_pu_boxed_2400_, v_inst_2397_, v_f_2398_, v_c_2399_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(uint8_t v_pu_2402_, lean_object* v_m_2403_, lean_object* v_inst_2404_, lean_object* v_inst_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2402_, v_inst_2404_, v_inst_2405_, v___y_2406_, v___y_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed(lean_object* v_pu_2409_, lean_object* v_m_2410_, lean_object* v_inst_2411_, lean_object* v_inst_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
uint8_t v_pu_boxed_2415_; lean_object* v_res_2416_; 
v_pu_boxed_2415_ = lean_unbox(v_pu_2409_);
v_res_2416_ = l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(v_pu_boxed_2415_, v_m_2410_, v_inst_2411_, v_inst_2412_, v___y_2413_, v___y_2414_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__1(lean_object* v_m_2417_, lean_object* v_inst_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2418_, v___y_2419_, v___y_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode(uint8_t v_pu_2423_){
_start:
{
lean_object* v___x_2424_; lean_object* v___f_2425_; lean_object* v___f_2426_; lean_object* v___x_2427_; 
v___x_2424_ = lean_box(v_pu_2423_);
v___f_2425_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2425_, 0, v___x_2424_);
v___f_2426_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0));
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___f_2425_);
lean_ctor_set(v___x_2427_, 1, v___f_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___boxed(lean_object* v_pu_2428_){
_start:
{
uint8_t v_pu_boxed_2429_; lean_object* v_res_2430_; 
v_pu_boxed_2429_ = lean_unbox(v_pu_2428_);
v_res_2430_ = l_Lean_Compiler_LCNF_instTraverseFVarCode(v_pu_boxed_2429_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(uint8_t v_pu_2431_, lean_object* v_decl_2432_, lean_object* v_____do__lift_2433_, lean_object* v_params_2434_, lean_object* v_inst_2435_, lean_object* v_____do__lift_2436_){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2437_ = lean_box(v_pu_2431_);
v___x_2438_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed), 10, 5);
lean_closure_set(v___x_2438_, 0, v___x_2437_);
lean_closure_set(v___x_2438_, 1, v_decl_2432_);
lean_closure_set(v___x_2438_, 2, v_____do__lift_2433_);
lean_closure_set(v___x_2438_, 3, v_params_2434_);
lean_closure_set(v___x_2438_, 4, v_____do__lift_2436_);
v___x_2439_ = lean_apply_2(v_inst_2435_, lean_box(0), v___x_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_2440_, lean_object* v_decl_2441_, lean_object* v_____do__lift_2442_, lean_object* v_params_2443_, lean_object* v_inst_2444_, lean_object* v_____do__lift_2445_){
_start:
{
uint8_t v_pu_boxed_2446_; lean_object* v_res_2447_; 
v_pu_boxed_2446_ = lean_unbox(v_pu_2440_);
v_res_2447_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(v_pu_boxed_2446_, v_decl_2441_, v_____do__lift_2442_, v_params_2443_, v_inst_2444_, v_____do__lift_2445_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(uint8_t v_pu_2448_, lean_object* v_decl_2449_, lean_object* v_params_2450_, lean_object* v_inst_2451_, lean_object* v_inst_2452_, lean_object* v_f_2453_, lean_object* v_value_2454_, lean_object* v_toBind_2455_, lean_object* v_____do__lift_2456_){
_start:
{
lean_object* v___x_2457_; lean_object* v___f_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2457_ = lean_box(v_pu_2448_);
lean_inc(v_inst_2451_);
v___f_2458_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2458_, 0, v___x_2457_);
lean_closure_set(v___f_2458_, 1, v_decl_2449_);
lean_closure_set(v___f_2458_, 2, v_____do__lift_2456_);
lean_closure_set(v___f_2458_, 3, v_params_2450_);
lean_closure_set(v___f_2458_, 4, v_inst_2451_);
v___x_2459_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2448_, v_inst_2451_, v_inst_2452_, v_f_2453_, v_value_2454_);
v___x_2460_ = lean_apply_4(v_toBind_2455_, lean_box(0), lean_box(0), v___x_2459_, v___f_2458_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed(lean_object* v_pu_2461_, lean_object* v_decl_2462_, lean_object* v_params_2463_, lean_object* v_inst_2464_, lean_object* v_inst_2465_, lean_object* v_f_2466_, lean_object* v_value_2467_, lean_object* v_toBind_2468_, lean_object* v_____do__lift_2469_){
_start:
{
uint8_t v_pu_boxed_2470_; lean_object* v_res_2471_; 
v_pu_boxed_2470_ = lean_unbox(v_pu_2461_);
v_res_2471_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(v_pu_boxed_2470_, v_decl_2462_, v_params_2463_, v_inst_2464_, v_inst_2465_, v_f_2466_, v_value_2467_, v_toBind_2468_, v_____do__lift_2469_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(uint8_t v_pu_2472_, lean_object* v_decl_2473_, lean_object* v_inst_2474_, lean_object* v_inst_2475_, lean_object* v_f_2476_, lean_object* v_value_2477_, lean_object* v_toBind_2478_, lean_object* v_type_2479_, lean_object* v_params_2480_){
_start:
{
lean_object* v___x_2481_; lean_object* v___f_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2481_ = lean_box(v_pu_2472_);
lean_inc(v_toBind_2478_);
lean_inc(v_f_2476_);
lean_inc_ref(v_inst_2475_);
v___f_2482_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2482_, 0, v___x_2481_);
lean_closure_set(v___f_2482_, 1, v_decl_2473_);
lean_closure_set(v___f_2482_, 2, v_params_2480_);
lean_closure_set(v___f_2482_, 3, v_inst_2474_);
lean_closure_set(v___f_2482_, 4, v_inst_2475_);
lean_closure_set(v___f_2482_, 5, v_f_2476_);
lean_closure_set(v___f_2482_, 6, v_value_2477_);
lean_closure_set(v___f_2482_, 7, v_toBind_2478_);
v___x_2483_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2475_, v_f_2476_, v_type_2479_);
v___x_2484_ = lean_apply_4(v_toBind_2478_, lean_box(0), lean_box(0), v___x_2483_, v___f_2482_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed(lean_object* v_pu_2485_, lean_object* v_decl_2486_, lean_object* v_inst_2487_, lean_object* v_inst_2488_, lean_object* v_f_2489_, lean_object* v_value_2490_, lean_object* v_toBind_2491_, lean_object* v_type_2492_, lean_object* v_params_2493_){
_start:
{
uint8_t v_pu_boxed_2494_; lean_object* v_res_2495_; 
v_pu_boxed_2494_ = lean_unbox(v_pu_2485_);
v_res_2495_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(v_pu_boxed_2494_, v_decl_2486_, v_inst_2487_, v_inst_2488_, v_f_2489_, v_value_2490_, v_toBind_2491_, v_type_2492_, v_params_2493_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(uint8_t v_pu_2496_, lean_object* v_inst_2497_, lean_object* v_inst_2498_, lean_object* v_f_2499_, lean_object* v_decl_2500_){
_start:
{
lean_object* v_toBind_2501_; lean_object* v_params_2502_; lean_object* v_type_2503_; lean_object* v_value_2504_; lean_object* v___x_2505_; lean_object* v___f_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; size_t v_sz_2509_; size_t v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v_toBind_2501_ = lean_ctor_get(v_inst_2498_, 1);
lean_inc_n(v_toBind_2501_, 2);
v_params_2502_ = lean_ctor_get(v_decl_2500_, 2);
lean_inc_ref(v_params_2502_);
v_type_2503_ = lean_ctor_get(v_decl_2500_, 3);
lean_inc_ref(v_type_2503_);
v_value_2504_ = lean_ctor_get(v_decl_2500_, 4);
lean_inc_ref(v_value_2504_);
v___x_2505_ = lean_box(v_pu_2496_);
lean_inc(v_f_2499_);
lean_inc_ref_n(v_inst_2498_, 2);
lean_inc(v_inst_2497_);
v___f_2506_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2506_, 0, v___x_2505_);
lean_closure_set(v___f_2506_, 1, v_decl_2500_);
lean_closure_set(v___f_2506_, 2, v_inst_2497_);
lean_closure_set(v___f_2506_, 3, v_inst_2498_);
lean_closure_set(v___f_2506_, 4, v_f_2499_);
lean_closure_set(v___f_2506_, 5, v_value_2504_);
lean_closure_set(v___f_2506_, 6, v_toBind_2501_);
lean_closure_set(v___f_2506_, 7, v_type_2503_);
v___x_2507_ = lean_box(v_pu_2496_);
v___x_2508_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2508_, 0, lean_box(0));
lean_closure_set(v___x_2508_, 1, v___x_2507_);
lean_closure_set(v___x_2508_, 2, v_inst_2497_);
lean_closure_set(v___x_2508_, 3, v_inst_2498_);
lean_closure_set(v___x_2508_, 4, v_f_2499_);
v_sz_2509_ = lean_array_size(v_params_2502_);
v___x_2510_ = ((size_t)0ULL);
v___x_2511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2498_, v___x_2508_, v_sz_2509_, v___x_2510_, v_params_2502_);
v___x_2512_ = lean_apply_4(v_toBind_2501_, lean_box(0), lean_box(0), v___x_2511_, v___f_2506_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___boxed(lean_object* v_pu_2513_, lean_object* v_inst_2514_, lean_object* v_inst_2515_, lean_object* v_f_2516_, lean_object* v_decl_2517_){
_start:
{
uint8_t v_pu_boxed_2518_; lean_object* v_res_2519_; 
v_pu_boxed_2518_ = lean_unbox(v_pu_2513_);
v_res_2519_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_boxed_2518_, v_inst_2514_, v_inst_2515_, v_f_2516_, v_decl_2517_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM(lean_object* v_m_2520_, uint8_t v_pu_2521_, lean_object* v_inst_2522_, lean_object* v_inst_2523_, lean_object* v_f_2524_, lean_object* v_decl_2525_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2521_, v_inst_2522_, v_inst_2523_, v_f_2524_, v_decl_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___boxed(lean_object* v_m_2527_, lean_object* v_pu_2528_, lean_object* v_inst_2529_, lean_object* v_inst_2530_, lean_object* v_f_2531_, lean_object* v_decl_2532_){
_start:
{
uint8_t v_pu_boxed_2533_; lean_object* v_res_2534_; 
v_pu_boxed_2533_ = lean_unbox(v_pu_2528_);
v_res_2534_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM(v_m_2527_, v_pu_boxed_2533_, v_inst_2529_, v_inst_2530_, v_f_2531_, v_decl_2532_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0(lean_object* v_inst_2535_, lean_object* v_f_2536_, lean_object* v_value_2537_, lean_object* v_____r_2538_){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2535_, v_f_2536_, v_value_2537_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1(lean_object* v_inst_2540_, lean_object* v_f_2541_, lean_object* v_type_2542_, lean_object* v_toBind_2543_, lean_object* v___f_2544_, lean_object* v_____r_2545_){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2540_, v_f_2541_, v_type_2542_);
v___x_2547_ = lean_apply_4(v_toBind_2543_, lean_box(0), lean_box(0), v___x_2546_, v___f_2544_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2(lean_object* v_inst_2548_, lean_object* v_f_2549_, lean_object* v_x_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v___x_2552_; 
v___x_2552_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_2548_, v_f_2549_, v___y_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(lean_object* v_inst_2553_, lean_object* v_f_2554_, lean_object* v_decl_2555_){
_start:
{
lean_object* v_toApplicative_2556_; lean_object* v_toBind_2557_; lean_object* v_params_2558_; lean_object* v_type_2559_; lean_object* v_value_2560_; lean_object* v_toPure_2561_; lean_object* v___f_2562_; lean_object* v___f_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
v_toApplicative_2556_ = lean_ctor_get(v_inst_2553_, 0);
v_toBind_2557_ = lean_ctor_get(v_inst_2553_, 1);
lean_inc_n(v_toBind_2557_, 2);
v_params_2558_ = lean_ctor_get(v_decl_2555_, 2);
lean_inc_ref(v_params_2558_);
v_type_2559_ = lean_ctor_get(v_decl_2555_, 3);
lean_inc_ref(v_type_2559_);
v_value_2560_ = lean_ctor_get(v_decl_2555_, 4);
lean_inc_ref(v_value_2560_);
lean_dec_ref(v_decl_2555_);
v_toPure_2561_ = lean_ctor_get(v_toApplicative_2556_, 1);
lean_inc_n(v_f_2554_, 2);
lean_inc_ref_n(v_inst_2553_, 2);
v___f_2562_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2562_, 0, v_inst_2553_);
lean_closure_set(v___f_2562_, 1, v_f_2554_);
lean_closure_set(v___f_2562_, 2, v_value_2560_);
v___f_2563_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2563_, 0, v_inst_2553_);
lean_closure_set(v___f_2563_, 1, v_f_2554_);
lean_closure_set(v___f_2563_, 2, v_type_2559_);
lean_closure_set(v___f_2563_, 3, v_toBind_2557_);
lean_closure_set(v___f_2563_, 4, v___f_2562_);
v___x_2564_ = lean_unsigned_to_nat(0u);
v___x_2565_ = lean_array_get_size(v_params_2558_);
v___x_2566_ = lean_box(0);
v___x_2567_ = lean_nat_dec_lt(v___x_2564_, v___x_2565_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; lean_object* v___x_2569_; 
lean_inc(v_toPure_2561_);
lean_dec_ref(v_params_2558_);
lean_dec(v_f_2554_);
lean_dec_ref(v_inst_2553_);
v___x_2568_ = lean_apply_2(v_toPure_2561_, lean_box(0), v___x_2566_);
v___x_2569_ = lean_apply_4(v_toBind_2557_, lean_box(0), lean_box(0), v___x_2568_, v___f_2563_);
return v___x_2569_;
}
else
{
lean_object* v___f_2570_; uint8_t v___x_2571_; 
lean_inc_ref(v_inst_2553_);
v___f_2570_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_2570_, 0, v_inst_2553_);
lean_closure_set(v___f_2570_, 1, v_f_2554_);
v___x_2571_ = lean_nat_dec_le(v___x_2565_, v___x_2565_);
if (v___x_2571_ == 0)
{
if (v___x_2567_ == 0)
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
lean_inc(v_toPure_2561_);
lean_dec_ref(v___f_2570_);
lean_dec_ref(v_params_2558_);
lean_dec_ref(v_inst_2553_);
v___x_2572_ = lean_apply_2(v_toPure_2561_, lean_box(0), v___x_2566_);
v___x_2573_ = lean_apply_4(v_toBind_2557_, lean_box(0), lean_box(0), v___x_2572_, v___f_2563_);
return v___x_2573_;
}
else
{
size_t v___x_2574_; size_t v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2574_ = ((size_t)0ULL);
v___x_2575_ = lean_usize_of_nat(v___x_2565_);
v___x_2576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2553_, v___f_2570_, v_params_2558_, v___x_2574_, v___x_2575_, v___x_2566_);
v___x_2577_ = lean_apply_4(v_toBind_2557_, lean_box(0), lean_box(0), v___x_2576_, v___f_2563_);
return v___x_2577_;
}
}
else
{
size_t v___x_2578_; size_t v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2578_ = ((size_t)0ULL);
v___x_2579_ = lean_usize_of_nat(v___x_2565_);
v___x_2580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2553_, v___f_2570_, v_params_2558_, v___x_2578_, v___x_2579_, v___x_2566_);
v___x_2581_ = lean_apply_4(v_toBind_2557_, lean_box(0), lean_box(0), v___x_2580_, v___f_2563_);
return v___x_2581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM(lean_object* v_m_2582_, uint8_t v_pu_2583_, lean_object* v_inst_2584_, lean_object* v_f_2585_, lean_object* v_decl_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2584_, v_f_2585_, v_decl_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___boxed(lean_object* v_m_2588_, lean_object* v_pu_2589_, lean_object* v_inst_2590_, lean_object* v_f_2591_, lean_object* v_decl_2592_){
_start:
{
uint8_t v_pu_boxed_2593_; lean_object* v_res_2594_; 
v_pu_boxed_2593_ = lean_unbox(v_pu_2589_);
v_res_2594_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM(v_m_2588_, v_pu_boxed_2593_, v_inst_2590_, v_f_2591_, v_decl_2592_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(uint8_t v_pu_2595_, lean_object* v_m_2596_, lean_object* v_inst_2597_, lean_object* v_inst_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2595_, v_inst_2597_, v_inst_2598_, v___y_2599_, v___y_2600_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed(lean_object* v_pu_2602_, lean_object* v_m_2603_, lean_object* v_inst_2604_, lean_object* v_inst_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
uint8_t v_pu_boxed_2608_; lean_object* v_res_2609_; 
v_pu_boxed_2608_ = lean_unbox(v_pu_2602_);
v_res_2609_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(v_pu_boxed_2608_, v_m_2603_, v_inst_2604_, v_inst_2605_, v___y_2606_, v___y_2607_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__1(lean_object* v_m_2610_, lean_object* v_inst_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2611_, v___y_2612_, v___y_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(uint8_t v_pu_2616_){
_start:
{
lean_object* v___x_2617_; lean_object* v___f_2618_; lean_object* v___f_2619_; lean_object* v___x_2620_; 
v___x_2617_ = lean_box(v_pu_2616_);
v___f_2618_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2618_, 0, v___x_2617_);
v___f_2619_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0));
v___x_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___f_2618_);
lean_ctor_set(v___x_2620_, 1, v___f_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___boxed(lean_object* v_pu_2621_){
_start:
{
uint8_t v_pu_boxed_2622_; lean_object* v_res_2623_; 
v_pu_boxed_2622_ = lean_unbox(v_pu_2621_);
v_res_2623_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(v_pu_boxed_2622_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0(lean_object* v_toPure_2624_, lean_object* v_____do__lift_2625_){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_____do__lift_2625_);
v___x_2627_ = lean_apply_2(v_toPure_2624_, lean_box(0), v___x_2626_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1(lean_object* v_toPure_2628_, lean_object* v_____do__lift_2629_){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2630_, 0, v_____do__lift_2629_);
v___x_2631_ = lean_apply_2(v_toPure_2628_, lean_box(0), v___x_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2(lean_object* v_toPure_2632_, lean_object* v_____do__lift_2633_){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2634_, 0, v_____do__lift_2633_);
v___x_2635_ = lean_apply_2(v_toPure_2632_, lean_box(0), v___x_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3(lean_object* v_____do__lift_2636_, lean_object* v_i_2637_, lean_object* v_toPure_2638_, lean_object* v_____do__lift_2639_){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2640_, 0, v_____do__lift_2636_);
lean_ctor_set(v___x_2640_, 1, v_i_2637_);
lean_ctor_set(v___x_2640_, 2, v_____do__lift_2639_);
v___x_2641_ = lean_apply_2(v_toPure_2638_, lean_box(0), v___x_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(lean_object* v_i_2642_, lean_object* v_toPure_2643_, uint8_t v_pu_2644_, lean_object* v_inst_2645_, lean_object* v_f_2646_, lean_object* v_y_2647_, lean_object* v_toBind_2648_, lean_object* v_____do__lift_2649_){
_start:
{
lean_object* v___f_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___f_2650_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3), 4, 3);
lean_closure_set(v___f_2650_, 0, v_____do__lift_2649_);
lean_closure_set(v___f_2650_, 1, v_i_2642_);
lean_closure_set(v___f_2650_, 2, v_toPure_2643_);
v___x_2651_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_2644_, v_inst_2645_, v_f_2646_, v_y_2647_);
v___x_2652_ = lean_apply_4(v_toBind_2648_, lean_box(0), lean_box(0), v___x_2651_, v___f_2650_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed(lean_object* v_i_2653_, lean_object* v_toPure_2654_, lean_object* v_pu_2655_, lean_object* v_inst_2656_, lean_object* v_f_2657_, lean_object* v_y_2658_, lean_object* v_toBind_2659_, lean_object* v_____do__lift_2660_){
_start:
{
uint8_t v_pu_boxed_2661_; lean_object* v_res_2662_; 
v_pu_boxed_2661_ = lean_unbox(v_pu_2655_);
v_res_2662_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(v_i_2653_, v_toPure_2654_, v_pu_boxed_2661_, v_inst_2656_, v_f_2657_, v_y_2658_, v_toBind_2659_, v_____do__lift_2660_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5(lean_object* v_____do__lift_2663_, lean_object* v_i_2664_, lean_object* v_toPure_2665_, lean_object* v_____do__lift_2666_){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_2667_, 0, v_____do__lift_2663_);
lean_ctor_set(v___x_2667_, 1, v_i_2664_);
lean_ctor_set(v___x_2667_, 2, v_____do__lift_2666_);
v___x_2668_ = lean_apply_2(v_toPure_2665_, lean_box(0), v___x_2667_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6(lean_object* v_i_2669_, lean_object* v_toPure_2670_, lean_object* v_f_2671_, lean_object* v_y_2672_, lean_object* v_toBind_2673_, lean_object* v_____do__lift_2674_){
_start:
{
lean_object* v___f_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___f_2675_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5), 4, 3);
lean_closure_set(v___f_2675_, 0, v_____do__lift_2674_);
lean_closure_set(v___f_2675_, 1, v_i_2669_);
lean_closure_set(v___f_2675_, 2, v_toPure_2670_);
v___x_2676_ = lean_apply_1(v_f_2671_, v_y_2672_);
v___x_2677_ = lean_apply_4(v_toBind_2673_, lean_box(0), lean_box(0), v___x_2676_, v___f_2675_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7(lean_object* v_____do__lift_2678_, lean_object* v_i_2679_, lean_object* v_offset_2680_, lean_object* v_____do__lift_2681_, lean_object* v_toPure_2682_, lean_object* v_____do__lift_2683_){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2684_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v___x_2684_, 0, v_____do__lift_2678_);
lean_ctor_set(v___x_2684_, 1, v_i_2679_);
lean_ctor_set(v___x_2684_, 2, v_offset_2680_);
lean_ctor_set(v___x_2684_, 3, v_____do__lift_2681_);
lean_ctor_set(v___x_2684_, 4, v_____do__lift_2683_);
v___x_2685_ = lean_apply_2(v_toPure_2682_, lean_box(0), v___x_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8(lean_object* v_____do__lift_2686_, lean_object* v_i_2687_, lean_object* v_offset_2688_, lean_object* v_toPure_2689_, lean_object* v_inst_2690_, lean_object* v_f_2691_, lean_object* v_ty_2692_, lean_object* v_toBind_2693_, lean_object* v_____do__lift_2694_){
_start:
{
lean_object* v___f_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___f_2695_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7), 6, 5);
lean_closure_set(v___f_2695_, 0, v_____do__lift_2686_);
lean_closure_set(v___f_2695_, 1, v_i_2687_);
lean_closure_set(v___f_2695_, 2, v_offset_2688_);
lean_closure_set(v___f_2695_, 3, v_____do__lift_2694_);
lean_closure_set(v___f_2695_, 4, v_toPure_2689_);
v___x_2696_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2690_, v_f_2691_, v_ty_2692_);
v___x_2697_ = lean_apply_4(v_toBind_2693_, lean_box(0), lean_box(0), v___x_2696_, v___f_2695_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9(lean_object* v_i_2698_, lean_object* v_offset_2699_, lean_object* v_toPure_2700_, lean_object* v_inst_2701_, lean_object* v_f_2702_, lean_object* v_ty_2703_, lean_object* v_toBind_2704_, lean_object* v_y_2705_, lean_object* v_____do__lift_2706_){
_start:
{
lean_object* v___f_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_inc(v_toBind_2704_);
lean_inc(v_f_2702_);
v___f_2707_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8), 9, 8);
lean_closure_set(v___f_2707_, 0, v_____do__lift_2706_);
lean_closure_set(v___f_2707_, 1, v_i_2698_);
lean_closure_set(v___f_2707_, 2, v_offset_2699_);
lean_closure_set(v___f_2707_, 3, v_toPure_2700_);
lean_closure_set(v___f_2707_, 4, v_inst_2701_);
lean_closure_set(v___f_2707_, 5, v_f_2702_);
lean_closure_set(v___f_2707_, 6, v_ty_2703_);
lean_closure_set(v___f_2707_, 7, v_toBind_2704_);
v___x_2708_ = lean_apply_1(v_f_2702_, v_y_2705_);
v___x_2709_ = lean_apply_4(v_toBind_2704_, lean_box(0), lean_box(0), v___x_2708_, v___f_2707_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10(lean_object* v_cidx_2710_, lean_object* v_toPure_2711_, lean_object* v_____do__lift_2712_){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2713_, 0, v_____do__lift_2712_);
lean_ctor_set(v___x_2713_, 1, v_cidx_2710_);
v___x_2714_ = lean_apply_2(v_toPure_2711_, lean_box(0), v___x_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(lean_object* v_n_2715_, uint8_t v_check_2716_, uint8_t v_persistent_2717_, lean_object* v_toPure_2718_, lean_object* v_____do__lift_2719_){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v___x_2720_, 0, v_____do__lift_2719_);
lean_ctor_set(v___x_2720_, 1, v_n_2715_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*2, v_check_2716_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*2 + 1, v_persistent_2717_);
v___x_2721_ = lean_apply_2(v_toPure_2718_, lean_box(0), v___x_2720_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed(lean_object* v_n_2722_, lean_object* v_check_2723_, lean_object* v_persistent_2724_, lean_object* v_toPure_2725_, lean_object* v_____do__lift_2726_){
_start:
{
uint8_t v_check_933__boxed_2727_; uint8_t v_persistent_934__boxed_2728_; lean_object* v_res_2729_; 
v_check_933__boxed_2727_ = lean_unbox(v_check_2723_);
v_persistent_934__boxed_2728_ = lean_unbox(v_persistent_2724_);
v_res_2729_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(v_n_2722_, v_check_933__boxed_2727_, v_persistent_934__boxed_2728_, v_toPure_2725_, v_____do__lift_2726_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(lean_object* v_n_2730_, uint8_t v_check_2731_, uint8_t v_persistent_2732_, lean_object* v_objs_x3f_2733_, lean_object* v_toPure_2734_, lean_object* v_____do__lift_2735_){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = lean_alloc_ctor(8, 3, 2);
lean_ctor_set(v___x_2736_, 0, v_____do__lift_2735_);
lean_ctor_set(v___x_2736_, 1, v_n_2730_);
lean_ctor_set(v___x_2736_, 2, v_objs_x3f_2733_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*3, v_check_2731_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*3 + 1, v_persistent_2732_);
v___x_2737_ = lean_apply_2(v_toPure_2734_, lean_box(0), v___x_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed(lean_object* v_n_2738_, lean_object* v_check_2739_, lean_object* v_persistent_2740_, lean_object* v_objs_x3f_2741_, lean_object* v_toPure_2742_, lean_object* v_____do__lift_2743_){
_start:
{
uint8_t v_check_949__boxed_2744_; uint8_t v_persistent_950__boxed_2745_; lean_object* v_res_2746_; 
v_check_949__boxed_2744_ = lean_unbox(v_check_2739_);
v_persistent_950__boxed_2745_ = lean_unbox(v_persistent_2740_);
v_res_2746_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(v_n_2738_, v_check_949__boxed_2744_, v_persistent_950__boxed_2745_, v_objs_x3f_2741_, v_toPure_2742_, v_____do__lift_2743_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13(lean_object* v_toPure_2747_, lean_object* v_____do__lift_2748_){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2749_, 0, v_____do__lift_2748_);
v___x_2750_ = lean_apply_2(v_toPure_2747_, lean_box(0), v___x_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(uint8_t v_pu_2751_, lean_object* v_m_2752_, lean_object* v_inst_2753_, lean_object* v_inst_2754_, lean_object* v_f_2755_, lean_object* v_decl_2756_){
_start:
{
switch(lean_obj_tag(v_decl_2756_))
{
case 0:
{
lean_object* v_toApplicative_2757_; lean_object* v_toBind_2758_; lean_object* v_toPure_2759_; lean_object* v_decl_2760_; lean_object* v___f_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v_toApplicative_2757_ = lean_ctor_get(v_inst_2754_, 0);
v_toBind_2758_ = lean_ctor_get(v_inst_2754_, 1);
lean_inc(v_toBind_2758_);
v_toPure_2759_ = lean_ctor_get(v_toApplicative_2757_, 1);
v_decl_2760_ = lean_ctor_get(v_decl_2756_, 0);
lean_inc_ref(v_decl_2760_);
lean_dec_ref_known(v_decl_2756_, 1);
lean_inc(v_toPure_2759_);
v___f_2761_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0), 2, 1);
lean_closure_set(v___f_2761_, 0, v_toPure_2759_);
v___x_2762_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_2751_, v_inst_2753_, v_inst_2754_, v_f_2755_, v_decl_2760_);
v___x_2763_ = lean_apply_4(v_toBind_2758_, lean_box(0), lean_box(0), v___x_2762_, v___f_2761_);
return v___x_2763_;
}
case 1:
{
lean_object* v_toApplicative_2764_; lean_object* v_toBind_2765_; lean_object* v_toPure_2766_; lean_object* v_decl_2767_; lean_object* v___f_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v_toApplicative_2764_ = lean_ctor_get(v_inst_2754_, 0);
v_toBind_2765_ = lean_ctor_get(v_inst_2754_, 1);
lean_inc(v_toBind_2765_);
v_toPure_2766_ = lean_ctor_get(v_toApplicative_2764_, 1);
v_decl_2767_ = lean_ctor_get(v_decl_2756_, 0);
lean_inc_ref(v_decl_2767_);
lean_dec_ref_known(v_decl_2756_, 1);
lean_inc(v_toPure_2766_);
v___f_2768_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1), 2, 1);
lean_closure_set(v___f_2768_, 0, v_toPure_2766_);
v___x_2769_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2751_, v_inst_2753_, v_inst_2754_, v_f_2755_, v_decl_2767_);
v___x_2770_ = lean_apply_4(v_toBind_2765_, lean_box(0), lean_box(0), v___x_2769_, v___f_2768_);
return v___x_2770_;
}
case 2:
{
lean_object* v_toApplicative_2771_; lean_object* v_toBind_2772_; lean_object* v_toPure_2773_; lean_object* v_decl_2774_; lean_object* v___f_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v_toApplicative_2771_ = lean_ctor_get(v_inst_2754_, 0);
v_toBind_2772_ = lean_ctor_get(v_inst_2754_, 1);
lean_inc(v_toBind_2772_);
v_toPure_2773_ = lean_ctor_get(v_toApplicative_2771_, 1);
v_decl_2774_ = lean_ctor_get(v_decl_2756_, 0);
lean_inc_ref(v_decl_2774_);
lean_dec_ref_known(v_decl_2756_, 1);
lean_inc(v_toPure_2773_);
v___f_2775_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2), 2, 1);
lean_closure_set(v___f_2775_, 0, v_toPure_2773_);
v___x_2776_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2751_, v_inst_2753_, v_inst_2754_, v_f_2755_, v_decl_2774_);
v___x_2777_ = lean_apply_4(v_toBind_2772_, lean_box(0), lean_box(0), v___x_2776_, v___f_2775_);
return v___x_2777_;
}
case 3:
{
lean_object* v_toApplicative_2778_; lean_object* v_toBind_2779_; lean_object* v_toPure_2780_; lean_object* v_fvarId_2781_; lean_object* v_i_2782_; lean_object* v_y_2783_; lean_object* v___x_2784_; lean_object* v___f_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v_toApplicative_2778_ = lean_ctor_get(v_inst_2754_, 0);
lean_dec(v_inst_2753_);
v_toBind_2779_ = lean_ctor_get(v_inst_2754_, 1);
lean_inc_n(v_toBind_2779_, 2);
v_toPure_2780_ = lean_ctor_get(v_toApplicative_2778_, 1);
lean_inc(v_toPure_2780_);
v_fvarId_2781_ = lean_ctor_get(v_decl_2756_, 0);
lean_inc(v_fvarId_2781_);
v_i_2782_ = lean_ctor_get(v_decl_2756_, 1);
lean_inc(v_i_2782_);
v_y_2783_ = lean_ctor_get(v_decl_2756_, 2);
lean_inc(v_y_2783_);
lean_dec_ref_known(v_decl_2756_, 3);
v___x_2784_ = lean_box(v_pu_2751_);
lean_inc(v_f_2755_);
v___f_2785_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed), 8, 7);
lean_closure_set(v___f_2785_, 0, v_i_2782_);
lean_closure_set(v___f_2785_, 1, v_toPure_2780_);
lean_closure_set(v___f_2785_, 2, v___x_2784_);
lean_closure_set(v___f_2785_, 3, v_inst_2754_);
lean_closure_set(v___f_2785_, 4, v_f_2755_);
lean_closure_set(v___f_2785_, 5, v_y_2783_);
lean_closure_set(v___f_2785_, 6, v_toBind_2779_);
v___x_2786_ = lean_apply_1(v_f_2755_, v_fvarId_2781_);
v___x_2787_ = lean_apply_4(v_toBind_2779_, lean_box(0), lean_box(0), v___x_2786_, v___f_2785_);
return v___x_2787_;
}
case 4:
{
lean_object* v_toApplicative_2788_; lean_object* v_toBind_2789_; lean_object* v_toPure_2790_; lean_object* v_fvarId_2791_; lean_object* v_i_2792_; lean_object* v_y_2793_; lean_object* v___f_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v_toApplicative_2788_ = lean_ctor_get(v_inst_2754_, 0);
lean_inc_ref(v_toApplicative_2788_);
lean_dec(v_inst_2753_);
v_toBind_2789_ = lean_ctor_get(v_inst_2754_, 1);
lean_inc_n(v_toBind_2789_, 2);
lean_dec_ref(v_inst_2754_);
v_toPure_2790_ = lean_ctor_get(v_toApplicative_2788_, 1);
lean_inc(v_toPure_2790_);
lean_dec_ref(v_toApplicative_2788_);
v_fvarId_2791_ = lean_ctor_get(v_decl_2756_, 0);
lean_inc(v_fvarId_2791_);
v_i_2792_ = lean_ctor_get(v_decl_2756_, 1);
lean_inc(v_i_2792_);
v_y_2793_ = lean_ctor_get(v_decl_2756_, 2);
lean_inc(v_y_2793_);
lean_dec_ref_known(v_decl_2756_, 3);
lean_inc(v_f_2755_);
v___f_2794_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6), 6, 5);
lean_closure_set(v___f_2794_, 0, v_i_2792_);
lean_closure_set(v___f_2794_, 1, v_toPure_2790_);
lean_closure_set(v___f_2794_, 2, v_f_2755_);
lean_closure_set(v___f_2794_, 3, v_y_2793_);
lean_closure_set(v___f_2794_, 4, v_toBind_2789_);
v___x_2795_ = lean_apply_1(v_f_2755_, v_fvarId_2791_);
v___x_2796_ = lean_apply_4(v_toBind_2789_, lean_box(0), lean_box(0), v___x_2795_, v___f_2794_);
return v___x_2796_;
}
case 5:
{
lean_object* v_toApplicative_2797_; lean_object* v_toBind_2798_; lean_object* v_toPure_2799_; lean_object* v_fvarId_2800_; lean_object* v_i_2801_; lean_object* v_offset_2802_; lean_object* v_y_2803_; lean_object* v_ty_2804_; lean_object* v___f_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_toApplicative_2797_ = lean_ctor_get(v_inst_2754_, 0);
lean_dec(v_inst_2753_);
v_toBind_2798_ = lean_ctor_get(v_inst_2754_, 1);
lean_inc_n(v_toBind_2798_, 2);
v_toPure_2799_ = lean_ctor_get(v_toApplicative_2797_, 1);
lean_inc(v_toPure_2799_);
v_fvarId_2800_ = lean_ctor_get(v_decl_2756_, 0);
lean_inc(v_fvarId_2800_);
v_i_2801_ = lean_ctor_get(v_decl_2756_, 1);
lean_inc(v_i_2801_);
v_offset_2802_ = lean_ctor_get(v_decl_2756_, 2);
lean_inc(v_offset_2802_);
v_y_2803_ = lean_ctor_get(v_decl_2756_, 3);
lean_inc(v_y_2803_);
v_ty_2804_ = lean_ctor_get(v_decl_2756_, 4);
lean_inc_ref(v_ty_2804_);
lean_dec_ref_known(v_decl_2756_, 5);
lean_inc(v_f_2755_);
v___f_2805_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9), 9, 8);
lean_closure_set(v___f_2805_, 0, v_i_2801_);
lean_closure_set(v___f_2805_, 1, v_offset_2802_);
lean_closure_set(v___f_2805_, 2, v_toPure_2799_);
lean_closure_set(v___f_2805_, 3, v_inst_2754_);
lean_closure_set(v___f_2805_, 4, v_f_2755_);
lean_closure_set(v___f_2805_, 5, v_ty_2804_);
lean_closure_set(v___f_2805_, 6, v_toBind_2798_);
lean_closure_set(v___f_2805_, 7, v_y_2803_);
v___x_2806_ = lean_apply_1(v_f_2755_, v_fvarId_2800_);
v___x_2807_ = lean_apply_4(v_toBind_2798_, lean_box(0), lean_box(0), v___x_2806_, v___f_2805_);
return v___x_2807_;
}
case 6:
{
lean_object* v_toApplicative_2808_; lean_object* v_toBind_2809_; lean_object* v_toPure_2810_; lean_object* v_fvarId_2811_; lean_object* v_cidx_2812_; lean_object* v___f_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v_toApplicative_2808_ = lean_ctor_get(v_inst_2754_, 0);
lean_inc_ref(v_toApplicative_2808_);
lean_dec(v_inst_2753_);
v_toBind_2809_ = lean_ctor_get(v_inst_2754_, 1);
lean_inc(v_toBind_2809_);
lean_dec_ref(v_inst_2754_);
v_toPure_2810_ = lean_ctor_get(v_toApplicative_2808_, 1);
lean_inc(v_toPure_2810_);
lean_dec_ref(v_toApplicative_2808_);
v_fvarId_2811_ = lean_ctor_get(v_decl_2756_, 0);
lean_inc(v_fvarId_2811_);
v_cidx_2812_ = lean_ctor_get(v_decl_2756_, 1);
lean_inc(v_cidx_2812_);
lean_dec_ref_known(v_decl_2756_, 2);
v___f_2813_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10), 3, 2);
lean_closure_set(v___f_2813_, 0, v_cidx_2812_);
lean_closure_set(v___f_2813_, 1, v_toPure_2810_);
v___x_2814_ = lean_apply_1(v_f_2755_, v_fvarId_2811_);
v___x_2815_ = lean_apply_4(v_toBind_2809_, lean_box(0), lean_box(0), v___x_2814_, v___f_2813_);
return v___x_2815_;
}
case 7:
{
lean_object* v_toApplicative_2816_; lean_object* v_toBind_2817_; lean_object* v_toPure_2818_; lean_object* v_fvarId_2819_; lean_object* v_n_2820_; uint8_t v_check_2821_; uint8_t v_persistent_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___f_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_toApplicative_2816_ = lean_ctor_get(v_inst_2754_, 0);
lean_inc_ref(v_toApplicative_2816_);
lean_dec(v_inst_2753_);
v_toBind_2817_ = lean_ctor_get(v_inst_2754_, 1);
lean_inc(v_toBind_2817_);
lean_dec_ref(v_inst_2754_);
v_toPure_2818_ = lean_ctor_get(v_toApplicative_2816_, 1);
lean_inc(v_toPure_2818_);
lean_dec_ref(v_toApplicative_2816_);
v_fvarId_2819_ = lean_ctor_get(v_decl_2756_, 0);
lean_inc(v_fvarId_2819_);
v_n_2820_ = lean_ctor_get(v_decl_2756_, 1);
lean_inc(v_n_2820_);
v_check_2821_ = lean_ctor_get_uint8(v_decl_2756_, sizeof(void*)*2);
v_persistent_2822_ = lean_ctor_get_uint8(v_decl_2756_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_decl_2756_, 2);
v___x_2823_ = lean_box(v_check_2821_);
v___x_2824_ = lean_box(v_persistent_2822_);
v___f_2825_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed), 5, 4);
lean_closure_set(v___f_2825_, 0, v_n_2820_);
lean_closure_set(v___f_2825_, 1, v___x_2823_);
lean_closure_set(v___f_2825_, 2, v___x_2824_);
lean_closure_set(v___f_2825_, 3, v_toPure_2818_);
v___x_2826_ = lean_apply_1(v_f_2755_, v_fvarId_2819_);
v___x_2827_ = lean_apply_4(v_toBind_2817_, lean_box(0), lean_box(0), v___x_2826_, v___f_2825_);
return v___x_2827_;
}
case 8:
{
lean_object* v_toApplicative_2828_; lean_object* v_toBind_2829_; lean_object* v_toPure_2830_; lean_object* v_fvarId_2831_; lean_object* v_n_2832_; uint8_t v_check_2833_; uint8_t v_persistent_2834_; lean_object* v_objs_x3f_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___f_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v_toApplicative_2828_ = lean_ctor_get(v_inst_2754_, 0);
lean_inc_ref(v_toApplicative_2828_);
lean_dec(v_inst_2753_);
v_toBind_2829_ = lean_ctor_get(v_inst_2754_, 1);
lean_inc(v_toBind_2829_);
lean_dec_ref(v_inst_2754_);
v_toPure_2830_ = lean_ctor_get(v_toApplicative_2828_, 1);
lean_inc(v_toPure_2830_);
lean_dec_ref(v_toApplicative_2828_);
v_fvarId_2831_ = lean_ctor_get(v_decl_2756_, 0);
lean_inc(v_fvarId_2831_);
v_n_2832_ = lean_ctor_get(v_decl_2756_, 1);
lean_inc(v_n_2832_);
v_check_2833_ = lean_ctor_get_uint8(v_decl_2756_, sizeof(void*)*3);
v_persistent_2834_ = lean_ctor_get_uint8(v_decl_2756_, sizeof(void*)*3 + 1);
v_objs_x3f_2835_ = lean_ctor_get(v_decl_2756_, 2);
lean_inc(v_objs_x3f_2835_);
lean_dec_ref_known(v_decl_2756_, 3);
v___x_2836_ = lean_box(v_check_2833_);
v___x_2837_ = lean_box(v_persistent_2834_);
v___f_2838_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed), 6, 5);
lean_closure_set(v___f_2838_, 0, v_n_2832_);
lean_closure_set(v___f_2838_, 1, v___x_2836_);
lean_closure_set(v___f_2838_, 2, v___x_2837_);
lean_closure_set(v___f_2838_, 3, v_objs_x3f_2835_);
lean_closure_set(v___f_2838_, 4, v_toPure_2830_);
v___x_2839_ = lean_apply_1(v_f_2755_, v_fvarId_2831_);
v___x_2840_ = lean_apply_4(v_toBind_2829_, lean_box(0), lean_box(0), v___x_2839_, v___f_2838_);
return v___x_2840_;
}
default: 
{
lean_object* v_toApplicative_2841_; lean_object* v_toBind_2842_; lean_object* v_toPure_2843_; lean_object* v_fvarId_2844_; lean_object* v___f_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v_toApplicative_2841_ = lean_ctor_get(v_inst_2754_, 0);
lean_inc_ref(v_toApplicative_2841_);
lean_dec(v_inst_2753_);
v_toBind_2842_ = lean_ctor_get(v_inst_2754_, 1);
lean_inc(v_toBind_2842_);
lean_dec_ref(v_inst_2754_);
v_toPure_2843_ = lean_ctor_get(v_toApplicative_2841_, 1);
lean_inc(v_toPure_2843_);
lean_dec_ref(v_toApplicative_2841_);
v_fvarId_2844_ = lean_ctor_get(v_decl_2756_, 0);
lean_inc(v_fvarId_2844_);
lean_dec_ref_known(v_decl_2756_, 1);
v___f_2845_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13), 2, 1);
lean_closure_set(v___f_2845_, 0, v_toPure_2843_);
v___x_2846_ = lean_apply_1(v_f_2755_, v_fvarId_2844_);
v___x_2847_ = lean_apply_4(v_toBind_2842_, lean_box(0), lean_box(0), v___x_2846_, v___f_2845_);
return v___x_2847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed(lean_object* v_pu_2848_, lean_object* v_m_2849_, lean_object* v_inst_2850_, lean_object* v_inst_2851_, lean_object* v_f_2852_, lean_object* v_decl_2853_){
_start:
{
uint8_t v_pu_boxed_2854_; lean_object* v_res_2855_; 
v_pu_boxed_2854_ = lean_unbox(v_pu_2848_);
v_res_2855_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(v_pu_boxed_2854_, v_m_2849_, v_inst_2850_, v_inst_2851_, v_f_2852_, v_decl_2853_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15(lean_object* v_inst_2856_, lean_object* v_f_2857_, lean_object* v_y_2858_, lean_object* v_____r_2859_){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2856_, v_f_2857_, v_y_2858_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16(lean_object* v_f_2861_, lean_object* v_y_2862_, lean_object* v_____r_2863_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = lean_apply_1(v_f_2861_, v_y_2862_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17(lean_object* v_inst_2865_, lean_object* v_f_2866_, lean_object* v_ty_2867_, lean_object* v_____r_2868_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2865_, v_f_2866_, v_ty_2867_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18(lean_object* v_f_2870_, lean_object* v_y_2871_, lean_object* v_toBind_2872_, lean_object* v___f_2873_, lean_object* v_____r_2874_){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2875_ = lean_apply_1(v_f_2870_, v_y_2871_);
v___x_2876_ = lean_apply_4(v_toBind_2872_, lean_box(0), lean_box(0), v___x_2875_, v___f_2873_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__19(lean_object* v_m_2877_, lean_object* v_inst_2878_, lean_object* v_f_2879_, lean_object* v_decl_2880_){
_start:
{
switch(lean_obj_tag(v_decl_2880_))
{
case 0:
{
lean_object* v_decl_2881_; lean_object* v___x_2882_; 
v_decl_2881_ = lean_ctor_get(v_decl_2880_, 0);
lean_inc_ref(v_decl_2881_);
lean_dec_ref_known(v_decl_2880_, 1);
v___x_2882_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_2878_, v_f_2879_, v_decl_2881_);
return v___x_2882_;
}
case 1:
{
lean_object* v_decl_2883_; lean_object* v___x_2884_; 
v_decl_2883_ = lean_ctor_get(v_decl_2880_, 0);
lean_inc_ref(v_decl_2883_);
lean_dec_ref_known(v_decl_2880_, 1);
v___x_2884_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2878_, v_f_2879_, v_decl_2883_);
return v___x_2884_;
}
case 2:
{
lean_object* v_decl_2885_; lean_object* v___x_2886_; 
v_decl_2885_ = lean_ctor_get(v_decl_2880_, 0);
lean_inc_ref(v_decl_2885_);
lean_dec_ref_known(v_decl_2880_, 1);
v___x_2886_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2878_, v_f_2879_, v_decl_2885_);
return v___x_2886_;
}
case 3:
{
lean_object* v_toBind_2887_; lean_object* v_fvarId_2888_; lean_object* v_y_2889_; lean_object* v___f_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_toBind_2887_ = lean_ctor_get(v_inst_2878_, 1);
lean_inc(v_toBind_2887_);
v_fvarId_2888_ = lean_ctor_get(v_decl_2880_, 0);
lean_inc(v_fvarId_2888_);
v_y_2889_ = lean_ctor_get(v_decl_2880_, 2);
lean_inc(v_y_2889_);
lean_dec_ref_known(v_decl_2880_, 3);
lean_inc(v_f_2879_);
v___f_2890_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15), 4, 3);
lean_closure_set(v___f_2890_, 0, v_inst_2878_);
lean_closure_set(v___f_2890_, 1, v_f_2879_);
lean_closure_set(v___f_2890_, 2, v_y_2889_);
v___x_2891_ = lean_apply_1(v_f_2879_, v_fvarId_2888_);
v___x_2892_ = lean_apply_4(v_toBind_2887_, lean_box(0), lean_box(0), v___x_2891_, v___f_2890_);
return v___x_2892_;
}
case 4:
{
lean_object* v_toBind_2893_; lean_object* v_fvarId_2894_; lean_object* v_y_2895_; lean_object* v___f_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v_toBind_2893_ = lean_ctor_get(v_inst_2878_, 1);
lean_inc(v_toBind_2893_);
lean_dec_ref(v_inst_2878_);
v_fvarId_2894_ = lean_ctor_get(v_decl_2880_, 0);
lean_inc(v_fvarId_2894_);
v_y_2895_ = lean_ctor_get(v_decl_2880_, 2);
lean_inc(v_y_2895_);
lean_dec_ref_known(v_decl_2880_, 3);
lean_inc(v_f_2879_);
v___f_2896_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16), 3, 2);
lean_closure_set(v___f_2896_, 0, v_f_2879_);
lean_closure_set(v___f_2896_, 1, v_y_2895_);
v___x_2897_ = lean_apply_1(v_f_2879_, v_fvarId_2894_);
v___x_2898_ = lean_apply_4(v_toBind_2893_, lean_box(0), lean_box(0), v___x_2897_, v___f_2896_);
return v___x_2898_;
}
case 5:
{
lean_object* v_toBind_2899_; lean_object* v_fvarId_2900_; lean_object* v_y_2901_; lean_object* v_ty_2902_; lean_object* v___f_2903_; lean_object* v___f_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v_toBind_2899_ = lean_ctor_get(v_inst_2878_, 1);
lean_inc_n(v_toBind_2899_, 2);
v_fvarId_2900_ = lean_ctor_get(v_decl_2880_, 0);
lean_inc(v_fvarId_2900_);
v_y_2901_ = lean_ctor_get(v_decl_2880_, 3);
lean_inc(v_y_2901_);
v_ty_2902_ = lean_ctor_get(v_decl_2880_, 4);
lean_inc_ref(v_ty_2902_);
lean_dec_ref_known(v_decl_2880_, 5);
lean_inc_n(v_f_2879_, 2);
v___f_2903_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17), 4, 3);
lean_closure_set(v___f_2903_, 0, v_inst_2878_);
lean_closure_set(v___f_2903_, 1, v_f_2879_);
lean_closure_set(v___f_2903_, 2, v_ty_2902_);
v___f_2904_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18), 5, 4);
lean_closure_set(v___f_2904_, 0, v_f_2879_);
lean_closure_set(v___f_2904_, 1, v_y_2901_);
lean_closure_set(v___f_2904_, 2, v_toBind_2899_);
lean_closure_set(v___f_2904_, 3, v___f_2903_);
v___x_2905_ = lean_apply_1(v_f_2879_, v_fvarId_2900_);
v___x_2906_ = lean_apply_4(v_toBind_2899_, lean_box(0), lean_box(0), v___x_2905_, v___f_2904_);
return v___x_2906_;
}
default: 
{
lean_object* v_fvarId_2907_; lean_object* v___x_2908_; 
lean_dec_ref(v_inst_2878_);
v_fvarId_2907_ = lean_ctor_get(v_decl_2880_, 0);
lean_inc(v_fvarId_2907_);
lean_dec_ref(v_decl_2880_);
v___x_2908_ = lean_apply_1(v_f_2879_, v_fvarId_2907_);
return v___x_2908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(uint8_t v_pu_2910_){
_start:
{
lean_object* v___x_2911_; lean_object* v___f_2912_; lean_object* v___f_2913_; lean_object* v___x_2914_; 
v___x_2911_ = lean_box(v_pu_2910_);
v___f_2912_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed), 6, 1);
lean_closure_set(v___f_2912_, 0, v___x_2911_);
v___f_2913_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0));
v___x_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___f_2912_);
lean_ctor_set(v___x_2914_, 1, v___f_2913_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___boxed(lean_object* v_pu_2915_){
_start:
{
uint8_t v_pu_boxed_2916_; lean_object* v_res_2917_; 
v_pu_boxed_2916_ = lean_unbox(v_pu_2915_);
v_res_2917_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(v_pu_boxed_2916_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0(lean_object* v_ctorName_2918_, lean_object* v_params_2919_, lean_object* v_toPure_2920_, lean_object* v_____do__lift_2921_){
_start:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2922_, 0, v_ctorName_2918_);
lean_ctor_set(v___x_2922_, 1, v_params_2919_);
lean_ctor_set(v___x_2922_, 2, v_____do__lift_2921_);
v___x_2923_ = lean_apply_2(v_toPure_2920_, lean_box(0), v___x_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(lean_object* v_ctorName_2924_, lean_object* v_toPure_2925_, uint8_t v_pu_2926_, lean_object* v_inst_2927_, lean_object* v_inst_2928_, lean_object* v_f_2929_, lean_object* v_code_2930_, lean_object* v_toBind_2931_, lean_object* v_params_2932_){
_start:
{
lean_object* v___f_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___f_2933_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0), 4, 3);
lean_closure_set(v___f_2933_, 0, v_ctorName_2924_);
lean_closure_set(v___f_2933_, 1, v_params_2932_);
lean_closure_set(v___f_2933_, 2, v_toPure_2925_);
v___x_2934_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2926_, v_inst_2927_, v_inst_2928_, v_f_2929_, v_code_2930_);
v___x_2935_ = lean_apply_4(v_toBind_2931_, lean_box(0), lean_box(0), v___x_2934_, v___f_2933_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed(lean_object* v_ctorName_2936_, lean_object* v_toPure_2937_, lean_object* v_pu_2938_, lean_object* v_inst_2939_, lean_object* v_inst_2940_, lean_object* v_f_2941_, lean_object* v_code_2942_, lean_object* v_toBind_2943_, lean_object* v_params_2944_){
_start:
{
uint8_t v_pu_boxed_2945_; lean_object* v_res_2946_; 
v_pu_boxed_2945_ = lean_unbox(v_pu_2938_);
v_res_2946_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(v_ctorName_2936_, v_toPure_2937_, v_pu_boxed_2945_, v_inst_2939_, v_inst_2940_, v_f_2941_, v_code_2942_, v_toBind_2943_, v_params_2944_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2(lean_object* v_info_2947_, lean_object* v_toPure_2948_, lean_object* v_____do__lift_2949_){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2950_, 0, v_info_2947_);
lean_ctor_set(v___x_2950_, 1, v_____do__lift_2949_);
v___x_2951_ = lean_apply_2(v_toPure_2948_, lean_box(0), v___x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3(lean_object* v_toPure_2952_, lean_object* v_____do__lift_2953_){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2954_, 0, v_____do__lift_2953_);
v___x_2955_ = lean_apply_2(v_toPure_2952_, lean_box(0), v___x_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(uint8_t v_pu_2956_, lean_object* v_m_2957_, lean_object* v_inst_2958_, lean_object* v_inst_2959_, lean_object* v_f_2960_, lean_object* v_alt_2961_){
_start:
{
switch(lean_obj_tag(v_alt_2961_))
{
case 0:
{
lean_object* v_toApplicative_2962_; lean_object* v_toBind_2963_; lean_object* v_toPure_2964_; lean_object* v_ctorName_2965_; lean_object* v_params_2966_; lean_object* v_code_2967_; lean_object* v___x_2968_; lean_object* v___f_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; size_t v_sz_2972_; size_t v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v_toApplicative_2962_ = lean_ctor_get(v_inst_2959_, 0);
v_toBind_2963_ = lean_ctor_get(v_inst_2959_, 1);
lean_inc_n(v_toBind_2963_, 2);
v_toPure_2964_ = lean_ctor_get(v_toApplicative_2962_, 1);
v_ctorName_2965_ = lean_ctor_get(v_alt_2961_, 0);
lean_inc(v_ctorName_2965_);
v_params_2966_ = lean_ctor_get(v_alt_2961_, 1);
lean_inc_ref(v_params_2966_);
v_code_2967_ = lean_ctor_get(v_alt_2961_, 2);
lean_inc_ref(v_code_2967_);
lean_dec_ref_known(v_alt_2961_, 3);
v___x_2968_ = lean_box(v_pu_2956_);
lean_inc(v_f_2960_);
lean_inc_ref_n(v_inst_2959_, 2);
lean_inc(v_inst_2958_);
lean_inc(v_toPure_2964_);
v___f_2969_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2969_, 0, v_ctorName_2965_);
lean_closure_set(v___f_2969_, 1, v_toPure_2964_);
lean_closure_set(v___f_2969_, 2, v___x_2968_);
lean_closure_set(v___f_2969_, 3, v_inst_2958_);
lean_closure_set(v___f_2969_, 4, v_inst_2959_);
lean_closure_set(v___f_2969_, 5, v_f_2960_);
lean_closure_set(v___f_2969_, 6, v_code_2967_);
lean_closure_set(v___f_2969_, 7, v_toBind_2963_);
v___x_2970_ = lean_box(v_pu_2956_);
v___x_2971_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2971_, 0, lean_box(0));
lean_closure_set(v___x_2971_, 1, v___x_2970_);
lean_closure_set(v___x_2971_, 2, v_inst_2958_);
lean_closure_set(v___x_2971_, 3, v_inst_2959_);
lean_closure_set(v___x_2971_, 4, v_f_2960_);
v_sz_2972_ = lean_array_size(v_params_2966_);
v___x_2973_ = ((size_t)0ULL);
v___x_2974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2959_, v___x_2971_, v_sz_2972_, v___x_2973_, v_params_2966_);
v___x_2975_ = lean_apply_4(v_toBind_2963_, lean_box(0), lean_box(0), v___x_2974_, v___f_2969_);
return v___x_2975_;
}
case 1:
{
lean_object* v_toApplicative_2976_; lean_object* v_toBind_2977_; lean_object* v_toPure_2978_; lean_object* v_info_2979_; lean_object* v_code_2980_; lean_object* v___f_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v_toApplicative_2976_ = lean_ctor_get(v_inst_2959_, 0);
v_toBind_2977_ = lean_ctor_get(v_inst_2959_, 1);
lean_inc(v_toBind_2977_);
v_toPure_2978_ = lean_ctor_get(v_toApplicative_2976_, 1);
v_info_2979_ = lean_ctor_get(v_alt_2961_, 0);
lean_inc_ref(v_info_2979_);
v_code_2980_ = lean_ctor_get(v_alt_2961_, 1);
lean_inc_ref(v_code_2980_);
lean_dec_ref_known(v_alt_2961_, 2);
lean_inc(v_toPure_2978_);
v___f_2981_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2), 3, 2);
lean_closure_set(v___f_2981_, 0, v_info_2979_);
lean_closure_set(v___f_2981_, 1, v_toPure_2978_);
v___x_2982_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2956_, v_inst_2958_, v_inst_2959_, v_f_2960_, v_code_2980_);
v___x_2983_ = lean_apply_4(v_toBind_2977_, lean_box(0), lean_box(0), v___x_2982_, v___f_2981_);
return v___x_2983_;
}
default: 
{
lean_object* v_toApplicative_2984_; lean_object* v_toBind_2985_; lean_object* v_toPure_2986_; lean_object* v_code_2987_; lean_object* v___f_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v_toApplicative_2984_ = lean_ctor_get(v_inst_2959_, 0);
v_toBind_2985_ = lean_ctor_get(v_inst_2959_, 1);
lean_inc(v_toBind_2985_);
v_toPure_2986_ = lean_ctor_get(v_toApplicative_2984_, 1);
v_code_2987_ = lean_ctor_get(v_alt_2961_, 0);
lean_inc_ref(v_code_2987_);
lean_dec_ref_known(v_alt_2961_, 1);
lean_inc(v_toPure_2986_);
v___f_2988_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3), 2, 1);
lean_closure_set(v___f_2988_, 0, v_toPure_2986_);
v___x_2989_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2956_, v_inst_2958_, v_inst_2959_, v_f_2960_, v_code_2987_);
v___x_2990_ = lean_apply_4(v_toBind_2985_, lean_box(0), lean_box(0), v___x_2989_, v___f_2988_);
return v___x_2990_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed(lean_object* v_pu_2991_, lean_object* v_m_2992_, lean_object* v_inst_2993_, lean_object* v_inst_2994_, lean_object* v_f_2995_, lean_object* v_alt_2996_){
_start:
{
uint8_t v_pu_boxed_2997_; lean_object* v_res_2998_; 
v_pu_boxed_2997_ = lean_unbox(v_pu_2991_);
v_res_2998_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(v_pu_boxed_2997_, v_m_2992_, v_inst_2993_, v_inst_2994_, v_f_2995_, v_alt_2996_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5(lean_object* v_inst_2999_, lean_object* v_f_3000_, lean_object* v_code_3001_, lean_object* v_____r_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2999_, v_f_3000_, v_code_3001_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__7(lean_object* v_m_3004_, lean_object* v_inst_3005_, lean_object* v_f_3006_, lean_object* v_alt_3007_){
_start:
{
switch(lean_obj_tag(v_alt_3007_))
{
case 0:
{
lean_object* v_toApplicative_3008_; lean_object* v_toBind_3009_; lean_object* v_params_3010_; lean_object* v_code_3011_; lean_object* v_toPure_3012_; lean_object* v___f_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; uint8_t v___x_3017_; 
v_toApplicative_3008_ = lean_ctor_get(v_inst_3005_, 0);
v_toBind_3009_ = lean_ctor_get(v_inst_3005_, 1);
lean_inc(v_toBind_3009_);
v_params_3010_ = lean_ctor_get(v_alt_3007_, 1);
lean_inc_ref(v_params_3010_);
v_code_3011_ = lean_ctor_get(v_alt_3007_, 2);
lean_inc_ref(v_code_3011_);
lean_dec_ref_known(v_alt_3007_, 3);
v_toPure_3012_ = lean_ctor_get(v_toApplicative_3008_, 1);
lean_inc(v_f_3006_);
lean_inc_ref(v_inst_3005_);
v___f_3013_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5), 4, 3);
lean_closure_set(v___f_3013_, 0, v_inst_3005_);
lean_closure_set(v___f_3013_, 1, v_f_3006_);
lean_closure_set(v___f_3013_, 2, v_code_3011_);
v___x_3014_ = lean_unsigned_to_nat(0u);
v___x_3015_ = lean_array_get_size(v_params_3010_);
v___x_3016_ = lean_box(0);
v___x_3017_ = lean_nat_dec_lt(v___x_3014_, v___x_3015_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
lean_inc(v_toPure_3012_);
lean_dec_ref(v_params_3010_);
lean_dec(v_f_3006_);
lean_dec_ref(v_inst_3005_);
v___x_3018_ = lean_apply_2(v_toPure_3012_, lean_box(0), v___x_3016_);
v___x_3019_ = lean_apply_4(v_toBind_3009_, lean_box(0), lean_box(0), v___x_3018_, v___f_3013_);
return v___x_3019_;
}
else
{
lean_object* v___f_3020_; uint8_t v___x_3021_; 
lean_inc_ref(v_inst_3005_);
v___f_3020_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_3020_, 0, v_inst_3005_);
lean_closure_set(v___f_3020_, 1, v_f_3006_);
v___x_3021_ = lean_nat_dec_le(v___x_3015_, v___x_3015_);
if (v___x_3021_ == 0)
{
if (v___x_3017_ == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
lean_inc(v_toPure_3012_);
lean_dec_ref(v___f_3020_);
lean_dec_ref(v_params_3010_);
lean_dec_ref(v_inst_3005_);
v___x_3022_ = lean_apply_2(v_toPure_3012_, lean_box(0), v___x_3016_);
v___x_3023_ = lean_apply_4(v_toBind_3009_, lean_box(0), lean_box(0), v___x_3022_, v___f_3013_);
return v___x_3023_;
}
else
{
size_t v___x_3024_; size_t v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3024_ = ((size_t)0ULL);
v___x_3025_ = lean_usize_of_nat(v___x_3015_);
v___x_3026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3005_, v___f_3020_, v_params_3010_, v___x_3024_, v___x_3025_, v___x_3016_);
v___x_3027_ = lean_apply_4(v_toBind_3009_, lean_box(0), lean_box(0), v___x_3026_, v___f_3013_);
return v___x_3027_;
}
}
else
{
size_t v___x_3028_; size_t v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3028_ = ((size_t)0ULL);
v___x_3029_ = lean_usize_of_nat(v___x_3015_);
v___x_3030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3005_, v___f_3020_, v_params_3010_, v___x_3028_, v___x_3029_, v___x_3016_);
v___x_3031_ = lean_apply_4(v_toBind_3009_, lean_box(0), lean_box(0), v___x_3030_, v___f_3013_);
return v___x_3031_;
}
}
}
case 1:
{
lean_object* v_code_3032_; lean_object* v___x_3033_; 
v_code_3032_ = lean_ctor_get(v_alt_3007_, 1);
lean_inc_ref(v_code_3032_);
lean_dec_ref_known(v_alt_3007_, 2);
v___x_3033_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_3005_, v_f_3006_, v_code_3032_);
return v___x_3033_;
}
default: 
{
lean_object* v_code_3034_; lean_object* v___x_3035_; 
v_code_3034_ = lean_ctor_get(v_alt_3007_, 0);
lean_inc_ref(v_code_3034_);
lean_dec_ref_known(v_alt_3007_, 1);
v___x_3035_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_3005_, v_f_3006_, v_code_3034_);
return v___x_3035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt(uint8_t v_pu_3037_){
_start:
{
lean_object* v___x_3038_; lean_object* v___f_3039_; lean_object* v___f_3040_; lean_object* v___x_3041_; 
v___x_3038_ = lean_box(v_pu_3037_);
v___f_3039_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed), 6, 1);
lean_closure_set(v___f_3039_, 0, v___x_3038_);
v___f_3040_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0));
v___x_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___f_3039_);
lean_ctor_set(v___x_3041_, 1, v___f_3040_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___boxed(lean_object* v_pu_3042_){
_start:
{
uint8_t v_pu_boxed_3043_; lean_object* v_res_3044_; 
v_pu_boxed_3043_ = lean_unbox(v_pu_3042_);
v_res_3044_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt(v_pu_boxed_3043_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(lean_object* v_toPure_3047_, lean_object* v_____do__lift_3048_){
_start:
{
if (lean_obj_tag(v_____do__lift_3048_) == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3049_ = lean_box(0);
v___x_3050_ = lean_apply_2(v_toPure_3047_, lean_box(0), v___x_3049_);
return v___x_3050_;
}
else
{
lean_object* v_val_3051_; uint8_t v___x_3052_; 
v_val_3051_ = lean_ctor_get(v_____do__lift_3048_, 0);
v___x_3052_ = lean_unbox(v_val_3051_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0));
v___x_3054_ = lean_apply_2(v_toPure_3047_, lean_box(0), v___x_3053_);
return v___x_3054_;
}
else
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = lean_box(0);
v___x_3056_ = lean_apply_2(v_toPure_3047_, lean_box(0), v___x_3055_);
return v___x_3056_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed(lean_object* v_toPure_3057_, lean_object* v_____do__lift_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(v_toPure_3057_, v_____do__lift_3058_);
lean_dec(v_____do__lift_3058_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(lean_object* v_toPure_3060_, uint8_t v_____do__lift_3061_){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3062_ = lean_box(v_____do__lift_3061_);
v___x_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
v___x_3064_ = lean_apply_2(v_toPure_3060_, lean_box(0), v___x_3063_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed(lean_object* v_toPure_3065_, lean_object* v_____do__lift_3066_){
_start:
{
uint8_t v_____do__lift_371__boxed_3067_; lean_object* v_res_3068_; 
v_____do__lift_371__boxed_3067_ = lean_unbox(v_____do__lift_3066_);
v_res_3068_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(v_toPure_3065_, v_____do__lift_371__boxed_3067_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(lean_object* v_inst_3069_, lean_object* v_f_3070_, lean_object* v_fvar_3071_){
_start:
{
lean_object* v_toApplicative_3072_; lean_object* v_toBind_3073_; lean_object* v_toPure_3074_; lean_object* v___x_3075_; lean_object* v___f_3076_; lean_object* v___f_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v_toApplicative_3072_ = lean_ctor_get(v_inst_3069_, 0);
lean_inc_ref(v_toApplicative_3072_);
v_toBind_3073_ = lean_ctor_get(v_inst_3069_, 1);
lean_inc_n(v_toBind_3073_, 2);
lean_dec_ref(v_inst_3069_);
v_toPure_3074_ = lean_ctor_get(v_toApplicative_3072_, 1);
lean_inc_n(v_toPure_3074_, 2);
lean_dec_ref(v_toApplicative_3072_);
v___x_3075_ = lean_apply_1(v_f_3070_, v_fvar_3071_);
v___f_3076_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3076_, 0, v_toPure_3074_);
v___f_3077_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3077_, 0, v_toPure_3074_);
v___x_3078_ = lean_apply_4(v_toBind_3073_, lean_box(0), lean_box(0), v___x_3075_, v___f_3077_);
v___x_3079_ = lean_apply_4(v_toBind_3073_, lean_box(0), lean_box(0), v___x_3078_, v___f_3076_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go(lean_object* v_m_3080_, lean_object* v_inst_3081_, lean_object* v_f_3082_, lean_object* v_fvar_3083_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(v_inst_3081_, v_f_3082_, v_fvar_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(lean_object* v_toPure_3085_, lean_object* v_____do__lift_3086_){
_start:
{
if (lean_obj_tag(v_____do__lift_3086_) == 0)
{
uint8_t v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3087_ = 1;
v___x_3088_ = lean_box(v___x_3087_);
v___x_3089_ = lean_apply_2(v_toPure_3085_, lean_box(0), v___x_3088_);
return v___x_3089_;
}
else
{
uint8_t v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = 0;
v___x_3091_ = lean_box(v___x_3090_);
v___x_3092_ = lean_apply_2(v_toPure_3085_, lean_box(0), v___x_3091_);
return v___x_3092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed(lean_object* v_toPure_3093_, lean_object* v_____do__lift_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(v_toPure_3093_, v_____do__lift_3094_);
lean_dec(v_____do__lift_3094_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg(lean_object* v_inst_3096_, lean_object* v_inst_3097_, lean_object* v_f_3098_, lean_object* v_x_3099_){
_start:
{
lean_object* v_toApplicative_3100_; lean_object* v_toBind_3101_; lean_object* v_forFVarM_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3123_; 
v_toApplicative_3100_ = lean_ctor_get(v_inst_3096_, 0);
v_toBind_3101_ = lean_ctor_get(v_inst_3096_, 1);
lean_inc(v_toBind_3101_);
v_forFVarM_3102_ = lean_ctor_get(v_inst_3097_, 1);
v_isSharedCheck_3123_ = !lean_is_exclusive(v_inst_3097_);
if (v_isSharedCheck_3123_ == 0)
{
lean_object* v_unused_3124_; 
v_unused_3124_ = lean_ctor_get(v_inst_3097_, 0);
lean_dec(v_unused_3124_);
v___x_3104_ = v_inst_3097_;
v_isShared_3105_ = v_isSharedCheck_3123_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_forFVarM_3102_);
lean_dec(v_inst_3097_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3123_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___f_3106_; lean_object* v___f_3107_; lean_object* v___f_3108_; lean_object* v___f_3109_; lean_object* v___f_3110_; lean_object* v___x_3112_; 
lean_inc_ref_n(v_inst_3096_, 5);
v___f_3106_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3106_, 0, v_inst_3096_);
v___f_3107_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3107_, 0, v_inst_3096_);
v___f_3108_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3108_, 0, v_inst_3096_);
v___f_3109_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3109_, 0, v_inst_3096_);
v___f_3110_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3110_, 0, v_inst_3096_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 1, v___f_3107_);
lean_ctor_set(v___x_3104_, 0, v___f_3106_);
v___x_3112_ = v___x_3104_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___f_3106_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v___f_3107_);
v___x_3112_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v_toPure_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___f_3120_; lean_object* v___x_3121_; 
lean_inc_ref_n(v_inst_3096_, 2);
v___x_3113_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3113_, 0, lean_box(0));
lean_closure_set(v___x_3113_, 1, v_inst_3096_);
v___x_3114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3112_);
lean_ctor_set(v___x_3114_, 1, v___x_3113_);
lean_ctor_set(v___x_3114_, 2, v___f_3108_);
lean_ctor_set(v___x_3114_, 3, v___f_3109_);
lean_ctor_set(v___x_3114_, 4, v___f_3110_);
v___x_3115_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3115_, 0, lean_box(0));
lean_closure_set(v___x_3115_, 1, v_inst_3096_);
v___x_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3114_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
v_toPure_3117_ = lean_ctor_get(v_toApplicative_3100_, 1);
lean_inc(v_toPure_3117_);
v___x_3118_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go), 4, 3);
lean_closure_set(v___x_3118_, 0, lean_box(0));
lean_closure_set(v___x_3118_, 1, v_inst_3096_);
lean_closure_set(v___x_3118_, 2, v_f_3098_);
v___x_3119_ = lean_apply_4(v_forFVarM_3102_, lean_box(0), v___x_3116_, v___x_3118_, v_x_3099_);
v___f_3120_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3120_, 0, v_toPure_3117_);
v___x_3121_ = lean_apply_4(v_toBind_3101_, lean_box(0), lean_box(0), v___x_3119_, v___f_3120_);
return v___x_3121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM(lean_object* v_m_3125_, lean_object* v_00_u03b1_3126_, lean_object* v_inst_3127_, lean_object* v_inst_3128_, lean_object* v_f_3129_, lean_object* v_x_3130_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Lean_Compiler_LCNF_anyFVarM___redArg(v_inst_3127_, v_inst_3128_, v_f_3129_, v_x_3130_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(lean_object* v_toPure_3132_, lean_object* v_____do__lift_3133_){
_start:
{
if (lean_obj_tag(v_____do__lift_3133_) == 0)
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = lean_box(0);
v___x_3135_ = lean_apply_2(v_toPure_3132_, lean_box(0), v___x_3134_);
return v___x_3135_;
}
else
{
lean_object* v_val_3136_; uint8_t v___x_3137_; 
v_val_3136_ = lean_ctor_get(v_____do__lift_3133_, 0);
v___x_3137_ = lean_unbox(v_val_3136_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3138_ = lean_box(0);
v___x_3139_ = lean_apply_2(v_toPure_3132_, lean_box(0), v___x_3138_);
return v___x_3139_;
}
else
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0));
v___x_3141_ = lean_apply_2(v_toPure_3132_, lean_box(0), v___x_3140_);
return v___x_3141_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed(lean_object* v_toPure_3142_, lean_object* v_____do__lift_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(v_toPure_3142_, v_____do__lift_3143_);
lean_dec(v_____do__lift_3143_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(lean_object* v_inst_3145_, lean_object* v_f_3146_, lean_object* v_fvar_3147_){
_start:
{
lean_object* v_toApplicative_3148_; lean_object* v_toBind_3149_; lean_object* v_toPure_3150_; lean_object* v___x_3151_; lean_object* v___f_3152_; lean_object* v___f_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v_toApplicative_3148_ = lean_ctor_get(v_inst_3145_, 0);
lean_inc_ref(v_toApplicative_3148_);
v_toBind_3149_ = lean_ctor_get(v_inst_3145_, 1);
lean_inc_n(v_toBind_3149_, 2);
lean_dec_ref(v_inst_3145_);
v_toPure_3150_ = lean_ctor_get(v_toApplicative_3148_, 1);
lean_inc_n(v_toPure_3150_, 2);
lean_dec_ref(v_toApplicative_3148_);
v___x_3151_ = lean_apply_1(v_f_3146_, v_fvar_3147_);
v___f_3152_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3152_, 0, v_toPure_3150_);
v___f_3153_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3153_, 0, v_toPure_3150_);
v___x_3154_ = lean_apply_4(v_toBind_3149_, lean_box(0), lean_box(0), v___x_3151_, v___f_3153_);
v___x_3155_ = lean_apply_4(v_toBind_3149_, lean_box(0), lean_box(0), v___x_3154_, v___f_3152_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go(lean_object* v_m_3156_, lean_object* v_inst_3157_, lean_object* v_f_3158_, lean_object* v_fvar_3159_){
_start:
{
lean_object* v___x_3160_; 
v___x_3160_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(v_inst_3157_, v_f_3158_, v_fvar_3159_);
return v___x_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(lean_object* v_toPure_3161_, lean_object* v_____do__lift_3162_){
_start:
{
if (lean_obj_tag(v_____do__lift_3162_) == 1)
{
uint8_t v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3163_ = 1;
v___x_3164_ = lean_box(v___x_3163_);
v___x_3165_ = lean_apply_2(v_toPure_3161_, lean_box(0), v___x_3164_);
return v___x_3165_;
}
else
{
uint8_t v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3166_ = 0;
v___x_3167_ = lean_box(v___x_3166_);
v___x_3168_ = lean_apply_2(v_toPure_3161_, lean_box(0), v___x_3167_);
return v___x_3168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed(lean_object* v_toPure_3169_, lean_object* v_____do__lift_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(v_toPure_3169_, v_____do__lift_3170_);
lean_dec(v_____do__lift_3170_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg(lean_object* v_inst_3172_, lean_object* v_inst_3173_, lean_object* v_f_3174_, lean_object* v_x_3175_){
_start:
{
lean_object* v_toApplicative_3176_; lean_object* v_toBind_3177_; lean_object* v_forFVarM_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3199_; 
v_toApplicative_3176_ = lean_ctor_get(v_inst_3172_, 0);
v_toBind_3177_ = lean_ctor_get(v_inst_3172_, 1);
lean_inc(v_toBind_3177_);
v_forFVarM_3178_ = lean_ctor_get(v_inst_3173_, 1);
v_isSharedCheck_3199_ = !lean_is_exclusive(v_inst_3173_);
if (v_isSharedCheck_3199_ == 0)
{
lean_object* v_unused_3200_; 
v_unused_3200_ = lean_ctor_get(v_inst_3173_, 0);
lean_dec(v_unused_3200_);
v___x_3180_ = v_inst_3173_;
v_isShared_3181_ = v_isSharedCheck_3199_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_forFVarM_3178_);
lean_dec(v_inst_3173_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3199_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___f_3182_; lean_object* v___f_3183_; lean_object* v___f_3184_; lean_object* v___f_3185_; lean_object* v___f_3186_; lean_object* v___x_3188_; 
lean_inc_ref_n(v_inst_3172_, 5);
v___f_3182_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3182_, 0, v_inst_3172_);
v___f_3183_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3183_, 0, v_inst_3172_);
v___f_3184_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3184_, 0, v_inst_3172_);
v___f_3185_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3185_, 0, v_inst_3172_);
v___f_3186_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3186_, 0, v_inst_3172_);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 1, v___f_3183_);
lean_ctor_set(v___x_3180_, 0, v___f_3182_);
v___x_3188_ = v___x_3180_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___f_3182_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v___f_3183_);
v___x_3188_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v_toPure_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___f_3196_; lean_object* v___x_3197_; 
lean_inc_ref_n(v_inst_3172_, 2);
v___x_3189_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3189_, 0, lean_box(0));
lean_closure_set(v___x_3189_, 1, v_inst_3172_);
v___x_3190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3188_);
lean_ctor_set(v___x_3190_, 1, v___x_3189_);
lean_ctor_set(v___x_3190_, 2, v___f_3184_);
lean_ctor_set(v___x_3190_, 3, v___f_3185_);
lean_ctor_set(v___x_3190_, 4, v___f_3186_);
v___x_3191_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3191_, 0, lean_box(0));
lean_closure_set(v___x_3191_, 1, v_inst_3172_);
v___x_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3190_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
v_toPure_3193_ = lean_ctor_get(v_toApplicative_3176_, 1);
lean_inc(v_toPure_3193_);
v___x_3194_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go), 4, 3);
lean_closure_set(v___x_3194_, 0, lean_box(0));
lean_closure_set(v___x_3194_, 1, v_inst_3172_);
lean_closure_set(v___x_3194_, 2, v_f_3174_);
v___x_3195_ = lean_apply_4(v_forFVarM_3178_, lean_box(0), v___x_3192_, v___x_3194_, v_x_3175_);
v___f_3196_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3196_, 0, v_toPure_3193_);
v___x_3197_ = lean_apply_4(v_toBind_3177_, lean_box(0), lean_box(0), v___x_3195_, v___f_3196_);
return v___x_3197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM(lean_object* v_m_3201_, lean_object* v_00_u03b1_3202_, lean_object* v_inst_3203_, lean_object* v_inst_3204_, lean_object* v_f_3205_, lean_object* v_x_3206_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Lean_Compiler_LCNF_allFVarM___redArg(v_inst_3203_, v_inst_3204_, v_f_3205_, v_x_3206_);
return v___x_3207_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(lean_object* v_f_3208_, lean_object* v_x_3209_){
_start:
{
lean_object* v___x_3210_; uint8_t v___x_3211_; 
v___x_3210_ = lean_apply_1(v_f_3208_, v_x_3209_);
v___x_3211_ = lean_unbox(v___x_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed(lean_object* v_f_3212_, lean_object* v_x_3213_){
_start:
{
uint8_t v_res_3214_; lean_object* v_r_3215_; 
v_res_3214_ = l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(v_f_3212_, v_x_3213_);
v_r_3215_ = lean_box(v_res_3214_);
return v_r_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg(lean_object* v_inst_3235_, lean_object* v_f_3236_, lean_object* v_x_3237_){
_start:
{
lean_object* v___f_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___f_3238_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3238_, 0, v_f_3236_);
v___x_3239_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9));
v___x_3240_ = l_Lean_Compiler_LCNF_anyFVarM___redArg(v___x_3239_, v_inst_3235_, v___f_3238_, v_x_3237_);
return v___x_3240_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar(lean_object* v_00_u03b1_3241_, lean_object* v_inst_3242_, lean_object* v_f_3243_, lean_object* v_x_3244_){
_start:
{
lean_object* v___x_3245_; uint8_t v___x_3246_; 
v___x_3245_ = l_Lean_Compiler_LCNF_anyFVar___redArg(v_inst_3242_, v_f_3243_, v_x_3244_);
v___x_3246_ = lean_unbox(v___x_3245_);
lean_dec(v___x_3245_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___boxed(lean_object* v_00_u03b1_3247_, lean_object* v_inst_3248_, lean_object* v_f_3249_, lean_object* v_x_3250_){
_start:
{
uint8_t v_res_3251_; lean_object* v_r_3252_; 
v_res_3251_ = l_Lean_Compiler_LCNF_anyFVar(v_00_u03b1_3247_, v_inst_3248_, v_f_3249_, v_x_3250_);
v_r_3252_ = lean_box(v_res_3251_);
return v_r_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___redArg(lean_object* v_inst_3253_, lean_object* v_f_3254_, lean_object* v_x_3255_){
_start:
{
lean_object* v___f_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___f_3256_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3256_, 0, v_f_3254_);
v___x_3257_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9));
v___x_3258_ = l_Lean_Compiler_LCNF_allFVarM___redArg(v___x_3257_, v_inst_3253_, v___f_3256_, v_x_3255_);
return v___x_3258_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar(lean_object* v_00_u03b1_3259_, lean_object* v_inst_3260_, lean_object* v_f_3261_, lean_object* v_x_3262_){
_start:
{
lean_object* v___x_3263_; uint8_t v___x_3264_; 
v___x_3263_ = l_Lean_Compiler_LCNF_allFVar___redArg(v_inst_3260_, v_f_3261_, v_x_3262_);
v___x_3264_ = lean_unbox(v___x_3263_);
lean_dec(v___x_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___boxed(lean_object* v_00_u03b1_3265_, lean_object* v_inst_3266_, lean_object* v_f_3267_, lean_object* v_x_3268_){
_start:
{
uint8_t v_res_3269_; lean_object* v_r_3270_; 
v_res_3269_ = l_Lean_Compiler_LCNF_allFVar(v_00_u03b1_3265_, v_inst_3266_, v_f_3267_, v_x_3268_);
v_r_3270_ = lean_box(v_res_3269_);
return v_r_3270_;
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
