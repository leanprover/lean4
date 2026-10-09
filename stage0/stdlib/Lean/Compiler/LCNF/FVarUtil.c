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
lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3(lean_object* v_binderType_38_, lean_object* v_____do__lift_39_, lean_object* v_binderName_40_, uint8_t v_binderInfo_41_, lean_object* v_toPure_42_, lean_object* v_body_43_, lean_object* v_e_44_, lean_object* v_____do__lift_45_){
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderType_38_ = stack[0].m_obj;
lean_object* v_____do__lift_39_ = stack[1].m_obj;
lean_object* v_binderName_40_ = stack[2].m_obj;
uint8_t v_binderInfo_41_ = stack[3].m_num;
lean_object* v_toPure_42_ = stack[4].m_obj;
lean_object* v_body_43_ = stack[5].m_obj;
lean_object* v_e_44_ = stack[6].m_obj;
lean_object* v_____do__lift_45_ = stack[7].m_obj;
lean_object* v_res_60_;
v_res_60_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3(v_binderType_38_, v_____do__lift_39_, v_binderName_40_, v_binderInfo_41_, v_toPure_42_, v_body_43_, v_e_44_, v_____do__lift_45_);
stack->m_obj
 = v_res_60_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3___boxed(lean_object* v_binderType_61_, lean_object* v_____do__lift_62_, lean_object* v_binderName_63_, lean_object* v_binderInfo_64_, lean_object* v_toPure_65_, lean_object* v_body_66_, lean_object* v_e_67_, lean_object* v_____do__lift_68_){
_start:
{
uint8_t v_binderInfo_675__boxed_69_; lean_object* v_res_70_; 
v_binderInfo_675__boxed_69_ = lean_unbox(v_binderInfo_64_);
v_res_70_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3(v_binderType_61_, v_____do__lift_62_, v_binderName_63_, v_binderInfo_675__boxed_69_, v_toPure_65_, v_body_66_, v_e_67_, v_____do__lift_68_);
lean_dec_ref(v_body_66_);
lean_dec_ref(v_binderType_61_);
return v_res_70_;
}
}
lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5(lean_object* v_binderType_71_, lean_object* v_____do__lift_72_, lean_object* v_binderName_73_, uint8_t v_binderInfo_74_, lean_object* v_toPure_75_, lean_object* v_body_76_, lean_object* v_e_77_, lean_object* v_____do__lift_78_){
_start:
{
size_t v___x_79_; size_t v___x_80_; uint8_t v___x_81_; 
v___x_79_ = lean_ptr_addr(v_binderType_71_);
v___x_80_ = lean_ptr_addr(v_____do__lift_72_);
v___x_81_ = lean_usize_dec_eq(v___x_79_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec_ref(v_e_77_);
v___x_82_ = l_Lean_Expr_forallE___override(v_binderName_73_, v_____do__lift_72_, v_____do__lift_78_, v_binderInfo_74_);
v___x_83_ = lean_apply_2(v_toPure_75_, lean_box(0), v___x_82_);
return v___x_83_;
}
else
{
size_t v___x_84_; size_t v___x_85_; uint8_t v___x_86_; 
v___x_84_ = lean_ptr_addr(v_body_76_);
v___x_85_ = lean_ptr_addr(v_____do__lift_78_);
v___x_86_ = lean_usize_dec_eq(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec_ref(v_e_77_);
v___x_87_ = l_Lean_Expr_forallE___override(v_binderName_73_, v_____do__lift_72_, v_____do__lift_78_, v_binderInfo_74_);
v___x_88_ = lean_apply_2(v_toPure_75_, lean_box(0), v___x_87_);
return v___x_88_;
}
else
{
uint8_t v___x_89_; 
v___x_89_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_74_, v_binderInfo_74_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec_ref(v_e_77_);
v___x_90_ = l_Lean_Expr_forallE___override(v_binderName_73_, v_____do__lift_72_, v_____do__lift_78_, v_binderInfo_74_);
v___x_91_ = lean_apply_2(v_toPure_75_, lean_box(0), v___x_90_);
return v___x_91_;
}
else
{
lean_object* v___x_92_; 
lean_dec_ref(v_____do__lift_78_);
lean_dec(v_binderName_73_);
lean_dec_ref(v_____do__lift_72_);
v___x_92_ = lean_apply_2(v_toPure_75_, lean_box(0), v_e_77_);
return v___x_92_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderType_71_ = stack[0].m_obj;
lean_object* v_____do__lift_72_ = stack[1].m_obj;
lean_object* v_binderName_73_ = stack[2].m_obj;
uint8_t v_binderInfo_74_ = stack[3].m_num;
lean_object* v_toPure_75_ = stack[4].m_obj;
lean_object* v_body_76_ = stack[5].m_obj;
lean_object* v_e_77_ = stack[6].m_obj;
lean_object* v_____do__lift_78_ = stack[7].m_obj;
lean_object* v_res_93_;
v_res_93_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5(v_binderType_71_, v_____do__lift_72_, v_binderName_73_, v_binderInfo_74_, v_toPure_75_, v_body_76_, v_e_77_, v_____do__lift_78_);
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5___boxed(lean_object* v_binderType_94_, lean_object* v_____do__lift_95_, lean_object* v_binderName_96_, lean_object* v_binderInfo_97_, lean_object* v_toPure_98_, lean_object* v_body_99_, lean_object* v_e_100_, lean_object* v_____do__lift_101_){
_start:
{
uint8_t v_binderInfo_747__boxed_102_; lean_object* v_res_103_; 
v_binderInfo_747__boxed_102_ = lean_unbox(v_binderInfo_97_);
v_res_103_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5(v_binderType_94_, v_____do__lift_95_, v_binderName_96_, v_binderInfo_747__boxed_102_, v_toPure_98_, v_body_99_, v_e_100_, v_____do__lift_101_);
lean_dec_ref(v_body_99_);
lean_dec_ref(v_binderType_94_);
return v_res_103_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_107_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2));
v___x_108_ = lean_unsigned_to_nat(41u);
v___x_109_ = lean_unsigned_to_nat(30u);
v___x_110_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1));
v___x_111_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0));
v___x_112_ = l_mkPanicMessageWithDecl(v___x_111_, v___x_110_, v___x_109_, v___x_108_, v___x_107_);
return v___x_112_;
}
}
lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4(lean_object* v_binderType_113_, lean_object* v_binderName_114_, uint8_t v_binderInfo_115_, lean_object* v_toPure_116_, lean_object* v_body_117_, lean_object* v_e_118_, lean_object* v_inst_119_, lean_object* v_f_120_, lean_object* v_toBind_121_, lean_object* v_____do__lift_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___f_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_123_ = lean_box(v_binderInfo_115_);
lean_inc_ref(v_body_117_);
v___f_124_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_124_, 0, v_binderType_113_);
lean_closure_set(v___f_124_, 1, v_____do__lift_122_);
lean_closure_set(v___f_124_, 2, v_binderName_114_);
lean_closure_set(v___f_124_, 3, v___x_123_);
lean_closure_set(v___f_124_, 4, v_toPure_116_);
lean_closure_set(v___f_124_, 5, v_body_117_);
lean_closure_set(v___f_124_, 6, v_e_118_);
v___x_125_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_119_, v_f_120_, v_body_117_);
v___x_126_ = lean_apply_4(v_toBind_121_, lean_box(0), lean_box(0), v___x_125_, v___f_124_);
return v___x_126_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderType_113_ = stack[0].m_obj;
lean_object* v_binderName_114_ = stack[1].m_obj;
uint8_t v_binderInfo_115_ = stack[2].m_num;
lean_object* v_toPure_116_ = stack[3].m_obj;
lean_object* v_body_117_ = stack[4].m_obj;
lean_object* v_e_118_ = stack[5].m_obj;
lean_object* v_inst_119_ = stack[6].m_obj;
lean_object* v_f_120_ = stack[7].m_obj;
lean_object* v_toBind_121_ = stack[8].m_obj;
lean_object* v_____do__lift_122_ = stack[9].m_obj;
lean_object* v_res_127_;
v_res_127_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4(v_binderType_113_, v_binderName_114_, v_binderInfo_115_, v_toPure_116_, v_body_117_, v_e_118_, v_inst_119_, v_f_120_, v_toBind_121_, v_____do__lift_122_);
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4___boxed(lean_object* v_binderType_128_, lean_object* v_binderName_129_, lean_object* v_binderInfo_130_, lean_object* v_toPure_131_, lean_object* v_body_132_, lean_object* v_e_133_, lean_object* v_inst_134_, lean_object* v_f_135_, lean_object* v_toBind_136_, lean_object* v_____do__lift_137_){
_start:
{
uint8_t v_binderInfo_852__boxed_138_; lean_object* v_res_139_; 
v_binderInfo_852__boxed_138_ = lean_unbox(v_binderInfo_130_);
v_res_139_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4(v_binderType_128_, v_binderName_129_, v_binderInfo_852__boxed_138_, v_toPure_131_, v_body_132_, v_e_133_, v_inst_134_, v_f_135_, v_toBind_136_, v_____do__lift_137_);
return v_res_139_;
}
}
lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6(lean_object* v_binderType_140_, lean_object* v_binderName_141_, uint8_t v_binderInfo_142_, lean_object* v_toPure_143_, lean_object* v_body_144_, lean_object* v_e_145_, lean_object* v_inst_146_, lean_object* v_f_147_, lean_object* v_toBind_148_, lean_object* v_____do__lift_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___f_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_150_ = lean_box(v_binderInfo_142_);
lean_inc_ref(v_body_144_);
v___f_151_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_151_, 0, v_binderType_140_);
lean_closure_set(v___f_151_, 1, v_____do__lift_149_);
lean_closure_set(v___f_151_, 2, v_binderName_141_);
lean_closure_set(v___f_151_, 3, v___x_150_);
lean_closure_set(v___f_151_, 4, v_toPure_143_);
lean_closure_set(v___f_151_, 5, v_body_144_);
lean_closure_set(v___f_151_, 6, v_e_145_);
v___x_152_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_146_, v_f_147_, v_body_144_);
v___x_153_ = lean_apply_4(v_toBind_148_, lean_box(0), lean_box(0), v___x_152_, v___f_151_);
return v___x_153_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderType_140_ = stack[0].m_obj;
lean_object* v_binderName_141_ = stack[1].m_obj;
uint8_t v_binderInfo_142_ = stack[2].m_num;
lean_object* v_toPure_143_ = stack[3].m_obj;
lean_object* v_body_144_ = stack[4].m_obj;
lean_object* v_e_145_ = stack[5].m_obj;
lean_object* v_inst_146_ = stack[6].m_obj;
lean_object* v_f_147_ = stack[7].m_obj;
lean_object* v_toBind_148_ = stack[8].m_obj;
lean_object* v_____do__lift_149_ = stack[9].m_obj;
lean_object* v_res_154_;
v_res_154_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6(v_binderType_140_, v_binderName_141_, v_binderInfo_142_, v_toPure_143_, v_body_144_, v_e_145_, v_inst_146_, v_f_147_, v_toBind_148_, v_____do__lift_149_);
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6___boxed(lean_object* v_binderType_155_, lean_object* v_binderName_156_, lean_object* v_binderInfo_157_, lean_object* v_toPure_158_, lean_object* v_body_159_, lean_object* v_e_160_, lean_object* v_inst_161_, lean_object* v_f_162_, lean_object* v_toBind_163_, lean_object* v_____do__lift_164_){
_start:
{
uint8_t v_binderInfo_861__boxed_165_; lean_object* v_res_166_; 
v_binderInfo_861__boxed_165_ = lean_unbox(v_binderInfo_157_);
v_res_166_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6(v_binderType_155_, v_binderName_156_, v_binderInfo_861__boxed_165_, v_toPure_158_, v_body_159_, v_e_160_, v_inst_161_, v_f_162_, v_toBind_163_, v_____do__lift_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(lean_object* v_inst_167_, lean_object* v_f_168_, lean_object* v_e_169_){
_start:
{
lean_object* v_toApplicative_170_; lean_object* v_toBind_171_; lean_object* v_toPure_172_; uint8_t v___x_173_; 
v_toApplicative_170_ = lean_ctor_get(v_inst_167_, 0);
v_toBind_171_ = lean_ctor_get(v_inst_167_, 1);
lean_inc(v_toBind_171_);
v_toPure_172_ = lean_ctor_get(v_toApplicative_170_, 1);
v___x_173_ = l_Lean_Expr_hasFVar(v_e_169_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
lean_inc(v_toPure_172_);
lean_dec(v_toBind_171_);
lean_dec(v_f_168_);
lean_dec_ref(v_inst_167_);
v___x_174_ = lean_apply_2(v_toPure_172_, lean_box(0), v_e_169_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_inst_167_);
v___x_176_ = l_instInhabitedOfMonad___redArg(v_inst_167_, v___x_175_);
switch(lean_obj_tag(v_e_169_))
{
case 1:
{
lean_object* v_fvarId_177_; lean_object* v___f_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
lean_inc(v_toPure_172_);
lean_dec(v___x_176_);
lean_dec_ref(v_inst_167_);
v_fvarId_177_ = lean_ctor_get(v_e_169_, 0);
lean_inc_n(v_fvarId_177_, 2);
v___f_178_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_178_, 0, v_fvarId_177_);
lean_closure_set(v___f_178_, 1, v_toPure_172_);
lean_closure_set(v___f_178_, 2, v_e_169_);
v___x_179_ = lean_apply_1(v_f_168_, v_fvarId_177_);
v___x_180_ = lean_apply_4(v_toBind_171_, lean_box(0), lean_box(0), v___x_179_, v___f_178_);
return v___x_180_;
}
case 2:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec_ref_known(v_e_169_, 1);
lean_dec(v_toBind_171_);
lean_dec(v_f_168_);
lean_dec_ref(v_inst_167_);
v___x_181_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3, &l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3);
v___x_182_ = l_panic___redArg(v___x_176_, v___x_181_);
lean_dec(v___x_176_);
return v___x_182_;
}
case 5:
{
lean_object* v_fn_183_; lean_object* v_arg_184_; lean_object* v___f_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec(v___x_176_);
v_fn_183_ = lean_ctor_get(v_e_169_, 0);
lean_inc_ref_n(v_fn_183_, 2);
v_arg_184_ = lean_ctor_get(v_e_169_, 1);
lean_inc_ref(v_arg_184_);
lean_inc(v_toBind_171_);
lean_inc(v_f_168_);
lean_inc_ref(v_inst_167_);
lean_inc(v_toPure_172_);
v___f_185_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__2), 8, 7);
lean_closure_set(v___f_185_, 0, v_fn_183_);
lean_closure_set(v___f_185_, 1, v_toPure_172_);
lean_closure_set(v___f_185_, 2, v_arg_184_);
lean_closure_set(v___f_185_, 3, v_e_169_);
lean_closure_set(v___f_185_, 4, v_inst_167_);
lean_closure_set(v___f_185_, 5, v_f_168_);
lean_closure_set(v___f_185_, 6, v_toBind_171_);
v___x_186_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_167_, v_f_168_, v_fn_183_);
v___x_187_ = lean_apply_4(v_toBind_171_, lean_box(0), lean_box(0), v___x_186_, v___f_185_);
return v___x_187_;
}
case 6:
{
lean_object* v_binderName_188_; lean_object* v_binderType_189_; lean_object* v_body_190_; uint8_t v_binderInfo_191_; lean_object* v___x_192_; lean_object* v___f_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec(v___x_176_);
v_binderName_188_ = lean_ctor_get(v_e_169_, 0);
lean_inc(v_binderName_188_);
v_binderType_189_ = lean_ctor_get(v_e_169_, 1);
lean_inc_ref_n(v_binderType_189_, 2);
v_body_190_ = lean_ctor_get(v_e_169_, 2);
lean_inc_ref(v_body_190_);
v_binderInfo_191_ = lean_ctor_get_uint8(v_e_169_, sizeof(void*)*3 + 8);
v___x_192_ = lean_box(v_binderInfo_191_);
lean_inc(v_toBind_171_);
lean_inc(v_f_168_);
lean_inc_ref(v_inst_167_);
lean_inc(v_toPure_172_);
v___f_193_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_193_, 0, v_binderType_189_);
lean_closure_set(v___f_193_, 1, v_binderName_188_);
lean_closure_set(v___f_193_, 2, v___x_192_);
lean_closure_set(v___f_193_, 3, v_toPure_172_);
lean_closure_set(v___f_193_, 4, v_body_190_);
lean_closure_set(v___f_193_, 5, v_e_169_);
lean_closure_set(v___f_193_, 6, v_inst_167_);
lean_closure_set(v___f_193_, 7, v_f_168_);
lean_closure_set(v___f_193_, 8, v_toBind_171_);
v___x_194_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_167_, v_f_168_, v_binderType_189_);
v___x_195_ = lean_apply_4(v_toBind_171_, lean_box(0), lean_box(0), v___x_194_, v___f_193_);
return v___x_195_;
}
case 7:
{
lean_object* v_binderName_196_; lean_object* v_binderType_197_; lean_object* v_body_198_; uint8_t v_binderInfo_199_; lean_object* v___x_200_; lean_object* v___f_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec(v___x_176_);
v_binderName_196_ = lean_ctor_get(v_e_169_, 0);
lean_inc(v_binderName_196_);
v_binderType_197_ = lean_ctor_get(v_e_169_, 1);
lean_inc_ref_n(v_binderType_197_, 2);
v_body_198_ = lean_ctor_get(v_e_169_, 2);
lean_inc_ref(v_body_198_);
v_binderInfo_199_ = lean_ctor_get_uint8(v_e_169_, sizeof(void*)*3 + 8);
v___x_200_ = lean_box(v_binderInfo_199_);
lean_inc(v_toBind_171_);
lean_inc(v_f_168_);
lean_inc_ref(v_inst_167_);
lean_inc(v_toPure_172_);
v___f_201_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_201_, 0, v_binderType_197_);
lean_closure_set(v___f_201_, 1, v_binderName_196_);
lean_closure_set(v___f_201_, 2, v___x_200_);
lean_closure_set(v___f_201_, 3, v_toPure_172_);
lean_closure_set(v___f_201_, 4, v_body_198_);
lean_closure_set(v___f_201_, 5, v_e_169_);
lean_closure_set(v___f_201_, 6, v_inst_167_);
lean_closure_set(v___f_201_, 7, v_f_168_);
lean_closure_set(v___f_201_, 8, v_toBind_171_);
v___x_202_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_167_, v_f_168_, v_binderType_197_);
v___x_203_ = lean_apply_4(v_toBind_171_, lean_box(0), lean_box(0), v___x_202_, v___f_201_);
return v___x_203_;
}
case 8:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec_ref_known(v_e_169_, 4);
lean_dec(v_toBind_171_);
lean_dec(v_f_168_);
lean_dec_ref(v_inst_167_);
v___x_204_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3, &l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3);
v___x_205_ = l_panic___redArg(v___x_176_, v___x_204_);
lean_dec(v___x_176_);
return v___x_205_;
}
case 11:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec_ref_known(v_e_169_, 3);
lean_dec(v_toBind_171_);
lean_dec(v_f_168_);
lean_dec_ref(v_inst_167_);
v___x_206_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3, &l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3);
v___x_207_ = l_panic___redArg(v___x_176_, v___x_206_);
lean_dec(v___x_176_);
return v___x_207_;
}
default: 
{
lean_object* v___x_208_; 
lean_inc(v_toPure_172_);
lean_dec(v___x_176_);
lean_dec(v_toBind_171_);
lean_dec(v_f_168_);
lean_dec_ref(v_inst_167_);
v___x_208_ = lean_apply_2(v_toPure_172_, lean_box(0), v_e_169_);
return v___x_208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__2(lean_object* v_fn_209_, lean_object* v_toPure_210_, lean_object* v_arg_211_, lean_object* v_e_212_, lean_object* v_inst_213_, lean_object* v_f_214_, lean_object* v_toBind_215_, lean_object* v_____do__lift_216_){
_start:
{
lean_object* v___f_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
lean_inc_ref(v_arg_211_);
v___f_217_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_217_, 0, v_fn_209_);
lean_closure_set(v___f_217_, 1, v_____do__lift_216_);
lean_closure_set(v___f_217_, 2, v_toPure_210_);
lean_closure_set(v___f_217_, 3, v_arg_211_);
lean_closure_set(v___f_217_, 4, v_e_212_);
v___x_218_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_213_, v_f_214_, v_arg_211_);
v___x_219_ = lean_apply_4(v_toBind_215_, lean_box(0), lean_box(0), v___x_218_, v___f_217_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM(lean_object* v_m_220_, lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_f_223_, lean_object* v_e_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_222_, v_f_223_, v_e_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___boxed(lean_object* v_m_226_, lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_f_229_, lean_object* v_e_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Compiler_LCNF_Expr_mapFVarM(v_m_226_, v_inst_227_, v_inst_228_, v_f_229_, v_e_230_);
lean_dec(v_inst_227_);
return v_res_231_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_233_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2));
v___x_234_ = lean_unsigned_to_nat(40u);
v___x_235_ = lean_unsigned_to_nat(49u);
v___x_236_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0));
v___x_237_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0));
v___x_238_ = l_mkPanicMessageWithDecl(v___x_237_, v___x_236_, v___x_235_, v___x_234_, v___x_233_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__1(lean_object* v_inst_239_, lean_object* v_f_240_, lean_object* v_arg_241_, lean_object* v_____r_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_239_, v_f_240_, v_arg_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(lean_object* v_inst_244_, lean_object* v_f_245_, lean_object* v_e_246_){
_start:
{
lean_object* v_toApplicative_247_; lean_object* v_toBind_248_; lean_object* v_ty_250_; lean_object* v_body_251_; lean_object* v_toPure_255_; uint8_t v___x_256_; 
v_toApplicative_247_ = lean_ctor_get(v_inst_244_, 0);
v_toBind_248_ = lean_ctor_get(v_inst_244_, 1);
lean_inc(v_toBind_248_);
v_toPure_255_ = lean_ctor_get(v_toApplicative_247_, 1);
v___x_256_ = l_Lean_Expr_hasFVar(v_e_246_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_inc(v_toPure_255_);
lean_dec(v_toBind_248_);
lean_dec_ref(v_e_246_);
lean_dec(v_f_245_);
lean_dec_ref(v_inst_244_);
v___x_257_ = lean_box(0);
v___x_258_ = lean_apply_2(v_toPure_255_, lean_box(0), v___x_257_);
return v___x_258_;
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_box(0);
lean_inc_ref(v_inst_244_);
v___x_260_ = l_instInhabitedOfMonad___redArg(v_inst_244_, v___x_259_);
switch(lean_obj_tag(v_e_246_))
{
case 1:
{
lean_object* v_fvarId_261_; lean_object* v___x_262_; 
lean_dec(v___x_260_);
lean_dec(v_toBind_248_);
lean_dec_ref(v_inst_244_);
v_fvarId_261_ = lean_ctor_get(v_e_246_, 0);
lean_inc(v_fvarId_261_);
lean_dec_ref_known(v_e_246_, 1);
v___x_262_ = lean_apply_1(v_f_245_, v_fvarId_261_);
return v___x_262_;
}
case 2:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec_ref_known(v_e_246_, 1);
lean_dec(v_toBind_248_);
lean_dec(v_f_245_);
lean_dec_ref(v_inst_244_);
v___x_263_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1, &l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1);
v___x_264_ = l_panic___redArg(v___x_260_, v___x_263_);
lean_dec(v___x_260_);
return v___x_264_;
}
case 5:
{
lean_object* v_fn_265_; lean_object* v_arg_266_; lean_object* v___f_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v___x_260_);
v_fn_265_ = lean_ctor_get(v_e_246_, 0);
lean_inc_ref(v_fn_265_);
v_arg_266_ = lean_ctor_get(v_e_246_, 1);
lean_inc_ref(v_arg_266_);
lean_dec_ref_known(v_e_246_, 2);
lean_inc(v_f_245_);
lean_inc_ref(v_inst_244_);
v___f_267_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_267_, 0, v_inst_244_);
lean_closure_set(v___f_267_, 1, v_f_245_);
lean_closure_set(v___f_267_, 2, v_arg_266_);
v___x_268_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_244_, v_f_245_, v_fn_265_);
v___x_269_ = lean_apply_4(v_toBind_248_, lean_box(0), lean_box(0), v___x_268_, v___f_267_);
return v___x_269_;
}
case 6:
{
lean_object* v_binderType_270_; lean_object* v_body_271_; 
lean_dec(v___x_260_);
v_binderType_270_ = lean_ctor_get(v_e_246_, 1);
lean_inc_ref(v_binderType_270_);
v_body_271_ = lean_ctor_get(v_e_246_, 2);
lean_inc_ref(v_body_271_);
lean_dec_ref_known(v_e_246_, 3);
v_ty_250_ = v_binderType_270_;
v_body_251_ = v_body_271_;
goto v___jp_249_;
}
case 7:
{
lean_object* v_binderType_272_; lean_object* v_body_273_; 
lean_dec(v___x_260_);
v_binderType_272_ = lean_ctor_get(v_e_246_, 1);
lean_inc_ref(v_binderType_272_);
v_body_273_ = lean_ctor_get(v_e_246_, 2);
lean_inc_ref(v_body_273_);
lean_dec_ref_known(v_e_246_, 3);
v_ty_250_ = v_binderType_272_;
v_body_251_ = v_body_273_;
goto v___jp_249_;
}
case 8:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec_ref_known(v_e_246_, 4);
lean_dec(v_toBind_248_);
lean_dec(v_f_245_);
lean_dec_ref(v_inst_244_);
v___x_274_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1, &l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1);
v___x_275_ = l_panic___redArg(v___x_260_, v___x_274_);
lean_dec(v___x_260_);
return v___x_275_;
}
case 11:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec_ref_known(v_e_246_, 3);
lean_dec(v_toBind_248_);
lean_dec(v_f_245_);
lean_dec_ref(v_inst_244_);
v___x_276_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1, &l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1);
v___x_277_ = l_panic___redArg(v___x_260_, v___x_276_);
lean_dec(v___x_260_);
return v___x_277_;
}
default: 
{
lean_object* v___x_278_; 
lean_inc(v_toPure_255_);
lean_dec(v___x_260_);
lean_dec(v_toBind_248_);
lean_dec_ref(v_e_246_);
lean_dec(v_f_245_);
lean_dec_ref(v_inst_244_);
v___x_278_ = lean_apply_2(v_toPure_255_, lean_box(0), v___x_259_);
return v___x_278_;
}
}
}
v___jp_249_:
{
lean_object* v___f_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
lean_inc(v_f_245_);
lean_inc_ref(v_inst_244_);
v___f_252_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_252_, 0, v_inst_244_);
lean_closure_set(v___f_252_, 1, v_f_245_);
lean_closure_set(v___f_252_, 2, v_body_251_);
v___x_253_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_244_, v_f_245_, v_ty_250_);
v___x_254_ = lean_apply_4(v_toBind_248_, lean_box(0), lean_box(0), v___x_253_, v___f_252_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__0(lean_object* v_inst_279_, lean_object* v_f_280_, lean_object* v_body_281_, lean_object* v_____r_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_279_, v_f_280_, v_body_281_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM(lean_object* v_m_284_, lean_object* v_inst_285_, lean_object* v_f_286_, lean_object* v_e_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_285_, v_f_286_, v_e_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0(lean_object* v_m_289_, lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_291_, v___y_292_, v___y_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0___boxed(lean_object* v_m_295_, lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0(v_m_295_, v_inst_296_, v_inst_297_, v___y_298_, v___y_299_);
lean_dec(v_inst_296_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__1(lean_object* v_m_301_, lean_object* v_inst_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_302_, v___y_303_, v___y_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__0(lean_object* v_arg_312_, lean_object* v_toPure_313_, lean_object* v_____do__lift_314_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(v_arg_312_, v_____do__lift_314_);
v___x_316_ = lean_apply_2(v_toPure_313_, lean_box(0), v___x_315_);
return v___x_316_;
}
}
lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1(uint8_t v_pu_317_, lean_object* v_arg_318_, lean_object* v_toPure_319_, lean_object* v_____do__lift_320_){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_317_, v_arg_318_, v_____do__lift_320_);
v___x_322_ = lean_apply_2(v_toPure_319_, lean_box(0), v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_317_ = stack[0].m_num;
lean_object* v_arg_318_ = stack[1].m_obj;
lean_object* v_toPure_319_ = stack[2].m_obj;
lean_object* v_____do__lift_320_ = stack[3].m_obj;
lean_object* v_res_323_;
v_res_323_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1(v_pu_317_, v_arg_318_, v_toPure_319_, v_____do__lift_320_);
stack->m_obj
 = v_res_323_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1___boxed(lean_object* v_pu_324_, lean_object* v_arg_325_, lean_object* v_toPure_326_, lean_object* v_____do__lift_327_){
_start:
{
uint8_t v_pu_boxed_328_; lean_object* v_res_329_; 
v_pu_boxed_328_ = lean_unbox(v_pu_324_);
v_res_329_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1(v_pu_boxed_328_, v_arg_325_, v_toPure_326_, v_____do__lift_327_);
return v_res_329_;
}
}
lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(uint8_t v_pu_330_, lean_object* v_inst_331_, lean_object* v_f_332_, lean_object* v_arg_333_){
_start:
{
switch(lean_obj_tag(v_arg_333_))
{
case 0:
{
lean_object* v_toApplicative_334_; lean_object* v_toPure_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_toApplicative_334_ = lean_ctor_get(v_inst_331_, 0);
lean_inc_ref(v_toApplicative_334_);
lean_dec(v_f_332_);
lean_dec_ref(v_inst_331_);
v_toPure_335_ = lean_ctor_get(v_toApplicative_334_, 1);
lean_inc(v_toPure_335_);
lean_dec_ref(v_toApplicative_334_);
v___x_336_ = lean_box(0);
v___x_337_ = lean_apply_2(v_toPure_335_, lean_box(0), v___x_336_);
return v___x_337_;
}
case 1:
{
lean_object* v_toApplicative_338_; lean_object* v_toBind_339_; lean_object* v_toPure_340_; lean_object* v_fvarId_341_; lean_object* v___f_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_toApplicative_338_ = lean_ctor_get(v_inst_331_, 0);
lean_inc_ref(v_toApplicative_338_);
v_toBind_339_ = lean_ctor_get(v_inst_331_, 1);
lean_inc(v_toBind_339_);
lean_dec_ref(v_inst_331_);
v_toPure_340_ = lean_ctor_get(v_toApplicative_338_, 1);
lean_inc(v_toPure_340_);
lean_dec_ref(v_toApplicative_338_);
v_fvarId_341_ = lean_ctor_get(v_arg_333_, 0);
lean_inc(v_fvarId_341_);
v___f_342_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_342_, 0, v_arg_333_);
lean_closure_set(v___f_342_, 1, v_toPure_340_);
v___x_343_ = lean_apply_1(v_f_332_, v_fvarId_341_);
v___x_344_ = lean_apply_4(v_toBind_339_, lean_box(0), lean_box(0), v___x_343_, v___f_342_);
return v___x_344_;
}
default: 
{
lean_object* v_toApplicative_345_; lean_object* v_toBind_346_; lean_object* v_toPure_347_; lean_object* v_expr_348_; lean_object* v___x_349_; lean_object* v___f_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_toApplicative_345_ = lean_ctor_get(v_inst_331_, 0);
v_toBind_346_ = lean_ctor_get(v_inst_331_, 1);
lean_inc(v_toBind_346_);
v_toPure_347_ = lean_ctor_get(v_toApplicative_345_, 1);
v_expr_348_ = lean_ctor_get(v_arg_333_, 0);
lean_inc_ref(v_expr_348_);
v___x_349_ = lean_box(v_pu_330_);
lean_inc(v_toPure_347_);
v___f_350_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_350_, 0, v___x_349_);
lean_closure_set(v___f_350_, 1, v_arg_333_);
lean_closure_set(v___f_350_, 2, v_toPure_347_);
v___x_351_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_331_, v_f_332_, v_expr_348_);
v___x_352_ = lean_apply_4(v_toBind_346_, lean_box(0), lean_box(0), v___x_351_, v___f_350_);
return v___x_352_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_330_ = stack[0].m_num;
lean_object* v_inst_331_ = stack[1].m_obj;
lean_object* v_f_332_ = stack[2].m_obj;
lean_object* v_arg_333_ = stack[3].m_obj;
lean_object* v_res_353_;
v_res_353_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_330_, v_inst_331_, v_f_332_, v_arg_333_);
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___boxed(lean_object* v_pu_354_, lean_object* v_inst_355_, lean_object* v_f_356_, lean_object* v_arg_357_){
_start:
{
uint8_t v_pu_boxed_358_; lean_object* v_res_359_; 
v_pu_boxed_358_ = lean_unbox(v_pu_354_);
v_res_359_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_boxed_358_, v_inst_355_, v_f_356_, v_arg_357_);
return v_res_359_;
}
}
lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM(lean_object* v_m_360_, uint8_t v_pu_361_, lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_f_364_, lean_object* v_arg_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_361_, v_inst_363_, v_f_364_, v_arg_365_);
return v___x_366_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Arg_mapFVarM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_361_ = stack[1].m_num;
lean_object* v_inst_362_ = stack[2].m_obj;
lean_object* v_inst_363_ = stack[3].m_obj;
lean_object* v_f_364_ = stack[4].m_obj;
lean_object* v_arg_365_ = stack[5].m_obj;
lean_object* v_res_367_;
v_res_367_ = l_Lean_Compiler_LCNF_Arg_mapFVarM(lean_box(0), v_pu_361_, v_inst_362_, v_inst_363_, v_f_364_, v_arg_365_);
stack->m_obj
 = v_res_367_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___boxed(lean_object* v_m_368_, lean_object* v_pu_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_f_372_, lean_object* v_arg_373_){
_start:
{
uint8_t v_pu_boxed_374_; lean_object* v_res_375_; 
v_pu_boxed_374_ = lean_unbox(v_pu_369_);
v_res_375_ = l_Lean_Compiler_LCNF_Arg_mapFVarM(v_m_368_, v_pu_boxed_374_, v_inst_370_, v_inst_371_, v_f_372_, v_arg_373_);
lean_dec(v_inst_370_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(lean_object* v_inst_376_, lean_object* v_f_377_, lean_object* v_arg_378_){
_start:
{
switch(lean_obj_tag(v_arg_378_))
{
case 0:
{
lean_object* v_toApplicative_379_; lean_object* v_toPure_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v_toApplicative_379_ = lean_ctor_get(v_inst_376_, 0);
lean_inc_ref(v_toApplicative_379_);
lean_dec(v_f_377_);
lean_dec_ref(v_inst_376_);
v_toPure_380_ = lean_ctor_get(v_toApplicative_379_, 1);
lean_inc(v_toPure_380_);
lean_dec_ref(v_toApplicative_379_);
v___x_381_ = lean_box(0);
v___x_382_ = lean_apply_2(v_toPure_380_, lean_box(0), v___x_381_);
return v___x_382_;
}
case 1:
{
lean_object* v_fvarId_383_; lean_object* v___x_384_; 
lean_dec_ref(v_inst_376_);
v_fvarId_383_ = lean_ctor_get(v_arg_378_, 0);
lean_inc(v_fvarId_383_);
lean_dec_ref_known(v_arg_378_, 1);
v___x_384_ = lean_apply_1(v_f_377_, v_fvarId_383_);
return v___x_384_;
}
default: 
{
lean_object* v_expr_385_; lean_object* v___x_386_; 
v_expr_385_ = lean_ctor_get(v_arg_378_, 0);
lean_inc_ref(v_expr_385_);
lean_dec_ref_known(v_arg_378_, 1);
v___x_386_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_376_, v_f_377_, v_expr_385_);
return v___x_386_;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM(lean_object* v_m_387_, uint8_t v_pu_388_, lean_object* v_inst_389_, lean_object* v_f_390_, lean_object* v_arg_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_389_, v_f_390_, v_arg_391_);
return v___x_392_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Arg_forFVarM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_388_ = stack[1].m_num;
lean_object* v_inst_389_ = stack[2].m_obj;
lean_object* v_f_390_ = stack[3].m_obj;
lean_object* v_arg_391_ = stack[4].m_obj;
lean_object* v_res_393_;
v_res_393_ = l_Lean_Compiler_LCNF_Arg_forFVarM(lean_box(0), v_pu_388_, v_inst_389_, v_f_390_, v_arg_391_);
stack->m_obj
 = v_res_393_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___boxed(lean_object* v_m_394_, lean_object* v_pu_395_, lean_object* v_inst_396_, lean_object* v_f_397_, lean_object* v_arg_398_){
_start:
{
uint8_t v_pu_boxed_399_; lean_object* v_res_400_; 
v_pu_boxed_399_ = lean_unbox(v_pu_395_);
v_res_400_ = l_Lean_Compiler_LCNF_Arg_forFVarM(v_m_394_, v_pu_boxed_399_, v_inst_396_, v_f_397_, v_arg_398_);
return v_res_400_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0(uint8_t v_pu_401_, lean_object* v_m_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_401_, v_inst_404_, v___y_405_, v___y_406_);
return v___x_407_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_401_ = stack[0].m_num;
lean_object* v_inst_403_ = stack[2].m_obj;
lean_object* v_inst_404_ = stack[3].m_obj;
lean_object* v___y_405_ = stack[4].m_obj;
lean_object* v___y_406_ = stack[5].m_obj;
lean_object* v_res_408_;
v_res_408_ = l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0(v_pu_401_, lean_box(0), v_inst_403_, v_inst_404_, v___y_405_, v___y_406_);
stack->m_obj
 = v_res_408_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0___boxed(lean_object* v_pu_409_, lean_object* v_m_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
uint8_t v_pu_boxed_415_; lean_object* v_res_416_; 
v_pu_boxed_415_ = lean_unbox(v_pu_409_);
v_res_416_ = l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0(v_pu_boxed_415_, v_m_410_, v_inst_411_, v_inst_412_, v___y_413_, v___y_414_);
lean_dec(v_inst_411_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__1(lean_object* v_m_417_, lean_object* v_inst_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_418_, v___y_419_, v___y_420_);
return v___x_421_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg(uint8_t v_pu_423_){
_start:
{
lean_object* v___x_424_; lean_object* v___f_425_; lean_object* v___f_426_; lean_object* v___x_427_; 
v___x_424_ = lean_box(v_pu_423_);
v___f_425_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_425_, 0, v___x_424_);
v___f_426_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarArg___closed__0));
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v___f_425_);
lean_ctor_set(v___x_427_, 1, v___f_426_);
return v___x_427_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_423_ = stack[0].m_num;
lean_object* v_res_428_;
v_res_428_ = l_Lean_Compiler_LCNF_instTraverseFVarArg(v_pu_423_);
stack->m_obj
 = v_res_428_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___boxed(lean_object* v_pu_429_){
_start:
{
uint8_t v_pu_boxed_430_; lean_object* v_res_431_; 
v_pu_boxed_430_ = lean_unbox(v_pu_429_);
v_res_431_ = l_Lean_Compiler_LCNF_instTraverseFVarArg(v_pu_boxed_430_);
return v_res_431_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0(uint8_t v_pu_432_, lean_object* v_inst_433_, lean_object* v_f_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_432_, v_inst_433_, v_f_434_, v___y_435_);
return v___x_436_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_432_ = stack[0].m_num;
lean_object* v_inst_433_ = stack[1].m_obj;
lean_object* v_f_434_ = stack[2].m_obj;
lean_object* v___y_435_ = stack[3].m_obj;
lean_object* v_res_437_;
v_res_437_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0(v_pu_432_, v_inst_433_, v_f_434_, v___y_435_);
stack->m_obj
 = v_res_437_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_438_, lean_object* v_inst_439_, lean_object* v_f_440_, lean_object* v___y_441_){
_start:
{
uint8_t v_pu_boxed_442_; lean_object* v_res_443_; 
v_pu_boxed_442_ = lean_unbox(v_pu_438_);
v_res_443_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0(v_pu_boxed_442_, v_inst_439_, v_f_440_, v___y_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1(lean_object* v_e_444_, lean_object* v_toPure_445_, lean_object* v_____do__lift_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_444_, v_____do__lift_446_);
v___x_448_ = lean_apply_2(v_toPure_445_, lean_box(0), v___x_447_);
return v___x_448_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(uint8_t v_pu_449_, lean_object* v_e_450_, lean_object* v_toPure_451_, lean_object* v_____do__lift_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_449_, v_e_450_, v_____do__lift_452_);
v___x_454_ = lean_apply_2(v_toPure_451_, lean_box(0), v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_449_ = stack[0].m_num;
lean_object* v_e_450_ = stack[1].m_obj;
lean_object* v_toPure_451_ = stack[2].m_obj;
lean_object* v_____do__lift_452_ = stack[3].m_obj;
lean_object* v_res_455_;
v_res_455_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(v_pu_449_, v_e_450_, v_toPure_451_, v_____do__lift_452_);
stack->m_obj
 = v_res_455_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed(lean_object* v_pu_456_, lean_object* v_e_457_, lean_object* v_toPure_458_, lean_object* v_____do__lift_459_){
_start:
{
uint8_t v_pu_boxed_460_; lean_object* v_res_461_; 
v_pu_boxed_460_ = lean_unbox(v_pu_456_);
v_res_461_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(v_pu_boxed_460_, v_e_457_, v_toPure_458_, v_____do__lift_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7(lean_object* v_e_462_, lean_object* v_____do__lift_463_, lean_object* v_toPure_464_, lean_object* v_____do__lift_465_){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___redArg(v_e_462_, v_____do__lift_463_, v_____do__lift_465_);
v___x_467_ = lean_apply_2(v_toPure_464_, lean_box(0), v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7___boxed(lean_object* v_e_468_, lean_object* v_____do__lift_469_, lean_object* v_toPure_470_, lean_object* v_____do__lift_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7(v_e_468_, v_____do__lift_469_, v_toPure_470_, v_____do__lift_471_);
lean_dec(v_e_468_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3(lean_object* v_e_473_, lean_object* v_toPure_474_, lean_object* v_args_475_, lean_object* v_inst_476_, lean_object* v___f_477_, lean_object* v_toBind_478_, lean_object* v_____do__lift_479_){
_start:
{
lean_object* v___f_480_; size_t v_sz_481_; size_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___f_480_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7___boxed), 4, 3);
lean_closure_set(v___f_480_, 0, v_e_473_);
lean_closure_set(v___f_480_, 1, v_____do__lift_479_);
lean_closure_set(v___f_480_, 2, v_toPure_474_);
v_sz_481_ = lean_array_size(v_args_475_);
v___x_482_ = ((size_t)0ULL);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_476_, v___f_477_, v_sz_481_, v___x_482_, v_args_475_);
v___x_484_ = lean_apply_4(v_toBind_478_, lean_box(0), lean_box(0), v___x_483_, v___f_480_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8(lean_object* v_e_485_, lean_object* v_n_486_, lean_object* v_toPure_487_, lean_object* v_____do__lift_488_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp___redArg(v_e_485_, v_n_486_, v_____do__lift_488_);
v___x_490_ = lean_apply_2(v_toPure_487_, lean_box(0), v___x_489_);
return v___x_490_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(lean_object* v_e_491_, lean_object* v_____do__lift_492_, lean_object* v_i_493_, uint8_t v_updateHeader_494_, lean_object* v_toPure_495_, lean_object* v_____do__lift_496_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp___redArg(v_e_491_, v_____do__lift_492_, v_i_493_, v_updateHeader_494_, v_____do__lift_496_);
v___x_498_ = lean_apply_2(v_toPure_495_, lean_box(0), v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_491_ = stack[0].m_obj;
lean_object* v_____do__lift_492_ = stack[1].m_obj;
lean_object* v_i_493_ = stack[2].m_obj;
uint8_t v_updateHeader_494_ = stack[3].m_num;
lean_object* v_toPure_495_ = stack[4].m_obj;
lean_object* v_____do__lift_496_ = stack[5].m_obj;
lean_object* v_res_499_;
v_res_499_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(v_e_491_, v_____do__lift_492_, v_i_493_, v_updateHeader_494_, v_toPure_495_, v_____do__lift_496_);
stack->m_obj
 = v_res_499_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed(lean_object* v_e_500_, lean_object* v_____do__lift_501_, lean_object* v_i_502_, lean_object* v_updateHeader_503_, lean_object* v_toPure_504_, lean_object* v_____do__lift_505_){
_start:
{
uint8_t v_updateHeader_662__boxed_506_; lean_object* v_res_507_; 
v_updateHeader_662__boxed_506_ = lean_unbox(v_updateHeader_503_);
v_res_507_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(v_e_500_, v_____do__lift_501_, v_i_502_, v_updateHeader_662__boxed_506_, v_toPure_504_, v_____do__lift_505_);
return v_res_507_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(lean_object* v_e_508_, lean_object* v_i_509_, uint8_t v_updateHeader_510_, lean_object* v_toPure_511_, lean_object* v_args_512_, lean_object* v_inst_513_, lean_object* v___f_514_, lean_object* v_toBind_515_, lean_object* v_____do__lift_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___f_518_; size_t v_sz_519_; size_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_517_ = lean_box(v_updateHeader_510_);
v___f_518_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_518_, 0, v_e_508_);
lean_closure_set(v___f_518_, 1, v_____do__lift_516_);
lean_closure_set(v___f_518_, 2, v_i_509_);
lean_closure_set(v___f_518_, 3, v___x_517_);
lean_closure_set(v___f_518_, 4, v_toPure_511_);
v_sz_519_ = lean_array_size(v_args_512_);
v___x_520_ = ((size_t)0ULL);
v___x_521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_513_, v___f_514_, v_sz_519_, v___x_520_, v_args_512_);
v___x_522_ = lean_apply_4(v_toBind_515_, lean_box(0), lean_box(0), v___x_521_, v___f_518_);
return v___x_522_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_508_ = stack[0].m_obj;
lean_object* v_i_509_ = stack[1].m_obj;
uint8_t v_updateHeader_510_ = stack[2].m_num;
lean_object* v_toPure_511_ = stack[3].m_obj;
lean_object* v_args_512_ = stack[4].m_obj;
lean_object* v_inst_513_ = stack[5].m_obj;
lean_object* v___f_514_ = stack[6].m_obj;
lean_object* v_toBind_515_ = stack[7].m_obj;
lean_object* v_____do__lift_516_ = stack[8].m_obj;
lean_object* v_res_523_;
v_res_523_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(v_e_508_, v_i_509_, v_updateHeader_510_, v_toPure_511_, v_args_512_, v_inst_513_, v___f_514_, v_toBind_515_, v_____do__lift_516_);
stack->m_obj
 = v_res_523_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed(lean_object* v_e_524_, lean_object* v_i_525_, lean_object* v_updateHeader_526_, lean_object* v_toPure_527_, lean_object* v_args_528_, lean_object* v_inst_529_, lean_object* v___f_530_, lean_object* v_toBind_531_, lean_object* v_____do__lift_532_){
_start:
{
uint8_t v_updateHeader_687__boxed_533_; lean_object* v_res_534_; 
v_updateHeader_687__boxed_533_ = lean_unbox(v_updateHeader_526_);
v_res_534_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(v_e_524_, v_i_525_, v_updateHeader_687__boxed_533_, v_toPure_527_, v_args_528_, v_inst_529_, v___f_530_, v_toBind_531_, v_____do__lift_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6(lean_object* v_e_535_, lean_object* v_ty_536_, lean_object* v_toPure_537_, lean_object* v_____do__lift_538_){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp___redArg(v_e_535_, v_ty_536_, v_____do__lift_538_);
v___x_540_ = lean_apply_2(v_toPure_537_, lean_box(0), v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9(lean_object* v_e_541_, lean_object* v_toPure_542_, lean_object* v_____do__lift_543_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp___redArg(v_e_541_, v_____do__lift_543_);
v___x_545_ = lean_apply_2(v_toPure_542_, lean_box(0), v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10(lean_object* v_e_546_, lean_object* v_toPure_547_, lean_object* v_____do__lift_548_){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp___redArg(v_e_546_, v_____do__lift_548_);
v___x_550_ = lean_apply_2(v_toPure_547_, lean_box(0), v___x_549_);
return v___x_550_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(uint8_t v_pu_551_, lean_object* v_inst_552_, lean_object* v_f_553_, lean_object* v_e_554_){
_start:
{
lean_object* v_toApplicative_555_; lean_object* v_toBind_556_; lean_object* v_toPure_557_; lean_object* v___x_558_; lean_object* v___f_559_; lean_object* v___f_560_; lean_object* v_args_562_; lean_object* v___x_567_; lean_object* v___f_568_; lean_object* v_fvarId_570_; 
v_toApplicative_555_ = lean_ctor_get(v_inst_552_, 0);
v_toBind_556_ = lean_ctor_get(v_inst_552_, 1);
lean_inc(v_toBind_556_);
v_toPure_557_ = lean_ctor_get(v_toApplicative_555_, 1);
v___x_558_ = lean_box(v_pu_551_);
lean_inc(v_f_553_);
lean_inc_ref(v_inst_552_);
v___f_559_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_559_, 0, v___x_558_);
lean_closure_set(v___f_559_, 1, v_inst_552_);
lean_closure_set(v___f_559_, 2, v_f_553_);
lean_inc_n(v_toPure_557_, 2);
lean_inc_n(v_e_554_, 2);
v___f_560_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1), 3, 2);
lean_closure_set(v___f_560_, 0, v_e_554_);
lean_closure_set(v___f_560_, 1, v_toPure_557_);
v___x_567_ = lean_box(v_pu_551_);
v___f_568_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_568_, 0, v___x_567_);
lean_closure_set(v___f_568_, 1, v_e_554_);
lean_closure_set(v___f_568_, 2, v_toPure_557_);
switch(lean_obj_tag(v_e_554_))
{
case 2:
{
lean_object* v_struct_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec_ref(v___f_560_);
lean_dec_ref(v___f_559_);
lean_dec_ref(v_inst_552_);
v_struct_573_ = lean_ctor_get(v_e_554_, 2);
lean_inc(v_struct_573_);
lean_dec_ref_known(v_e_554_, 3);
v___x_574_ = lean_apply_1(v_f_553_, v_struct_573_);
v___x_575_ = lean_apply_4(v_toBind_556_, lean_box(0), lean_box(0), v___x_574_, v___f_568_);
return v___x_575_;
}
case 3:
{
lean_object* v_args_576_; size_t v_sz_577_; size_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec_ref(v___f_568_);
lean_dec(v_f_553_);
v_args_576_ = lean_ctor_get(v_e_554_, 2);
lean_inc_ref(v_args_576_);
lean_dec_ref_known(v_e_554_, 3);
v_sz_577_ = lean_array_size(v_args_576_);
v___x_578_ = ((size_t)0ULL);
v___x_579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_552_, v___f_559_, v_sz_577_, v___x_578_, v_args_576_);
v___x_580_ = lean_apply_4(v_toBind_556_, lean_box(0), lean_box(0), v___x_579_, v___f_560_);
return v___x_580_;
}
case 4:
{
lean_object* v_fvarId_581_; lean_object* v_args_582_; lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
lean_inc(v_toPure_557_);
lean_dec_ref(v___f_568_);
lean_dec_ref(v___f_560_);
v_fvarId_581_ = lean_ctor_get(v_e_554_, 0);
lean_inc(v_fvarId_581_);
v_args_582_ = lean_ctor_get(v_e_554_, 1);
lean_inc_ref(v_args_582_);
lean_inc(v_toBind_556_);
v___f_583_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3), 7, 6);
lean_closure_set(v___f_583_, 0, v_e_554_);
lean_closure_set(v___f_583_, 1, v_toPure_557_);
lean_closure_set(v___f_583_, 2, v_args_582_);
lean_closure_set(v___f_583_, 3, v_inst_552_);
lean_closure_set(v___f_583_, 4, v___f_559_);
lean_closure_set(v___f_583_, 5, v_toBind_556_);
v___x_584_ = lean_apply_1(v_f_553_, v_fvarId_581_);
v___x_585_ = lean_apply_4(v_toBind_556_, lean_box(0), lean_box(0), v___x_584_, v___f_583_);
return v___x_585_;
}
case 5:
{
lean_object* v_args_586_; size_t v_sz_587_; size_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec_ref(v___f_568_);
lean_dec(v_f_553_);
v_args_586_ = lean_ctor_get(v_e_554_, 1);
lean_inc_ref(v_args_586_);
lean_dec_ref_known(v_e_554_, 2);
v_sz_587_ = lean_array_size(v_args_586_);
v___x_588_ = ((size_t)0ULL);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_552_, v___f_559_, v_sz_587_, v___x_588_, v_args_586_);
v___x_590_ = lean_apply_4(v_toBind_556_, lean_box(0), lean_box(0), v___x_589_, v___f_560_);
return v___x_590_;
}
case 6:
{
lean_object* v_var_591_; 
lean_dec_ref(v___f_560_);
lean_dec_ref(v___f_559_);
lean_dec_ref(v_inst_552_);
v_var_591_ = lean_ctor_get(v_e_554_, 1);
lean_inc(v_var_591_);
lean_dec_ref_known(v_e_554_, 2);
v_fvarId_570_ = v_var_591_;
goto v___jp_569_;
}
case 7:
{
lean_object* v_var_592_; 
lean_dec_ref(v___f_560_);
lean_dec_ref(v___f_559_);
lean_dec_ref(v_inst_552_);
v_var_592_ = lean_ctor_get(v_e_554_, 1);
lean_inc(v_var_592_);
lean_dec_ref_known(v_e_554_, 2);
v_fvarId_570_ = v_var_592_;
goto v___jp_569_;
}
case 8:
{
lean_object* v_var_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec_ref(v___f_560_);
lean_dec_ref(v___f_559_);
lean_dec_ref(v_inst_552_);
v_var_593_ = lean_ctor_get(v_e_554_, 2);
lean_inc(v_var_593_);
lean_dec_ref_known(v_e_554_, 3);
v___x_594_ = lean_apply_1(v_f_553_, v_var_593_);
v___x_595_ = lean_apply_4(v_toBind_556_, lean_box(0), lean_box(0), v___x_594_, v___f_568_);
return v___x_595_;
}
case 9:
{
lean_object* v_args_596_; 
lean_dec_ref(v___f_568_);
lean_dec(v_f_553_);
v_args_596_ = lean_ctor_get(v_e_554_, 1);
lean_inc_ref(v_args_596_);
lean_dec_ref_known(v_e_554_, 2);
v_args_562_ = v_args_596_;
goto v___jp_561_;
}
case 10:
{
lean_object* v_args_597_; 
lean_dec_ref(v___f_568_);
lean_dec(v_f_553_);
v_args_597_ = lean_ctor_get(v_e_554_, 1);
lean_inc_ref(v_args_597_);
lean_dec_ref_known(v_e_554_, 2);
v_args_562_ = v_args_597_;
goto v___jp_561_;
}
case 11:
{
lean_object* v_n_598_; lean_object* v_var_599_; lean_object* v___f_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
lean_inc(v_toPure_557_);
lean_dec_ref(v___f_568_);
lean_dec_ref(v___f_560_);
lean_dec_ref(v___f_559_);
lean_dec_ref(v_inst_552_);
v_n_598_ = lean_ctor_get(v_e_554_, 0);
lean_inc(v_n_598_);
v_var_599_ = lean_ctor_get(v_e_554_, 1);
lean_inc(v_var_599_);
v___f_600_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8), 4, 3);
lean_closure_set(v___f_600_, 0, v_e_554_);
lean_closure_set(v___f_600_, 1, v_n_598_);
lean_closure_set(v___f_600_, 2, v_toPure_557_);
v___x_601_ = lean_apply_1(v_f_553_, v_var_599_);
v___x_602_ = lean_apply_4(v_toBind_556_, lean_box(0), lean_box(0), v___x_601_, v___f_600_);
return v___x_602_;
}
case 12:
{
lean_object* v_var_603_; lean_object* v_i_604_; uint8_t v_updateHeader_605_; lean_object* v_args_606_; lean_object* v___x_607_; lean_object* v___f_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_inc(v_toPure_557_);
lean_dec_ref(v___f_568_);
lean_dec_ref(v___f_560_);
v_var_603_ = lean_ctor_get(v_e_554_, 0);
lean_inc(v_var_603_);
v_i_604_ = lean_ctor_get(v_e_554_, 1);
lean_inc_ref(v_i_604_);
v_updateHeader_605_ = lean_ctor_get_uint8(v_e_554_, sizeof(void*)*3);
v_args_606_ = lean_ctor_get(v_e_554_, 2);
lean_inc_ref(v_args_606_);
v___x_607_ = lean_box(v_updateHeader_605_);
lean_inc(v_toBind_556_);
v___f_608_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_608_, 0, v_e_554_);
lean_closure_set(v___f_608_, 1, v_i_604_);
lean_closure_set(v___f_608_, 2, v___x_607_);
lean_closure_set(v___f_608_, 3, v_toPure_557_);
lean_closure_set(v___f_608_, 4, v_args_606_);
lean_closure_set(v___f_608_, 5, v_inst_552_);
lean_closure_set(v___f_608_, 6, v___f_559_);
lean_closure_set(v___f_608_, 7, v_toBind_556_);
v___x_609_ = lean_apply_1(v_f_553_, v_var_603_);
v___x_610_ = lean_apply_4(v_toBind_556_, lean_box(0), lean_box(0), v___x_609_, v___f_608_);
return v___x_610_;
}
case 13:
{
lean_object* v_ty_611_; lean_object* v_fvarId_612_; lean_object* v___f_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
lean_inc(v_toPure_557_);
lean_dec_ref(v___f_568_);
lean_dec_ref(v___f_560_);
lean_dec_ref(v___f_559_);
lean_dec_ref(v_inst_552_);
v_ty_611_ = lean_ctor_get(v_e_554_, 0);
lean_inc_ref(v_ty_611_);
v_fvarId_612_ = lean_ctor_get(v_e_554_, 1);
lean_inc(v_fvarId_612_);
v___f_613_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6), 4, 3);
lean_closure_set(v___f_613_, 0, v_e_554_);
lean_closure_set(v___f_613_, 1, v_ty_611_);
lean_closure_set(v___f_613_, 2, v_toPure_557_);
v___x_614_ = lean_apply_1(v_f_553_, v_fvarId_612_);
v___x_615_ = lean_apply_4(v_toBind_556_, lean_box(0), lean_box(0), v___x_614_, v___f_613_);
return v___x_615_;
}
case 14:
{
lean_object* v_fvarId_616_; lean_object* v___f_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_inc(v_toPure_557_);
lean_dec_ref(v___f_568_);
lean_dec_ref(v___f_560_);
lean_dec_ref(v___f_559_);
lean_dec_ref(v_inst_552_);
v_fvarId_616_ = lean_ctor_get(v_e_554_, 0);
lean_inc(v_fvarId_616_);
v___f_617_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9), 3, 2);
lean_closure_set(v___f_617_, 0, v_e_554_);
lean_closure_set(v___f_617_, 1, v_toPure_557_);
v___x_618_ = lean_apply_1(v_f_553_, v_fvarId_616_);
v___x_619_ = lean_apply_4(v_toBind_556_, lean_box(0), lean_box(0), v___x_618_, v___f_617_);
return v___x_619_;
}
case 15:
{
lean_object* v_fvarId_620_; lean_object* v___f_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
lean_inc(v_toPure_557_);
lean_dec_ref(v___f_568_);
lean_dec_ref(v___f_560_);
lean_dec_ref(v___f_559_);
lean_dec_ref(v_inst_552_);
v_fvarId_620_ = lean_ctor_get(v_e_554_, 0);
lean_inc(v_fvarId_620_);
v___f_621_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10), 3, 2);
lean_closure_set(v___f_621_, 0, v_e_554_);
lean_closure_set(v___f_621_, 1, v_toPure_557_);
v___x_622_ = lean_apply_1(v_f_553_, v_fvarId_620_);
v___x_623_ = lean_apply_4(v_toBind_556_, lean_box(0), lean_box(0), v___x_622_, v___f_621_);
return v___x_623_;
}
default: 
{
lean_object* v___x_624_; 
lean_inc(v_toPure_557_);
lean_dec_ref(v___f_568_);
lean_dec_ref(v___f_560_);
lean_dec_ref(v___f_559_);
lean_dec(v_toBind_556_);
lean_dec(v_f_553_);
lean_dec_ref(v_inst_552_);
v___x_624_ = lean_apply_2(v_toPure_557_, lean_box(0), v_e_554_);
return v___x_624_;
}
}
v___jp_561_:
{
size_t v_sz_563_; size_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_sz_563_ = lean_array_size(v_args_562_);
v___x_564_ = ((size_t)0ULL);
v___x_565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_552_, v___f_559_, v_sz_563_, v___x_564_, v_args_562_);
v___x_566_ = lean_apply_4(v_toBind_556_, lean_box(0), lean_box(0), v___x_565_, v___f_560_);
return v___x_566_;
}
v___jp_569_:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_apply_1(v_f_553_, v_fvarId_570_);
v___x_572_ = lean_apply_4(v_toBind_556_, lean_box(0), lean_box(0), v___x_571_, v___f_568_);
return v___x_572_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_551_ = stack[0].m_num;
lean_object* v_inst_552_ = stack[1].m_obj;
lean_object* v_f_553_ = stack[2].m_obj;
lean_object* v_e_554_ = stack[3].m_obj;
lean_object* v_res_625_;
v_res_625_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_551_, v_inst_552_, v_f_553_, v_e_554_);
stack->m_obj
 = v_res_625_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___boxed(lean_object* v_pu_626_, lean_object* v_inst_627_, lean_object* v_f_628_, lean_object* v_e_629_){
_start:
{
uint8_t v_pu_boxed_630_; lean_object* v_res_631_; 
v_pu_boxed_630_ = lean_unbox(v_pu_626_);
v_res_631_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_boxed_630_, v_inst_627_, v_f_628_, v_e_629_);
return v_res_631_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM(lean_object* v_m_632_, uint8_t v_pu_633_, lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_f_636_, lean_object* v_e_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_633_, v_inst_635_, v_f_636_, v_e_637_);
return v___x_638_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetValue_mapFVarM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_633_ = stack[1].m_num;
lean_object* v_inst_634_ = stack[2].m_obj;
lean_object* v_inst_635_ = stack[3].m_obj;
lean_object* v_f_636_ = stack[4].m_obj;
lean_object* v_e_637_ = stack[5].m_obj;
lean_object* v_res_639_;
v_res_639_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM(lean_box(0), v_pu_633_, v_inst_634_, v_inst_635_, v_f_636_, v_e_637_);
stack->m_obj
 = v_res_639_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___boxed(lean_object* v_m_640_, lean_object* v_pu_641_, lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_f_644_, lean_object* v_e_645_){
_start:
{
uint8_t v_pu_boxed_646_; lean_object* v_res_647_; 
v_pu_boxed_646_ = lean_unbox(v_pu_641_);
v_res_647_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM(v_m_640_, v_pu_boxed_646_, v_inst_642_, v_inst_643_, v_f_644_, v_e_645_);
lean_dec(v_inst_642_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0(lean_object* v_inst_648_, lean_object* v_f_649_, lean_object* v_x_650_, lean_object* v___y_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_648_, v_f_649_, v___y_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3(lean_object* v_args_653_, lean_object* v_toPure_654_, lean_object* v_inst_655_, lean_object* v___f_656_, lean_object* v_____r_657_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = lean_array_get_size(v_args_653_);
v___x_660_ = lean_box(0);
v___x_661_ = lean_nat_dec_lt(v___x_658_, v___x_659_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
lean_dec(v___f_656_);
lean_dec_ref(v_inst_655_);
lean_dec_ref(v_args_653_);
v___x_662_ = lean_apply_2(v_toPure_654_, lean_box(0), v___x_660_);
return v___x_662_;
}
else
{
uint8_t v___x_663_; 
v___x_663_ = lean_nat_dec_le(v___x_659_, v___x_659_);
if (v___x_663_ == 0)
{
if (v___x_661_ == 0)
{
lean_object* v___x_664_; 
lean_dec(v___f_656_);
lean_dec_ref(v_inst_655_);
lean_dec_ref(v_args_653_);
v___x_664_ = lean_apply_2(v_toPure_654_, lean_box(0), v___x_660_);
return v___x_664_;
}
else
{
size_t v___x_665_; size_t v___x_666_; lean_object* v___x_667_; 
lean_dec(v_toPure_654_);
v___x_665_ = ((size_t)0ULL);
v___x_666_ = lean_usize_of_nat(v___x_659_);
v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_655_, v___f_656_, v_args_653_, v___x_665_, v___x_666_, v___x_660_);
return v___x_667_;
}
}
else
{
size_t v___x_668_; size_t v___x_669_; lean_object* v___x_670_; 
lean_dec(v_toPure_654_);
v___x_668_ = ((size_t)0ULL);
v___x_669_ = lean_usize_of_nat(v___x_659_);
v___x_670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_655_, v___f_656_, v_args_653_, v___x_668_, v___x_669_, v___x_660_);
return v___x_670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(lean_object* v_inst_671_, lean_object* v_f_672_, lean_object* v_e_673_){
_start:
{
lean_object* v_toApplicative_674_; lean_object* v_toBind_675_; lean_object* v_toPure_676_; lean_object* v___f_677_; lean_object* v_args_679_; 
v_toApplicative_674_ = lean_ctor_get(v_inst_671_, 0);
v_toBind_675_ = lean_ctor_get(v_inst_671_, 1);
v_toPure_676_ = lean_ctor_get(v_toApplicative_674_, 1);
lean_inc(v_f_672_);
lean_inc_ref(v_inst_671_);
v___f_677_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_677_, 0, v_inst_671_);
lean_closure_set(v___f_677_, 1, v_f_672_);
switch(lean_obj_tag(v_e_673_))
{
case 2:
{
lean_object* v_struct_693_; lean_object* v___x_694_; 
lean_dec_ref(v___f_677_);
lean_dec_ref(v_inst_671_);
v_struct_693_ = lean_ctor_get(v_e_673_, 2);
lean_inc(v_struct_693_);
lean_dec_ref_known(v_e_673_, 3);
v___x_694_ = lean_apply_1(v_f_672_, v_struct_693_);
return v___x_694_;
}
case 3:
{
lean_object* v_args_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
lean_dec(v_f_672_);
v_args_695_ = lean_ctor_get(v_e_673_, 2);
lean_inc_ref(v_args_695_);
lean_dec_ref_known(v_e_673_, 3);
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = lean_array_get_size(v_args_695_);
v___x_698_ = lean_box(0);
v___x_699_ = lean_nat_dec_lt(v___x_696_, v___x_697_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
lean_inc(v_toPure_676_);
lean_dec_ref(v_args_695_);
lean_dec_ref(v___f_677_);
lean_dec_ref(v_inst_671_);
v___x_700_ = lean_apply_2(v_toPure_676_, lean_box(0), v___x_698_);
return v___x_700_;
}
else
{
uint8_t v___x_701_; 
v___x_701_ = lean_nat_dec_le(v___x_697_, v___x_697_);
if (v___x_701_ == 0)
{
if (v___x_699_ == 0)
{
lean_object* v___x_702_; 
lean_inc(v_toPure_676_);
lean_dec_ref(v_args_695_);
lean_dec_ref(v___f_677_);
lean_dec_ref(v_inst_671_);
v___x_702_ = lean_apply_2(v_toPure_676_, lean_box(0), v___x_698_);
return v___x_702_;
}
else
{
size_t v___x_703_; size_t v___x_704_; lean_object* v___x_705_; 
v___x_703_ = ((size_t)0ULL);
v___x_704_ = lean_usize_of_nat(v___x_697_);
v___x_705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_671_, v___f_677_, v_args_695_, v___x_703_, v___x_704_, v___x_698_);
return v___x_705_;
}
}
else
{
size_t v___x_706_; size_t v___x_707_; lean_object* v___x_708_; 
v___x_706_ = ((size_t)0ULL);
v___x_707_ = lean_usize_of_nat(v___x_697_);
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_671_, v___f_677_, v_args_695_, v___x_706_, v___x_707_, v___x_698_);
return v___x_708_;
}
}
}
case 4:
{
lean_object* v_fvarId_709_; lean_object* v_args_710_; lean_object* v___f_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
lean_inc(v_toPure_676_);
lean_inc(v_toBind_675_);
v_fvarId_709_ = lean_ctor_get(v_e_673_, 0);
lean_inc(v_fvarId_709_);
v_args_710_ = lean_ctor_get(v_e_673_, 1);
lean_inc_ref(v_args_710_);
lean_dec_ref_known(v_e_673_, 2);
v___f_711_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3), 5, 4);
lean_closure_set(v___f_711_, 0, v_args_710_);
lean_closure_set(v___f_711_, 1, v_toPure_676_);
lean_closure_set(v___f_711_, 2, v_inst_671_);
lean_closure_set(v___f_711_, 3, v___f_677_);
v___x_712_ = lean_apply_1(v_f_672_, v_fvarId_709_);
v___x_713_ = lean_apply_4(v_toBind_675_, lean_box(0), lean_box(0), v___x_712_, v___f_711_);
return v___x_713_;
}
case 5:
{
lean_object* v_args_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
lean_dec(v_f_672_);
v_args_714_ = lean_ctor_get(v_e_673_, 1);
lean_inc_ref(v_args_714_);
lean_dec_ref_known(v_e_673_, 2);
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = lean_array_get_size(v_args_714_);
v___x_717_ = lean_box(0);
v___x_718_ = lean_nat_dec_lt(v___x_715_, v___x_716_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
lean_inc(v_toPure_676_);
lean_dec_ref(v_args_714_);
lean_dec_ref(v___f_677_);
lean_dec_ref(v_inst_671_);
v___x_719_ = lean_apply_2(v_toPure_676_, lean_box(0), v___x_717_);
return v___x_719_;
}
else
{
uint8_t v___x_720_; 
v___x_720_ = lean_nat_dec_le(v___x_716_, v___x_716_);
if (v___x_720_ == 0)
{
if (v___x_718_ == 0)
{
lean_object* v___x_721_; 
lean_inc(v_toPure_676_);
lean_dec_ref(v_args_714_);
lean_dec_ref(v___f_677_);
lean_dec_ref(v_inst_671_);
v___x_721_ = lean_apply_2(v_toPure_676_, lean_box(0), v___x_717_);
return v___x_721_;
}
else
{
size_t v___x_722_; size_t v___x_723_; lean_object* v___x_724_; 
v___x_722_ = ((size_t)0ULL);
v___x_723_ = lean_usize_of_nat(v___x_716_);
v___x_724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_671_, v___f_677_, v_args_714_, v___x_722_, v___x_723_, v___x_717_);
return v___x_724_;
}
}
else
{
size_t v___x_725_; size_t v___x_726_; lean_object* v___x_727_; 
v___x_725_ = ((size_t)0ULL);
v___x_726_ = lean_usize_of_nat(v___x_716_);
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_671_, v___f_677_, v_args_714_, v___x_725_, v___x_726_, v___x_717_);
return v___x_727_;
}
}
}
case 6:
{
lean_object* v_var_728_; lean_object* v___x_729_; 
lean_dec_ref(v___f_677_);
lean_dec_ref(v_inst_671_);
v_var_728_ = lean_ctor_get(v_e_673_, 1);
lean_inc(v_var_728_);
lean_dec_ref_known(v_e_673_, 2);
v___x_729_ = lean_apply_1(v_f_672_, v_var_728_);
return v___x_729_;
}
case 7:
{
lean_object* v_var_730_; lean_object* v___x_731_; 
lean_dec_ref(v___f_677_);
lean_dec_ref(v_inst_671_);
v_var_730_ = lean_ctor_get(v_e_673_, 1);
lean_inc(v_var_730_);
lean_dec_ref_known(v_e_673_, 2);
v___x_731_ = lean_apply_1(v_f_672_, v_var_730_);
return v___x_731_;
}
case 8:
{
lean_object* v_var_732_; lean_object* v___x_733_; 
lean_dec_ref(v___f_677_);
lean_dec_ref(v_inst_671_);
v_var_732_ = lean_ctor_get(v_e_673_, 2);
lean_inc(v_var_732_);
lean_dec_ref_known(v_e_673_, 3);
v___x_733_ = lean_apply_1(v_f_672_, v_var_732_);
return v___x_733_;
}
case 9:
{
lean_object* v_args_734_; 
lean_dec(v_f_672_);
v_args_734_ = lean_ctor_get(v_e_673_, 1);
lean_inc_ref(v_args_734_);
lean_dec_ref_known(v_e_673_, 2);
v_args_679_ = v_args_734_;
goto v___jp_678_;
}
case 10:
{
lean_object* v_args_735_; 
lean_dec(v_f_672_);
v_args_735_ = lean_ctor_get(v_e_673_, 1);
lean_inc_ref(v_args_735_);
lean_dec_ref_known(v_e_673_, 2);
v_args_679_ = v_args_735_;
goto v___jp_678_;
}
case 11:
{
lean_object* v_var_736_; lean_object* v___x_737_; 
lean_dec_ref(v___f_677_);
lean_dec_ref(v_inst_671_);
v_var_736_ = lean_ctor_get(v_e_673_, 1);
lean_inc(v_var_736_);
lean_dec_ref_known(v_e_673_, 2);
v___x_737_ = lean_apply_1(v_f_672_, v_var_736_);
return v___x_737_;
}
case 12:
{
lean_object* v_var_738_; lean_object* v_args_739_; lean_object* v___f_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_inc(v_toPure_676_);
lean_inc(v_toBind_675_);
v_var_738_ = lean_ctor_get(v_e_673_, 0);
lean_inc(v_var_738_);
v_args_739_ = lean_ctor_get(v_e_673_, 2);
lean_inc_ref(v_args_739_);
lean_dec_ref_known(v_e_673_, 3);
v___f_740_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3), 5, 4);
lean_closure_set(v___f_740_, 0, v_args_739_);
lean_closure_set(v___f_740_, 1, v_toPure_676_);
lean_closure_set(v___f_740_, 2, v_inst_671_);
lean_closure_set(v___f_740_, 3, v___f_677_);
v___x_741_ = lean_apply_1(v_f_672_, v_var_738_);
v___x_742_ = lean_apply_4(v_toBind_675_, lean_box(0), lean_box(0), v___x_741_, v___f_740_);
return v___x_742_;
}
case 13:
{
lean_object* v_fvarId_743_; lean_object* v___x_744_; 
lean_dec_ref(v___f_677_);
lean_dec_ref(v_inst_671_);
v_fvarId_743_ = lean_ctor_get(v_e_673_, 1);
lean_inc(v_fvarId_743_);
lean_dec_ref_known(v_e_673_, 2);
v___x_744_ = lean_apply_1(v_f_672_, v_fvarId_743_);
return v___x_744_;
}
case 14:
{
lean_object* v_fvarId_745_; lean_object* v___x_746_; 
lean_dec_ref(v___f_677_);
lean_dec_ref(v_inst_671_);
v_fvarId_745_ = lean_ctor_get(v_e_673_, 0);
lean_inc(v_fvarId_745_);
lean_dec_ref_known(v_e_673_, 1);
v___x_746_ = lean_apply_1(v_f_672_, v_fvarId_745_);
return v___x_746_;
}
case 15:
{
lean_object* v_fvarId_747_; lean_object* v___x_748_; 
lean_dec_ref(v___f_677_);
lean_dec_ref(v_inst_671_);
v_fvarId_747_ = lean_ctor_get(v_e_673_, 0);
lean_inc(v_fvarId_747_);
lean_dec_ref_known(v_e_673_, 1);
v___x_748_ = lean_apply_1(v_f_672_, v_fvarId_747_);
return v___x_748_;
}
default: 
{
lean_object* v___x_749_; lean_object* v___x_750_; 
lean_inc(v_toPure_676_);
lean_dec_ref(v___f_677_);
lean_dec(v_e_673_);
lean_dec(v_f_672_);
lean_dec_ref(v_inst_671_);
v___x_749_ = lean_box(0);
v___x_750_ = lean_apply_2(v_toPure_676_, lean_box(0), v___x_749_);
return v___x_750_;
}
}
v___jp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_array_get_size(v_args_679_);
v___x_682_ = lean_box(0);
v___x_683_ = lean_nat_dec_lt(v___x_680_, v___x_681_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
lean_inc(v_toPure_676_);
lean_dec_ref(v_args_679_);
lean_dec_ref(v___f_677_);
lean_dec_ref(v_inst_671_);
v___x_684_ = lean_apply_2(v_toPure_676_, lean_box(0), v___x_682_);
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
lean_inc(v_toPure_676_);
lean_dec_ref(v_args_679_);
lean_dec_ref(v___f_677_);
lean_dec_ref(v_inst_671_);
v___x_686_ = lean_apply_2(v_toPure_676_, lean_box(0), v___x_682_);
return v___x_686_;
}
else
{
size_t v___x_687_; size_t v___x_688_; lean_object* v___x_689_; 
v___x_687_ = ((size_t)0ULL);
v___x_688_ = lean_usize_of_nat(v___x_681_);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_671_, v___f_677_, v_args_679_, v___x_687_, v___x_688_, v___x_682_);
return v___x_689_;
}
}
else
{
size_t v___x_690_; size_t v___x_691_; lean_object* v___x_692_; 
v___x_690_ = ((size_t)0ULL);
v___x_691_ = lean_usize_of_nat(v___x_681_);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_671_, v___f_677_, v_args_679_, v___x_690_, v___x_691_, v___x_682_);
return v___x_692_;
}
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM(lean_object* v_m_751_, uint8_t v_pu_752_, lean_object* v_inst_753_, lean_object* v_f_754_, lean_object* v_e_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_753_, v_f_754_, v_e_755_);
return v___x_756_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetValue_forFVarM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_752_ = stack[1].m_num;
lean_object* v_inst_753_ = stack[2].m_obj;
lean_object* v_f_754_ = stack[3].m_obj;
lean_object* v_e_755_ = stack[4].m_obj;
lean_object* v_res_757_;
v_res_757_ = l_Lean_Compiler_LCNF_LetValue_forFVarM(lean_box(0), v_pu_752_, v_inst_753_, v_f_754_, v_e_755_);
stack->m_obj
 = v_res_757_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___boxed(lean_object* v_m_758_, lean_object* v_pu_759_, lean_object* v_inst_760_, lean_object* v_f_761_, lean_object* v_e_762_){
_start:
{
uint8_t v_pu_boxed_763_; lean_object* v_res_764_; 
v_pu_boxed_763_ = lean_unbox(v_pu_759_);
v_res_764_ = l_Lean_Compiler_LCNF_LetValue_forFVarM(v_m_758_, v_pu_boxed_763_, v_inst_760_, v_f_761_, v_e_762_);
return v_res_764_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(uint8_t v_pu_765_, lean_object* v_m_766_, lean_object* v_inst_767_, lean_object* v_inst_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_765_, v_inst_768_, v___y_769_, v___y_770_);
return v___x_771_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_765_ = stack[0].m_num;
lean_object* v_inst_767_ = stack[2].m_obj;
lean_object* v_inst_768_ = stack[3].m_obj;
lean_object* v___y_769_ = stack[4].m_obj;
lean_object* v___y_770_ = stack[5].m_obj;
lean_object* v_res_772_;
v_res_772_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(v_pu_765_, lean_box(0), v_inst_767_, v_inst_768_, v___y_769_, v___y_770_);
stack->m_obj
 = v_res_772_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0___boxed(lean_object* v_pu_773_, lean_object* v_m_774_, lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
uint8_t v_pu_boxed_779_; lean_object* v_res_780_; 
v_pu_boxed_779_ = lean_unbox(v_pu_773_);
v_res_780_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(v_pu_boxed_779_, v_m_774_, v_inst_775_, v_inst_776_, v___y_777_, v___y_778_);
lean_dec(v_inst_775_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__1(lean_object* v_m_781_, lean_object* v_inst_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_782_, v___y_783_, v___y_784_);
return v___x_785_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue(uint8_t v_pu_787_){
_start:
{
lean_object* v___x_788_; lean_object* v___f_789_; lean_object* v___f_790_; lean_object* v___x_791_; 
v___x_788_ = lean_box(v_pu_787_);
v___f_789_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0___boxed), 6, 1);
lean_closure_set(v___f_789_, 0, v___x_788_);
v___f_790_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarLetValue___closed__0));
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___f_789_);
lean_ctor_set(v___x_791_, 1, v___f_790_);
return v___x_791_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarLetValue_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_787_ = stack[0].m_num;
lean_object* v_res_792_;
v_res_792_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue(v_pu_787_);
stack->m_obj
 = v_res_792_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___boxed(lean_object* v_pu_793_){
_start:
{
uint8_t v_pu_boxed_794_; lean_object* v_res_795_; 
v_pu_boxed_794_ = lean_unbox(v_pu_793_);
v_res_795_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue(v_pu_boxed_794_);
return v_res_795_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(uint8_t v_pu_796_, lean_object* v_decl_797_, lean_object* v_____do__lift_798_, lean_object* v_inst_799_, lean_object* v_____do__lift_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_box(v_pu_796_);
v___x_802_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_802_, 0, v___x_801_);
lean_closure_set(v___x_802_, 1, v_decl_797_);
lean_closure_set(v___x_802_, 2, v_____do__lift_798_);
lean_closure_set(v___x_802_, 3, v_____do__lift_800_);
v___x_803_ = lean_apply_2(v_inst_799_, lean_box(0), v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_796_ = stack[0].m_num;
lean_object* v_decl_797_ = stack[1].m_obj;
lean_object* v_____do__lift_798_ = stack[2].m_obj;
lean_object* v_inst_799_ = stack[3].m_obj;
lean_object* v_____do__lift_800_ = stack[4].m_obj;
lean_object* v_res_804_;
v_res_804_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(v_pu_796_, v_decl_797_, v_____do__lift_798_, v_inst_799_, v_____do__lift_800_);
stack->m_obj
 = v_res_804_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_805_, lean_object* v_decl_806_, lean_object* v_____do__lift_807_, lean_object* v_inst_808_, lean_object* v_____do__lift_809_){
_start:
{
uint8_t v_pu_boxed_810_; lean_object* v_res_811_; 
v_pu_boxed_810_ = lean_unbox(v_pu_805_);
v_res_811_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(v_pu_boxed_810_, v_decl_806_, v_____do__lift_807_, v_inst_808_, v_____do__lift_809_);
return v_res_811_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(uint8_t v_pu_812_, lean_object* v_decl_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_f_816_, lean_object* v_value_817_, lean_object* v_toBind_818_, lean_object* v_____do__lift_819_){
_start:
{
lean_object* v___x_820_; lean_object* v___f_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_820_ = lean_box(v_pu_812_);
v___f_821_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_821_, 0, v___x_820_);
lean_closure_set(v___f_821_, 1, v_decl_813_);
lean_closure_set(v___f_821_, 2, v_____do__lift_819_);
lean_closure_set(v___f_821_, 3, v_inst_814_);
v___x_822_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_812_, v_inst_815_, v_f_816_, v_value_817_);
v___x_823_ = lean_apply_4(v_toBind_818_, lean_box(0), lean_box(0), v___x_822_, v___f_821_);
return v___x_823_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_812_ = stack[0].m_num;
lean_object* v_decl_813_ = stack[1].m_obj;
lean_object* v_inst_814_ = stack[2].m_obj;
lean_object* v_inst_815_ = stack[3].m_obj;
lean_object* v_f_816_ = stack[4].m_obj;
lean_object* v_value_817_ = stack[5].m_obj;
lean_object* v_toBind_818_ = stack[6].m_obj;
lean_object* v_____do__lift_819_ = stack[7].m_obj;
lean_object* v_res_824_;
v_res_824_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(v_pu_812_, v_decl_813_, v_inst_814_, v_inst_815_, v_f_816_, v_value_817_, v_toBind_818_, v_____do__lift_819_);
stack->m_obj
 = v_res_824_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1___boxed(lean_object* v_pu_825_, lean_object* v_decl_826_, lean_object* v_inst_827_, lean_object* v_inst_828_, lean_object* v_f_829_, lean_object* v_value_830_, lean_object* v_toBind_831_, lean_object* v_____do__lift_832_){
_start:
{
uint8_t v_pu_boxed_833_; lean_object* v_res_834_; 
v_pu_boxed_833_ = lean_unbox(v_pu_825_);
v_res_834_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(v_pu_boxed_833_, v_decl_826_, v_inst_827_, v_inst_828_, v_f_829_, v_value_830_, v_toBind_831_, v_____do__lift_832_);
return v_res_834_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(uint8_t v_pu_835_, lean_object* v_inst_836_, lean_object* v_inst_837_, lean_object* v_f_838_, lean_object* v_decl_839_){
_start:
{
lean_object* v_toBind_840_; lean_object* v_type_841_; lean_object* v_value_842_; lean_object* v___x_843_; lean_object* v___f_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_toBind_840_ = lean_ctor_get(v_inst_837_, 1);
lean_inc_n(v_toBind_840_, 2);
v_type_841_ = lean_ctor_get(v_decl_839_, 2);
lean_inc_ref(v_type_841_);
v_value_842_ = lean_ctor_get(v_decl_839_, 3);
lean_inc(v_value_842_);
v___x_843_ = lean_box(v_pu_835_);
lean_inc(v_f_838_);
lean_inc_ref(v_inst_837_);
v___f_844_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_844_, 0, v___x_843_);
lean_closure_set(v___f_844_, 1, v_decl_839_);
lean_closure_set(v___f_844_, 2, v_inst_836_);
lean_closure_set(v___f_844_, 3, v_inst_837_);
lean_closure_set(v___f_844_, 4, v_f_838_);
lean_closure_set(v___f_844_, 5, v_value_842_);
lean_closure_set(v___f_844_, 6, v_toBind_840_);
v___x_845_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_837_, v_f_838_, v_type_841_);
v___x_846_ = lean_apply_4(v_toBind_840_, lean_box(0), lean_box(0), v___x_845_, v___f_844_);
return v___x_846_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_835_ = stack[0].m_num;
lean_object* v_inst_836_ = stack[1].m_obj;
lean_object* v_inst_837_ = stack[2].m_obj;
lean_object* v_f_838_ = stack[3].m_obj;
lean_object* v_decl_839_ = stack[4].m_obj;
lean_object* v_res_847_;
v_res_847_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_835_, v_inst_836_, v_inst_837_, v_f_838_, v_decl_839_);
stack->m_obj
 = v_res_847_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___boxed(lean_object* v_pu_848_, lean_object* v_inst_849_, lean_object* v_inst_850_, lean_object* v_f_851_, lean_object* v_decl_852_){
_start:
{
uint8_t v_pu_boxed_853_; lean_object* v_res_854_; 
v_pu_boxed_853_ = lean_unbox(v_pu_848_);
v_res_854_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_boxed_853_, v_inst_849_, v_inst_850_, v_f_851_, v_decl_852_);
return v_res_854_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM(lean_object* v_m_855_, uint8_t v_pu_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_f_859_, lean_object* v_decl_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_856_, v_inst_857_, v_inst_858_, v_f_859_, v_decl_860_);
return v___x_861_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetDecl_mapFVarM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_856_ = stack[1].m_num;
lean_object* v_inst_857_ = stack[2].m_obj;
lean_object* v_inst_858_ = stack[3].m_obj;
lean_object* v_f_859_ = stack[4].m_obj;
lean_object* v_decl_860_ = stack[5].m_obj;
lean_object* v_res_862_;
v_res_862_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM(lean_box(0), v_pu_856_, v_inst_857_, v_inst_858_, v_f_859_, v_decl_860_);
stack->m_obj
 = v_res_862_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___boxed(lean_object* v_m_863_, lean_object* v_pu_864_, lean_object* v_inst_865_, lean_object* v_inst_866_, lean_object* v_f_867_, lean_object* v_decl_868_){
_start:
{
uint8_t v_pu_boxed_869_; lean_object* v_res_870_; 
v_pu_boxed_869_ = lean_unbox(v_pu_864_);
v_res_870_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM(v_m_863_, v_pu_boxed_869_, v_inst_865_, v_inst_866_, v_f_867_, v_decl_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg___lam__0(lean_object* v_inst_871_, lean_object* v_f_872_, lean_object* v_value_873_, lean_object* v_____r_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_871_, v_f_872_, v_value_873_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(lean_object* v_inst_876_, lean_object* v_f_877_, lean_object* v_decl_878_){
_start:
{
lean_object* v_toBind_879_; lean_object* v_type_880_; lean_object* v_value_881_; lean_object* v___f_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_toBind_879_ = lean_ctor_get(v_inst_876_, 1);
lean_inc(v_toBind_879_);
v_type_880_ = lean_ctor_get(v_decl_878_, 2);
lean_inc_ref(v_type_880_);
v_value_881_ = lean_ctor_get(v_decl_878_, 3);
lean_inc(v_value_881_);
lean_dec_ref(v_decl_878_);
lean_inc(v_f_877_);
lean_inc_ref(v_inst_876_);
v___f_882_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_882_, 0, v_inst_876_);
lean_closure_set(v___f_882_, 1, v_f_877_);
lean_closure_set(v___f_882_, 2, v_value_881_);
v___x_883_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_876_, v_f_877_, v_type_880_);
v___x_884_ = lean_apply_4(v_toBind_879_, lean_box(0), lean_box(0), v___x_883_, v___f_882_);
return v___x_884_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM(lean_object* v_m_885_, uint8_t v_pu_886_, lean_object* v_inst_887_, lean_object* v_f_888_, lean_object* v_decl_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_887_, v_f_888_, v_decl_889_);
return v___x_890_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetDecl_forFVarM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_886_ = stack[1].m_num;
lean_object* v_inst_887_ = stack[2].m_obj;
lean_object* v_f_888_ = stack[3].m_obj;
lean_object* v_decl_889_ = stack[4].m_obj;
lean_object* v_res_891_;
v_res_891_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM(lean_box(0), v_pu_886_, v_inst_887_, v_f_888_, v_decl_889_);
stack->m_obj
 = v_res_891_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___boxed(lean_object* v_m_892_, lean_object* v_pu_893_, lean_object* v_inst_894_, lean_object* v_f_895_, lean_object* v_decl_896_){
_start:
{
uint8_t v_pu_boxed_897_; lean_object* v_res_898_; 
v_pu_boxed_897_ = lean_unbox(v_pu_893_);
v_res_898_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM(v_m_892_, v_pu_boxed_897_, v_inst_894_, v_f_895_, v_decl_896_);
return v_res_898_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(uint8_t v_pu_899_, lean_object* v_m_900_, lean_object* v_inst_901_, lean_object* v_inst_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_899_, v_inst_901_, v_inst_902_, v___y_903_, v___y_904_);
return v___x_905_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_899_ = stack[0].m_num;
lean_object* v_inst_901_ = stack[2].m_obj;
lean_object* v_inst_902_ = stack[3].m_obj;
lean_object* v___y_903_ = stack[4].m_obj;
lean_object* v___y_904_ = stack[5].m_obj;
lean_object* v_res_906_;
v_res_906_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(v_pu_899_, lean_box(0), v_inst_901_, v_inst_902_, v___y_903_, v___y_904_);
stack->m_obj
 = v_res_906_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0___boxed(lean_object* v_pu_907_, lean_object* v_m_908_, lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
uint8_t v_pu_boxed_913_; lean_object* v_res_914_; 
v_pu_boxed_913_ = lean_unbox(v_pu_907_);
v_res_914_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(v_pu_boxed_913_, v_m_908_, v_inst_909_, v_inst_910_, v___y_911_, v___y_912_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__1(lean_object* v_m_915_, lean_object* v_inst_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_916_, v___y_917_, v___y_918_);
return v___x_919_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(uint8_t v_pu_921_){
_start:
{
lean_object* v___x_922_; lean_object* v___f_923_; lean_object* v___f_924_; lean_object* v___x_925_; 
v___x_922_ = lean_box(v_pu_921_);
v___f_923_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0___boxed), 6, 1);
lean_closure_set(v___f_923_, 0, v___x_922_);
v___f_924_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___closed__0));
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v___f_923_);
lean_ctor_set(v___x_925_, 1, v___f_924_);
return v___x_925_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarLetDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_921_ = stack[0].m_num;
lean_object* v_res_926_;
v_res_926_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(v_pu_921_);
stack->m_obj
 = v_res_926_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___boxed(lean_object* v_pu_927_){
_start:
{
uint8_t v_pu_boxed_928_; lean_object* v_res_929_; 
v_pu_boxed_928_ = lean_unbox(v_pu_927_);
v_res_929_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(v_pu_boxed_928_);
return v_res_929_;
}
}
lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(uint8_t v_pu_930_, lean_object* v_param_931_, lean_object* v_inst_932_, lean_object* v_____do__lift_933_){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = lean_box(v_pu_930_);
v___x_935_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_935_, 0, v___x_934_);
lean_closure_set(v___x_935_, 1, v_param_931_);
lean_closure_set(v___x_935_, 2, v_____do__lift_933_);
v___x_936_ = lean_apply_2(v_inst_932_, lean_box(0), v___x_935_);
return v___x_936_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_930_ = stack[0].m_num;
lean_object* v_param_931_ = stack[1].m_obj;
lean_object* v_inst_932_ = stack[2].m_obj;
lean_object* v_____do__lift_933_ = stack[3].m_obj;
lean_object* v_res_937_;
v_res_937_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(v_pu_930_, v_param_931_, v_inst_932_, v_____do__lift_933_);
stack->m_obj
 = v_res_937_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_938_, lean_object* v_param_939_, lean_object* v_inst_940_, lean_object* v_____do__lift_941_){
_start:
{
uint8_t v_pu_boxed_942_; lean_object* v_res_943_; 
v_pu_boxed_942_ = lean_unbox(v_pu_938_);
v_res_943_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(v_pu_boxed_942_, v_param_939_, v_inst_940_, v_____do__lift_941_);
return v_res_943_;
}
}
lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(uint8_t v_pu_944_, lean_object* v_inst_945_, lean_object* v_inst_946_, lean_object* v_f_947_, lean_object* v_param_948_){
_start:
{
lean_object* v_toBind_949_; lean_object* v_type_950_; lean_object* v___x_951_; lean_object* v___f_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_toBind_949_ = lean_ctor_get(v_inst_946_, 1);
lean_inc(v_toBind_949_);
v_type_950_ = lean_ctor_get(v_param_948_, 2);
lean_inc_ref(v_type_950_);
v___x_951_ = lean_box(v_pu_944_);
v___f_952_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_952_, 0, v___x_951_);
lean_closure_set(v___f_952_, 1, v_param_948_);
lean_closure_set(v___f_952_, 2, v_inst_945_);
v___x_953_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_946_, v_f_947_, v_type_950_);
v___x_954_ = lean_apply_4(v_toBind_949_, lean_box(0), lean_box(0), v___x_953_, v___f_952_);
return v___x_954_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Param_mapFVarM___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_944_ = stack[0].m_num;
lean_object* v_inst_945_ = stack[1].m_obj;
lean_object* v_inst_946_ = stack[2].m_obj;
lean_object* v_f_947_ = stack[3].m_obj;
lean_object* v_param_948_ = stack[4].m_obj;
lean_object* v_res_955_;
v_res_955_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(v_pu_944_, v_inst_945_, v_inst_946_, v_f_947_, v_param_948_);
stack->m_obj
 = v_res_955_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___boxed(lean_object* v_pu_956_, lean_object* v_inst_957_, lean_object* v_inst_958_, lean_object* v_f_959_, lean_object* v_param_960_){
_start:
{
uint8_t v_pu_boxed_961_; lean_object* v_res_962_; 
v_pu_boxed_961_ = lean_unbox(v_pu_956_);
v_res_962_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(v_pu_boxed_961_, v_inst_957_, v_inst_958_, v_f_959_, v_param_960_);
return v_res_962_;
}
}
lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM(lean_object* v_m_963_, uint8_t v_pu_964_, lean_object* v_inst_965_, lean_object* v_inst_966_, lean_object* v_f_967_, lean_object* v_param_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(v_pu_964_, v_inst_965_, v_inst_966_, v_f_967_, v_param_968_);
return v___x_969_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Param_mapFVarM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_964_ = stack[1].m_num;
lean_object* v_inst_965_ = stack[2].m_obj;
lean_object* v_inst_966_ = stack[3].m_obj;
lean_object* v_f_967_ = stack[4].m_obj;
lean_object* v_param_968_ = stack[5].m_obj;
lean_object* v_res_970_;
v_res_970_ = l_Lean_Compiler_LCNF_Param_mapFVarM(lean_box(0), v_pu_964_, v_inst_965_, v_inst_966_, v_f_967_, v_param_968_);
stack->m_obj
 = v_res_970_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___boxed(lean_object* v_m_971_, lean_object* v_pu_972_, lean_object* v_inst_973_, lean_object* v_inst_974_, lean_object* v_f_975_, lean_object* v_param_976_){
_start:
{
uint8_t v_pu_boxed_977_; lean_object* v_res_978_; 
v_pu_boxed_977_ = lean_unbox(v_pu_972_);
v_res_978_ = l_Lean_Compiler_LCNF_Param_mapFVarM(v_m_971_, v_pu_boxed_977_, v_inst_973_, v_inst_974_, v_f_975_, v_param_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___redArg(lean_object* v_inst_979_, lean_object* v_f_980_, lean_object* v_param_981_){
_start:
{
lean_object* v_type_982_; lean_object* v___x_983_; 
v_type_982_ = lean_ctor_get(v_param_981_, 2);
lean_inc_ref(v_type_982_);
lean_dec_ref(v_param_981_);
v___x_983_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_979_, v_f_980_, v_type_982_);
return v___x_983_;
}
}
lean_object* l_Lean_Compiler_LCNF_Param_forFVarM(lean_object* v_m_984_, uint8_t v_pu_985_, lean_object* v_inst_986_, lean_object* v_f_987_, lean_object* v_param_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_986_, v_f_987_, v_param_988_);
return v___x_989_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Param_forFVarM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_985_ = stack[1].m_num;
lean_object* v_inst_986_ = stack[2].m_obj;
lean_object* v_f_987_ = stack[3].m_obj;
lean_object* v_param_988_ = stack[4].m_obj;
lean_object* v_res_990_;
v_res_990_ = l_Lean_Compiler_LCNF_Param_forFVarM(lean_box(0), v_pu_985_, v_inst_986_, v_f_987_, v_param_988_);
stack->m_obj
 = v_res_990_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___boxed(lean_object* v_m_991_, lean_object* v_pu_992_, lean_object* v_inst_993_, lean_object* v_f_994_, lean_object* v_param_995_){
_start:
{
uint8_t v_pu_boxed_996_; lean_object* v_res_997_; 
v_pu_boxed_996_ = lean_unbox(v_pu_992_);
v_res_997_ = l_Lean_Compiler_LCNF_Param_forFVarM(v_m_991_, v_pu_boxed_996_, v_inst_993_, v_f_994_, v_param_995_);
return v_res_997_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(uint8_t v_pu_998_, lean_object* v_m_999_, lean_object* v_inst_1000_, lean_object* v_inst_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(v_pu_998_, v_inst_1000_, v_inst_1001_, v___y_1002_, v___y_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_998_ = stack[0].m_num;
lean_object* v_inst_1000_ = stack[2].m_obj;
lean_object* v_inst_1001_ = stack[3].m_obj;
lean_object* v___y_1002_ = stack[4].m_obj;
lean_object* v___y_1003_ = stack[5].m_obj;
lean_object* v_res_1005_;
v_res_1005_ = l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(v_pu_998_, lean_box(0), v_inst_1000_, v_inst_1001_, v___y_1002_, v___y_1003_);
stack->m_obj
 = v_res_1005_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0___boxed(lean_object* v_pu_1006_, lean_object* v_m_1007_, lean_object* v_inst_1008_, lean_object* v_inst_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
uint8_t v_pu_boxed_1012_; lean_object* v_res_1013_; 
v_pu_boxed_1012_ = lean_unbox(v_pu_1006_);
v_res_1013_ = l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(v_pu_boxed_1012_, v_m_1007_, v_inst_1008_, v_inst_1009_, v___y_1010_, v___y_1011_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__1(lean_object* v_m_1014_, lean_object* v_inst_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_1015_, v___y_1016_, v___y_1017_);
return v___x_1018_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam(uint8_t v_pu_1020_){
_start:
{
lean_object* v___x_1021_; lean_object* v___f_1022_; lean_object* v___f_1023_; lean_object* v___x_1024_; 
v___x_1021_ = lean_box(v_pu_1020_);
v___f_1022_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1022_, 0, v___x_1021_);
v___f_1023_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarParam___closed__0));
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___f_1022_);
lean_ctor_set(v___x_1024_, 1, v___f_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarParam_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1020_ = stack[0].m_num;
lean_object* v_res_1025_;
v_res_1025_ = l_Lean_Compiler_LCNF_instTraverseFVarParam(v_pu_1020_);
stack->m_obj
 = v_res_1025_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___boxed(lean_object* v_pu_1026_){
_start:
{
uint8_t v_pu_boxed_1027_; lean_object* v_res_1028_; 
v_pu_boxed_1027_ = lean_unbox(v_pu_1026_);
v_res_1028_ = l_Lean_Compiler_LCNF_instTraverseFVarParam(v_pu_boxed_1027_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0(lean_object* v_k_1029_, lean_object* v_decl_1030_, lean_object* v_toPure_1031_, lean_object* v_decl_1032_, lean_object* v_c_1033_, lean_object* v_____do__lift_1034_){
_start:
{
size_t v___x_1035_; size_t v___x_1036_; uint8_t v___x_1037_; 
v___x_1035_ = lean_ptr_addr(v_k_1029_);
v___x_1036_ = lean_ptr_addr(v_____do__lift_1034_);
v___x_1037_ = lean_usize_dec_eq(v___x_1035_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_dec_ref(v_c_1033_);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v_decl_1030_);
lean_ctor_set(v___x_1038_, 1, v_____do__lift_1034_);
v___x_1039_ = lean_apply_2(v_toPure_1031_, lean_box(0), v___x_1038_);
return v___x_1039_;
}
else
{
size_t v___x_1040_; size_t v___x_1041_; uint8_t v___x_1042_; 
v___x_1040_ = lean_ptr_addr(v_decl_1032_);
v___x_1041_ = lean_ptr_addr(v_decl_1030_);
v___x_1042_ = lean_usize_dec_eq(v___x_1040_, v___x_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec_ref(v_c_1033_);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v_decl_1030_);
lean_ctor_set(v___x_1043_, 1, v_____do__lift_1034_);
v___x_1044_ = lean_apply_2(v_toPure_1031_, lean_box(0), v___x_1043_);
return v___x_1044_;
}
else
{
lean_object* v___x_1045_; 
lean_dec_ref(v_____do__lift_1034_);
lean_dec_ref(v_decl_1030_);
v___x_1045_ = lean_apply_2(v_toPure_1031_, lean_box(0), v_c_1033_);
return v___x_1045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed(lean_object* v_k_1046_, lean_object* v_decl_1047_, lean_object* v_toPure_1048_, lean_object* v_decl_1049_, lean_object* v_c_1050_, lean_object* v_____do__lift_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0(v_k_1046_, v_decl_1047_, v_toPure_1048_, v_decl_1049_, v_c_1050_, v_____do__lift_1051_);
lean_dec_ref(v_decl_1049_);
lean_dec_ref(v_k_1046_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(lean_object* v_fvarId_1053_, lean_object* v_____do__lift_1054_, lean_object* v_i_1055_, lean_object* v_____do__lift_1056_, lean_object* v_toPure_1057_, lean_object* v_y_1058_, lean_object* v_k_1059_, lean_object* v_c_1060_, lean_object* v_____do__lift_1061_){
_start:
{
size_t v___x_1062_; size_t v___x_1063_; uint8_t v___x_1064_; 
v___x_1062_ = lean_ptr_addr(v_fvarId_1053_);
v___x_1063_ = lean_ptr_addr(v_____do__lift_1054_);
v___x_1064_ = lean_usize_dec_eq(v___x_1062_, v___x_1063_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_dec_ref(v_c_1060_);
v___x_1065_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1065_, 0, v_____do__lift_1054_);
lean_ctor_set(v___x_1065_, 1, v_i_1055_);
lean_ctor_set(v___x_1065_, 2, v_____do__lift_1056_);
lean_ctor_set(v___x_1065_, 3, v_____do__lift_1061_);
v___x_1066_ = lean_apply_2(v_toPure_1057_, lean_box(0), v___x_1065_);
return v___x_1066_;
}
else
{
uint8_t v___x_1067_; 
v___x_1067_ = lean_nat_dec_eq(v_i_1055_, v_i_1055_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_dec_ref(v_c_1060_);
v___x_1068_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1068_, 0, v_____do__lift_1054_);
lean_ctor_set(v___x_1068_, 1, v_i_1055_);
lean_ctor_set(v___x_1068_, 2, v_____do__lift_1056_);
lean_ctor_set(v___x_1068_, 3, v_____do__lift_1061_);
v___x_1069_ = lean_apply_2(v_toPure_1057_, lean_box(0), v___x_1068_);
return v___x_1069_;
}
else
{
size_t v___x_1070_; size_t v___x_1071_; uint8_t v___x_1072_; 
v___x_1070_ = lean_ptr_addr(v_y_1058_);
v___x_1071_ = lean_ptr_addr(v_____do__lift_1056_);
v___x_1072_ = lean_usize_dec_eq(v___x_1070_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
lean_dec_ref(v_c_1060_);
v___x_1073_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1073_, 0, v_____do__lift_1054_);
lean_ctor_set(v___x_1073_, 1, v_i_1055_);
lean_ctor_set(v___x_1073_, 2, v_____do__lift_1056_);
lean_ctor_set(v___x_1073_, 3, v_____do__lift_1061_);
v___x_1074_ = lean_apply_2(v_toPure_1057_, lean_box(0), v___x_1073_);
return v___x_1074_;
}
else
{
size_t v___x_1075_; size_t v___x_1076_; uint8_t v___x_1077_; 
v___x_1075_ = lean_ptr_addr(v_k_1059_);
v___x_1076_ = lean_ptr_addr(v_____do__lift_1061_);
v___x_1077_ = lean_usize_dec_eq(v___x_1075_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
lean_dec_ref(v_c_1060_);
v___x_1078_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1078_, 0, v_____do__lift_1054_);
lean_ctor_set(v___x_1078_, 1, v_i_1055_);
lean_ctor_set(v___x_1078_, 2, v_____do__lift_1056_);
lean_ctor_set(v___x_1078_, 3, v_____do__lift_1061_);
v___x_1079_ = lean_apply_2(v_toPure_1057_, lean_box(0), v___x_1078_);
return v___x_1079_;
}
else
{
lean_object* v___x_1080_; 
lean_dec_ref(v_____do__lift_1061_);
lean_dec(v_____do__lift_1056_);
lean_dec(v_i_1055_);
lean_dec(v_____do__lift_1054_);
v___x_1080_ = lean_apply_2(v_toPure_1057_, lean_box(0), v_c_1060_);
return v___x_1080_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed(lean_object* v_fvarId_1081_, lean_object* v_____do__lift_1082_, lean_object* v_i_1083_, lean_object* v_____do__lift_1084_, lean_object* v_toPure_1085_, lean_object* v_y_1086_, lean_object* v_k_1087_, lean_object* v_c_1088_, lean_object* v_____do__lift_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(v_fvarId_1081_, v_____do__lift_1082_, v_i_1083_, v_____do__lift_1084_, v_toPure_1085_, v_y_1086_, v_k_1087_, v_c_1088_, v_____do__lift_1089_);
lean_dec_ref(v_k_1087_);
lean_dec(v_y_1086_);
lean_dec(v_fvarId_1081_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(lean_object* v_fvarId_1091_, lean_object* v_toPure_1092_, lean_object* v_c_1093_, lean_object* v_____do__lift_1094_){
_start:
{
uint8_t v___x_1095_; 
v___x_1095_ = l_Lean_instBEqFVarId_beq(v_fvarId_1091_, v_____do__lift_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec_ref(v_c_1093_);
v___x_1096_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_____do__lift_1094_);
v___x_1097_ = lean_apply_2(v_toPure_1092_, lean_box(0), v___x_1096_);
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; 
lean_dec(v_____do__lift_1094_);
v___x_1098_ = lean_apply_2(v_toPure_1092_, lean_box(0), v_c_1093_);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed(lean_object* v_fvarId_1099_, lean_object* v_toPure_1100_, lean_object* v_c_1101_, lean_object* v_____do__lift_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(v_fvarId_1099_, v_toPure_1100_, v_c_1101_, v_____do__lift_1102_);
lean_dec(v_fvarId_1099_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27(lean_object* v_fvarId_1104_, lean_object* v_____do__lift_1105_, lean_object* v_cidx_1106_, lean_object* v_toPure_1107_, lean_object* v_k_1108_, lean_object* v_c_1109_, lean_object* v_____do__lift_1110_){
_start:
{
size_t v___x_1111_; size_t v___x_1112_; uint8_t v___x_1113_; 
v___x_1111_ = lean_ptr_addr(v_fvarId_1104_);
v___x_1112_ = lean_ptr_addr(v_____do__lift_1105_);
v___x_1113_ = lean_usize_dec_eq(v___x_1111_, v___x_1112_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec_ref(v_c_1109_);
v___x_1114_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1114_, 0, v_____do__lift_1105_);
lean_ctor_set(v___x_1114_, 1, v_cidx_1106_);
lean_ctor_set(v___x_1114_, 2, v_____do__lift_1110_);
v___x_1115_ = lean_apply_2(v_toPure_1107_, lean_box(0), v___x_1114_);
return v___x_1115_;
}
else
{
uint8_t v___x_1116_; 
v___x_1116_ = lean_nat_dec_eq(v_cidx_1106_, v_cidx_1106_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_dec_ref(v_c_1109_);
v___x_1117_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1117_, 0, v_____do__lift_1105_);
lean_ctor_set(v___x_1117_, 1, v_cidx_1106_);
lean_ctor_set(v___x_1117_, 2, v_____do__lift_1110_);
v___x_1118_ = lean_apply_2(v_toPure_1107_, lean_box(0), v___x_1117_);
return v___x_1118_;
}
else
{
size_t v___x_1119_; size_t v___x_1120_; uint8_t v___x_1121_; 
v___x_1119_ = lean_ptr_addr(v_k_1108_);
v___x_1120_ = lean_ptr_addr(v_____do__lift_1110_);
v___x_1121_ = lean_usize_dec_eq(v___x_1119_, v___x_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec_ref(v_c_1109_);
v___x_1122_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1122_, 0, v_____do__lift_1105_);
lean_ctor_set(v___x_1122_, 1, v_cidx_1106_);
lean_ctor_set(v___x_1122_, 2, v_____do__lift_1110_);
v___x_1123_ = lean_apply_2(v_toPure_1107_, lean_box(0), v___x_1122_);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; 
lean_dec_ref(v_____do__lift_1110_);
lean_dec(v_cidx_1106_);
lean_dec(v_____do__lift_1105_);
v___x_1124_ = lean_apply_2(v_toPure_1107_, lean_box(0), v_c_1109_);
return v___x_1124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27___boxed(lean_object* v_fvarId_1125_, lean_object* v_____do__lift_1126_, lean_object* v_cidx_1127_, lean_object* v_toPure_1128_, lean_object* v_k_1129_, lean_object* v_c_1130_, lean_object* v_____do__lift_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27(v_fvarId_1125_, v_____do__lift_1126_, v_cidx_1127_, v_toPure_1128_, v_k_1129_, v_c_1130_, v_____do__lift_1131_);
lean_dec_ref(v_k_1129_);
lean_dec(v_fvarId_1125_);
return v_res_1132_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(lean_object* v_fvarId_1133_, lean_object* v_____do__lift_1134_, lean_object* v_n_1135_, uint8_t v_check_1136_, uint8_t v_persistent_1137_, lean_object* v_toPure_1138_, lean_object* v_k_1139_, lean_object* v_c_1140_, lean_object* v_____do__lift_1141_){
_start:
{
size_t v___x_1142_; size_t v___x_1143_; uint8_t v___x_1144_; 
v___x_1142_ = lean_ptr_addr(v_fvarId_1133_);
v___x_1143_ = lean_ptr_addr(v_____do__lift_1134_);
v___x_1144_ = lean_usize_dec_eq(v___x_1142_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec_ref(v_c_1140_);
v___x_1145_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1145_, 0, v_____do__lift_1134_);
lean_ctor_set(v___x_1145_, 1, v_n_1135_);
lean_ctor_set(v___x_1145_, 2, v_____do__lift_1141_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*3, v_check_1136_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*3 + 1, v_persistent_1137_);
v___x_1146_ = lean_apply_2(v_toPure_1138_, lean_box(0), v___x_1145_);
return v___x_1146_;
}
else
{
uint8_t v___x_1147_; 
v___x_1147_ = lean_nat_dec_eq(v_n_1135_, v_n_1135_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_dec_ref(v_c_1140_);
v___x_1148_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1148_, 0, v_____do__lift_1134_);
lean_ctor_set(v___x_1148_, 1, v_n_1135_);
lean_ctor_set(v___x_1148_, 2, v_____do__lift_1141_);
lean_ctor_set_uint8(v___x_1148_, sizeof(void*)*3, v_check_1136_);
lean_ctor_set_uint8(v___x_1148_, sizeof(void*)*3 + 1, v_persistent_1137_);
v___x_1149_ = lean_apply_2(v_toPure_1138_, lean_box(0), v___x_1148_);
return v___x_1149_;
}
else
{
size_t v___x_1150_; size_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1150_ = lean_ptr_addr(v_k_1139_);
v___x_1151_ = lean_ptr_addr(v_____do__lift_1141_);
v___x_1152_ = lean_usize_dec_eq(v___x_1150_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec_ref(v_c_1140_);
v___x_1153_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1153_, 0, v_____do__lift_1134_);
lean_ctor_set(v___x_1153_, 1, v_n_1135_);
lean_ctor_set(v___x_1153_, 2, v_____do__lift_1141_);
lean_ctor_set_uint8(v___x_1153_, sizeof(void*)*3, v_check_1136_);
lean_ctor_set_uint8(v___x_1153_, sizeof(void*)*3 + 1, v_persistent_1137_);
v___x_1154_ = lean_apply_2(v_toPure_1138_, lean_box(0), v___x_1153_);
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; 
lean_dec_ref(v_____do__lift_1141_);
lean_dec(v_n_1135_);
lean_dec(v_____do__lift_1134_);
v___x_1155_ = lean_apply_2(v_toPure_1138_, lean_box(0), v_c_1140_);
return v___x_1155_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1133_ = stack[0].m_obj;
lean_object* v_____do__lift_1134_ = stack[1].m_obj;
lean_object* v_n_1135_ = stack[2].m_obj;
uint8_t v_check_1136_ = stack[3].m_num;
uint8_t v_persistent_1137_ = stack[4].m_num;
lean_object* v_toPure_1138_ = stack[5].m_obj;
lean_object* v_k_1139_ = stack[6].m_obj;
lean_object* v_c_1140_ = stack[7].m_obj;
lean_object* v_____do__lift_1141_ = stack[8].m_obj;
lean_object* v_res_1156_;
v_res_1156_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(v_fvarId_1133_, v_____do__lift_1134_, v_n_1135_, v_check_1136_, v_persistent_1137_, v_toPure_1138_, v_k_1139_, v_c_1140_, v_____do__lift_1141_);
stack->m_obj
 = v_res_1156_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29___boxed(lean_object* v_fvarId_1157_, lean_object* v_____do__lift_1158_, lean_object* v_n_1159_, lean_object* v_check_1160_, lean_object* v_persistent_1161_, lean_object* v_toPure_1162_, lean_object* v_k_1163_, lean_object* v_c_1164_, lean_object* v_____do__lift_1165_){
_start:
{
uint8_t v_check_2055__boxed_1166_; uint8_t v_persistent_2056__boxed_1167_; lean_object* v_res_1168_; 
v_check_2055__boxed_1166_ = lean_unbox(v_check_1160_);
v_persistent_2056__boxed_1167_ = lean_unbox(v_persistent_1161_);
v_res_1168_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(v_fvarId_1157_, v_____do__lift_1158_, v_n_1159_, v_check_2055__boxed_1166_, v_persistent_2056__boxed_1167_, v_toPure_1162_, v_k_1163_, v_c_1164_, v_____do__lift_1165_);
lean_dec_ref(v_k_1163_);
lean_dec(v_fvarId_1157_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(lean_object* v_fvarId_1169_, lean_object* v_____do__lift_1170_, lean_object* v_i_1171_, lean_object* v_offset_1172_, lean_object* v_____do__lift_1173_, lean_object* v_____do__lift_1174_, lean_object* v_toPure_1175_, lean_object* v_y_1176_, lean_object* v_ty_1177_, lean_object* v_k_1178_, lean_object* v_c_1179_, lean_object* v_____do__lift_1180_){
_start:
{
size_t v___x_1181_; size_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1181_ = lean_ptr_addr(v_fvarId_1169_);
v___x_1182_ = lean_ptr_addr(v_____do__lift_1170_);
v___x_1183_ = lean_usize_dec_eq(v___x_1181_, v___x_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec_ref(v_c_1179_);
v___x_1184_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1184_, 0, v_____do__lift_1170_);
lean_ctor_set(v___x_1184_, 1, v_i_1171_);
lean_ctor_set(v___x_1184_, 2, v_offset_1172_);
lean_ctor_set(v___x_1184_, 3, v_____do__lift_1173_);
lean_ctor_set(v___x_1184_, 4, v_____do__lift_1174_);
lean_ctor_set(v___x_1184_, 5, v_____do__lift_1180_);
v___x_1185_ = lean_apply_2(v_toPure_1175_, lean_box(0), v___x_1184_);
return v___x_1185_;
}
else
{
uint8_t v___x_1186_; 
v___x_1186_ = lean_nat_dec_eq(v_i_1171_, v_i_1171_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec_ref(v_c_1179_);
v___x_1187_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1187_, 0, v_____do__lift_1170_);
lean_ctor_set(v___x_1187_, 1, v_i_1171_);
lean_ctor_set(v___x_1187_, 2, v_offset_1172_);
lean_ctor_set(v___x_1187_, 3, v_____do__lift_1173_);
lean_ctor_set(v___x_1187_, 4, v_____do__lift_1174_);
lean_ctor_set(v___x_1187_, 5, v_____do__lift_1180_);
v___x_1188_ = lean_apply_2(v_toPure_1175_, lean_box(0), v___x_1187_);
return v___x_1188_;
}
else
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_nat_dec_eq(v_offset_1172_, v_offset_1172_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_dec_ref(v_c_1179_);
v___x_1190_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1190_, 0, v_____do__lift_1170_);
lean_ctor_set(v___x_1190_, 1, v_i_1171_);
lean_ctor_set(v___x_1190_, 2, v_offset_1172_);
lean_ctor_set(v___x_1190_, 3, v_____do__lift_1173_);
lean_ctor_set(v___x_1190_, 4, v_____do__lift_1174_);
lean_ctor_set(v___x_1190_, 5, v_____do__lift_1180_);
v___x_1191_ = lean_apply_2(v_toPure_1175_, lean_box(0), v___x_1190_);
return v___x_1191_;
}
else
{
size_t v___x_1192_; size_t v___x_1193_; uint8_t v___x_1194_; 
v___x_1192_ = lean_ptr_addr(v_y_1176_);
v___x_1193_ = lean_ptr_addr(v_____do__lift_1173_);
v___x_1194_ = lean_usize_dec_eq(v___x_1192_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec_ref(v_c_1179_);
v___x_1195_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1195_, 0, v_____do__lift_1170_);
lean_ctor_set(v___x_1195_, 1, v_i_1171_);
lean_ctor_set(v___x_1195_, 2, v_offset_1172_);
lean_ctor_set(v___x_1195_, 3, v_____do__lift_1173_);
lean_ctor_set(v___x_1195_, 4, v_____do__lift_1174_);
lean_ctor_set(v___x_1195_, 5, v_____do__lift_1180_);
v___x_1196_ = lean_apply_2(v_toPure_1175_, lean_box(0), v___x_1195_);
return v___x_1196_;
}
else
{
size_t v___x_1197_; size_t v___x_1198_; uint8_t v___x_1199_; 
v___x_1197_ = lean_ptr_addr(v_ty_1177_);
v___x_1198_ = lean_ptr_addr(v_____do__lift_1174_);
v___x_1199_ = lean_usize_dec_eq(v___x_1197_, v___x_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_dec_ref(v_c_1179_);
v___x_1200_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1200_, 0, v_____do__lift_1170_);
lean_ctor_set(v___x_1200_, 1, v_i_1171_);
lean_ctor_set(v___x_1200_, 2, v_offset_1172_);
lean_ctor_set(v___x_1200_, 3, v_____do__lift_1173_);
lean_ctor_set(v___x_1200_, 4, v_____do__lift_1174_);
lean_ctor_set(v___x_1200_, 5, v_____do__lift_1180_);
v___x_1201_ = lean_apply_2(v_toPure_1175_, lean_box(0), v___x_1200_);
return v___x_1201_;
}
else
{
size_t v___x_1202_; size_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1202_ = lean_ptr_addr(v_k_1178_);
v___x_1203_ = lean_ptr_addr(v_____do__lift_1180_);
v___x_1204_ = lean_usize_dec_eq(v___x_1202_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec_ref(v_c_1179_);
v___x_1205_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1205_, 0, v_____do__lift_1170_);
lean_ctor_set(v___x_1205_, 1, v_i_1171_);
lean_ctor_set(v___x_1205_, 2, v_offset_1172_);
lean_ctor_set(v___x_1205_, 3, v_____do__lift_1173_);
lean_ctor_set(v___x_1205_, 4, v_____do__lift_1174_);
lean_ctor_set(v___x_1205_, 5, v_____do__lift_1180_);
v___x_1206_ = lean_apply_2(v_toPure_1175_, lean_box(0), v___x_1205_);
return v___x_1206_;
}
else
{
lean_object* v___x_1207_; 
lean_dec_ref(v_____do__lift_1180_);
lean_dec_ref(v_____do__lift_1174_);
lean_dec(v_____do__lift_1173_);
lean_dec(v_offset_1172_);
lean_dec(v_i_1171_);
lean_dec(v_____do__lift_1170_);
v___x_1207_ = lean_apply_2(v_toPure_1175_, lean_box(0), v_c_1179_);
return v___x_1207_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed(lean_object* v_fvarId_1208_, lean_object* v_____do__lift_1209_, lean_object* v_i_1210_, lean_object* v_offset_1211_, lean_object* v_____do__lift_1212_, lean_object* v_____do__lift_1213_, lean_object* v_toPure_1214_, lean_object* v_y_1215_, lean_object* v_ty_1216_, lean_object* v_k_1217_, lean_object* v_c_1218_, lean_object* v_____do__lift_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(v_fvarId_1208_, v_____do__lift_1209_, v_i_1210_, v_offset_1211_, v_____do__lift_1212_, v_____do__lift_1213_, v_toPure_1214_, v_y_1215_, v_ty_1216_, v_k_1217_, v_c_1218_, v_____do__lift_1219_);
lean_dec_ref(v_k_1217_);
lean_dec_ref(v_ty_1216_);
lean_dec(v_y_1215_);
lean_dec(v_fvarId_1208_);
return v_res_1220_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(uint8_t v_pu_1221_, lean_object* v_decl_1222_, lean_object* v_____do__lift_1223_, lean_object* v_params_1224_, lean_object* v_inst_1225_, lean_object* v_toBind_1226_, lean_object* v___f_1227_, lean_object* v_____do__lift_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1229_ = lean_box(v_pu_1221_);
v___x_1230_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed), 10, 5);
lean_closure_set(v___x_1230_, 0, v___x_1229_);
lean_closure_set(v___x_1230_, 1, v_decl_1222_);
lean_closure_set(v___x_1230_, 2, v_____do__lift_1223_);
lean_closure_set(v___x_1230_, 3, v_params_1224_);
lean_closure_set(v___x_1230_, 4, v_____do__lift_1228_);
v___x_1231_ = lean_apply_2(v_inst_1225_, lean_box(0), v___x_1230_);
v___x_1232_ = lean_apply_4(v_toBind_1226_, lean_box(0), lean_box(0), v___x_1231_, v___f_1227_);
return v___x_1232_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1221_ = stack[0].m_num;
lean_object* v_decl_1222_ = stack[1].m_obj;
lean_object* v_____do__lift_1223_ = stack[2].m_obj;
lean_object* v_params_1224_ = stack[3].m_obj;
lean_object* v_inst_1225_ = stack[4].m_obj;
lean_object* v_toBind_1226_ = stack[5].m_obj;
lean_object* v___f_1227_ = stack[6].m_obj;
lean_object* v_____do__lift_1228_ = stack[7].m_obj;
lean_object* v_res_1233_;
v_res_1233_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(v_pu_1221_, v_decl_1222_, v_____do__lift_1223_, v_params_1224_, v_inst_1225_, v_toBind_1226_, v___f_1227_, v_____do__lift_1228_);
stack->m_obj
 = v_res_1233_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed(lean_object* v_pu_1234_, lean_object* v_decl_1235_, lean_object* v_____do__lift_1236_, lean_object* v_params_1237_, lean_object* v_inst_1238_, lean_object* v_toBind_1239_, lean_object* v___f_1240_, lean_object* v_____do__lift_1241_){
_start:
{
uint8_t v_pu_boxed_1242_; lean_object* v_res_1243_; 
v_pu_boxed_1242_ = lean_unbox(v_pu_1234_);
v_res_1243_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(v_pu_boxed_1242_, v_decl_1235_, v_____do__lift_1236_, v_params_1237_, v_inst_1238_, v_toBind_1239_, v___f_1240_, v_____do__lift_1241_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(lean_object* v_____do__lift_1244_, lean_object* v_toPure_1245_, lean_object* v_c_1246_, lean_object* v_fvarId_1247_, lean_object* v_args_1248_, lean_object* v_____do__lift_1249_){
_start:
{
uint8_t v___y_1251_; uint8_t v___x_1255_; 
v___x_1255_ = l_Lean_instBEqFVarId_beq(v_fvarId_1247_, v_____do__lift_1244_);
if (v___x_1255_ == 0)
{
v___y_1251_ = v___x_1255_;
goto v___jp_1250_;
}
else
{
size_t v___x_1256_; size_t v___x_1257_; uint8_t v___x_1258_; 
v___x_1256_ = lean_ptr_addr(v_args_1248_);
v___x_1257_ = lean_ptr_addr(v_____do__lift_1249_);
v___x_1258_ = lean_usize_dec_eq(v___x_1256_, v___x_1257_);
v___y_1251_ = v___x_1258_;
goto v___jp_1250_;
}
v___jp_1250_:
{
if (v___y_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec_ref(v_c_1246_);
v___x_1252_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_____do__lift_1244_);
lean_ctor_set(v___x_1252_, 1, v_____do__lift_1249_);
v___x_1253_ = lean_apply_2(v_toPure_1245_, lean_box(0), v___x_1252_);
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; 
lean_dec_ref(v_____do__lift_1249_);
lean_dec(v_____do__lift_1244_);
v___x_1254_ = lean_apply_2(v_toPure_1245_, lean_box(0), v_c_1246_);
return v___x_1254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed(lean_object* v_____do__lift_1259_, lean_object* v_toPure_1260_, lean_object* v_c_1261_, lean_object* v_fvarId_1262_, lean_object* v_args_1263_, lean_object* v_____do__lift_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(v_____do__lift_1259_, v_toPure_1260_, v_c_1261_, v_fvarId_1262_, v_args_1263_, v_____do__lift_1264_);
lean_dec_ref(v_args_1263_);
lean_dec(v_fvarId_1262_);
return v_res_1265_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(lean_object* v_toPure_1266_, lean_object* v_c_1267_, lean_object* v_fvarId_1268_, lean_object* v_args_1269_, uint8_t v_pu_1270_, lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_f_1273_, lean_object* v_toBind_1274_, lean_object* v_____do__lift_1275_){
_start:
{
lean_object* v___f_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; size_t v_sz_1279_; size_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_inc_ref(v_args_1269_);
v___f_1276_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed), 6, 5);
lean_closure_set(v___f_1276_, 0, v_____do__lift_1275_);
lean_closure_set(v___f_1276_, 1, v_toPure_1266_);
lean_closure_set(v___f_1276_, 2, v_c_1267_);
lean_closure_set(v___f_1276_, 3, v_fvarId_1268_);
lean_closure_set(v___f_1276_, 4, v_args_1269_);
v___x_1277_ = lean_box(v_pu_1270_);
lean_inc_ref(v_inst_1272_);
v___x_1278_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Arg_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_1278_, 0, lean_box(0));
lean_closure_set(v___x_1278_, 1, v___x_1277_);
lean_closure_set(v___x_1278_, 2, v_inst_1271_);
lean_closure_set(v___x_1278_, 3, v_inst_1272_);
lean_closure_set(v___x_1278_, 4, v_f_1273_);
v_sz_1279_ = lean_array_size(v_args_1269_);
v___x_1280_ = ((size_t)0ULL);
v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1272_, v___x_1278_, v_sz_1279_, v___x_1280_, v_args_1269_);
v___x_1282_ = lean_apply_4(v_toBind_1274_, lean_box(0), lean_box(0), v___x_1281_, v___f_1276_);
return v___x_1282_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_1266_ = stack[0].m_obj;
lean_object* v_c_1267_ = stack[1].m_obj;
lean_object* v_fvarId_1268_ = stack[2].m_obj;
lean_object* v_args_1269_ = stack[3].m_obj;
uint8_t v_pu_1270_ = stack[4].m_num;
lean_object* v_inst_1271_ = stack[5].m_obj;
lean_object* v_inst_1272_ = stack[6].m_obj;
lean_object* v_f_1273_ = stack[7].m_obj;
lean_object* v_toBind_1274_ = stack[8].m_obj;
lean_object* v_____do__lift_1275_ = stack[9].m_obj;
lean_object* v_res_1283_;
v_res_1283_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(v_toPure_1266_, v_c_1267_, v_fvarId_1268_, v_args_1269_, v_pu_1270_, v_inst_1271_, v_inst_1272_, v_f_1273_, v_toBind_1274_, v_____do__lift_1275_);
stack->m_obj
 = v_res_1283_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed(lean_object* v_toPure_1284_, lean_object* v_c_1285_, lean_object* v_fvarId_1286_, lean_object* v_args_1287_, lean_object* v_pu_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_f_1291_, lean_object* v_toBind_1292_, lean_object* v_____do__lift_1293_){
_start:
{
uint8_t v_pu_boxed_1294_; lean_object* v_res_1295_; 
v_pu_boxed_1294_ = lean_unbox(v_pu_1288_);
v_res_1295_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(v_toPure_1284_, v_c_1285_, v_fvarId_1286_, v_args_1287_, v_pu_boxed_1294_, v_inst_1289_, v_inst_1290_, v_f_1291_, v_toBind_1292_, v_____do__lift_1293_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(lean_object* v_typeName_1296_, lean_object* v_____do__lift_1297_, lean_object* v_____do__lift_1298_, lean_object* v_toPure_1299_, lean_object* v_alts_1300_, lean_object* v_resultType_1301_, lean_object* v_discr_1302_, lean_object* v_c_1303_, lean_object* v_____do__lift_1304_){
_start:
{
size_t v___x_1309_; size_t v___x_1310_; uint8_t v___x_1311_; 
v___x_1309_ = lean_ptr_addr(v_alts_1300_);
v___x_1310_ = lean_ptr_addr(v_____do__lift_1304_);
v___x_1311_ = lean_usize_dec_eq(v___x_1309_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_dec_ref(v_c_1303_);
goto v___jp_1305_;
}
else
{
size_t v___x_1312_; size_t v___x_1313_; uint8_t v___x_1314_; 
v___x_1312_ = lean_ptr_addr(v_resultType_1301_);
v___x_1313_ = lean_ptr_addr(v_____do__lift_1297_);
v___x_1314_ = lean_usize_dec_eq(v___x_1312_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_dec_ref(v_c_1303_);
goto v___jp_1305_;
}
else
{
uint8_t v___x_1315_; 
v___x_1315_ = l_Lean_instBEqFVarId_beq(v_discr_1302_, v_____do__lift_1298_);
if (v___x_1315_ == 0)
{
lean_dec_ref(v_c_1303_);
goto v___jp_1305_;
}
else
{
lean_object* v___x_1316_; 
lean_dec_ref(v_____do__lift_1304_);
lean_dec(v_____do__lift_1298_);
lean_dec_ref(v_____do__lift_1297_);
lean_dec(v_typeName_1296_);
v___x_1316_ = lean_apply_2(v_toPure_1299_, lean_box(0), v_c_1303_);
return v___x_1316_;
}
}
}
v___jp_1305_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1306_, 0, v_typeName_1296_);
lean_ctor_set(v___x_1306_, 1, v_____do__lift_1297_);
lean_ctor_set(v___x_1306_, 2, v_____do__lift_1298_);
lean_ctor_set(v___x_1306_, 3, v_____do__lift_1304_);
v___x_1307_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
v___x_1308_ = lean_apply_2(v_toPure_1299_, lean_box(0), v___x_1307_);
return v___x_1308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed(lean_object* v_typeName_1317_, lean_object* v_____do__lift_1318_, lean_object* v_____do__lift_1319_, lean_object* v_toPure_1320_, lean_object* v_alts_1321_, lean_object* v_resultType_1322_, lean_object* v_discr_1323_, lean_object* v_c_1324_, lean_object* v_____do__lift_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(v_typeName_1317_, v_____do__lift_1318_, v_____do__lift_1319_, v_toPure_1320_, v_alts_1321_, v_resultType_1322_, v_discr_1323_, v_c_1324_, v_____do__lift_1325_);
lean_dec(v_discr_1323_);
lean_dec_ref(v_resultType_1322_);
lean_dec_ref(v_alts_1321_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13(lean_object* v_typeName_1327_, lean_object* v_____do__lift_1328_, lean_object* v_toPure_1329_, lean_object* v_alts_1330_, lean_object* v_resultType_1331_, lean_object* v_discr_1332_, lean_object* v_c_1333_, lean_object* v_inst_1334_, lean_object* v___f_1335_, lean_object* v_toBind_1336_, lean_object* v_____do__lift_1337_){
_start:
{
lean_object* v___f_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_inc_ref(v_alts_1330_);
v___f_1338_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed), 9, 8);
lean_closure_set(v___f_1338_, 0, v_typeName_1327_);
lean_closure_set(v___f_1338_, 1, v_____do__lift_1328_);
lean_closure_set(v___f_1338_, 2, v_____do__lift_1337_);
lean_closure_set(v___f_1338_, 3, v_toPure_1329_);
lean_closure_set(v___f_1338_, 4, v_alts_1330_);
lean_closure_set(v___f_1338_, 5, v_resultType_1331_);
lean_closure_set(v___f_1338_, 6, v_discr_1332_);
lean_closure_set(v___f_1338_, 7, v_c_1333_);
v___x_1339_ = lean_unsigned_to_nat(0u);
v___x_1340_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_1334_, v___f_1335_, v___x_1339_, v_alts_1330_);
v___x_1341_ = lean_apply_4(v_toBind_1336_, lean_box(0), lean_box(0), v___x_1340_, v___f_1338_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14(lean_object* v_typeName_1342_, lean_object* v_toPure_1343_, lean_object* v_alts_1344_, lean_object* v_resultType_1345_, lean_object* v_discr_1346_, lean_object* v_c_1347_, lean_object* v_inst_1348_, lean_object* v___f_1349_, lean_object* v_toBind_1350_, lean_object* v_f_1351_, lean_object* v_____do__lift_1352_){
_start:
{
lean_object* v___f_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_inc(v_toBind_1350_);
lean_inc(v_discr_1346_);
v___f_1353_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13), 11, 10);
lean_closure_set(v___f_1353_, 0, v_typeName_1342_);
lean_closure_set(v___f_1353_, 1, v_____do__lift_1352_);
lean_closure_set(v___f_1353_, 2, v_toPure_1343_);
lean_closure_set(v___f_1353_, 3, v_alts_1344_);
lean_closure_set(v___f_1353_, 4, v_resultType_1345_);
lean_closure_set(v___f_1353_, 5, v_discr_1346_);
lean_closure_set(v___f_1353_, 6, v_c_1347_);
lean_closure_set(v___f_1353_, 7, v_inst_1348_);
lean_closure_set(v___f_1353_, 8, v___f_1349_);
lean_closure_set(v___f_1353_, 9, v_toBind_1350_);
v___x_1354_ = lean_apply_1(v_f_1351_, v_discr_1346_);
v___x_1355_ = lean_apply_4(v_toBind_1350_, lean_box(0), lean_box(0), v___x_1354_, v___f_1353_);
return v___x_1355_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(lean_object* v_fvarId_1356_, lean_object* v_____do__lift_1357_, lean_object* v_n_1358_, uint8_t v_check_1359_, uint8_t v_persistent_1360_, lean_object* v_objs_x3f_1361_, lean_object* v_toPure_1362_, lean_object* v_k_1363_, lean_object* v_c_1364_, lean_object* v_____do__lift_1365_){
_start:
{
size_t v___x_1366_; size_t v___x_1367_; uint8_t v___x_1368_; 
v___x_1366_ = lean_ptr_addr(v_fvarId_1356_);
v___x_1367_ = lean_ptr_addr(v_____do__lift_1357_);
v___x_1368_ = lean_usize_dec_eq(v___x_1366_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_dec_ref(v_c_1364_);
v___x_1369_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1369_, 0, v_____do__lift_1357_);
lean_ctor_set(v___x_1369_, 1, v_n_1358_);
lean_ctor_set(v___x_1369_, 2, v_objs_x3f_1361_);
lean_ctor_set(v___x_1369_, 3, v_____do__lift_1365_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*4, v_check_1359_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*4 + 1, v_persistent_1360_);
v___x_1370_ = lean_apply_2(v_toPure_1362_, lean_box(0), v___x_1369_);
return v___x_1370_;
}
else
{
uint8_t v___x_1371_; 
v___x_1371_ = lean_nat_dec_eq(v_n_1358_, v_n_1358_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_dec_ref(v_c_1364_);
v___x_1372_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1372_, 0, v_____do__lift_1357_);
lean_ctor_set(v___x_1372_, 1, v_n_1358_);
lean_ctor_set(v___x_1372_, 2, v_objs_x3f_1361_);
lean_ctor_set(v___x_1372_, 3, v_____do__lift_1365_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*4, v_check_1359_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*4 + 1, v_persistent_1360_);
v___x_1373_ = lean_apply_2(v_toPure_1362_, lean_box(0), v___x_1372_);
return v___x_1373_;
}
else
{
size_t v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = lean_ptr_addr(v_objs_x3f_1361_);
v___x_1375_ = lean_usize_dec_eq(v___x_1374_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec_ref(v_c_1364_);
v___x_1376_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1376_, 0, v_____do__lift_1357_);
lean_ctor_set(v___x_1376_, 1, v_n_1358_);
lean_ctor_set(v___x_1376_, 2, v_objs_x3f_1361_);
lean_ctor_set(v___x_1376_, 3, v_____do__lift_1365_);
lean_ctor_set_uint8(v___x_1376_, sizeof(void*)*4, v_check_1359_);
lean_ctor_set_uint8(v___x_1376_, sizeof(void*)*4 + 1, v_persistent_1360_);
v___x_1377_ = lean_apply_2(v_toPure_1362_, lean_box(0), v___x_1376_);
return v___x_1377_;
}
else
{
size_t v___x_1378_; size_t v___x_1379_; uint8_t v___x_1380_; 
v___x_1378_ = lean_ptr_addr(v_k_1363_);
v___x_1379_ = lean_ptr_addr(v_____do__lift_1365_);
v___x_1380_ = lean_usize_dec_eq(v___x_1378_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_dec_ref(v_c_1364_);
v___x_1381_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1381_, 0, v_____do__lift_1357_);
lean_ctor_set(v___x_1381_, 1, v_n_1358_);
lean_ctor_set(v___x_1381_, 2, v_objs_x3f_1361_);
lean_ctor_set(v___x_1381_, 3, v_____do__lift_1365_);
lean_ctor_set_uint8(v___x_1381_, sizeof(void*)*4, v_check_1359_);
lean_ctor_set_uint8(v___x_1381_, sizeof(void*)*4 + 1, v_persistent_1360_);
v___x_1382_ = lean_apply_2(v_toPure_1362_, lean_box(0), v___x_1381_);
return v___x_1382_;
}
else
{
lean_object* v___x_1383_; 
lean_dec_ref(v_____do__lift_1365_);
lean_dec(v_objs_x3f_1361_);
lean_dec(v_n_1358_);
lean_dec(v_____do__lift_1357_);
v___x_1383_ = lean_apply_2(v_toPure_1362_, lean_box(0), v_c_1364_);
return v___x_1383_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1356_ = stack[0].m_obj;
lean_object* v_____do__lift_1357_ = stack[1].m_obj;
lean_object* v_n_1358_ = stack[2].m_obj;
uint8_t v_check_1359_ = stack[3].m_num;
uint8_t v_persistent_1360_ = stack[4].m_num;
lean_object* v_objs_x3f_1361_ = stack[5].m_obj;
lean_object* v_toPure_1362_ = stack[6].m_obj;
lean_object* v_k_1363_ = stack[7].m_obj;
lean_object* v_c_1364_ = stack[8].m_obj;
lean_object* v_____do__lift_1365_ = stack[9].m_obj;
lean_object* v_res_1384_;
v_res_1384_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(v_fvarId_1356_, v_____do__lift_1357_, v_n_1358_, v_check_1359_, v_persistent_1360_, v_objs_x3f_1361_, v_toPure_1362_, v_k_1363_, v_c_1364_, v_____do__lift_1365_);
stack->m_obj
 = v_res_1384_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed(lean_object* v_fvarId_1385_, lean_object* v_____do__lift_1386_, lean_object* v_n_1387_, lean_object* v_check_1388_, lean_object* v_persistent_1389_, lean_object* v_objs_x3f_1390_, lean_object* v_toPure_1391_, lean_object* v_k_1392_, lean_object* v_c_1393_, lean_object* v_____do__lift_1394_){
_start:
{
uint8_t v_check_2527__boxed_1395_; uint8_t v_persistent_2528__boxed_1396_; lean_object* v_res_1397_; 
v_check_2527__boxed_1395_ = lean_unbox(v_check_1388_);
v_persistent_2528__boxed_1396_ = lean_unbox(v_persistent_1389_);
v_res_1397_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(v_fvarId_1385_, v_____do__lift_1386_, v_n_1387_, v_check_2527__boxed_1395_, v_persistent_2528__boxed_1396_, v_objs_x3f_1390_, v_toPure_1391_, v_k_1392_, v_c_1393_, v_____do__lift_1394_);
lean_dec_ref(v_k_1392_);
lean_dec(v_fvarId_1385_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(lean_object* v_k_1398_, lean_object* v_decl_1399_, lean_object* v_toPure_1400_, lean_object* v_decl_1401_, lean_object* v_c_1402_, lean_object* v_____do__lift_1403_){
_start:
{
size_t v___x_1404_; size_t v___x_1405_; uint8_t v___x_1406_; 
v___x_1404_ = lean_ptr_addr(v_k_1398_);
v___x_1405_ = lean_ptr_addr(v_____do__lift_1403_);
v___x_1406_ = lean_usize_dec_eq(v___x_1404_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_dec_ref(v_c_1402_);
v___x_1407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1407_, 0, v_decl_1399_);
lean_ctor_set(v___x_1407_, 1, v_____do__lift_1403_);
v___x_1408_ = lean_apply_2(v_toPure_1400_, lean_box(0), v___x_1407_);
return v___x_1408_;
}
else
{
size_t v___x_1409_; size_t v___x_1410_; uint8_t v___x_1411_; 
v___x_1409_ = lean_ptr_addr(v_decl_1401_);
v___x_1410_ = lean_ptr_addr(v_decl_1399_);
v___x_1411_ = lean_usize_dec_eq(v___x_1409_, v___x_1410_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
lean_dec_ref(v_c_1402_);
v___x_1412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1412_, 0, v_decl_1399_);
lean_ctor_set(v___x_1412_, 1, v_____do__lift_1403_);
v___x_1413_ = lean_apply_2(v_toPure_1400_, lean_box(0), v___x_1412_);
return v___x_1413_;
}
else
{
lean_object* v___x_1414_; 
lean_dec_ref(v_____do__lift_1403_);
lean_dec_ref(v_decl_1399_);
v___x_1414_ = lean_apply_2(v_toPure_1400_, lean_box(0), v_c_1402_);
return v___x_1414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed(lean_object* v_k_1415_, lean_object* v_decl_1416_, lean_object* v_toPure_1417_, lean_object* v_decl_1418_, lean_object* v_c_1419_, lean_object* v_____do__lift_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(v_k_1415_, v_decl_1416_, v_toPure_1417_, v_decl_1418_, v_c_1419_, v_____do__lift_1420_);
lean_dec_ref(v_decl_1418_);
lean_dec_ref(v_k_1415_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(lean_object* v_k_1422_, lean_object* v_decl_1423_, lean_object* v_toPure_1424_, lean_object* v_decl_1425_, lean_object* v_c_1426_, lean_object* v_____do__lift_1427_){
_start:
{
size_t v___x_1428_; size_t v___x_1429_; uint8_t v___x_1430_; 
v___x_1428_ = lean_ptr_addr(v_k_1422_);
v___x_1429_ = lean_ptr_addr(v_____do__lift_1427_);
v___x_1430_ = lean_usize_dec_eq(v___x_1428_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_dec_ref(v_c_1426_);
v___x_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1431_, 0, v_decl_1423_);
lean_ctor_set(v___x_1431_, 1, v_____do__lift_1427_);
v___x_1432_ = lean_apply_2(v_toPure_1424_, lean_box(0), v___x_1431_);
return v___x_1432_;
}
else
{
size_t v___x_1433_; size_t v___x_1434_; uint8_t v___x_1435_; 
v___x_1433_ = lean_ptr_addr(v_decl_1425_);
v___x_1434_ = lean_ptr_addr(v_decl_1423_);
v___x_1435_ = lean_usize_dec_eq(v___x_1433_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec_ref(v_c_1426_);
v___x_1436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1436_, 0, v_decl_1423_);
lean_ctor_set(v___x_1436_, 1, v_____do__lift_1427_);
v___x_1437_ = lean_apply_2(v_toPure_1424_, lean_box(0), v___x_1436_);
return v___x_1437_;
}
else
{
lean_object* v___x_1438_; 
lean_dec_ref(v_____do__lift_1427_);
lean_dec_ref(v_decl_1423_);
v___x_1438_ = lean_apply_2(v_toPure_1424_, lean_box(0), v_c_1426_);
return v___x_1438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed(lean_object* v_k_1439_, lean_object* v_decl_1440_, lean_object* v_toPure_1441_, lean_object* v_decl_1442_, lean_object* v_c_1443_, lean_object* v_____do__lift_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(v_k_1439_, v_decl_1440_, v_toPure_1441_, v_decl_1442_, v_c_1443_, v_____do__lift_1444_);
lean_dec_ref(v_decl_1442_);
lean_dec_ref(v_k_1439_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(lean_object* v_fvarId_1446_, lean_object* v_____do__lift_1447_, lean_object* v_i_1448_, lean_object* v_____do__lift_1449_, lean_object* v_toPure_1450_, lean_object* v_y_1451_, lean_object* v_k_1452_, lean_object* v_c_1453_, lean_object* v_____do__lift_1454_){
_start:
{
size_t v___x_1455_; size_t v___x_1456_; uint8_t v___x_1457_; 
v___x_1455_ = lean_ptr_addr(v_fvarId_1446_);
v___x_1456_ = lean_ptr_addr(v_____do__lift_1447_);
v___x_1457_ = lean_usize_dec_eq(v___x_1455_, v___x_1456_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec_ref(v_c_1453_);
v___x_1458_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1458_, 0, v_____do__lift_1447_);
lean_ctor_set(v___x_1458_, 1, v_i_1448_);
lean_ctor_set(v___x_1458_, 2, v_____do__lift_1449_);
lean_ctor_set(v___x_1458_, 3, v_____do__lift_1454_);
v___x_1459_ = lean_apply_2(v_toPure_1450_, lean_box(0), v___x_1458_);
return v___x_1459_;
}
else
{
uint8_t v___x_1460_; 
v___x_1460_ = lean_nat_dec_eq(v_i_1448_, v_i_1448_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec_ref(v_c_1453_);
v___x_1461_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1461_, 0, v_____do__lift_1447_);
lean_ctor_set(v___x_1461_, 1, v_i_1448_);
lean_ctor_set(v___x_1461_, 2, v_____do__lift_1449_);
lean_ctor_set(v___x_1461_, 3, v_____do__lift_1454_);
v___x_1462_ = lean_apply_2(v_toPure_1450_, lean_box(0), v___x_1461_);
return v___x_1462_;
}
else
{
size_t v___x_1463_; size_t v___x_1464_; uint8_t v___x_1465_; 
v___x_1463_ = lean_ptr_addr(v_y_1451_);
v___x_1464_ = lean_ptr_addr(v_____do__lift_1449_);
v___x_1465_ = lean_usize_dec_eq(v___x_1463_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec_ref(v_c_1453_);
v___x_1466_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1466_, 0, v_____do__lift_1447_);
lean_ctor_set(v___x_1466_, 1, v_i_1448_);
lean_ctor_set(v___x_1466_, 2, v_____do__lift_1449_);
lean_ctor_set(v___x_1466_, 3, v_____do__lift_1454_);
v___x_1467_ = lean_apply_2(v_toPure_1450_, lean_box(0), v___x_1466_);
return v___x_1467_;
}
else
{
size_t v___x_1468_; size_t v___x_1469_; uint8_t v___x_1470_; 
v___x_1468_ = lean_ptr_addr(v_k_1452_);
v___x_1469_ = lean_ptr_addr(v_____do__lift_1454_);
v___x_1470_ = lean_usize_dec_eq(v___x_1468_, v___x_1469_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_dec_ref(v_c_1453_);
v___x_1471_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1471_, 0, v_____do__lift_1447_);
lean_ctor_set(v___x_1471_, 1, v_i_1448_);
lean_ctor_set(v___x_1471_, 2, v_____do__lift_1449_);
lean_ctor_set(v___x_1471_, 3, v_____do__lift_1454_);
v___x_1472_ = lean_apply_2(v_toPure_1450_, lean_box(0), v___x_1471_);
return v___x_1472_;
}
else
{
lean_object* v___x_1473_; 
lean_dec_ref(v_____do__lift_1454_);
lean_dec(v_____do__lift_1449_);
lean_dec(v_i_1448_);
lean_dec(v_____do__lift_1447_);
v___x_1473_ = lean_apply_2(v_toPure_1450_, lean_box(0), v_c_1453_);
return v___x_1473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed(lean_object* v_fvarId_1474_, lean_object* v_____do__lift_1475_, lean_object* v_i_1476_, lean_object* v_____do__lift_1477_, lean_object* v_toPure_1478_, lean_object* v_y_1479_, lean_object* v_k_1480_, lean_object* v_c_1481_, lean_object* v_____do__lift_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(v_fvarId_1474_, v_____do__lift_1475_, v_i_1476_, v_____do__lift_1477_, v_toPure_1478_, v_y_1479_, v_k_1480_, v_c_1481_, v_____do__lift_1482_);
lean_dec_ref(v_k_1480_);
lean_dec(v_y_1479_);
lean_dec(v_fvarId_1474_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(lean_object* v_fvarId_1484_, lean_object* v_____do__lift_1485_, lean_object* v_toPure_1486_, lean_object* v_k_1487_, lean_object* v_c_1488_, lean_object* v_____do__lift_1489_){
_start:
{
size_t v___x_1490_; size_t v___x_1491_; uint8_t v___x_1492_; 
v___x_1490_ = lean_ptr_addr(v_fvarId_1484_);
v___x_1491_ = lean_ptr_addr(v_____do__lift_1485_);
v___x_1492_ = lean_usize_dec_eq(v___x_1490_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_dec_ref(v_c_1488_);
v___x_1493_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_1493_, 0, v_____do__lift_1485_);
lean_ctor_set(v___x_1493_, 1, v_____do__lift_1489_);
v___x_1494_ = lean_apply_2(v_toPure_1486_, lean_box(0), v___x_1493_);
return v___x_1494_;
}
else
{
size_t v___x_1495_; size_t v___x_1496_; uint8_t v___x_1497_; 
v___x_1495_ = lean_ptr_addr(v_k_1487_);
v___x_1496_ = lean_ptr_addr(v_____do__lift_1489_);
v___x_1497_ = lean_usize_dec_eq(v___x_1495_, v___x_1496_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_dec_ref(v_c_1488_);
v___x_1498_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_1498_, 0, v_____do__lift_1485_);
lean_ctor_set(v___x_1498_, 1, v_____do__lift_1489_);
v___x_1499_ = lean_apply_2(v_toPure_1486_, lean_box(0), v___x_1498_);
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; 
lean_dec_ref(v_____do__lift_1489_);
lean_dec(v_____do__lift_1485_);
v___x_1500_ = lean_apply_2(v_toPure_1486_, lean_box(0), v_c_1488_);
return v___x_1500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed(lean_object* v_fvarId_1501_, lean_object* v_____do__lift_1502_, lean_object* v_toPure_1503_, lean_object* v_k_1504_, lean_object* v_c_1505_, lean_object* v_____do__lift_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(v_fvarId_1501_, v_____do__lift_1502_, v_toPure_1503_, v_k_1504_, v_c_1505_, v_____do__lift_1506_);
lean_dec_ref(v_k_1504_);
lean_dec(v_fvarId_1501_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(lean_object* v_type_1508_, lean_object* v_toPure_1509_, lean_object* v_c_1510_, lean_object* v_____do__lift_1511_){
_start:
{
size_t v___x_1512_; size_t v___x_1513_; uint8_t v___x_1514_; 
v___x_1512_ = lean_ptr_addr(v_type_1508_);
v___x_1513_ = lean_ptr_addr(v_____do__lift_1511_);
v___x_1514_ = lean_usize_dec_eq(v___x_1512_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_dec_ref(v_c_1510_);
v___x_1515_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1515_, 0, v_____do__lift_1511_);
v___x_1516_ = lean_apply_2(v_toPure_1509_, lean_box(0), v___x_1515_);
return v___x_1516_;
}
else
{
lean_object* v___x_1517_; 
lean_dec_ref(v_____do__lift_1511_);
v___x_1517_ = lean_apply_2(v_toPure_1509_, lean_box(0), v_c_1510_);
return v___x_1517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed(lean_object* v_type_1518_, lean_object* v_toPure_1519_, lean_object* v_c_1520_, lean_object* v_____do__lift_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(v_type_1518_, v_toPure_1519_, v_c_1520_, v_____do__lift_1521_);
lean_dec_ref(v_type_1518_);
return v_res_1522_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(lean_object* v_k_1523_, lean_object* v_toPure_1524_, lean_object* v_decl_1525_, lean_object* v_c_1526_, uint8_t v_pu_1527_, lean_object* v_inst_1528_, lean_object* v_inst_1529_, lean_object* v_f_1530_, lean_object* v_toBind_1531_, lean_object* v_decl_1532_){
_start:
{
lean_object* v___f_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_inc_ref(v_k_1523_);
v___f_1533_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1533_, 0, v_k_1523_);
lean_closure_set(v___f_1533_, 1, v_decl_1532_);
lean_closure_set(v___f_1533_, 2, v_toPure_1524_);
lean_closure_set(v___f_1533_, 3, v_decl_1525_);
lean_closure_set(v___f_1533_, 4, v_c_1526_);
v___x_1534_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1527_, v_inst_1528_, v_inst_1529_, v_f_1530_, v_k_1523_);
v___x_1535_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1534_, v___f_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1523_ = stack[0].m_obj;
lean_object* v_toPure_1524_ = stack[1].m_obj;
lean_object* v_decl_1525_ = stack[2].m_obj;
lean_object* v_c_1526_ = stack[3].m_obj;
uint8_t v_pu_1527_ = stack[4].m_num;
lean_object* v_inst_1528_ = stack[5].m_obj;
lean_object* v_inst_1529_ = stack[6].m_obj;
lean_object* v_f_1530_ = stack[7].m_obj;
lean_object* v_toBind_1531_ = stack[8].m_obj;
lean_object* v_decl_1532_ = stack[9].m_obj;
lean_object* v_res_1536_;
v_res_1536_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(v_k_1523_, v_toPure_1524_, v_decl_1525_, v_c_1526_, v_pu_1527_, v_inst_1528_, v_inst_1529_, v_f_1530_, v_toBind_1531_, v_decl_1532_);
stack->m_obj
 = v_res_1536_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed(lean_object* v_k_1537_, lean_object* v_toPure_1538_, lean_object* v_decl_1539_, lean_object* v_c_1540_, lean_object* v_pu_1541_, lean_object* v_inst_1542_, lean_object* v_inst_1543_, lean_object* v_f_1544_, lean_object* v_toBind_1545_, lean_object* v_decl_1546_){
_start:
{
uint8_t v_pu_boxed_1547_; lean_object* v_res_1548_; 
v_pu_boxed_1547_ = lean_unbox(v_pu_1541_);
v_res_1548_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(v_k_1537_, v_toPure_1538_, v_decl_1539_, v_c_1540_, v_pu_boxed_1547_, v_inst_1542_, v_inst_1543_, v_f_1544_, v_toBind_1545_, v_decl_1546_);
return v_res_1548_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(lean_object* v_k_1549_, lean_object* v_toPure_1550_, lean_object* v_decl_1551_, lean_object* v_c_1552_, uint8_t v_pu_1553_, lean_object* v_inst_1554_, lean_object* v_inst_1555_, lean_object* v_f_1556_, lean_object* v_toBind_1557_, lean_object* v_decl_1558_){
_start:
{
lean_object* v___f_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_inc_ref(v_k_1549_);
v___f_1559_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_1559_, 0, v_k_1549_);
lean_closure_set(v___f_1559_, 1, v_decl_1558_);
lean_closure_set(v___f_1559_, 2, v_toPure_1550_);
lean_closure_set(v___f_1559_, 3, v_decl_1551_);
lean_closure_set(v___f_1559_, 4, v_c_1552_);
v___x_1560_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1553_, v_inst_1554_, v_inst_1555_, v_f_1556_, v_k_1549_);
v___x_1561_ = lean_apply_4(v_toBind_1557_, lean_box(0), lean_box(0), v___x_1560_, v___f_1559_);
return v___x_1561_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1549_ = stack[0].m_obj;
lean_object* v_toPure_1550_ = stack[1].m_obj;
lean_object* v_decl_1551_ = stack[2].m_obj;
lean_object* v_c_1552_ = stack[3].m_obj;
uint8_t v_pu_1553_ = stack[4].m_num;
lean_object* v_inst_1554_ = stack[5].m_obj;
lean_object* v_inst_1555_ = stack[6].m_obj;
lean_object* v_f_1556_ = stack[7].m_obj;
lean_object* v_toBind_1557_ = stack[8].m_obj;
lean_object* v_decl_1558_ = stack[9].m_obj;
lean_object* v_res_1562_;
v_res_1562_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(v_k_1549_, v_toPure_1550_, v_decl_1551_, v_c_1552_, v_pu_1553_, v_inst_1554_, v_inst_1555_, v_f_1556_, v_toBind_1557_, v_decl_1558_);
stack->m_obj
 = v_res_1562_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed(lean_object* v_k_1563_, lean_object* v_toPure_1564_, lean_object* v_decl_1565_, lean_object* v_c_1566_, lean_object* v_pu_1567_, lean_object* v_inst_1568_, lean_object* v_inst_1569_, lean_object* v_f_1570_, lean_object* v_toBind_1571_, lean_object* v_decl_1572_){
_start:
{
uint8_t v_pu_boxed_1573_; lean_object* v_res_1574_; 
v_pu_boxed_1573_ = lean_unbox(v_pu_1567_);
v_res_1574_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(v_k_1563_, v_toPure_1564_, v_decl_1565_, v_c_1566_, v_pu_boxed_1573_, v_inst_1568_, v_inst_1569_, v_f_1570_, v_toBind_1571_, v_decl_1572_);
return v_res_1574_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(uint8_t v_pu_1575_, lean_object* v_decl_1576_, lean_object* v_params_1577_, lean_object* v_inst_1578_, lean_object* v_toBind_1579_, lean_object* v___f_1580_, lean_object* v_inst_1581_, lean_object* v_f_1582_, lean_object* v_value_1583_, lean_object* v_____do__lift_1584_){
_start:
{
lean_object* v___x_1585_; lean_object* v___f_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1585_ = lean_box(v_pu_1575_);
lean_inc(v_toBind_1579_);
lean_inc(v_inst_1578_);
v___f_1586_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_1586_, 0, v___x_1585_);
lean_closure_set(v___f_1586_, 1, v_decl_1576_);
lean_closure_set(v___f_1586_, 2, v_____do__lift_1584_);
lean_closure_set(v___f_1586_, 3, v_params_1577_);
lean_closure_set(v___f_1586_, 4, v_inst_1578_);
lean_closure_set(v___f_1586_, 5, v_toBind_1579_);
lean_closure_set(v___f_1586_, 6, v___f_1580_);
v___x_1587_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1575_, v_inst_1578_, v_inst_1581_, v_f_1582_, v_value_1583_);
v___x_1588_ = lean_apply_4(v_toBind_1579_, lean_box(0), lean_box(0), v___x_1587_, v___f_1586_);
return v___x_1588_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1575_ = stack[0].m_num;
lean_object* v_decl_1576_ = stack[1].m_obj;
lean_object* v_params_1577_ = stack[2].m_obj;
lean_object* v_inst_1578_ = stack[3].m_obj;
lean_object* v_toBind_1579_ = stack[4].m_obj;
lean_object* v___f_1580_ = stack[5].m_obj;
lean_object* v_inst_1581_ = stack[6].m_obj;
lean_object* v_f_1582_ = stack[7].m_obj;
lean_object* v_value_1583_ = stack[8].m_obj;
lean_object* v_____do__lift_1584_ = stack[9].m_obj;
lean_object* v_res_1589_;
v_res_1589_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(v_pu_1575_, v_decl_1576_, v_params_1577_, v_inst_1578_, v_toBind_1579_, v___f_1580_, v_inst_1581_, v_f_1582_, v_value_1583_, v_____do__lift_1584_);
stack->m_obj
 = v_res_1589_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed(lean_object* v_pu_1590_, lean_object* v_decl_1591_, lean_object* v_params_1592_, lean_object* v_inst_1593_, lean_object* v_toBind_1594_, lean_object* v___f_1595_, lean_object* v_inst_1596_, lean_object* v_f_1597_, lean_object* v_value_1598_, lean_object* v_____do__lift_1599_){
_start:
{
uint8_t v_pu_boxed_1600_; lean_object* v_res_1601_; 
v_pu_boxed_1600_ = lean_unbox(v_pu_1590_);
v_res_1601_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(v_pu_boxed_1600_, v_decl_1591_, v_params_1592_, v_inst_1593_, v_toBind_1594_, v___f_1595_, v_inst_1596_, v_f_1597_, v_value_1598_, v_____do__lift_1599_);
return v_res_1601_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(uint8_t v_pu_1602_, lean_object* v_decl_1603_, lean_object* v_inst_1604_, lean_object* v_toBind_1605_, lean_object* v___f_1606_, lean_object* v_inst_1607_, lean_object* v_f_1608_, lean_object* v_value_1609_, lean_object* v_type_1610_, lean_object* v_params_1611_){
_start:
{
lean_object* v___x_1612_; lean_object* v___f_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1612_ = lean_box(v_pu_1602_);
lean_inc(v_f_1608_);
lean_inc_ref(v_inst_1607_);
lean_inc(v_toBind_1605_);
v___f_1613_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed), 10, 9);
lean_closure_set(v___f_1613_, 0, v___x_1612_);
lean_closure_set(v___f_1613_, 1, v_decl_1603_);
lean_closure_set(v___f_1613_, 2, v_params_1611_);
lean_closure_set(v___f_1613_, 3, v_inst_1604_);
lean_closure_set(v___f_1613_, 4, v_toBind_1605_);
lean_closure_set(v___f_1613_, 5, v___f_1606_);
lean_closure_set(v___f_1613_, 6, v_inst_1607_);
lean_closure_set(v___f_1613_, 7, v_f_1608_);
lean_closure_set(v___f_1613_, 8, v_value_1609_);
v___x_1614_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1607_, v_f_1608_, v_type_1610_);
v___x_1615_ = lean_apply_4(v_toBind_1605_, lean_box(0), lean_box(0), v___x_1614_, v___f_1613_);
return v___x_1615_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1602_ = stack[0].m_num;
lean_object* v_decl_1603_ = stack[1].m_obj;
lean_object* v_inst_1604_ = stack[2].m_obj;
lean_object* v_toBind_1605_ = stack[3].m_obj;
lean_object* v___f_1606_ = stack[4].m_obj;
lean_object* v_inst_1607_ = stack[5].m_obj;
lean_object* v_f_1608_ = stack[6].m_obj;
lean_object* v_value_1609_ = stack[7].m_obj;
lean_object* v_type_1610_ = stack[8].m_obj;
lean_object* v_params_1611_ = stack[9].m_obj;
lean_object* v_res_1616_;
v_res_1616_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(v_pu_1602_, v_decl_1603_, v_inst_1604_, v_toBind_1605_, v___f_1606_, v_inst_1607_, v_f_1608_, v_value_1609_, v_type_1610_, v_params_1611_);
stack->m_obj
 = v_res_1616_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed(lean_object* v_pu_1617_, lean_object* v_decl_1618_, lean_object* v_inst_1619_, lean_object* v_toBind_1620_, lean_object* v___f_1621_, lean_object* v_inst_1622_, lean_object* v_f_1623_, lean_object* v_value_1624_, lean_object* v_type_1625_, lean_object* v_params_1626_){
_start:
{
uint8_t v_pu_boxed_1627_; lean_object* v_res_1628_; 
v_pu_boxed_1627_ = lean_unbox(v_pu_1617_);
v_res_1628_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(v_pu_boxed_1627_, v_decl_1618_, v_inst_1619_, v_toBind_1620_, v___f_1621_, v_inst_1622_, v_f_1623_, v_value_1624_, v_type_1625_, v_params_1626_);
return v_res_1628_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(lean_object* v_k_1629_, lean_object* v_toPure_1630_, lean_object* v_decl_1631_, lean_object* v_c_1632_, uint8_t v_pu_1633_, lean_object* v_inst_1634_, lean_object* v_inst_1635_, lean_object* v_f_1636_, lean_object* v_toBind_1637_, lean_object* v_decl_1638_){
_start:
{
lean_object* v___f_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_inc_ref(v_k_1629_);
v___f_1639_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_1639_, 0, v_k_1629_);
lean_closure_set(v___f_1639_, 1, v_decl_1638_);
lean_closure_set(v___f_1639_, 2, v_toPure_1630_);
lean_closure_set(v___f_1639_, 3, v_decl_1631_);
lean_closure_set(v___f_1639_, 4, v_c_1632_);
v___x_1640_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1633_, v_inst_1634_, v_inst_1635_, v_f_1636_, v_k_1629_);
v___x_1641_ = lean_apply_4(v_toBind_1637_, lean_box(0), lean_box(0), v___x_1640_, v___f_1639_);
return v___x_1641_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1629_ = stack[0].m_obj;
lean_object* v_toPure_1630_ = stack[1].m_obj;
lean_object* v_decl_1631_ = stack[2].m_obj;
lean_object* v_c_1632_ = stack[3].m_obj;
uint8_t v_pu_1633_ = stack[4].m_num;
lean_object* v_inst_1634_ = stack[5].m_obj;
lean_object* v_inst_1635_ = stack[6].m_obj;
lean_object* v_f_1636_ = stack[7].m_obj;
lean_object* v_toBind_1637_ = stack[8].m_obj;
lean_object* v_decl_1638_ = stack[9].m_obj;
lean_object* v_res_1642_;
v_res_1642_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(v_k_1629_, v_toPure_1630_, v_decl_1631_, v_c_1632_, v_pu_1633_, v_inst_1634_, v_inst_1635_, v_f_1636_, v_toBind_1637_, v_decl_1638_);
stack->m_obj
 = v_res_1642_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed(lean_object* v_k_1643_, lean_object* v_toPure_1644_, lean_object* v_decl_1645_, lean_object* v_c_1646_, lean_object* v_pu_1647_, lean_object* v_inst_1648_, lean_object* v_inst_1649_, lean_object* v_f_1650_, lean_object* v_toBind_1651_, lean_object* v_decl_1652_){
_start:
{
uint8_t v_pu_boxed_1653_; lean_object* v_res_1654_; 
v_pu_boxed_1653_ = lean_unbox(v_pu_1647_);
v_res_1654_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(v_k_1643_, v_toPure_1644_, v_decl_1645_, v_c_1646_, v_pu_boxed_1653_, v_inst_1648_, v_inst_1649_, v_f_1650_, v_toBind_1651_, v_decl_1652_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed(lean_object* v_pu_1655_, lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_f_1658_, lean_object* v_x_1659_){
_start:
{
uint8_t v_pu_boxed_1660_; lean_object* v_res_1661_; 
v_pu_boxed_1660_ = lean_unbox(v_pu_1655_);
v_res_1661_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(v_pu_boxed_1660_, v_inst_1656_, v_inst_1657_, v_f_1658_, v_x_1659_);
return v_res_1661_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(lean_object* v_fvarId_1662_, lean_object* v_____do__lift_1663_, lean_object* v_i_1664_, lean_object* v_toPure_1665_, lean_object* v_y_1666_, lean_object* v_k_1667_, lean_object* v_c_1668_, uint8_t v_pu_1669_, lean_object* v_inst_1670_, lean_object* v_inst_1671_, lean_object* v_f_1672_, lean_object* v_toBind_1673_, lean_object* v_____do__lift_1674_){
_start:
{
lean_object* v___f_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_inc_ref(v_k_1667_);
v___f_1675_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed), 9, 8);
lean_closure_set(v___f_1675_, 0, v_fvarId_1662_);
lean_closure_set(v___f_1675_, 1, v_____do__lift_1663_);
lean_closure_set(v___f_1675_, 2, v_i_1664_);
lean_closure_set(v___f_1675_, 3, v_____do__lift_1674_);
lean_closure_set(v___f_1675_, 4, v_toPure_1665_);
lean_closure_set(v___f_1675_, 5, v_y_1666_);
lean_closure_set(v___f_1675_, 6, v_k_1667_);
lean_closure_set(v___f_1675_, 7, v_c_1668_);
v___x_1676_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1669_, v_inst_1670_, v_inst_1671_, v_f_1672_, v_k_1667_);
v___x_1677_ = lean_apply_4(v_toBind_1673_, lean_box(0), lean_box(0), v___x_1676_, v___f_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1662_ = stack[0].m_obj;
lean_object* v_____do__lift_1663_ = stack[1].m_obj;
lean_object* v_i_1664_ = stack[2].m_obj;
lean_object* v_toPure_1665_ = stack[3].m_obj;
lean_object* v_y_1666_ = stack[4].m_obj;
lean_object* v_k_1667_ = stack[5].m_obj;
lean_object* v_c_1668_ = stack[6].m_obj;
uint8_t v_pu_1669_ = stack[7].m_num;
lean_object* v_inst_1670_ = stack[8].m_obj;
lean_object* v_inst_1671_ = stack[9].m_obj;
lean_object* v_f_1672_ = stack[10].m_obj;
lean_object* v_toBind_1673_ = stack[11].m_obj;
lean_object* v_____do__lift_1674_ = stack[12].m_obj;
lean_object* v_res_1678_;
v_res_1678_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(v_fvarId_1662_, v_____do__lift_1663_, v_i_1664_, v_toPure_1665_, v_y_1666_, v_k_1667_, v_c_1668_, v_pu_1669_, v_inst_1670_, v_inst_1671_, v_f_1672_, v_toBind_1673_, v_____do__lift_1674_);
stack->m_obj
 = v_res_1678_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed(lean_object* v_fvarId_1679_, lean_object* v_____do__lift_1680_, lean_object* v_i_1681_, lean_object* v_toPure_1682_, lean_object* v_y_1683_, lean_object* v_k_1684_, lean_object* v_c_1685_, lean_object* v_pu_1686_, lean_object* v_inst_1687_, lean_object* v_inst_1688_, lean_object* v_f_1689_, lean_object* v_toBind_1690_, lean_object* v_____do__lift_1691_){
_start:
{
uint8_t v_pu_boxed_1692_; lean_object* v_res_1693_; 
v_pu_boxed_1692_ = lean_unbox(v_pu_1686_);
v_res_1693_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(v_fvarId_1679_, v_____do__lift_1680_, v_i_1681_, v_toPure_1682_, v_y_1683_, v_k_1684_, v_c_1685_, v_pu_boxed_1692_, v_inst_1687_, v_inst_1688_, v_f_1689_, v_toBind_1690_, v_____do__lift_1691_);
return v_res_1693_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(lean_object* v_fvarId_1694_, lean_object* v_i_1695_, lean_object* v_toPure_1696_, lean_object* v_y_1697_, lean_object* v_k_1698_, lean_object* v_c_1699_, uint8_t v_pu_1700_, lean_object* v_inst_1701_, lean_object* v_inst_1702_, lean_object* v_f_1703_, lean_object* v_toBind_1704_, lean_object* v_____do__lift_1705_){
_start:
{
lean_object* v___x_1706_; lean_object* v___f_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1706_ = lean_box(v_pu_1700_);
lean_inc(v_toBind_1704_);
lean_inc(v_f_1703_);
lean_inc_ref(v_inst_1702_);
lean_inc(v_y_1697_);
v___f_1707_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed), 13, 12);
lean_closure_set(v___f_1707_, 0, v_fvarId_1694_);
lean_closure_set(v___f_1707_, 1, v_____do__lift_1705_);
lean_closure_set(v___f_1707_, 2, v_i_1695_);
lean_closure_set(v___f_1707_, 3, v_toPure_1696_);
lean_closure_set(v___f_1707_, 4, v_y_1697_);
lean_closure_set(v___f_1707_, 5, v_k_1698_);
lean_closure_set(v___f_1707_, 6, v_c_1699_);
lean_closure_set(v___f_1707_, 7, v___x_1706_);
lean_closure_set(v___f_1707_, 8, v_inst_1701_);
lean_closure_set(v___f_1707_, 9, v_inst_1702_);
lean_closure_set(v___f_1707_, 10, v_f_1703_);
lean_closure_set(v___f_1707_, 11, v_toBind_1704_);
v___x_1708_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_1700_, v_inst_1702_, v_f_1703_, v_y_1697_);
v___x_1709_ = lean_apply_4(v_toBind_1704_, lean_box(0), lean_box(0), v___x_1708_, v___f_1707_);
return v___x_1709_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1694_ = stack[0].m_obj;
lean_object* v_i_1695_ = stack[1].m_obj;
lean_object* v_toPure_1696_ = stack[2].m_obj;
lean_object* v_y_1697_ = stack[3].m_obj;
lean_object* v_k_1698_ = stack[4].m_obj;
lean_object* v_c_1699_ = stack[5].m_obj;
uint8_t v_pu_1700_ = stack[6].m_num;
lean_object* v_inst_1701_ = stack[7].m_obj;
lean_object* v_inst_1702_ = stack[8].m_obj;
lean_object* v_f_1703_ = stack[9].m_obj;
lean_object* v_toBind_1704_ = stack[10].m_obj;
lean_object* v_____do__lift_1705_ = stack[11].m_obj;
lean_object* v_res_1710_;
v_res_1710_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(v_fvarId_1694_, v_i_1695_, v_toPure_1696_, v_y_1697_, v_k_1698_, v_c_1699_, v_pu_1700_, v_inst_1701_, v_inst_1702_, v_f_1703_, v_toBind_1704_, v_____do__lift_1705_);
stack->m_obj
 = v_res_1710_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed(lean_object* v_fvarId_1711_, lean_object* v_i_1712_, lean_object* v_toPure_1713_, lean_object* v_y_1714_, lean_object* v_k_1715_, lean_object* v_c_1716_, lean_object* v_pu_1717_, lean_object* v_inst_1718_, lean_object* v_inst_1719_, lean_object* v_f_1720_, lean_object* v_toBind_1721_, lean_object* v_____do__lift_1722_){
_start:
{
uint8_t v_pu_boxed_1723_; lean_object* v_res_1724_; 
v_pu_boxed_1723_ = lean_unbox(v_pu_1717_);
v_res_1724_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(v_fvarId_1711_, v_i_1712_, v_toPure_1713_, v_y_1714_, v_k_1715_, v_c_1716_, v_pu_boxed_1723_, v_inst_1718_, v_inst_1719_, v_f_1720_, v_toBind_1721_, v_____do__lift_1722_);
return v_res_1724_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(lean_object* v_fvarId_1725_, lean_object* v_____do__lift_1726_, lean_object* v_i_1727_, lean_object* v_toPure_1728_, lean_object* v_y_1729_, lean_object* v_k_1730_, lean_object* v_c_1731_, uint8_t v_pu_1732_, lean_object* v_inst_1733_, lean_object* v_inst_1734_, lean_object* v_f_1735_, lean_object* v_toBind_1736_, lean_object* v_____do__lift_1737_){
_start:
{
lean_object* v___f_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_inc_ref(v_k_1730_);
v___f_1738_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed), 9, 8);
lean_closure_set(v___f_1738_, 0, v_fvarId_1725_);
lean_closure_set(v___f_1738_, 1, v_____do__lift_1726_);
lean_closure_set(v___f_1738_, 2, v_i_1727_);
lean_closure_set(v___f_1738_, 3, v_____do__lift_1737_);
lean_closure_set(v___f_1738_, 4, v_toPure_1728_);
lean_closure_set(v___f_1738_, 5, v_y_1729_);
lean_closure_set(v___f_1738_, 6, v_k_1730_);
lean_closure_set(v___f_1738_, 7, v_c_1731_);
v___x_1739_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1732_, v_inst_1733_, v_inst_1734_, v_f_1735_, v_k_1730_);
v___x_1740_ = lean_apply_4(v_toBind_1736_, lean_box(0), lean_box(0), v___x_1739_, v___f_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1725_ = stack[0].m_obj;
lean_object* v_____do__lift_1726_ = stack[1].m_obj;
lean_object* v_i_1727_ = stack[2].m_obj;
lean_object* v_toPure_1728_ = stack[3].m_obj;
lean_object* v_y_1729_ = stack[4].m_obj;
lean_object* v_k_1730_ = stack[5].m_obj;
lean_object* v_c_1731_ = stack[6].m_obj;
uint8_t v_pu_1732_ = stack[7].m_num;
lean_object* v_inst_1733_ = stack[8].m_obj;
lean_object* v_inst_1734_ = stack[9].m_obj;
lean_object* v_f_1735_ = stack[10].m_obj;
lean_object* v_toBind_1736_ = stack[11].m_obj;
lean_object* v_____do__lift_1737_ = stack[12].m_obj;
lean_object* v_res_1741_;
v_res_1741_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(v_fvarId_1725_, v_____do__lift_1726_, v_i_1727_, v_toPure_1728_, v_y_1729_, v_k_1730_, v_c_1731_, v_pu_1732_, v_inst_1733_, v_inst_1734_, v_f_1735_, v_toBind_1736_, v_____do__lift_1737_);
stack->m_obj
 = v_res_1741_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed(lean_object* v_fvarId_1742_, lean_object* v_____do__lift_1743_, lean_object* v_i_1744_, lean_object* v_toPure_1745_, lean_object* v_y_1746_, lean_object* v_k_1747_, lean_object* v_c_1748_, lean_object* v_pu_1749_, lean_object* v_inst_1750_, lean_object* v_inst_1751_, lean_object* v_f_1752_, lean_object* v_toBind_1753_, lean_object* v_____do__lift_1754_){
_start:
{
uint8_t v_pu_boxed_1755_; lean_object* v_res_1756_; 
v_pu_boxed_1755_ = lean_unbox(v_pu_1749_);
v_res_1756_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(v_fvarId_1742_, v_____do__lift_1743_, v_i_1744_, v_toPure_1745_, v_y_1746_, v_k_1747_, v_c_1748_, v_pu_boxed_1755_, v_inst_1750_, v_inst_1751_, v_f_1752_, v_toBind_1753_, v_____do__lift_1754_);
return v_res_1756_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(lean_object* v_fvarId_1757_, lean_object* v_i_1758_, lean_object* v_toPure_1759_, lean_object* v_y_1760_, lean_object* v_k_1761_, lean_object* v_c_1762_, uint8_t v_pu_1763_, lean_object* v_inst_1764_, lean_object* v_inst_1765_, lean_object* v_f_1766_, lean_object* v_toBind_1767_, lean_object* v_____do__lift_1768_){
_start:
{
lean_object* v___x_1769_; lean_object* v___f_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1769_ = lean_box(v_pu_1763_);
lean_inc(v_toBind_1767_);
lean_inc(v_f_1766_);
lean_inc(v_y_1760_);
v___f_1770_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed), 13, 12);
lean_closure_set(v___f_1770_, 0, v_fvarId_1757_);
lean_closure_set(v___f_1770_, 1, v_____do__lift_1768_);
lean_closure_set(v___f_1770_, 2, v_i_1758_);
lean_closure_set(v___f_1770_, 3, v_toPure_1759_);
lean_closure_set(v___f_1770_, 4, v_y_1760_);
lean_closure_set(v___f_1770_, 5, v_k_1761_);
lean_closure_set(v___f_1770_, 6, v_c_1762_);
lean_closure_set(v___f_1770_, 7, v___x_1769_);
lean_closure_set(v___f_1770_, 8, v_inst_1764_);
lean_closure_set(v___f_1770_, 9, v_inst_1765_);
lean_closure_set(v___f_1770_, 10, v_f_1766_);
lean_closure_set(v___f_1770_, 11, v_toBind_1767_);
v___x_1771_ = lean_apply_1(v_f_1766_, v_y_1760_);
v___x_1772_ = lean_apply_4(v_toBind_1767_, lean_box(0), lean_box(0), v___x_1771_, v___f_1770_);
return v___x_1772_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1757_ = stack[0].m_obj;
lean_object* v_i_1758_ = stack[1].m_obj;
lean_object* v_toPure_1759_ = stack[2].m_obj;
lean_object* v_y_1760_ = stack[3].m_obj;
lean_object* v_k_1761_ = stack[4].m_obj;
lean_object* v_c_1762_ = stack[5].m_obj;
uint8_t v_pu_1763_ = stack[6].m_num;
lean_object* v_inst_1764_ = stack[7].m_obj;
lean_object* v_inst_1765_ = stack[8].m_obj;
lean_object* v_f_1766_ = stack[9].m_obj;
lean_object* v_toBind_1767_ = stack[10].m_obj;
lean_object* v_____do__lift_1768_ = stack[11].m_obj;
lean_object* v_res_1773_;
v_res_1773_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(v_fvarId_1757_, v_i_1758_, v_toPure_1759_, v_y_1760_, v_k_1761_, v_c_1762_, v_pu_1763_, v_inst_1764_, v_inst_1765_, v_f_1766_, v_toBind_1767_, v_____do__lift_1768_);
stack->m_obj
 = v_res_1773_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed(lean_object* v_fvarId_1774_, lean_object* v_i_1775_, lean_object* v_toPure_1776_, lean_object* v_y_1777_, lean_object* v_k_1778_, lean_object* v_c_1779_, lean_object* v_pu_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_f_1783_, lean_object* v_toBind_1784_, lean_object* v_____do__lift_1785_){
_start:
{
uint8_t v_pu_boxed_1786_; lean_object* v_res_1787_; 
v_pu_boxed_1786_ = lean_unbox(v_pu_1780_);
v_res_1787_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(v_fvarId_1774_, v_i_1775_, v_toPure_1776_, v_y_1777_, v_k_1778_, v_c_1779_, v_pu_boxed_1786_, v_inst_1781_, v_inst_1782_, v_f_1783_, v_toBind_1784_, v_____do__lift_1785_);
return v_res_1787_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(lean_object* v_fvarId_1788_, lean_object* v_____do__lift_1789_, lean_object* v_i_1790_, lean_object* v_offset_1791_, lean_object* v_____do__lift_1792_, lean_object* v_toPure_1793_, lean_object* v_y_1794_, lean_object* v_ty_1795_, lean_object* v_k_1796_, lean_object* v_c_1797_, uint8_t v_pu_1798_, lean_object* v_inst_1799_, lean_object* v_inst_1800_, lean_object* v_f_1801_, lean_object* v_toBind_1802_, lean_object* v_____do__lift_1803_){
_start:
{
lean_object* v___f_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_inc_ref(v_k_1796_);
v___f_1804_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed), 12, 11);
lean_closure_set(v___f_1804_, 0, v_fvarId_1788_);
lean_closure_set(v___f_1804_, 1, v_____do__lift_1789_);
lean_closure_set(v___f_1804_, 2, v_i_1790_);
lean_closure_set(v___f_1804_, 3, v_offset_1791_);
lean_closure_set(v___f_1804_, 4, v_____do__lift_1792_);
lean_closure_set(v___f_1804_, 5, v_____do__lift_1803_);
lean_closure_set(v___f_1804_, 6, v_toPure_1793_);
lean_closure_set(v___f_1804_, 7, v_y_1794_);
lean_closure_set(v___f_1804_, 8, v_ty_1795_);
lean_closure_set(v___f_1804_, 9, v_k_1796_);
lean_closure_set(v___f_1804_, 10, v_c_1797_);
v___x_1805_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1798_, v_inst_1799_, v_inst_1800_, v_f_1801_, v_k_1796_);
v___x_1806_ = lean_apply_4(v_toBind_1802_, lean_box(0), lean_box(0), v___x_1805_, v___f_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1788_ = stack[0].m_obj;
lean_object* v_____do__lift_1789_ = stack[1].m_obj;
lean_object* v_i_1790_ = stack[2].m_obj;
lean_object* v_offset_1791_ = stack[3].m_obj;
lean_object* v_____do__lift_1792_ = stack[4].m_obj;
lean_object* v_toPure_1793_ = stack[5].m_obj;
lean_object* v_y_1794_ = stack[6].m_obj;
lean_object* v_ty_1795_ = stack[7].m_obj;
lean_object* v_k_1796_ = stack[8].m_obj;
lean_object* v_c_1797_ = stack[9].m_obj;
uint8_t v_pu_1798_ = stack[10].m_num;
lean_object* v_inst_1799_ = stack[11].m_obj;
lean_object* v_inst_1800_ = stack[12].m_obj;
lean_object* v_f_1801_ = stack[13].m_obj;
lean_object* v_toBind_1802_ = stack[14].m_obj;
lean_object* v_____do__lift_1803_ = stack[15].m_obj;
lean_object* v_res_1807_;
v_res_1807_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(v_fvarId_1788_, v_____do__lift_1789_, v_i_1790_, v_offset_1791_, v_____do__lift_1792_, v_toPure_1793_, v_y_1794_, v_ty_1795_, v_k_1796_, v_c_1797_, v_pu_1798_, v_inst_1799_, v_inst_1800_, v_f_1801_, v_toBind_1802_, v_____do__lift_1803_);
stack->m_obj
 = v_res_1807_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed(lean_object* v_fvarId_1808_, lean_object* v_____do__lift_1809_, lean_object* v_i_1810_, lean_object* v_offset_1811_, lean_object* v_____do__lift_1812_, lean_object* v_toPure_1813_, lean_object* v_y_1814_, lean_object* v_ty_1815_, lean_object* v_k_1816_, lean_object* v_c_1817_, lean_object* v_pu_1818_, lean_object* v_inst_1819_, lean_object* v_inst_1820_, lean_object* v_f_1821_, lean_object* v_toBind_1822_, lean_object* v_____do__lift_1823_){
_start:
{
uint8_t v_pu_boxed_1824_; lean_object* v_res_1825_; 
v_pu_boxed_1824_ = lean_unbox(v_pu_1818_);
v_res_1825_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(v_fvarId_1808_, v_____do__lift_1809_, v_i_1810_, v_offset_1811_, v_____do__lift_1812_, v_toPure_1813_, v_y_1814_, v_ty_1815_, v_k_1816_, v_c_1817_, v_pu_boxed_1824_, v_inst_1819_, v_inst_1820_, v_f_1821_, v_toBind_1822_, v_____do__lift_1823_);
return v_res_1825_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(lean_object* v_fvarId_1826_, lean_object* v_____do__lift_1827_, lean_object* v_i_1828_, lean_object* v_offset_1829_, lean_object* v_toPure_1830_, lean_object* v_y_1831_, lean_object* v_ty_1832_, lean_object* v_k_1833_, lean_object* v_c_1834_, uint8_t v_pu_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_f_1838_, lean_object* v_toBind_1839_, lean_object* v_____do__lift_1840_){
_start:
{
lean_object* v___x_1841_; lean_object* v___f_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1841_ = lean_box(v_pu_1835_);
lean_inc(v_toBind_1839_);
lean_inc(v_f_1838_);
lean_inc_ref(v_inst_1837_);
lean_inc_ref(v_ty_1832_);
v___f_1842_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed), 16, 15);
lean_closure_set(v___f_1842_, 0, v_fvarId_1826_);
lean_closure_set(v___f_1842_, 1, v_____do__lift_1827_);
lean_closure_set(v___f_1842_, 2, v_i_1828_);
lean_closure_set(v___f_1842_, 3, v_offset_1829_);
lean_closure_set(v___f_1842_, 4, v_____do__lift_1840_);
lean_closure_set(v___f_1842_, 5, v_toPure_1830_);
lean_closure_set(v___f_1842_, 6, v_y_1831_);
lean_closure_set(v___f_1842_, 7, v_ty_1832_);
lean_closure_set(v___f_1842_, 8, v_k_1833_);
lean_closure_set(v___f_1842_, 9, v_c_1834_);
lean_closure_set(v___f_1842_, 10, v___x_1841_);
lean_closure_set(v___f_1842_, 11, v_inst_1836_);
lean_closure_set(v___f_1842_, 12, v_inst_1837_);
lean_closure_set(v___f_1842_, 13, v_f_1838_);
lean_closure_set(v___f_1842_, 14, v_toBind_1839_);
v___x_1843_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1837_, v_f_1838_, v_ty_1832_);
v___x_1844_ = lean_apply_4(v_toBind_1839_, lean_box(0), lean_box(0), v___x_1843_, v___f_1842_);
return v___x_1844_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1826_ = stack[0].m_obj;
lean_object* v_____do__lift_1827_ = stack[1].m_obj;
lean_object* v_i_1828_ = stack[2].m_obj;
lean_object* v_offset_1829_ = stack[3].m_obj;
lean_object* v_toPure_1830_ = stack[4].m_obj;
lean_object* v_y_1831_ = stack[5].m_obj;
lean_object* v_ty_1832_ = stack[6].m_obj;
lean_object* v_k_1833_ = stack[7].m_obj;
lean_object* v_c_1834_ = stack[8].m_obj;
uint8_t v_pu_1835_ = stack[9].m_num;
lean_object* v_inst_1836_ = stack[10].m_obj;
lean_object* v_inst_1837_ = stack[11].m_obj;
lean_object* v_f_1838_ = stack[12].m_obj;
lean_object* v_toBind_1839_ = stack[13].m_obj;
lean_object* v_____do__lift_1840_ = stack[14].m_obj;
lean_object* v_res_1845_;
v_res_1845_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(v_fvarId_1826_, v_____do__lift_1827_, v_i_1828_, v_offset_1829_, v_toPure_1830_, v_y_1831_, v_ty_1832_, v_k_1833_, v_c_1834_, v_pu_1835_, v_inst_1836_, v_inst_1837_, v_f_1838_, v_toBind_1839_, v_____do__lift_1840_);
stack->m_obj
 = v_res_1845_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed(lean_object* v_fvarId_1846_, lean_object* v_____do__lift_1847_, lean_object* v_i_1848_, lean_object* v_offset_1849_, lean_object* v_toPure_1850_, lean_object* v_y_1851_, lean_object* v_ty_1852_, lean_object* v_k_1853_, lean_object* v_c_1854_, lean_object* v_pu_1855_, lean_object* v_inst_1856_, lean_object* v_inst_1857_, lean_object* v_f_1858_, lean_object* v_toBind_1859_, lean_object* v_____do__lift_1860_){
_start:
{
uint8_t v_pu_boxed_1861_; lean_object* v_res_1862_; 
v_pu_boxed_1861_ = lean_unbox(v_pu_1855_);
v_res_1862_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(v_fvarId_1846_, v_____do__lift_1847_, v_i_1848_, v_offset_1849_, v_toPure_1850_, v_y_1851_, v_ty_1852_, v_k_1853_, v_c_1854_, v_pu_boxed_1861_, v_inst_1856_, v_inst_1857_, v_f_1858_, v_toBind_1859_, v_____do__lift_1860_);
return v_res_1862_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(lean_object* v_fvarId_1863_, lean_object* v_i_1864_, lean_object* v_offset_1865_, lean_object* v_toPure_1866_, lean_object* v_y_1867_, lean_object* v_ty_1868_, lean_object* v_k_1869_, lean_object* v_c_1870_, uint8_t v_pu_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_f_1874_, lean_object* v_toBind_1875_, lean_object* v_____do__lift_1876_){
_start:
{
lean_object* v___x_1877_; lean_object* v___f_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1877_ = lean_box(v_pu_1871_);
lean_inc(v_toBind_1875_);
lean_inc(v_f_1874_);
lean_inc(v_y_1867_);
v___f_1878_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed), 15, 14);
lean_closure_set(v___f_1878_, 0, v_fvarId_1863_);
lean_closure_set(v___f_1878_, 1, v_____do__lift_1876_);
lean_closure_set(v___f_1878_, 2, v_i_1864_);
lean_closure_set(v___f_1878_, 3, v_offset_1865_);
lean_closure_set(v___f_1878_, 4, v_toPure_1866_);
lean_closure_set(v___f_1878_, 5, v_y_1867_);
lean_closure_set(v___f_1878_, 6, v_ty_1868_);
lean_closure_set(v___f_1878_, 7, v_k_1869_);
lean_closure_set(v___f_1878_, 8, v_c_1870_);
lean_closure_set(v___f_1878_, 9, v___x_1877_);
lean_closure_set(v___f_1878_, 10, v_inst_1872_);
lean_closure_set(v___f_1878_, 11, v_inst_1873_);
lean_closure_set(v___f_1878_, 12, v_f_1874_);
lean_closure_set(v___f_1878_, 13, v_toBind_1875_);
v___x_1879_ = lean_apply_1(v_f_1874_, v_y_1867_);
v___x_1880_ = lean_apply_4(v_toBind_1875_, lean_box(0), lean_box(0), v___x_1879_, v___f_1878_);
return v___x_1880_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1863_ = stack[0].m_obj;
lean_object* v_i_1864_ = stack[1].m_obj;
lean_object* v_offset_1865_ = stack[2].m_obj;
lean_object* v_toPure_1866_ = stack[3].m_obj;
lean_object* v_y_1867_ = stack[4].m_obj;
lean_object* v_ty_1868_ = stack[5].m_obj;
lean_object* v_k_1869_ = stack[6].m_obj;
lean_object* v_c_1870_ = stack[7].m_obj;
uint8_t v_pu_1871_ = stack[8].m_num;
lean_object* v_inst_1872_ = stack[9].m_obj;
lean_object* v_inst_1873_ = stack[10].m_obj;
lean_object* v_f_1874_ = stack[11].m_obj;
lean_object* v_toBind_1875_ = stack[12].m_obj;
lean_object* v_____do__lift_1876_ = stack[13].m_obj;
lean_object* v_res_1881_;
v_res_1881_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(v_fvarId_1863_, v_i_1864_, v_offset_1865_, v_toPure_1866_, v_y_1867_, v_ty_1868_, v_k_1869_, v_c_1870_, v_pu_1871_, v_inst_1872_, v_inst_1873_, v_f_1874_, v_toBind_1875_, v_____do__lift_1876_);
stack->m_obj
 = v_res_1881_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed(lean_object* v_fvarId_1882_, lean_object* v_i_1883_, lean_object* v_offset_1884_, lean_object* v_toPure_1885_, lean_object* v_y_1886_, lean_object* v_ty_1887_, lean_object* v_k_1888_, lean_object* v_c_1889_, lean_object* v_pu_1890_, lean_object* v_inst_1891_, lean_object* v_inst_1892_, lean_object* v_f_1893_, lean_object* v_toBind_1894_, lean_object* v_____do__lift_1895_){
_start:
{
uint8_t v_pu_boxed_1896_; lean_object* v_res_1897_; 
v_pu_boxed_1896_ = lean_unbox(v_pu_1890_);
v_res_1897_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(v_fvarId_1882_, v_i_1883_, v_offset_1884_, v_toPure_1885_, v_y_1886_, v_ty_1887_, v_k_1888_, v_c_1889_, v_pu_boxed_1896_, v_inst_1891_, v_inst_1892_, v_f_1893_, v_toBind_1894_, v_____do__lift_1895_);
return v_res_1897_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(lean_object* v_fvarId_1898_, lean_object* v_cidx_1899_, lean_object* v_toPure_1900_, lean_object* v_k_1901_, lean_object* v_c_1902_, uint8_t v_pu_1903_, lean_object* v_inst_1904_, lean_object* v_inst_1905_, lean_object* v_f_1906_, lean_object* v_toBind_1907_, lean_object* v_____do__lift_1908_){
_start:
{
lean_object* v___f_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
lean_inc_ref(v_k_1901_);
v___f_1909_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27___boxed), 7, 6);
lean_closure_set(v___f_1909_, 0, v_fvarId_1898_);
lean_closure_set(v___f_1909_, 1, v_____do__lift_1908_);
lean_closure_set(v___f_1909_, 2, v_cidx_1899_);
lean_closure_set(v___f_1909_, 3, v_toPure_1900_);
lean_closure_set(v___f_1909_, 4, v_k_1901_);
lean_closure_set(v___f_1909_, 5, v_c_1902_);
v___x_1910_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1903_, v_inst_1904_, v_inst_1905_, v_f_1906_, v_k_1901_);
v___x_1911_ = lean_apply_4(v_toBind_1907_, lean_box(0), lean_box(0), v___x_1910_, v___f_1909_);
return v___x_1911_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1898_ = stack[0].m_obj;
lean_object* v_cidx_1899_ = stack[1].m_obj;
lean_object* v_toPure_1900_ = stack[2].m_obj;
lean_object* v_k_1901_ = stack[3].m_obj;
lean_object* v_c_1902_ = stack[4].m_obj;
uint8_t v_pu_1903_ = stack[5].m_num;
lean_object* v_inst_1904_ = stack[6].m_obj;
lean_object* v_inst_1905_ = stack[7].m_obj;
lean_object* v_f_1906_ = stack[8].m_obj;
lean_object* v_toBind_1907_ = stack[9].m_obj;
lean_object* v_____do__lift_1908_ = stack[10].m_obj;
lean_object* v_res_1912_;
v_res_1912_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(v_fvarId_1898_, v_cidx_1899_, v_toPure_1900_, v_k_1901_, v_c_1902_, v_pu_1903_, v_inst_1904_, v_inst_1905_, v_f_1906_, v_toBind_1907_, v_____do__lift_1908_);
stack->m_obj
 = v_res_1912_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed(lean_object* v_fvarId_1913_, lean_object* v_cidx_1914_, lean_object* v_toPure_1915_, lean_object* v_k_1916_, lean_object* v_c_1917_, lean_object* v_pu_1918_, lean_object* v_inst_1919_, lean_object* v_inst_1920_, lean_object* v_f_1921_, lean_object* v_toBind_1922_, lean_object* v_____do__lift_1923_){
_start:
{
uint8_t v_pu_boxed_1924_; lean_object* v_res_1925_; 
v_pu_boxed_1924_ = lean_unbox(v_pu_1918_);
v_res_1925_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(v_fvarId_1913_, v_cidx_1914_, v_toPure_1915_, v_k_1916_, v_c_1917_, v_pu_boxed_1924_, v_inst_1919_, v_inst_1920_, v_f_1921_, v_toBind_1922_, v_____do__lift_1923_);
return v_res_1925_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(lean_object* v_fvarId_1926_, lean_object* v_n_1927_, uint8_t v_check_1928_, uint8_t v_persistent_1929_, lean_object* v_toPure_1930_, lean_object* v_k_1931_, lean_object* v_c_1932_, uint8_t v_pu_1933_, lean_object* v_inst_1934_, lean_object* v_inst_1935_, lean_object* v_f_1936_, lean_object* v_toBind_1937_, lean_object* v_____do__lift_1938_){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___f_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1939_ = lean_box(v_check_1928_);
v___x_1940_ = lean_box(v_persistent_1929_);
lean_inc_ref(v_k_1931_);
v___f_1941_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29___boxed), 9, 8);
lean_closure_set(v___f_1941_, 0, v_fvarId_1926_);
lean_closure_set(v___f_1941_, 1, v_____do__lift_1938_);
lean_closure_set(v___f_1941_, 2, v_n_1927_);
lean_closure_set(v___f_1941_, 3, v___x_1939_);
lean_closure_set(v___f_1941_, 4, v___x_1940_);
lean_closure_set(v___f_1941_, 5, v_toPure_1930_);
lean_closure_set(v___f_1941_, 6, v_k_1931_);
lean_closure_set(v___f_1941_, 7, v_c_1932_);
v___x_1942_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1933_, v_inst_1934_, v_inst_1935_, v_f_1936_, v_k_1931_);
v___x_1943_ = lean_apply_4(v_toBind_1937_, lean_box(0), lean_box(0), v___x_1942_, v___f_1941_);
return v___x_1943_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1926_ = stack[0].m_obj;
lean_object* v_n_1927_ = stack[1].m_obj;
uint8_t v_check_1928_ = stack[2].m_num;
uint8_t v_persistent_1929_ = stack[3].m_num;
lean_object* v_toPure_1930_ = stack[4].m_obj;
lean_object* v_k_1931_ = stack[5].m_obj;
lean_object* v_c_1932_ = stack[6].m_obj;
uint8_t v_pu_1933_ = stack[7].m_num;
lean_object* v_inst_1934_ = stack[8].m_obj;
lean_object* v_inst_1935_ = stack[9].m_obj;
lean_object* v_f_1936_ = stack[10].m_obj;
lean_object* v_toBind_1937_ = stack[11].m_obj;
lean_object* v_____do__lift_1938_ = stack[12].m_obj;
lean_object* v_res_1944_;
v_res_1944_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(v_fvarId_1926_, v_n_1927_, v_check_1928_, v_persistent_1929_, v_toPure_1930_, v_k_1931_, v_c_1932_, v_pu_1933_, v_inst_1934_, v_inst_1935_, v_f_1936_, v_toBind_1937_, v_____do__lift_1938_);
stack->m_obj
 = v_res_1944_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed(lean_object* v_fvarId_1945_, lean_object* v_n_1946_, lean_object* v_check_1947_, lean_object* v_persistent_1948_, lean_object* v_toPure_1949_, lean_object* v_k_1950_, lean_object* v_c_1951_, lean_object* v_pu_1952_, lean_object* v_inst_1953_, lean_object* v_inst_1954_, lean_object* v_f_1955_, lean_object* v_toBind_1956_, lean_object* v_____do__lift_1957_){
_start:
{
uint8_t v_check_2998__boxed_1958_; uint8_t v_persistent_2999__boxed_1959_; uint8_t v_pu_boxed_1960_; lean_object* v_res_1961_; 
v_check_2998__boxed_1958_ = lean_unbox(v_check_1947_);
v_persistent_2999__boxed_1959_ = lean_unbox(v_persistent_1948_);
v_pu_boxed_1960_ = lean_unbox(v_pu_1952_);
v_res_1961_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(v_fvarId_1945_, v_n_1946_, v_check_2998__boxed_1958_, v_persistent_2999__boxed_1959_, v_toPure_1949_, v_k_1950_, v_c_1951_, v_pu_boxed_1960_, v_inst_1953_, v_inst_1954_, v_f_1955_, v_toBind_1956_, v_____do__lift_1957_);
return v_res_1961_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(lean_object* v_fvarId_1962_, lean_object* v_n_1963_, uint8_t v_check_1964_, uint8_t v_persistent_1965_, lean_object* v_objs_x3f_1966_, lean_object* v_toPure_1967_, lean_object* v_k_1968_, lean_object* v_c_1969_, uint8_t v_pu_1970_, lean_object* v_inst_1971_, lean_object* v_inst_1972_, lean_object* v_f_1973_, lean_object* v_toBind_1974_, lean_object* v_____do__lift_1975_){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___f_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1976_ = lean_box(v_check_1964_);
v___x_1977_ = lean_box(v_persistent_1965_);
lean_inc_ref(v_k_1968_);
v___f_1978_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed), 10, 9);
lean_closure_set(v___f_1978_, 0, v_fvarId_1962_);
lean_closure_set(v___f_1978_, 1, v_____do__lift_1975_);
lean_closure_set(v___f_1978_, 2, v_n_1963_);
lean_closure_set(v___f_1978_, 3, v___x_1976_);
lean_closure_set(v___f_1978_, 4, v___x_1977_);
lean_closure_set(v___f_1978_, 5, v_objs_x3f_1966_);
lean_closure_set(v___f_1978_, 6, v_toPure_1967_);
lean_closure_set(v___f_1978_, 7, v_k_1968_);
lean_closure_set(v___f_1978_, 8, v_c_1969_);
v___x_1979_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1970_, v_inst_1971_, v_inst_1972_, v_f_1973_, v_k_1968_);
v___x_1980_ = lean_apply_4(v_toBind_1974_, lean_box(0), lean_box(0), v___x_1979_, v___f_1978_);
return v___x_1980_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1962_ = stack[0].m_obj;
lean_object* v_n_1963_ = stack[1].m_obj;
uint8_t v_check_1964_ = stack[2].m_num;
uint8_t v_persistent_1965_ = stack[3].m_num;
lean_object* v_objs_x3f_1966_ = stack[4].m_obj;
lean_object* v_toPure_1967_ = stack[5].m_obj;
lean_object* v_k_1968_ = stack[6].m_obj;
lean_object* v_c_1969_ = stack[7].m_obj;
uint8_t v_pu_1970_ = stack[8].m_num;
lean_object* v_inst_1971_ = stack[9].m_obj;
lean_object* v_inst_1972_ = stack[10].m_obj;
lean_object* v_f_1973_ = stack[11].m_obj;
lean_object* v_toBind_1974_ = stack[12].m_obj;
lean_object* v_____do__lift_1975_ = stack[13].m_obj;
lean_object* v_res_1981_;
v_res_1981_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(v_fvarId_1962_, v_n_1963_, v_check_1964_, v_persistent_1965_, v_objs_x3f_1966_, v_toPure_1967_, v_k_1968_, v_c_1969_, v_pu_1970_, v_inst_1971_, v_inst_1972_, v_f_1973_, v_toBind_1974_, v_____do__lift_1975_);
stack->m_obj
 = v_res_1981_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed(lean_object* v_fvarId_1982_, lean_object* v_n_1983_, lean_object* v_check_1984_, lean_object* v_persistent_1985_, lean_object* v_objs_x3f_1986_, lean_object* v_toPure_1987_, lean_object* v_k_1988_, lean_object* v_c_1989_, lean_object* v_pu_1990_, lean_object* v_inst_1991_, lean_object* v_inst_1992_, lean_object* v_f_1993_, lean_object* v_toBind_1994_, lean_object* v_____do__lift_1995_){
_start:
{
uint8_t v_check_3009__boxed_1996_; uint8_t v_persistent_3010__boxed_1997_; uint8_t v_pu_boxed_1998_; lean_object* v_res_1999_; 
v_check_3009__boxed_1996_ = lean_unbox(v_check_1984_);
v_persistent_3010__boxed_1997_ = lean_unbox(v_persistent_1985_);
v_pu_boxed_1998_ = lean_unbox(v_pu_1990_);
v_res_1999_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(v_fvarId_1982_, v_n_1983_, v_check_3009__boxed_1996_, v_persistent_3010__boxed_1997_, v_objs_x3f_1986_, v_toPure_1987_, v_k_1988_, v_c_1989_, v_pu_boxed_1998_, v_inst_1991_, v_inst_1992_, v_f_1993_, v_toBind_1994_, v_____do__lift_1995_);
return v_res_1999_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(lean_object* v_fvarId_2000_, lean_object* v_toPure_2001_, lean_object* v_k_2002_, lean_object* v_c_2003_, uint8_t v_pu_2004_, lean_object* v_inst_2005_, lean_object* v_inst_2006_, lean_object* v_f_2007_, lean_object* v_toBind_2008_, lean_object* v_____do__lift_2009_){
_start:
{
lean_object* v___f_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
lean_inc_ref(v_k_2002_);
v___f_2010_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed), 6, 5);
lean_closure_set(v___f_2010_, 0, v_fvarId_2000_);
lean_closure_set(v___f_2010_, 1, v_____do__lift_2009_);
lean_closure_set(v___f_2010_, 2, v_toPure_2001_);
lean_closure_set(v___f_2010_, 3, v_k_2002_);
lean_closure_set(v___f_2010_, 4, v_c_2003_);
v___x_2011_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2004_, v_inst_2005_, v_inst_2006_, v_f_2007_, v_k_2002_);
v___x_2012_ = lean_apply_4(v_toBind_2008_, lean_box(0), lean_box(0), v___x_2011_, v___f_2010_);
return v___x_2012_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2000_ = stack[0].m_obj;
lean_object* v_toPure_2001_ = stack[1].m_obj;
lean_object* v_k_2002_ = stack[2].m_obj;
lean_object* v_c_2003_ = stack[3].m_obj;
uint8_t v_pu_2004_ = stack[4].m_num;
lean_object* v_inst_2005_ = stack[5].m_obj;
lean_object* v_inst_2006_ = stack[6].m_obj;
lean_object* v_f_2007_ = stack[7].m_obj;
lean_object* v_toBind_2008_ = stack[8].m_obj;
lean_object* v_____do__lift_2009_ = stack[9].m_obj;
lean_object* v_res_2013_;
v_res_2013_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(v_fvarId_2000_, v_toPure_2001_, v_k_2002_, v_c_2003_, v_pu_2004_, v_inst_2005_, v_inst_2006_, v_f_2007_, v_toBind_2008_, v_____do__lift_2009_);
stack->m_obj
 = v_res_2013_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed(lean_object* v_fvarId_2014_, lean_object* v_toPure_2015_, lean_object* v_k_2016_, lean_object* v_c_2017_, lean_object* v_pu_2018_, lean_object* v_inst_2019_, lean_object* v_inst_2020_, lean_object* v_f_2021_, lean_object* v_toBind_2022_, lean_object* v_____do__lift_2023_){
_start:
{
uint8_t v_pu_boxed_2024_; lean_object* v_res_2025_; 
v_pu_boxed_2024_ = lean_unbox(v_pu_2018_);
v_res_2025_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(v_fvarId_2014_, v_toPure_2015_, v_k_2016_, v_c_2017_, v_pu_boxed_2024_, v_inst_2019_, v_inst_2020_, v_f_2021_, v_toBind_2022_, v_____do__lift_2023_);
return v_res_2025_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(uint8_t v_pu_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_, lean_object* v_f_2029_, lean_object* v_c_2030_){
_start:
{
switch(lean_obj_tag(v_c_2030_))
{
case 0:
{
lean_object* v_toApplicative_2031_; lean_object* v_toBind_2032_; lean_object* v_toPure_2033_; lean_object* v_decl_2034_; lean_object* v_k_2035_; lean_object* v___x_2036_; lean_object* v___f_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v_toApplicative_2031_ = lean_ctor_get(v_inst_2028_, 0);
v_toBind_2032_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc_n(v_toBind_2032_, 2);
v_toPure_2033_ = lean_ctor_get(v_toApplicative_2031_, 1);
v_decl_2034_ = lean_ctor_get(v_c_2030_, 0);
lean_inc_ref_n(v_decl_2034_, 2);
v_k_2035_ = lean_ctor_get(v_c_2030_, 1);
lean_inc_ref(v_k_2035_);
v___x_2036_ = lean_box(v_pu_2026_);
lean_inc(v_f_2029_);
lean_inc_ref(v_inst_2028_);
lean_inc(v_inst_2027_);
lean_inc(v_toPure_2033_);
v___f_2037_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_2037_, 0, v_k_2035_);
lean_closure_set(v___f_2037_, 1, v_toPure_2033_);
lean_closure_set(v___f_2037_, 2, v_decl_2034_);
lean_closure_set(v___f_2037_, 3, v_c_2030_);
lean_closure_set(v___f_2037_, 4, v___x_2036_);
lean_closure_set(v___f_2037_, 5, v_inst_2027_);
lean_closure_set(v___f_2037_, 6, v_inst_2028_);
lean_closure_set(v___f_2037_, 7, v_f_2029_);
lean_closure_set(v___f_2037_, 8, v_toBind_2032_);
v___x_2038_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_2026_, v_inst_2027_, v_inst_2028_, v_f_2029_, v_decl_2034_);
v___x_2039_ = lean_apply_4(v_toBind_2032_, lean_box(0), lean_box(0), v___x_2038_, v___f_2037_);
return v___x_2039_;
}
case 1:
{
lean_object* v_toApplicative_2040_; lean_object* v_decl_2041_; lean_object* v_toBind_2042_; lean_object* v_toPure_2043_; lean_object* v_k_2044_; lean_object* v_params_2045_; lean_object* v_type_2046_; lean_object* v_value_2047_; lean_object* v___x_2048_; lean_object* v___f_2049_; lean_object* v___x_2050_; lean_object* v___f_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; size_t v_sz_2054_; size_t v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v_toApplicative_2040_ = lean_ctor_get(v_inst_2028_, 0);
v_decl_2041_ = lean_ctor_get(v_c_2030_, 0);
lean_inc_ref_n(v_decl_2041_, 2);
v_toBind_2042_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc_n(v_toBind_2042_, 3);
v_toPure_2043_ = lean_ctor_get(v_toApplicative_2040_, 1);
v_k_2044_ = lean_ctor_get(v_c_2030_, 1);
lean_inc_ref(v_k_2044_);
v_params_2045_ = lean_ctor_get(v_decl_2041_, 2);
lean_inc_ref(v_params_2045_);
v_type_2046_ = lean_ctor_get(v_decl_2041_, 3);
lean_inc_ref(v_type_2046_);
v_value_2047_ = lean_ctor_get(v_decl_2041_, 4);
lean_inc_ref(v_value_2047_);
v___x_2048_ = lean_box(v_pu_2026_);
lean_inc_n(v_f_2029_, 2);
lean_inc_ref_n(v_inst_2028_, 3);
lean_inc_n(v_inst_2027_, 2);
lean_inc(v_toPure_2043_);
v___f_2049_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_2049_, 0, v_k_2044_);
lean_closure_set(v___f_2049_, 1, v_toPure_2043_);
lean_closure_set(v___f_2049_, 2, v_decl_2041_);
lean_closure_set(v___f_2049_, 3, v_c_2030_);
lean_closure_set(v___f_2049_, 4, v___x_2048_);
lean_closure_set(v___f_2049_, 5, v_inst_2027_);
lean_closure_set(v___f_2049_, 6, v_inst_2028_);
lean_closure_set(v___f_2049_, 7, v_f_2029_);
lean_closure_set(v___f_2049_, 8, v_toBind_2042_);
v___x_2050_ = lean_box(v_pu_2026_);
v___f_2051_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_2051_, 0, v___x_2050_);
lean_closure_set(v___f_2051_, 1, v_decl_2041_);
lean_closure_set(v___f_2051_, 2, v_inst_2027_);
lean_closure_set(v___f_2051_, 3, v_toBind_2042_);
lean_closure_set(v___f_2051_, 4, v___f_2049_);
lean_closure_set(v___f_2051_, 5, v_inst_2028_);
lean_closure_set(v___f_2051_, 6, v_f_2029_);
lean_closure_set(v___f_2051_, 7, v_value_2047_);
lean_closure_set(v___f_2051_, 8, v_type_2046_);
v___x_2052_ = lean_box(v_pu_2026_);
v___x_2053_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2053_, 0, lean_box(0));
lean_closure_set(v___x_2053_, 1, v___x_2052_);
lean_closure_set(v___x_2053_, 2, v_inst_2027_);
lean_closure_set(v___x_2053_, 3, v_inst_2028_);
lean_closure_set(v___x_2053_, 4, v_f_2029_);
v_sz_2054_ = lean_array_size(v_params_2045_);
v___x_2055_ = ((size_t)0ULL);
v___x_2056_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2028_, v___x_2053_, v_sz_2054_, v___x_2055_, v_params_2045_);
v___x_2057_ = lean_apply_4(v_toBind_2042_, lean_box(0), lean_box(0), v___x_2056_, v___f_2051_);
return v___x_2057_;
}
case 2:
{
lean_object* v_toApplicative_2058_; lean_object* v_decl_2059_; lean_object* v_toBind_2060_; lean_object* v_toPure_2061_; lean_object* v_k_2062_; lean_object* v_params_2063_; lean_object* v_type_2064_; lean_object* v_value_2065_; lean_object* v___x_2066_; lean_object* v___f_2067_; lean_object* v___x_2068_; lean_object* v___f_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; size_t v_sz_2072_; size_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v_toApplicative_2058_ = lean_ctor_get(v_inst_2028_, 0);
v_decl_2059_ = lean_ctor_get(v_c_2030_, 0);
lean_inc_ref_n(v_decl_2059_, 2);
v_toBind_2060_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc_n(v_toBind_2060_, 3);
v_toPure_2061_ = lean_ctor_get(v_toApplicative_2058_, 1);
v_k_2062_ = lean_ctor_get(v_c_2030_, 1);
lean_inc_ref(v_k_2062_);
v_params_2063_ = lean_ctor_get(v_decl_2059_, 2);
lean_inc_ref(v_params_2063_);
v_type_2064_ = lean_ctor_get(v_decl_2059_, 3);
lean_inc_ref(v_type_2064_);
v_value_2065_ = lean_ctor_get(v_decl_2059_, 4);
lean_inc_ref(v_value_2065_);
v___x_2066_ = lean_box(v_pu_2026_);
lean_inc_n(v_f_2029_, 2);
lean_inc_ref_n(v_inst_2028_, 3);
lean_inc_n(v_inst_2027_, 2);
lean_inc(v_toPure_2061_);
v___f_2067_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed), 10, 9);
lean_closure_set(v___f_2067_, 0, v_k_2062_);
lean_closure_set(v___f_2067_, 1, v_toPure_2061_);
lean_closure_set(v___f_2067_, 2, v_decl_2059_);
lean_closure_set(v___f_2067_, 3, v_c_2030_);
lean_closure_set(v___f_2067_, 4, v___x_2066_);
lean_closure_set(v___f_2067_, 5, v_inst_2027_);
lean_closure_set(v___f_2067_, 6, v_inst_2028_);
lean_closure_set(v___f_2067_, 7, v_f_2029_);
lean_closure_set(v___f_2067_, 8, v_toBind_2060_);
v___x_2068_ = lean_box(v_pu_2026_);
v___f_2069_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_2069_, 0, v___x_2068_);
lean_closure_set(v___f_2069_, 1, v_decl_2059_);
lean_closure_set(v___f_2069_, 2, v_inst_2027_);
lean_closure_set(v___f_2069_, 3, v_toBind_2060_);
lean_closure_set(v___f_2069_, 4, v___f_2067_);
lean_closure_set(v___f_2069_, 5, v_inst_2028_);
lean_closure_set(v___f_2069_, 6, v_f_2029_);
lean_closure_set(v___f_2069_, 7, v_value_2065_);
lean_closure_set(v___f_2069_, 8, v_type_2064_);
v___x_2070_ = lean_box(v_pu_2026_);
v___x_2071_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2071_, 0, lean_box(0));
lean_closure_set(v___x_2071_, 1, v___x_2070_);
lean_closure_set(v___x_2071_, 2, v_inst_2027_);
lean_closure_set(v___x_2071_, 3, v_inst_2028_);
lean_closure_set(v___x_2071_, 4, v_f_2029_);
v_sz_2072_ = lean_array_size(v_params_2063_);
v___x_2073_ = ((size_t)0ULL);
v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2028_, v___x_2071_, v_sz_2072_, v___x_2073_, v_params_2063_);
v___x_2075_ = lean_apply_4(v_toBind_2060_, lean_box(0), lean_box(0), v___x_2074_, v___f_2069_);
return v___x_2075_;
}
case 3:
{
lean_object* v_toApplicative_2076_; lean_object* v_toBind_2077_; lean_object* v_toPure_2078_; lean_object* v_fvarId_2079_; lean_object* v_args_2080_; lean_object* v___x_2081_; lean_object* v___f_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v_toApplicative_2076_ = lean_ctor_get(v_inst_2028_, 0);
v_toBind_2077_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc_n(v_toBind_2077_, 2);
v_toPure_2078_ = lean_ctor_get(v_toApplicative_2076_, 1);
lean_inc(v_toPure_2078_);
v_fvarId_2079_ = lean_ctor_get(v_c_2030_, 0);
lean_inc_n(v_fvarId_2079_, 2);
v_args_2080_ = lean_ctor_get(v_c_2030_, 1);
lean_inc_ref(v_args_2080_);
v___x_2081_ = lean_box(v_pu_2026_);
lean_inc(v_f_2029_);
v___f_2082_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_2082_, 0, v_toPure_2078_);
lean_closure_set(v___f_2082_, 1, v_c_2030_);
lean_closure_set(v___f_2082_, 2, v_fvarId_2079_);
lean_closure_set(v___f_2082_, 3, v_args_2080_);
lean_closure_set(v___f_2082_, 4, v___x_2081_);
lean_closure_set(v___f_2082_, 5, v_inst_2027_);
lean_closure_set(v___f_2082_, 6, v_inst_2028_);
lean_closure_set(v___f_2082_, 7, v_f_2029_);
lean_closure_set(v___f_2082_, 8, v_toBind_2077_);
v___x_2083_ = lean_apply_1(v_f_2029_, v_fvarId_2079_);
v___x_2084_ = lean_apply_4(v_toBind_2077_, lean_box(0), lean_box(0), v___x_2083_, v___f_2082_);
return v___x_2084_;
}
case 4:
{
lean_object* v_toApplicative_2085_; lean_object* v_cases_2086_; lean_object* v_toBind_2087_; lean_object* v_toPure_2088_; lean_object* v_typeName_2089_; lean_object* v_resultType_2090_; lean_object* v_discr_2091_; lean_object* v_alts_2092_; lean_object* v___x_2093_; lean_object* v___f_2094_; lean_object* v___f_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v_toApplicative_2085_ = lean_ctor_get(v_inst_2028_, 0);
v_cases_2086_ = lean_ctor_get(v_c_2030_, 0);
v_toBind_2087_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc_n(v_toBind_2087_, 2);
v_toPure_2088_ = lean_ctor_get(v_toApplicative_2085_, 1);
v_typeName_2089_ = lean_ctor_get(v_cases_2086_, 0);
lean_inc(v_typeName_2089_);
v_resultType_2090_ = lean_ctor_get(v_cases_2086_, 1);
lean_inc_ref_n(v_resultType_2090_, 2);
v_discr_2091_ = lean_ctor_get(v_cases_2086_, 2);
lean_inc(v_discr_2091_);
v_alts_2092_ = lean_ctor_get(v_cases_2086_, 3);
lean_inc_ref(v_alts_2092_);
v___x_2093_ = lean_box(v_pu_2026_);
lean_inc_n(v_f_2029_, 2);
lean_inc_ref_n(v_inst_2028_, 2);
v___f_2094_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed), 5, 4);
lean_closure_set(v___f_2094_, 0, v___x_2093_);
lean_closure_set(v___f_2094_, 1, v_inst_2027_);
lean_closure_set(v___f_2094_, 2, v_inst_2028_);
lean_closure_set(v___f_2094_, 3, v_f_2029_);
lean_inc(v_toPure_2088_);
v___f_2095_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14), 11, 10);
lean_closure_set(v___f_2095_, 0, v_typeName_2089_);
lean_closure_set(v___f_2095_, 1, v_toPure_2088_);
lean_closure_set(v___f_2095_, 2, v_alts_2092_);
lean_closure_set(v___f_2095_, 3, v_resultType_2090_);
lean_closure_set(v___f_2095_, 4, v_discr_2091_);
lean_closure_set(v___f_2095_, 5, v_c_2030_);
lean_closure_set(v___f_2095_, 6, v_inst_2028_);
lean_closure_set(v___f_2095_, 7, v___f_2094_);
lean_closure_set(v___f_2095_, 8, v_toBind_2087_);
lean_closure_set(v___f_2095_, 9, v_f_2029_);
v___x_2096_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2028_, v_f_2029_, v_resultType_2090_);
v___x_2097_ = lean_apply_4(v_toBind_2087_, lean_box(0), lean_box(0), v___x_2096_, v___f_2095_);
return v___x_2097_;
}
case 5:
{
lean_object* v_toApplicative_2098_; lean_object* v_toBind_2099_; lean_object* v_toPure_2100_; lean_object* v_fvarId_2101_; lean_object* v___f_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v_toApplicative_2098_ = lean_ctor_get(v_inst_2028_, 0);
lean_inc_ref(v_toApplicative_2098_);
lean_dec(v_inst_2027_);
v_toBind_2099_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc(v_toBind_2099_);
lean_dec_ref(v_inst_2028_);
v_toPure_2100_ = lean_ctor_get(v_toApplicative_2098_, 1);
lean_inc(v_toPure_2100_);
lean_dec_ref(v_toApplicative_2098_);
v_fvarId_2101_ = lean_ctor_get(v_c_2030_, 0);
lean_inc_n(v_fvarId_2101_, 2);
v___f_2102_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed), 4, 3);
lean_closure_set(v___f_2102_, 0, v_fvarId_2101_);
lean_closure_set(v___f_2102_, 1, v_toPure_2100_);
lean_closure_set(v___f_2102_, 2, v_c_2030_);
v___x_2103_ = lean_apply_1(v_f_2029_, v_fvarId_2101_);
v___x_2104_ = lean_apply_4(v_toBind_2099_, lean_box(0), lean_box(0), v___x_2103_, v___f_2102_);
return v___x_2104_;
}
case 6:
{
lean_object* v_toApplicative_2105_; lean_object* v_toBind_2106_; lean_object* v_toPure_2107_; lean_object* v_type_2108_; lean_object* v___f_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v_toApplicative_2105_ = lean_ctor_get(v_inst_2028_, 0);
lean_dec(v_inst_2027_);
v_toBind_2106_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc(v_toBind_2106_);
v_toPure_2107_ = lean_ctor_get(v_toApplicative_2105_, 1);
v_type_2108_ = lean_ctor_get(v_c_2030_, 0);
lean_inc_ref_n(v_type_2108_, 2);
lean_inc(v_toPure_2107_);
v___f_2109_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed), 4, 3);
lean_closure_set(v___f_2109_, 0, v_type_2108_);
lean_closure_set(v___f_2109_, 1, v_toPure_2107_);
lean_closure_set(v___f_2109_, 2, v_c_2030_);
v___x_2110_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2028_, v_f_2029_, v_type_2108_);
v___x_2111_ = lean_apply_4(v_toBind_2106_, lean_box(0), lean_box(0), v___x_2110_, v___f_2109_);
return v___x_2111_;
}
case 7:
{
lean_object* v_toApplicative_2112_; lean_object* v_toBind_2113_; lean_object* v_toPure_2114_; lean_object* v_fvarId_2115_; lean_object* v_i_2116_; lean_object* v_y_2117_; lean_object* v_k_2118_; lean_object* v___x_2119_; lean_object* v___f_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_toApplicative_2112_ = lean_ctor_get(v_inst_2028_, 0);
v_toBind_2113_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc_n(v_toBind_2113_, 2);
v_toPure_2114_ = lean_ctor_get(v_toApplicative_2112_, 1);
lean_inc(v_toPure_2114_);
v_fvarId_2115_ = lean_ctor_get(v_c_2030_, 0);
lean_inc_n(v_fvarId_2115_, 2);
v_i_2116_ = lean_ctor_get(v_c_2030_, 1);
lean_inc(v_i_2116_);
v_y_2117_ = lean_ctor_get(v_c_2030_, 2);
lean_inc(v_y_2117_);
v_k_2118_ = lean_ctor_get(v_c_2030_, 3);
lean_inc_ref(v_k_2118_);
v___x_2119_ = lean_box(v_pu_2026_);
lean_inc(v_f_2029_);
v___f_2120_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed), 12, 11);
lean_closure_set(v___f_2120_, 0, v_fvarId_2115_);
lean_closure_set(v___f_2120_, 1, v_i_2116_);
lean_closure_set(v___f_2120_, 2, v_toPure_2114_);
lean_closure_set(v___f_2120_, 3, v_y_2117_);
lean_closure_set(v___f_2120_, 4, v_k_2118_);
lean_closure_set(v___f_2120_, 5, v_c_2030_);
lean_closure_set(v___f_2120_, 6, v___x_2119_);
lean_closure_set(v___f_2120_, 7, v_inst_2027_);
lean_closure_set(v___f_2120_, 8, v_inst_2028_);
lean_closure_set(v___f_2120_, 9, v_f_2029_);
lean_closure_set(v___f_2120_, 10, v_toBind_2113_);
v___x_2121_ = lean_apply_1(v_f_2029_, v_fvarId_2115_);
v___x_2122_ = lean_apply_4(v_toBind_2113_, lean_box(0), lean_box(0), v___x_2121_, v___f_2120_);
return v___x_2122_;
}
case 8:
{
lean_object* v_toApplicative_2123_; lean_object* v_toBind_2124_; lean_object* v_toPure_2125_; lean_object* v_fvarId_2126_; lean_object* v_i_2127_; lean_object* v_y_2128_; lean_object* v_k_2129_; lean_object* v___x_2130_; lean_object* v___f_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_toApplicative_2123_ = lean_ctor_get(v_inst_2028_, 0);
v_toBind_2124_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc_n(v_toBind_2124_, 2);
v_toPure_2125_ = lean_ctor_get(v_toApplicative_2123_, 1);
lean_inc(v_toPure_2125_);
v_fvarId_2126_ = lean_ctor_get(v_c_2030_, 0);
lean_inc_n(v_fvarId_2126_, 2);
v_i_2127_ = lean_ctor_get(v_c_2030_, 1);
lean_inc(v_i_2127_);
v_y_2128_ = lean_ctor_get(v_c_2030_, 2);
lean_inc(v_y_2128_);
v_k_2129_ = lean_ctor_get(v_c_2030_, 3);
lean_inc_ref(v_k_2129_);
v___x_2130_ = lean_box(v_pu_2026_);
lean_inc(v_f_2029_);
v___f_2131_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed), 12, 11);
lean_closure_set(v___f_2131_, 0, v_fvarId_2126_);
lean_closure_set(v___f_2131_, 1, v_i_2127_);
lean_closure_set(v___f_2131_, 2, v_toPure_2125_);
lean_closure_set(v___f_2131_, 3, v_y_2128_);
lean_closure_set(v___f_2131_, 4, v_k_2129_);
lean_closure_set(v___f_2131_, 5, v_c_2030_);
lean_closure_set(v___f_2131_, 6, v___x_2130_);
lean_closure_set(v___f_2131_, 7, v_inst_2027_);
lean_closure_set(v___f_2131_, 8, v_inst_2028_);
lean_closure_set(v___f_2131_, 9, v_f_2029_);
lean_closure_set(v___f_2131_, 10, v_toBind_2124_);
v___x_2132_ = lean_apply_1(v_f_2029_, v_fvarId_2126_);
v___x_2133_ = lean_apply_4(v_toBind_2124_, lean_box(0), lean_box(0), v___x_2132_, v___f_2131_);
return v___x_2133_;
}
case 9:
{
lean_object* v_toApplicative_2134_; lean_object* v_toBind_2135_; lean_object* v_toPure_2136_; lean_object* v_fvarId_2137_; lean_object* v_i_2138_; lean_object* v_offset_2139_; lean_object* v_y_2140_; lean_object* v_ty_2141_; lean_object* v_k_2142_; lean_object* v___x_2143_; lean_object* v___f_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v_toApplicative_2134_ = lean_ctor_get(v_inst_2028_, 0);
v_toBind_2135_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc_n(v_toBind_2135_, 2);
v_toPure_2136_ = lean_ctor_get(v_toApplicative_2134_, 1);
lean_inc(v_toPure_2136_);
v_fvarId_2137_ = lean_ctor_get(v_c_2030_, 0);
lean_inc_n(v_fvarId_2137_, 2);
v_i_2138_ = lean_ctor_get(v_c_2030_, 1);
lean_inc(v_i_2138_);
v_offset_2139_ = lean_ctor_get(v_c_2030_, 2);
lean_inc(v_offset_2139_);
v_y_2140_ = lean_ctor_get(v_c_2030_, 3);
lean_inc(v_y_2140_);
v_ty_2141_ = lean_ctor_get(v_c_2030_, 4);
lean_inc_ref(v_ty_2141_);
v_k_2142_ = lean_ctor_get(v_c_2030_, 5);
lean_inc_ref(v_k_2142_);
v___x_2143_ = lean_box(v_pu_2026_);
lean_inc(v_f_2029_);
v___f_2144_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed), 14, 13);
lean_closure_set(v___f_2144_, 0, v_fvarId_2137_);
lean_closure_set(v___f_2144_, 1, v_i_2138_);
lean_closure_set(v___f_2144_, 2, v_offset_2139_);
lean_closure_set(v___f_2144_, 3, v_toPure_2136_);
lean_closure_set(v___f_2144_, 4, v_y_2140_);
lean_closure_set(v___f_2144_, 5, v_ty_2141_);
lean_closure_set(v___f_2144_, 6, v_k_2142_);
lean_closure_set(v___f_2144_, 7, v_c_2030_);
lean_closure_set(v___f_2144_, 8, v___x_2143_);
lean_closure_set(v___f_2144_, 9, v_inst_2027_);
lean_closure_set(v___f_2144_, 10, v_inst_2028_);
lean_closure_set(v___f_2144_, 11, v_f_2029_);
lean_closure_set(v___f_2144_, 12, v_toBind_2135_);
v___x_2145_ = lean_apply_1(v_f_2029_, v_fvarId_2137_);
v___x_2146_ = lean_apply_4(v_toBind_2135_, lean_box(0), lean_box(0), v___x_2145_, v___f_2144_);
return v___x_2146_;
}
case 10:
{
lean_object* v_toApplicative_2147_; lean_object* v_toBind_2148_; lean_object* v_toPure_2149_; lean_object* v_fvarId_2150_; lean_object* v_cidx_2151_; lean_object* v_k_2152_; lean_object* v___x_2153_; lean_object* v___f_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v_toApplicative_2147_ = lean_ctor_get(v_inst_2028_, 0);
v_toBind_2148_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc_n(v_toBind_2148_, 2);
v_toPure_2149_ = lean_ctor_get(v_toApplicative_2147_, 1);
lean_inc(v_toPure_2149_);
v_fvarId_2150_ = lean_ctor_get(v_c_2030_, 0);
lean_inc_n(v_fvarId_2150_, 2);
v_cidx_2151_ = lean_ctor_get(v_c_2030_, 1);
lean_inc(v_cidx_2151_);
v_k_2152_ = lean_ctor_get(v_c_2030_, 2);
lean_inc_ref(v_k_2152_);
v___x_2153_ = lean_box(v_pu_2026_);
lean_inc(v_f_2029_);
v___f_2154_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed), 11, 10);
lean_closure_set(v___f_2154_, 0, v_fvarId_2150_);
lean_closure_set(v___f_2154_, 1, v_cidx_2151_);
lean_closure_set(v___f_2154_, 2, v_toPure_2149_);
lean_closure_set(v___f_2154_, 3, v_k_2152_);
lean_closure_set(v___f_2154_, 4, v_c_2030_);
lean_closure_set(v___f_2154_, 5, v___x_2153_);
lean_closure_set(v___f_2154_, 6, v_inst_2027_);
lean_closure_set(v___f_2154_, 7, v_inst_2028_);
lean_closure_set(v___f_2154_, 8, v_f_2029_);
lean_closure_set(v___f_2154_, 9, v_toBind_2148_);
v___x_2155_ = lean_apply_1(v_f_2029_, v_fvarId_2150_);
v___x_2156_ = lean_apply_4(v_toBind_2148_, lean_box(0), lean_box(0), v___x_2155_, v___f_2154_);
return v___x_2156_;
}
case 11:
{
lean_object* v_toApplicative_2157_; lean_object* v_toBind_2158_; lean_object* v_toPure_2159_; lean_object* v_fvarId_2160_; lean_object* v_n_2161_; uint8_t v_check_2162_; uint8_t v_persistent_2163_; lean_object* v_k_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___f_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_toApplicative_2157_ = lean_ctor_get(v_inst_2028_, 0);
v_toBind_2158_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc_n(v_toBind_2158_, 2);
v_toPure_2159_ = lean_ctor_get(v_toApplicative_2157_, 1);
lean_inc(v_toPure_2159_);
v_fvarId_2160_ = lean_ctor_get(v_c_2030_, 0);
lean_inc_n(v_fvarId_2160_, 2);
v_n_2161_ = lean_ctor_get(v_c_2030_, 1);
lean_inc(v_n_2161_);
v_check_2162_ = lean_ctor_get_uint8(v_c_2030_, sizeof(void*)*3);
v_persistent_2163_ = lean_ctor_get_uint8(v_c_2030_, sizeof(void*)*3 + 1);
v_k_2164_ = lean_ctor_get(v_c_2030_, 2);
lean_inc_ref(v_k_2164_);
v___x_2165_ = lean_box(v_check_2162_);
v___x_2166_ = lean_box(v_persistent_2163_);
v___x_2167_ = lean_box(v_pu_2026_);
lean_inc(v_f_2029_);
v___f_2168_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed), 13, 12);
lean_closure_set(v___f_2168_, 0, v_fvarId_2160_);
lean_closure_set(v___f_2168_, 1, v_n_2161_);
lean_closure_set(v___f_2168_, 2, v___x_2165_);
lean_closure_set(v___f_2168_, 3, v___x_2166_);
lean_closure_set(v___f_2168_, 4, v_toPure_2159_);
lean_closure_set(v___f_2168_, 5, v_k_2164_);
lean_closure_set(v___f_2168_, 6, v_c_2030_);
lean_closure_set(v___f_2168_, 7, v___x_2167_);
lean_closure_set(v___f_2168_, 8, v_inst_2027_);
lean_closure_set(v___f_2168_, 9, v_inst_2028_);
lean_closure_set(v___f_2168_, 10, v_f_2029_);
lean_closure_set(v___f_2168_, 11, v_toBind_2158_);
v___x_2169_ = lean_apply_1(v_f_2029_, v_fvarId_2160_);
v___x_2170_ = lean_apply_4(v_toBind_2158_, lean_box(0), lean_box(0), v___x_2169_, v___f_2168_);
return v___x_2170_;
}
case 12:
{
lean_object* v_toApplicative_2171_; lean_object* v_toBind_2172_; lean_object* v_toPure_2173_; lean_object* v_fvarId_2174_; lean_object* v_n_2175_; uint8_t v_check_2176_; uint8_t v_persistent_2177_; lean_object* v_objs_x3f_2178_; lean_object* v_k_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___f_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v_toApplicative_2171_ = lean_ctor_get(v_inst_2028_, 0);
v_toBind_2172_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc_n(v_toBind_2172_, 2);
v_toPure_2173_ = lean_ctor_get(v_toApplicative_2171_, 1);
lean_inc(v_toPure_2173_);
v_fvarId_2174_ = lean_ctor_get(v_c_2030_, 0);
lean_inc_n(v_fvarId_2174_, 2);
v_n_2175_ = lean_ctor_get(v_c_2030_, 1);
lean_inc(v_n_2175_);
v_check_2176_ = lean_ctor_get_uint8(v_c_2030_, sizeof(void*)*4);
v_persistent_2177_ = lean_ctor_get_uint8(v_c_2030_, sizeof(void*)*4 + 1);
v_objs_x3f_2178_ = lean_ctor_get(v_c_2030_, 2);
lean_inc(v_objs_x3f_2178_);
v_k_2179_ = lean_ctor_get(v_c_2030_, 3);
lean_inc_ref(v_k_2179_);
v___x_2180_ = lean_box(v_check_2176_);
v___x_2181_ = lean_box(v_persistent_2177_);
v___x_2182_ = lean_box(v_pu_2026_);
lean_inc(v_f_2029_);
v___f_2183_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed), 14, 13);
lean_closure_set(v___f_2183_, 0, v_fvarId_2174_);
lean_closure_set(v___f_2183_, 1, v_n_2175_);
lean_closure_set(v___f_2183_, 2, v___x_2180_);
lean_closure_set(v___f_2183_, 3, v___x_2181_);
lean_closure_set(v___f_2183_, 4, v_objs_x3f_2178_);
lean_closure_set(v___f_2183_, 5, v_toPure_2173_);
lean_closure_set(v___f_2183_, 6, v_k_2179_);
lean_closure_set(v___f_2183_, 7, v_c_2030_);
lean_closure_set(v___f_2183_, 8, v___x_2182_);
lean_closure_set(v___f_2183_, 9, v_inst_2027_);
lean_closure_set(v___f_2183_, 10, v_inst_2028_);
lean_closure_set(v___f_2183_, 11, v_f_2029_);
lean_closure_set(v___f_2183_, 12, v_toBind_2172_);
v___x_2184_ = lean_apply_1(v_f_2029_, v_fvarId_2174_);
v___x_2185_ = lean_apply_4(v_toBind_2172_, lean_box(0), lean_box(0), v___x_2184_, v___f_2183_);
return v___x_2185_;
}
default: 
{
lean_object* v_toApplicative_2186_; lean_object* v_toBind_2187_; lean_object* v_toPure_2188_; lean_object* v_fvarId_2189_; lean_object* v_k_2190_; lean_object* v___x_2191_; lean_object* v___f_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v_toApplicative_2186_ = lean_ctor_get(v_inst_2028_, 0);
v_toBind_2187_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc_n(v_toBind_2187_, 2);
v_toPure_2188_ = lean_ctor_get(v_toApplicative_2186_, 1);
lean_inc(v_toPure_2188_);
v_fvarId_2189_ = lean_ctor_get(v_c_2030_, 0);
lean_inc_n(v_fvarId_2189_, 2);
v_k_2190_ = lean_ctor_get(v_c_2030_, 1);
lean_inc_ref(v_k_2190_);
v___x_2191_ = lean_box(v_pu_2026_);
lean_inc(v_f_2029_);
v___f_2192_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed), 10, 9);
lean_closure_set(v___f_2192_, 0, v_fvarId_2189_);
lean_closure_set(v___f_2192_, 1, v_toPure_2188_);
lean_closure_set(v___f_2192_, 2, v_k_2190_);
lean_closure_set(v___f_2192_, 3, v_c_2030_);
lean_closure_set(v___f_2192_, 4, v___x_2191_);
lean_closure_set(v___f_2192_, 5, v_inst_2027_);
lean_closure_set(v___f_2192_, 6, v_inst_2028_);
lean_closure_set(v___f_2192_, 7, v_f_2029_);
lean_closure_set(v___f_2192_, 8, v_toBind_2187_);
v___x_2193_ = lean_apply_1(v_f_2029_, v_fvarId_2189_);
v___x_2194_ = lean_apply_4(v_toBind_2187_, lean_box(0), lean_box(0), v___x_2193_, v___f_2192_);
return v___x_2194_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2026_ = stack[0].m_num;
lean_object* v_inst_2027_ = stack[1].m_obj;
lean_object* v_inst_2028_ = stack[2].m_obj;
lean_object* v_f_2029_ = stack[3].m_obj;
lean_object* v_c_2030_ = stack[4].m_obj;
lean_object* v_res_2195_;
v_res_2195_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2026_, v_inst_2027_, v_inst_2028_, v_f_2029_, v_c_2030_);
stack->m_obj
 = v_res_2195_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed(lean_object* v_pu_2196_, lean_object* v_inst_2197_, lean_object* v_inst_2198_, lean_object* v_f_2199_, lean_object* v_c_2200_){
_start:
{
uint8_t v_pu_boxed_2201_; lean_object* v_res_2202_; 
v_pu_boxed_2201_ = lean_unbox(v_pu_2196_);
v_res_2202_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_boxed_2201_, v_inst_2197_, v_inst_2198_, v_f_2199_, v_c_2200_);
return v_res_2202_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(uint8_t v_pu_2203_, lean_object* v_inst_2204_, lean_object* v_inst_2205_, lean_object* v_f_2206_, lean_object* v_x_2207_){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = lean_box(v_pu_2203_);
lean_inc_ref(v_inst_2205_);
v___x_2209_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed), 5, 4);
lean_closure_set(v___x_2209_, 0, v___x_2208_);
lean_closure_set(v___x_2209_, 1, v_inst_2204_);
lean_closure_set(v___x_2209_, 2, v_inst_2205_);
lean_closure_set(v___x_2209_, 3, v_f_2206_);
v___x_2210_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg(v_inst_2205_, v_x_2207_, v___x_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2203_ = stack[0].m_num;
lean_object* v_inst_2204_ = stack[1].m_obj;
lean_object* v_inst_2205_ = stack[2].m_obj;
lean_object* v_f_2206_ = stack[3].m_obj;
lean_object* v_x_2207_ = stack[4].m_obj;
lean_object* v_res_2211_;
v_res_2211_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(v_pu_2203_, v_inst_2204_, v_inst_2205_, v_f_2206_, v_x_2207_);
stack->m_obj
 = v_res_2211_;
}
lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM(lean_object* v_m_2212_, uint8_t v_pu_2213_, lean_object* v_inst_2214_, lean_object* v_inst_2215_, lean_object* v_f_2216_, lean_object* v_c_2217_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2213_, v_inst_2214_, v_inst_2215_, v_f_2216_, v_c_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_mapFVarM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2213_ = stack[1].m_num;
lean_object* v_inst_2214_ = stack[2].m_obj;
lean_object* v_inst_2215_ = stack[3].m_obj;
lean_object* v_f_2216_ = stack[4].m_obj;
lean_object* v_c_2217_ = stack[5].m_obj;
lean_object* v_res_2219_;
v_res_2219_ = l_Lean_Compiler_LCNF_Code_mapFVarM(lean_box(0), v_pu_2213_, v_inst_2214_, v_inst_2215_, v_f_2216_, v_c_2217_);
stack->m_obj
 = v_res_2219_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___boxed(lean_object* v_m_2220_, lean_object* v_pu_2221_, lean_object* v_inst_2222_, lean_object* v_inst_2223_, lean_object* v_f_2224_, lean_object* v_c_2225_){
_start:
{
uint8_t v_pu_boxed_2226_; lean_object* v_res_2227_; 
v_pu_boxed_2226_ = lean_unbox(v_pu_2221_);
v_res_2227_ = l_Lean_Compiler_LCNF_Code_mapFVarM(v_m_2220_, v_pu_boxed_2226_, v_inst_2222_, v_inst_2223_, v_f_2224_, v_c_2225_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1(lean_object* v_inst_2228_, lean_object* v_f_2229_, lean_object* v_type_2230_, lean_object* v_toBind_2231_, lean_object* v___f_2232_, lean_object* v_____r_2233_){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2228_, v_f_2229_, v_type_2230_);
v___x_2235_ = lean_apply_4(v_toBind_2231_, lean_box(0), lean_box(0), v___x_2234_, v___f_2232_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12(lean_object* v_inst_2236_, lean_object* v_f_2237_, lean_object* v_ty_2238_, lean_object* v_toBind_2239_, lean_object* v___f_2240_, lean_object* v_____r_2241_){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2236_, v_f_2237_, v_ty_2238_);
v___x_2243_ = lean_apply_4(v_toBind_2239_, lean_box(0), lean_box(0), v___x_2242_, v___f_2240_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4(lean_object* v_toApplicative_2244_, lean_object* v_args_2245_, lean_object* v_inst_2246_, lean_object* v___f_2247_, lean_object* v_____r_2248_){
_start:
{
lean_object* v_toPure_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; uint8_t v___x_2253_; 
v_toPure_2249_ = lean_ctor_get(v_toApplicative_2244_, 1);
lean_inc(v_toPure_2249_);
lean_dec_ref(v_toApplicative_2244_);
v___x_2250_ = lean_unsigned_to_nat(0u);
v___x_2251_ = lean_array_get_size(v_args_2245_);
v___x_2252_ = lean_box(0);
v___x_2253_ = lean_nat_dec_lt(v___x_2250_, v___x_2251_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; 
lean_dec(v___f_2247_);
lean_dec_ref(v_inst_2246_);
lean_dec_ref(v_args_2245_);
v___x_2254_ = lean_apply_2(v_toPure_2249_, lean_box(0), v___x_2252_);
return v___x_2254_;
}
else
{
uint8_t v___x_2255_; 
v___x_2255_ = lean_nat_dec_le(v___x_2251_, v___x_2251_);
if (v___x_2255_ == 0)
{
if (v___x_2253_ == 0)
{
lean_object* v___x_2256_; 
lean_dec(v___f_2247_);
lean_dec_ref(v_inst_2246_);
lean_dec_ref(v_args_2245_);
v___x_2256_ = lean_apply_2(v_toPure_2249_, lean_box(0), v___x_2252_);
return v___x_2256_;
}
else
{
size_t v___x_2257_; size_t v___x_2258_; lean_object* v___x_2259_; 
lean_dec(v_toPure_2249_);
v___x_2257_ = ((size_t)0ULL);
v___x_2258_ = lean_usize_of_nat(v___x_2251_);
v___x_2259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2246_, v___f_2247_, v_args_2245_, v___x_2257_, v___x_2258_, v___x_2252_);
return v___x_2259_;
}
}
else
{
size_t v___x_2260_; size_t v___x_2261_; lean_object* v___x_2262_; 
lean_dec(v_toPure_2249_);
v___x_2260_ = ((size_t)0ULL);
v___x_2261_ = lean_usize_of_nat(v___x_2251_);
v___x_2262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2246_, v___f_2247_, v_args_2245_, v___x_2260_, v___x_2261_, v___x_2252_);
return v___x_2262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3(lean_object* v_inst_2263_, lean_object* v_f_2264_, lean_object* v_x_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_2263_, v_f_2264_, v___y_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10(lean_object* v_inst_2268_, lean_object* v_f_2269_, lean_object* v_y_2270_, lean_object* v_toBind_2271_, lean_object* v___f_2272_, lean_object* v_____r_2273_){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2268_, v_f_2269_, v_y_2270_);
v___x_2275_ = lean_apply_4(v_toBind_2271_, lean_box(0), lean_box(0), v___x_2274_, v___f_2272_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11(lean_object* v_f_2276_, lean_object* v_y_2277_, lean_object* v_toBind_2278_, lean_object* v___f_2279_, lean_object* v_____r_2280_){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = lean_apply_1(v_f_2276_, v_y_2277_);
v___x_2282_ = lean_apply_4(v_toBind_2278_, lean_box(0), lean_box(0), v___x_2281_, v___f_2279_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7(lean_object* v_f_2283_, lean_object* v_discr_2284_, lean_object* v_toBind_2285_, lean_object* v___f_2286_, lean_object* v_____r_2287_){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = lean_apply_1(v_f_2283_, v_discr_2284_);
v___x_2289_ = lean_apply_4(v_toBind_2285_, lean_box(0), lean_box(0), v___x_2288_, v___f_2286_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6(lean_object* v_toApplicative_2290_, lean_object* v_alts_2291_, lean_object* v_inst_2292_, lean_object* v___f_2293_, lean_object* v_____r_2294_){
_start:
{
lean_object* v_toPure_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v_toPure_2295_ = lean_ctor_get(v_toApplicative_2290_, 1);
lean_inc(v_toPure_2295_);
lean_dec_ref(v_toApplicative_2290_);
v___x_2296_ = lean_unsigned_to_nat(0u);
v___x_2297_ = lean_array_get_size(v_alts_2291_);
v___x_2298_ = lean_box(0);
v___x_2299_ = lean_nat_dec_lt(v___x_2296_, v___x_2297_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; 
lean_dec(v___f_2293_);
lean_dec_ref(v_inst_2292_);
lean_dec_ref(v_alts_2291_);
v___x_2300_ = lean_apply_2(v_toPure_2295_, lean_box(0), v___x_2298_);
return v___x_2300_;
}
else
{
uint8_t v___x_2301_; 
v___x_2301_ = lean_nat_dec_le(v___x_2297_, v___x_2297_);
if (v___x_2301_ == 0)
{
if (v___x_2299_ == 0)
{
lean_object* v___x_2302_; 
lean_dec(v___f_2293_);
lean_dec_ref(v_inst_2292_);
lean_dec_ref(v_alts_2291_);
v___x_2302_ = lean_apply_2(v_toPure_2295_, lean_box(0), v___x_2298_);
return v___x_2302_;
}
else
{
size_t v___x_2303_; size_t v___x_2304_; lean_object* v___x_2305_; 
lean_dec(v_toPure_2295_);
v___x_2303_ = ((size_t)0ULL);
v___x_2304_ = lean_usize_of_nat(v___x_2297_);
v___x_2305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2292_, v___f_2293_, v_alts_2291_, v___x_2303_, v___x_2304_, v___x_2298_);
return v___x_2305_;
}
}
else
{
size_t v___x_2306_; size_t v___x_2307_; lean_object* v___x_2308_; 
lean_dec(v_toPure_2295_);
v___x_2306_ = ((size_t)0ULL);
v___x_2307_ = lean_usize_of_nat(v___x_2297_);
v___x_2308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2292_, v___f_2293_, v_alts_2291_, v___x_2306_, v___x_2307_, v___x_2298_);
return v___x_2308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8(lean_object* v_inst_2309_, lean_object* v_f_2310_, lean_object* v_x_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2309_, v_f_2310_, v___y_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5(lean_object* v_inst_2314_, lean_object* v_f_2315_, lean_object* v_x_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg), 3, 2);
lean_closure_set(v___x_2318_, 0, v_inst_2314_);
lean_closure_set(v___x_2318_, 1, v_f_2315_);
v___x_2319_ = l_Lean_Compiler_LCNF_Alt_forCodeM___redArg(v___y_2317_, v___x_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2(lean_object* v_inst_2320_, lean_object* v_f_2321_, lean_object* v_value_2322_, lean_object* v_toBind_2323_, lean_object* v___f_2324_, lean_object* v_____r_2325_){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2320_, v_f_2321_, v_value_2322_);
v___x_2327_ = lean_apply_4(v_toBind_2323_, lean_box(0), lean_box(0), v___x_2326_, v___f_2324_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg(lean_object* v_inst_2328_, lean_object* v_f_2329_, lean_object* v_c_2330_){
_start:
{
switch(lean_obj_tag(v_c_2330_))
{
case 0:
{
lean_object* v_toBind_2331_; lean_object* v_decl_2332_; lean_object* v_k_2333_; lean_object* v___f_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_toBind_2331_ = lean_ctor_get(v_inst_2328_, 1);
lean_inc(v_toBind_2331_);
v_decl_2332_ = lean_ctor_get(v_c_2330_, 0);
lean_inc_ref(v_decl_2332_);
v_k_2333_ = lean_ctor_get(v_c_2330_, 1);
lean_inc_ref(v_k_2333_);
lean_dec_ref_known(v_c_2330_, 2);
lean_inc(v_f_2329_);
lean_inc_ref(v_inst_2328_);
v___f_2334_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2334_, 0, v_inst_2328_);
lean_closure_set(v___f_2334_, 1, v_f_2329_);
lean_closure_set(v___f_2334_, 2, v_k_2333_);
v___x_2335_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_2328_, v_f_2329_, v_decl_2332_);
v___x_2336_ = lean_apply_4(v_toBind_2331_, lean_box(0), lean_box(0), v___x_2335_, v___f_2334_);
return v___x_2336_;
}
case 3:
{
lean_object* v_toApplicative_2337_; lean_object* v_toBind_2338_; lean_object* v_fvarId_2339_; lean_object* v_args_2340_; lean_object* v___f_2341_; lean_object* v___f_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v_toApplicative_2337_ = lean_ctor_get(v_inst_2328_, 0);
lean_inc_ref(v_toApplicative_2337_);
v_toBind_2338_ = lean_ctor_get(v_inst_2328_, 1);
lean_inc(v_toBind_2338_);
v_fvarId_2339_ = lean_ctor_get(v_c_2330_, 0);
lean_inc(v_fvarId_2339_);
v_args_2340_ = lean_ctor_get(v_c_2330_, 1);
lean_inc_ref(v_args_2340_);
lean_dec_ref_known(v_c_2330_, 2);
lean_inc(v_f_2329_);
lean_inc_ref(v_inst_2328_);
v___f_2341_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8), 4, 2);
lean_closure_set(v___f_2341_, 0, v_inst_2328_);
lean_closure_set(v___f_2341_, 1, v_f_2329_);
v___f_2342_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2342_, 0, v_toApplicative_2337_);
lean_closure_set(v___f_2342_, 1, v_args_2340_);
lean_closure_set(v___f_2342_, 2, v_inst_2328_);
lean_closure_set(v___f_2342_, 3, v___f_2341_);
v___x_2343_ = lean_apply_1(v_f_2329_, v_fvarId_2339_);
v___x_2344_ = lean_apply_4(v_toBind_2338_, lean_box(0), lean_box(0), v___x_2343_, v___f_2342_);
return v___x_2344_;
}
case 4:
{
lean_object* v_cases_2345_; lean_object* v_toApplicative_2346_; lean_object* v_toBind_2347_; lean_object* v_resultType_2348_; lean_object* v_discr_2349_; lean_object* v_alts_2350_; lean_object* v___f_2351_; lean_object* v___f_2352_; lean_object* v___f_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v_cases_2345_ = lean_ctor_get(v_c_2330_, 0);
lean_inc_ref(v_cases_2345_);
lean_dec_ref_known(v_c_2330_, 1);
v_toApplicative_2346_ = lean_ctor_get(v_inst_2328_, 0);
v_toBind_2347_ = lean_ctor_get(v_inst_2328_, 1);
lean_inc_n(v_toBind_2347_, 2);
v_resultType_2348_ = lean_ctor_get(v_cases_2345_, 1);
lean_inc_ref(v_resultType_2348_);
v_discr_2349_ = lean_ctor_get(v_cases_2345_, 2);
lean_inc(v_discr_2349_);
v_alts_2350_ = lean_ctor_get(v_cases_2345_, 3);
lean_inc_ref(v_alts_2350_);
lean_dec_ref(v_cases_2345_);
lean_inc_n(v_f_2329_, 2);
lean_inc_ref_n(v_inst_2328_, 2);
v___f_2351_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5), 4, 2);
lean_closure_set(v___f_2351_, 0, v_inst_2328_);
lean_closure_set(v___f_2351_, 1, v_f_2329_);
lean_inc_ref(v_toApplicative_2346_);
v___f_2352_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6), 5, 4);
lean_closure_set(v___f_2352_, 0, v_toApplicative_2346_);
lean_closure_set(v___f_2352_, 1, v_alts_2350_);
lean_closure_set(v___f_2352_, 2, v_inst_2328_);
lean_closure_set(v___f_2352_, 3, v___f_2351_);
v___f_2353_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7), 5, 4);
lean_closure_set(v___f_2353_, 0, v_f_2329_);
lean_closure_set(v___f_2353_, 1, v_discr_2349_);
lean_closure_set(v___f_2353_, 2, v_toBind_2347_);
lean_closure_set(v___f_2353_, 3, v___f_2352_);
v___x_2354_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2328_, v_f_2329_, v_resultType_2348_);
v___x_2355_ = lean_apply_4(v_toBind_2347_, lean_box(0), lean_box(0), v___x_2354_, v___f_2353_);
return v___x_2355_;
}
case 5:
{
lean_object* v_fvarId_2356_; lean_object* v___x_2357_; 
lean_dec_ref(v_inst_2328_);
v_fvarId_2356_ = lean_ctor_get(v_c_2330_, 0);
lean_inc(v_fvarId_2356_);
lean_dec_ref_known(v_c_2330_, 1);
v___x_2357_ = lean_apply_1(v_f_2329_, v_fvarId_2356_);
return v___x_2357_;
}
case 6:
{
lean_object* v_type_2358_; lean_object* v___x_2359_; 
v_type_2358_ = lean_ctor_get(v_c_2330_, 0);
lean_inc_ref(v_type_2358_);
lean_dec_ref_known(v_c_2330_, 1);
v___x_2359_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2328_, v_f_2329_, v_type_2358_);
return v___x_2359_;
}
case 7:
{
lean_object* v_toBind_2360_; lean_object* v_fvarId_2361_; lean_object* v_y_2362_; lean_object* v_k_2363_; lean_object* v___f_2364_; lean_object* v___f_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v_toBind_2360_ = lean_ctor_get(v_inst_2328_, 1);
lean_inc_n(v_toBind_2360_, 2);
v_fvarId_2361_ = lean_ctor_get(v_c_2330_, 0);
lean_inc(v_fvarId_2361_);
v_y_2362_ = lean_ctor_get(v_c_2330_, 2);
lean_inc(v_y_2362_);
v_k_2363_ = lean_ctor_get(v_c_2330_, 3);
lean_inc_ref(v_k_2363_);
lean_dec_ref_known(v_c_2330_, 4);
lean_inc_n(v_f_2329_, 2);
lean_inc_ref(v_inst_2328_);
v___f_2364_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2364_, 0, v_inst_2328_);
lean_closure_set(v___f_2364_, 1, v_f_2329_);
lean_closure_set(v___f_2364_, 2, v_k_2363_);
v___f_2365_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10), 6, 5);
lean_closure_set(v___f_2365_, 0, v_inst_2328_);
lean_closure_set(v___f_2365_, 1, v_f_2329_);
lean_closure_set(v___f_2365_, 2, v_y_2362_);
lean_closure_set(v___f_2365_, 3, v_toBind_2360_);
lean_closure_set(v___f_2365_, 4, v___f_2364_);
v___x_2366_ = lean_apply_1(v_f_2329_, v_fvarId_2361_);
v___x_2367_ = lean_apply_4(v_toBind_2360_, lean_box(0), lean_box(0), v___x_2366_, v___f_2365_);
return v___x_2367_;
}
case 8:
{
lean_object* v_toBind_2368_; lean_object* v_fvarId_2369_; lean_object* v_y_2370_; lean_object* v_k_2371_; lean_object* v___f_2372_; lean_object* v___f_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v_toBind_2368_ = lean_ctor_get(v_inst_2328_, 1);
lean_inc_n(v_toBind_2368_, 2);
v_fvarId_2369_ = lean_ctor_get(v_c_2330_, 0);
lean_inc(v_fvarId_2369_);
v_y_2370_ = lean_ctor_get(v_c_2330_, 2);
lean_inc(v_y_2370_);
v_k_2371_ = lean_ctor_get(v_c_2330_, 3);
lean_inc_ref(v_k_2371_);
lean_dec_ref_known(v_c_2330_, 4);
lean_inc_n(v_f_2329_, 2);
v___f_2372_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2372_, 0, v_inst_2328_);
lean_closure_set(v___f_2372_, 1, v_f_2329_);
lean_closure_set(v___f_2372_, 2, v_k_2371_);
v___f_2373_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11), 5, 4);
lean_closure_set(v___f_2373_, 0, v_f_2329_);
lean_closure_set(v___f_2373_, 1, v_y_2370_);
lean_closure_set(v___f_2373_, 2, v_toBind_2368_);
lean_closure_set(v___f_2373_, 3, v___f_2372_);
v___x_2374_ = lean_apply_1(v_f_2329_, v_fvarId_2369_);
v___x_2375_ = lean_apply_4(v_toBind_2368_, lean_box(0), lean_box(0), v___x_2374_, v___f_2373_);
return v___x_2375_;
}
case 9:
{
lean_object* v_toBind_2376_; lean_object* v_fvarId_2377_; lean_object* v_y_2378_; lean_object* v_ty_2379_; lean_object* v_k_2380_; lean_object* v___f_2381_; lean_object* v___f_2382_; lean_object* v___f_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v_toBind_2376_ = lean_ctor_get(v_inst_2328_, 1);
lean_inc_n(v_toBind_2376_, 3);
v_fvarId_2377_ = lean_ctor_get(v_c_2330_, 0);
lean_inc(v_fvarId_2377_);
v_y_2378_ = lean_ctor_get(v_c_2330_, 3);
lean_inc(v_y_2378_);
v_ty_2379_ = lean_ctor_get(v_c_2330_, 4);
lean_inc_ref(v_ty_2379_);
v_k_2380_ = lean_ctor_get(v_c_2330_, 5);
lean_inc_ref(v_k_2380_);
lean_dec_ref_known(v_c_2330_, 6);
lean_inc_n(v_f_2329_, 3);
lean_inc_ref(v_inst_2328_);
v___f_2381_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2381_, 0, v_inst_2328_);
lean_closure_set(v___f_2381_, 1, v_f_2329_);
lean_closure_set(v___f_2381_, 2, v_k_2380_);
v___f_2382_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12), 6, 5);
lean_closure_set(v___f_2382_, 0, v_inst_2328_);
lean_closure_set(v___f_2382_, 1, v_f_2329_);
lean_closure_set(v___f_2382_, 2, v_ty_2379_);
lean_closure_set(v___f_2382_, 3, v_toBind_2376_);
lean_closure_set(v___f_2382_, 4, v___f_2381_);
v___f_2383_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11), 5, 4);
lean_closure_set(v___f_2383_, 0, v_f_2329_);
lean_closure_set(v___f_2383_, 1, v_y_2378_);
lean_closure_set(v___f_2383_, 2, v_toBind_2376_);
lean_closure_set(v___f_2383_, 3, v___f_2382_);
v___x_2384_ = lean_apply_1(v_f_2329_, v_fvarId_2377_);
v___x_2385_ = lean_apply_4(v_toBind_2376_, lean_box(0), lean_box(0), v___x_2384_, v___f_2383_);
return v___x_2385_;
}
case 10:
{
lean_object* v_toBind_2386_; lean_object* v_fvarId_2387_; lean_object* v_k_2388_; lean_object* v___f_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v_toBind_2386_ = lean_ctor_get(v_inst_2328_, 1);
lean_inc(v_toBind_2386_);
v_fvarId_2387_ = lean_ctor_get(v_c_2330_, 0);
lean_inc(v_fvarId_2387_);
v_k_2388_ = lean_ctor_get(v_c_2330_, 2);
lean_inc_ref(v_k_2388_);
lean_dec_ref_known(v_c_2330_, 3);
lean_inc(v_f_2329_);
v___f_2389_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2389_, 0, v_inst_2328_);
lean_closure_set(v___f_2389_, 1, v_f_2329_);
lean_closure_set(v___f_2389_, 2, v_k_2388_);
v___x_2390_ = lean_apply_1(v_f_2329_, v_fvarId_2387_);
v___x_2391_ = lean_apply_4(v_toBind_2386_, lean_box(0), lean_box(0), v___x_2390_, v___f_2389_);
return v___x_2391_;
}
case 11:
{
lean_object* v_toBind_2392_; lean_object* v_fvarId_2393_; lean_object* v_k_2394_; lean_object* v___f_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_toBind_2392_ = lean_ctor_get(v_inst_2328_, 1);
lean_inc(v_toBind_2392_);
v_fvarId_2393_ = lean_ctor_get(v_c_2330_, 0);
lean_inc(v_fvarId_2393_);
v_k_2394_ = lean_ctor_get(v_c_2330_, 2);
lean_inc_ref(v_k_2394_);
lean_dec_ref_known(v_c_2330_, 3);
lean_inc(v_f_2329_);
v___f_2395_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2395_, 0, v_inst_2328_);
lean_closure_set(v___f_2395_, 1, v_f_2329_);
lean_closure_set(v___f_2395_, 2, v_k_2394_);
v___x_2396_ = lean_apply_1(v_f_2329_, v_fvarId_2393_);
v___x_2397_ = lean_apply_4(v_toBind_2392_, lean_box(0), lean_box(0), v___x_2396_, v___f_2395_);
return v___x_2397_;
}
case 12:
{
lean_object* v_toBind_2398_; lean_object* v_fvarId_2399_; lean_object* v_k_2400_; lean_object* v___f_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v_toBind_2398_ = lean_ctor_get(v_inst_2328_, 1);
lean_inc(v_toBind_2398_);
v_fvarId_2399_ = lean_ctor_get(v_c_2330_, 0);
lean_inc(v_fvarId_2399_);
v_k_2400_ = lean_ctor_get(v_c_2330_, 3);
lean_inc_ref(v_k_2400_);
lean_dec_ref_known(v_c_2330_, 4);
lean_inc(v_f_2329_);
v___f_2401_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2401_, 0, v_inst_2328_);
lean_closure_set(v___f_2401_, 1, v_f_2329_);
lean_closure_set(v___f_2401_, 2, v_k_2400_);
v___x_2402_ = lean_apply_1(v_f_2329_, v_fvarId_2399_);
v___x_2403_ = lean_apply_4(v_toBind_2398_, lean_box(0), lean_box(0), v___x_2402_, v___f_2401_);
return v___x_2403_;
}
case 13:
{
lean_object* v_toBind_2404_; lean_object* v_fvarId_2405_; lean_object* v_k_2406_; lean_object* v___f_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v_toBind_2404_ = lean_ctor_get(v_inst_2328_, 1);
lean_inc(v_toBind_2404_);
v_fvarId_2405_ = lean_ctor_get(v_c_2330_, 0);
lean_inc(v_fvarId_2405_);
v_k_2406_ = lean_ctor_get(v_c_2330_, 1);
lean_inc_ref(v_k_2406_);
lean_dec_ref_known(v_c_2330_, 2);
lean_inc(v_f_2329_);
v___f_2407_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2407_, 0, v_inst_2328_);
lean_closure_set(v___f_2407_, 1, v_f_2329_);
lean_closure_set(v___f_2407_, 2, v_k_2406_);
v___x_2408_ = lean_apply_1(v_f_2329_, v_fvarId_2405_);
v___x_2409_ = lean_apply_4(v_toBind_2404_, lean_box(0), lean_box(0), v___x_2408_, v___f_2407_);
return v___x_2409_;
}
default: 
{
lean_object* v_decl_2410_; lean_object* v_toApplicative_2411_; lean_object* v_toBind_2412_; lean_object* v_k_2413_; lean_object* v_params_2414_; lean_object* v_type_2415_; lean_object* v_value_2416_; lean_object* v_toPure_2417_; lean_object* v___f_2418_; lean_object* v___f_2419_; lean_object* v___f_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v_decl_2410_ = lean_ctor_get(v_c_2330_, 0);
lean_inc_ref(v_decl_2410_);
v_toApplicative_2411_ = lean_ctor_get(v_inst_2328_, 0);
v_toBind_2412_ = lean_ctor_get(v_inst_2328_, 1);
lean_inc_n(v_toBind_2412_, 3);
v_k_2413_ = lean_ctor_get(v_c_2330_, 1);
lean_inc_ref(v_k_2413_);
lean_dec_ref(v_c_2330_);
v_params_2414_ = lean_ctor_get(v_decl_2410_, 2);
lean_inc_ref(v_params_2414_);
v_type_2415_ = lean_ctor_get(v_decl_2410_, 3);
lean_inc_ref(v_type_2415_);
v_value_2416_ = lean_ctor_get(v_decl_2410_, 4);
lean_inc_ref(v_value_2416_);
lean_dec_ref(v_decl_2410_);
v_toPure_2417_ = lean_ctor_get(v_toApplicative_2411_, 1);
lean_inc_n(v_f_2329_, 3);
lean_inc_ref_n(v_inst_2328_, 3);
v___f_2418_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2418_, 0, v_inst_2328_);
lean_closure_set(v___f_2418_, 1, v_f_2329_);
lean_closure_set(v___f_2418_, 2, v_k_2413_);
v___f_2419_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2419_, 0, v_inst_2328_);
lean_closure_set(v___f_2419_, 1, v_f_2329_);
lean_closure_set(v___f_2419_, 2, v_value_2416_);
lean_closure_set(v___f_2419_, 3, v_toBind_2412_);
lean_closure_set(v___f_2419_, 4, v___f_2418_);
v___f_2420_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2420_, 0, v_inst_2328_);
lean_closure_set(v___f_2420_, 1, v_f_2329_);
lean_closure_set(v___f_2420_, 2, v_type_2415_);
lean_closure_set(v___f_2420_, 3, v_toBind_2412_);
lean_closure_set(v___f_2420_, 4, v___f_2419_);
v___x_2421_ = lean_unsigned_to_nat(0u);
v___x_2422_ = lean_array_get_size(v_params_2414_);
v___x_2423_ = lean_box(0);
v___x_2424_ = lean_nat_dec_lt(v___x_2421_, v___x_2422_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
lean_inc(v_toPure_2417_);
lean_dec_ref(v_params_2414_);
lean_dec(v_f_2329_);
lean_dec_ref(v_inst_2328_);
v___x_2425_ = lean_apply_2(v_toPure_2417_, lean_box(0), v___x_2423_);
v___x_2426_ = lean_apply_4(v_toBind_2412_, lean_box(0), lean_box(0), v___x_2425_, v___f_2420_);
return v___x_2426_;
}
else
{
lean_object* v___f_2427_; uint8_t v___x_2428_; 
lean_inc_ref(v_inst_2328_);
v___f_2427_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2427_, 0, v_inst_2328_);
lean_closure_set(v___f_2427_, 1, v_f_2329_);
v___x_2428_ = lean_nat_dec_le(v___x_2422_, v___x_2422_);
if (v___x_2428_ == 0)
{
if (v___x_2424_ == 0)
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
lean_inc(v_toPure_2417_);
lean_dec_ref(v___f_2427_);
lean_dec_ref(v_params_2414_);
lean_dec_ref(v_inst_2328_);
v___x_2429_ = lean_apply_2(v_toPure_2417_, lean_box(0), v___x_2423_);
v___x_2430_ = lean_apply_4(v_toBind_2412_, lean_box(0), lean_box(0), v___x_2429_, v___f_2420_);
return v___x_2430_;
}
else
{
size_t v___x_2431_; size_t v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2431_ = ((size_t)0ULL);
v___x_2432_ = lean_usize_of_nat(v___x_2422_);
v___x_2433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2328_, v___f_2427_, v_params_2414_, v___x_2431_, v___x_2432_, v___x_2423_);
v___x_2434_ = lean_apply_4(v_toBind_2412_, lean_box(0), lean_box(0), v___x_2433_, v___f_2420_);
return v___x_2434_;
}
}
else
{
size_t v___x_2435_; size_t v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2435_ = ((size_t)0ULL);
v___x_2436_ = lean_usize_of_nat(v___x_2422_);
v___x_2437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2328_, v___f_2427_, v_params_2414_, v___x_2435_, v___x_2436_, v___x_2423_);
v___x_2438_ = lean_apply_4(v_toBind_2412_, lean_box(0), lean_box(0), v___x_2437_, v___f_2420_);
return v___x_2438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0(lean_object* v_inst_2439_, lean_object* v_f_2440_, lean_object* v_k_2441_, lean_object* v_____r_2442_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2439_, v_f_2440_, v_k_2441_);
return v___x_2443_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_forFVarM(lean_object* v_m_2444_, uint8_t v_pu_2445_, lean_object* v_inst_2446_, lean_object* v_f_2447_, lean_object* v_c_2448_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2446_, v_f_2447_, v_c_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_forFVarM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2445_ = stack[1].m_num;
lean_object* v_inst_2446_ = stack[2].m_obj;
lean_object* v_f_2447_ = stack[3].m_obj;
lean_object* v_c_2448_ = stack[4].m_obj;
lean_object* v_res_2450_;
v_res_2450_ = l_Lean_Compiler_LCNF_Code_forFVarM(lean_box(0), v_pu_2445_, v_inst_2446_, v_f_2447_, v_c_2448_);
stack->m_obj
 = v_res_2450_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___boxed(lean_object* v_m_2451_, lean_object* v_pu_2452_, lean_object* v_inst_2453_, lean_object* v_f_2454_, lean_object* v_c_2455_){
_start:
{
uint8_t v_pu_boxed_2456_; lean_object* v_res_2457_; 
v_pu_boxed_2456_ = lean_unbox(v_pu_2452_);
v_res_2457_ = l_Lean_Compiler_LCNF_Code_forFVarM(v_m_2451_, v_pu_boxed_2456_, v_inst_2453_, v_f_2454_, v_c_2455_);
return v_res_2457_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(uint8_t v_pu_2458_, lean_object* v_m_2459_, lean_object* v_inst_2460_, lean_object* v_inst_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2458_, v_inst_2460_, v_inst_2461_, v___y_2462_, v___y_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2458_ = stack[0].m_num;
lean_object* v_inst_2460_ = stack[2].m_obj;
lean_object* v_inst_2461_ = stack[3].m_obj;
lean_object* v___y_2462_ = stack[4].m_obj;
lean_object* v___y_2463_ = stack[5].m_obj;
lean_object* v_res_2465_;
v_res_2465_ = l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(v_pu_2458_, lean_box(0), v_inst_2460_, v_inst_2461_, v___y_2462_, v___y_2463_);
stack->m_obj
 = v_res_2465_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed(lean_object* v_pu_2466_, lean_object* v_m_2467_, lean_object* v_inst_2468_, lean_object* v_inst_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
uint8_t v_pu_boxed_2472_; lean_object* v_res_2473_; 
v_pu_boxed_2472_ = lean_unbox(v_pu_2466_);
v_res_2473_ = l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(v_pu_boxed_2472_, v_m_2467_, v_inst_2468_, v_inst_2469_, v___y_2470_, v___y_2471_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__1(lean_object* v_m_2474_, lean_object* v_inst_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2475_, v___y_2476_, v___y_2477_);
return v___x_2478_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode(uint8_t v_pu_2480_){
_start:
{
lean_object* v___x_2481_; lean_object* v___f_2482_; lean_object* v___f_2483_; lean_object* v___x_2484_; 
v___x_2481_ = lean_box(v_pu_2480_);
v___f_2482_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2482_, 0, v___x_2481_);
v___f_2483_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0));
v___x_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___f_2482_);
lean_ctor_set(v___x_2484_, 1, v___f_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarCode_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2480_ = stack[0].m_num;
lean_object* v_res_2485_;
v_res_2485_ = l_Lean_Compiler_LCNF_instTraverseFVarCode(v_pu_2480_);
stack->m_obj
 = v_res_2485_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___boxed(lean_object* v_pu_2486_){
_start:
{
uint8_t v_pu_boxed_2487_; lean_object* v_res_2488_; 
v_pu_boxed_2487_ = lean_unbox(v_pu_2486_);
v_res_2488_ = l_Lean_Compiler_LCNF_instTraverseFVarCode(v_pu_boxed_2487_);
return v_res_2488_;
}
}
lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(uint8_t v_pu_2489_, lean_object* v_decl_2490_, lean_object* v_____do__lift_2491_, lean_object* v_params_2492_, lean_object* v_inst_2493_, lean_object* v_____do__lift_2494_){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2495_ = lean_box(v_pu_2489_);
v___x_2496_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed), 10, 5);
lean_closure_set(v___x_2496_, 0, v___x_2495_);
lean_closure_set(v___x_2496_, 1, v_decl_2490_);
lean_closure_set(v___x_2496_, 2, v_____do__lift_2491_);
lean_closure_set(v___x_2496_, 3, v_params_2492_);
lean_closure_set(v___x_2496_, 4, v_____do__lift_2494_);
v___x_2497_ = lean_apply_2(v_inst_2493_, lean_box(0), v___x_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2489_ = stack[0].m_num;
lean_object* v_decl_2490_ = stack[1].m_obj;
lean_object* v_____do__lift_2491_ = stack[2].m_obj;
lean_object* v_params_2492_ = stack[3].m_obj;
lean_object* v_inst_2493_ = stack[4].m_obj;
lean_object* v_____do__lift_2494_ = stack[5].m_obj;
lean_object* v_res_2498_;
v_res_2498_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(v_pu_2489_, v_decl_2490_, v_____do__lift_2491_, v_params_2492_, v_inst_2493_, v_____do__lift_2494_);
stack->m_obj
 = v_res_2498_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_2499_, lean_object* v_decl_2500_, lean_object* v_____do__lift_2501_, lean_object* v_params_2502_, lean_object* v_inst_2503_, lean_object* v_____do__lift_2504_){
_start:
{
uint8_t v_pu_boxed_2505_; lean_object* v_res_2506_; 
v_pu_boxed_2505_ = lean_unbox(v_pu_2499_);
v_res_2506_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(v_pu_boxed_2505_, v_decl_2500_, v_____do__lift_2501_, v_params_2502_, v_inst_2503_, v_____do__lift_2504_);
return v_res_2506_;
}
}
lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(uint8_t v_pu_2507_, lean_object* v_decl_2508_, lean_object* v_params_2509_, lean_object* v_inst_2510_, lean_object* v_inst_2511_, lean_object* v_f_2512_, lean_object* v_value_2513_, lean_object* v_toBind_2514_, lean_object* v_____do__lift_2515_){
_start:
{
lean_object* v___x_2516_; lean_object* v___f_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2516_ = lean_box(v_pu_2507_);
lean_inc(v_inst_2510_);
v___f_2517_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2517_, 0, v___x_2516_);
lean_closure_set(v___f_2517_, 1, v_decl_2508_);
lean_closure_set(v___f_2517_, 2, v_____do__lift_2515_);
lean_closure_set(v___f_2517_, 3, v_params_2509_);
lean_closure_set(v___f_2517_, 4, v_inst_2510_);
v___x_2518_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2507_, v_inst_2510_, v_inst_2511_, v_f_2512_, v_value_2513_);
v___x_2519_ = lean_apply_4(v_toBind_2514_, lean_box(0), lean_box(0), v___x_2518_, v___f_2517_);
return v___x_2519_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2507_ = stack[0].m_num;
lean_object* v_decl_2508_ = stack[1].m_obj;
lean_object* v_params_2509_ = stack[2].m_obj;
lean_object* v_inst_2510_ = stack[3].m_obj;
lean_object* v_inst_2511_ = stack[4].m_obj;
lean_object* v_f_2512_ = stack[5].m_obj;
lean_object* v_value_2513_ = stack[6].m_obj;
lean_object* v_toBind_2514_ = stack[7].m_obj;
lean_object* v_____do__lift_2515_ = stack[8].m_obj;
lean_object* v_res_2520_;
v_res_2520_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(v_pu_2507_, v_decl_2508_, v_params_2509_, v_inst_2510_, v_inst_2511_, v_f_2512_, v_value_2513_, v_toBind_2514_, v_____do__lift_2515_);
stack->m_obj
 = v_res_2520_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed(lean_object* v_pu_2521_, lean_object* v_decl_2522_, lean_object* v_params_2523_, lean_object* v_inst_2524_, lean_object* v_inst_2525_, lean_object* v_f_2526_, lean_object* v_value_2527_, lean_object* v_toBind_2528_, lean_object* v_____do__lift_2529_){
_start:
{
uint8_t v_pu_boxed_2530_; lean_object* v_res_2531_; 
v_pu_boxed_2530_ = lean_unbox(v_pu_2521_);
v_res_2531_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(v_pu_boxed_2530_, v_decl_2522_, v_params_2523_, v_inst_2524_, v_inst_2525_, v_f_2526_, v_value_2527_, v_toBind_2528_, v_____do__lift_2529_);
return v_res_2531_;
}
}
lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(uint8_t v_pu_2532_, lean_object* v_decl_2533_, lean_object* v_inst_2534_, lean_object* v_inst_2535_, lean_object* v_f_2536_, lean_object* v_value_2537_, lean_object* v_toBind_2538_, lean_object* v_type_2539_, lean_object* v_params_2540_){
_start:
{
lean_object* v___x_2541_; lean_object* v___f_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2541_ = lean_box(v_pu_2532_);
lean_inc(v_toBind_2538_);
lean_inc(v_f_2536_);
lean_inc_ref(v_inst_2535_);
v___f_2542_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2542_, 0, v___x_2541_);
lean_closure_set(v___f_2542_, 1, v_decl_2533_);
lean_closure_set(v___f_2542_, 2, v_params_2540_);
lean_closure_set(v___f_2542_, 3, v_inst_2534_);
lean_closure_set(v___f_2542_, 4, v_inst_2535_);
lean_closure_set(v___f_2542_, 5, v_f_2536_);
lean_closure_set(v___f_2542_, 6, v_value_2537_);
lean_closure_set(v___f_2542_, 7, v_toBind_2538_);
v___x_2543_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2535_, v_f_2536_, v_type_2539_);
v___x_2544_ = lean_apply_4(v_toBind_2538_, lean_box(0), lean_box(0), v___x_2543_, v___f_2542_);
return v___x_2544_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2532_ = stack[0].m_num;
lean_object* v_decl_2533_ = stack[1].m_obj;
lean_object* v_inst_2534_ = stack[2].m_obj;
lean_object* v_inst_2535_ = stack[3].m_obj;
lean_object* v_f_2536_ = stack[4].m_obj;
lean_object* v_value_2537_ = stack[5].m_obj;
lean_object* v_toBind_2538_ = stack[6].m_obj;
lean_object* v_type_2539_ = stack[7].m_obj;
lean_object* v_params_2540_ = stack[8].m_obj;
lean_object* v_res_2545_;
v_res_2545_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(v_pu_2532_, v_decl_2533_, v_inst_2534_, v_inst_2535_, v_f_2536_, v_value_2537_, v_toBind_2538_, v_type_2539_, v_params_2540_);
stack->m_obj
 = v_res_2545_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed(lean_object* v_pu_2546_, lean_object* v_decl_2547_, lean_object* v_inst_2548_, lean_object* v_inst_2549_, lean_object* v_f_2550_, lean_object* v_value_2551_, lean_object* v_toBind_2552_, lean_object* v_type_2553_, lean_object* v_params_2554_){
_start:
{
uint8_t v_pu_boxed_2555_; lean_object* v_res_2556_; 
v_pu_boxed_2555_ = lean_unbox(v_pu_2546_);
v_res_2556_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(v_pu_boxed_2555_, v_decl_2547_, v_inst_2548_, v_inst_2549_, v_f_2550_, v_value_2551_, v_toBind_2552_, v_type_2553_, v_params_2554_);
return v_res_2556_;
}
}
lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(uint8_t v_pu_2557_, lean_object* v_inst_2558_, lean_object* v_inst_2559_, lean_object* v_f_2560_, lean_object* v_decl_2561_){
_start:
{
lean_object* v_toBind_2562_; lean_object* v_params_2563_; lean_object* v_type_2564_; lean_object* v_value_2565_; lean_object* v___x_2566_; lean_object* v___f_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; size_t v_sz_2570_; size_t v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v_toBind_2562_ = lean_ctor_get(v_inst_2559_, 1);
lean_inc_n(v_toBind_2562_, 2);
v_params_2563_ = lean_ctor_get(v_decl_2561_, 2);
lean_inc_ref(v_params_2563_);
v_type_2564_ = lean_ctor_get(v_decl_2561_, 3);
lean_inc_ref(v_type_2564_);
v_value_2565_ = lean_ctor_get(v_decl_2561_, 4);
lean_inc_ref(v_value_2565_);
v___x_2566_ = lean_box(v_pu_2557_);
lean_inc(v_f_2560_);
lean_inc_ref_n(v_inst_2559_, 2);
lean_inc(v_inst_2558_);
v___f_2567_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2567_, 0, v___x_2566_);
lean_closure_set(v___f_2567_, 1, v_decl_2561_);
lean_closure_set(v___f_2567_, 2, v_inst_2558_);
lean_closure_set(v___f_2567_, 3, v_inst_2559_);
lean_closure_set(v___f_2567_, 4, v_f_2560_);
lean_closure_set(v___f_2567_, 5, v_value_2565_);
lean_closure_set(v___f_2567_, 6, v_toBind_2562_);
lean_closure_set(v___f_2567_, 7, v_type_2564_);
v___x_2568_ = lean_box(v_pu_2557_);
v___x_2569_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2569_, 0, lean_box(0));
lean_closure_set(v___x_2569_, 1, v___x_2568_);
lean_closure_set(v___x_2569_, 2, v_inst_2558_);
lean_closure_set(v___x_2569_, 3, v_inst_2559_);
lean_closure_set(v___x_2569_, 4, v_f_2560_);
v_sz_2570_ = lean_array_size(v_params_2563_);
v___x_2571_ = ((size_t)0ULL);
v___x_2572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2559_, v___x_2569_, v_sz_2570_, v___x_2571_, v_params_2563_);
v___x_2573_ = lean_apply_4(v_toBind_2562_, lean_box(0), lean_box(0), v___x_2572_, v___f_2567_);
return v___x_2573_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2557_ = stack[0].m_num;
lean_object* v_inst_2558_ = stack[1].m_obj;
lean_object* v_inst_2559_ = stack[2].m_obj;
lean_object* v_f_2560_ = stack[3].m_obj;
lean_object* v_decl_2561_ = stack[4].m_obj;
lean_object* v_res_2574_;
v_res_2574_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2557_, v_inst_2558_, v_inst_2559_, v_f_2560_, v_decl_2561_);
stack->m_obj
 = v_res_2574_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___boxed(lean_object* v_pu_2575_, lean_object* v_inst_2576_, lean_object* v_inst_2577_, lean_object* v_f_2578_, lean_object* v_decl_2579_){
_start:
{
uint8_t v_pu_boxed_2580_; lean_object* v_res_2581_; 
v_pu_boxed_2580_ = lean_unbox(v_pu_2575_);
v_res_2581_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_boxed_2580_, v_inst_2576_, v_inst_2577_, v_f_2578_, v_decl_2579_);
return v_res_2581_;
}
}
lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM(lean_object* v_m_2582_, uint8_t v_pu_2583_, lean_object* v_inst_2584_, lean_object* v_inst_2585_, lean_object* v_f_2586_, lean_object* v_decl_2587_){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2583_, v_inst_2584_, v_inst_2585_, v_f_2586_, v_decl_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_mapFVarM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2583_ = stack[1].m_num;
lean_object* v_inst_2584_ = stack[2].m_obj;
lean_object* v_inst_2585_ = stack[3].m_obj;
lean_object* v_f_2586_ = stack[4].m_obj;
lean_object* v_decl_2587_ = stack[5].m_obj;
lean_object* v_res_2589_;
v_res_2589_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM(lean_box(0), v_pu_2583_, v_inst_2584_, v_inst_2585_, v_f_2586_, v_decl_2587_);
stack->m_obj
 = v_res_2589_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___boxed(lean_object* v_m_2590_, lean_object* v_pu_2591_, lean_object* v_inst_2592_, lean_object* v_inst_2593_, lean_object* v_f_2594_, lean_object* v_decl_2595_){
_start:
{
uint8_t v_pu_boxed_2596_; lean_object* v_res_2597_; 
v_pu_boxed_2596_ = lean_unbox(v_pu_2591_);
v_res_2597_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM(v_m_2590_, v_pu_boxed_2596_, v_inst_2592_, v_inst_2593_, v_f_2594_, v_decl_2595_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0(lean_object* v_inst_2598_, lean_object* v_f_2599_, lean_object* v_value_2600_, lean_object* v_____r_2601_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2598_, v_f_2599_, v_value_2600_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1(lean_object* v_inst_2603_, lean_object* v_f_2604_, lean_object* v_type_2605_, lean_object* v_toBind_2606_, lean_object* v___f_2607_, lean_object* v_____r_2608_){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2603_, v_f_2604_, v_type_2605_);
v___x_2610_ = lean_apply_4(v_toBind_2606_, lean_box(0), lean_box(0), v___x_2609_, v___f_2607_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2(lean_object* v_inst_2611_, lean_object* v_f_2612_, lean_object* v_x_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_2611_, v_f_2612_, v___y_2614_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(lean_object* v_inst_2616_, lean_object* v_f_2617_, lean_object* v_decl_2618_){
_start:
{
lean_object* v_toApplicative_2619_; lean_object* v_toBind_2620_; lean_object* v_params_2621_; lean_object* v_type_2622_; lean_object* v_value_2623_; lean_object* v_toPure_2624_; lean_object* v___f_2625_; lean_object* v___f_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; 
v_toApplicative_2619_ = lean_ctor_get(v_inst_2616_, 0);
v_toBind_2620_ = lean_ctor_get(v_inst_2616_, 1);
lean_inc_n(v_toBind_2620_, 2);
v_params_2621_ = lean_ctor_get(v_decl_2618_, 2);
lean_inc_ref(v_params_2621_);
v_type_2622_ = lean_ctor_get(v_decl_2618_, 3);
lean_inc_ref(v_type_2622_);
v_value_2623_ = lean_ctor_get(v_decl_2618_, 4);
lean_inc_ref(v_value_2623_);
lean_dec_ref(v_decl_2618_);
v_toPure_2624_ = lean_ctor_get(v_toApplicative_2619_, 1);
lean_inc_n(v_f_2617_, 2);
lean_inc_ref_n(v_inst_2616_, 2);
v___f_2625_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2625_, 0, v_inst_2616_);
lean_closure_set(v___f_2625_, 1, v_f_2617_);
lean_closure_set(v___f_2625_, 2, v_value_2623_);
v___f_2626_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2626_, 0, v_inst_2616_);
lean_closure_set(v___f_2626_, 1, v_f_2617_);
lean_closure_set(v___f_2626_, 2, v_type_2622_);
lean_closure_set(v___f_2626_, 3, v_toBind_2620_);
lean_closure_set(v___f_2626_, 4, v___f_2625_);
v___x_2627_ = lean_unsigned_to_nat(0u);
v___x_2628_ = lean_array_get_size(v_params_2621_);
v___x_2629_ = lean_box(0);
v___x_2630_ = lean_nat_dec_lt(v___x_2627_, v___x_2628_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_inc(v_toPure_2624_);
lean_dec_ref(v_params_2621_);
lean_dec(v_f_2617_);
lean_dec_ref(v_inst_2616_);
v___x_2631_ = lean_apply_2(v_toPure_2624_, lean_box(0), v___x_2629_);
v___x_2632_ = lean_apply_4(v_toBind_2620_, lean_box(0), lean_box(0), v___x_2631_, v___f_2626_);
return v___x_2632_;
}
else
{
lean_object* v___f_2633_; uint8_t v___x_2634_; 
lean_inc_ref(v_inst_2616_);
v___f_2633_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_2633_, 0, v_inst_2616_);
lean_closure_set(v___f_2633_, 1, v_f_2617_);
v___x_2634_ = lean_nat_dec_le(v___x_2628_, v___x_2628_);
if (v___x_2634_ == 0)
{
if (v___x_2630_ == 0)
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
lean_inc(v_toPure_2624_);
lean_dec_ref(v___f_2633_);
lean_dec_ref(v_params_2621_);
lean_dec_ref(v_inst_2616_);
v___x_2635_ = lean_apply_2(v_toPure_2624_, lean_box(0), v___x_2629_);
v___x_2636_ = lean_apply_4(v_toBind_2620_, lean_box(0), lean_box(0), v___x_2635_, v___f_2626_);
return v___x_2636_;
}
else
{
size_t v___x_2637_; size_t v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2637_ = ((size_t)0ULL);
v___x_2638_ = lean_usize_of_nat(v___x_2628_);
v___x_2639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2616_, v___f_2633_, v_params_2621_, v___x_2637_, v___x_2638_, v___x_2629_);
v___x_2640_ = lean_apply_4(v_toBind_2620_, lean_box(0), lean_box(0), v___x_2639_, v___f_2626_);
return v___x_2640_;
}
}
else
{
size_t v___x_2641_; size_t v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2641_ = ((size_t)0ULL);
v___x_2642_ = lean_usize_of_nat(v___x_2628_);
v___x_2643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2616_, v___f_2633_, v_params_2621_, v___x_2641_, v___x_2642_, v___x_2629_);
v___x_2644_ = lean_apply_4(v_toBind_2620_, lean_box(0), lean_box(0), v___x_2643_, v___f_2626_);
return v___x_2644_;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM(lean_object* v_m_2645_, uint8_t v_pu_2646_, lean_object* v_inst_2647_, lean_object* v_f_2648_, lean_object* v_decl_2649_){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2647_, v_f_2648_, v_decl_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_forFVarM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2646_ = stack[1].m_num;
lean_object* v_inst_2647_ = stack[2].m_obj;
lean_object* v_f_2648_ = stack[3].m_obj;
lean_object* v_decl_2649_ = stack[4].m_obj;
lean_object* v_res_2651_;
v_res_2651_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM(lean_box(0), v_pu_2646_, v_inst_2647_, v_f_2648_, v_decl_2649_);
stack->m_obj
 = v_res_2651_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___boxed(lean_object* v_m_2652_, lean_object* v_pu_2653_, lean_object* v_inst_2654_, lean_object* v_f_2655_, lean_object* v_decl_2656_){
_start:
{
uint8_t v_pu_boxed_2657_; lean_object* v_res_2658_; 
v_pu_boxed_2657_ = lean_unbox(v_pu_2653_);
v_res_2658_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM(v_m_2652_, v_pu_boxed_2657_, v_inst_2654_, v_f_2655_, v_decl_2656_);
return v_res_2658_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(uint8_t v_pu_2659_, lean_object* v_m_2660_, lean_object* v_inst_2661_, lean_object* v_inst_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2659_, v_inst_2661_, v_inst_2662_, v___y_2663_, v___y_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2659_ = stack[0].m_num;
lean_object* v_inst_2661_ = stack[2].m_obj;
lean_object* v_inst_2662_ = stack[3].m_obj;
lean_object* v___y_2663_ = stack[4].m_obj;
lean_object* v___y_2664_ = stack[5].m_obj;
lean_object* v_res_2666_;
v_res_2666_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(v_pu_2659_, lean_box(0), v_inst_2661_, v_inst_2662_, v___y_2663_, v___y_2664_);
stack->m_obj
 = v_res_2666_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed(lean_object* v_pu_2667_, lean_object* v_m_2668_, lean_object* v_inst_2669_, lean_object* v_inst_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
uint8_t v_pu_boxed_2673_; lean_object* v_res_2674_; 
v_pu_boxed_2673_ = lean_unbox(v_pu_2667_);
v_res_2674_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(v_pu_boxed_2673_, v_m_2668_, v_inst_2669_, v_inst_2670_, v___y_2671_, v___y_2672_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__1(lean_object* v_m_2675_, lean_object* v_inst_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2676_, v___y_2677_, v___y_2678_);
return v___x_2679_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(uint8_t v_pu_2681_){
_start:
{
lean_object* v___x_2682_; lean_object* v___f_2683_; lean_object* v___f_2684_; lean_object* v___x_2685_; 
v___x_2682_ = lean_box(v_pu_2681_);
v___f_2683_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2683_, 0, v___x_2682_);
v___f_2684_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0));
v___x_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___f_2683_);
lean_ctor_set(v___x_2685_, 1, v___f_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarFunDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2681_ = stack[0].m_num;
lean_object* v_res_2686_;
v_res_2686_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(v_pu_2681_);
stack->m_obj
 = v_res_2686_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___boxed(lean_object* v_pu_2687_){
_start:
{
uint8_t v_pu_boxed_2688_; lean_object* v_res_2689_; 
v_pu_boxed_2688_ = lean_unbox(v_pu_2687_);
v_res_2689_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(v_pu_boxed_2688_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0(lean_object* v_toPure_2690_, lean_object* v_____do__lift_2691_){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2692_, 0, v_____do__lift_2691_);
v___x_2693_ = lean_apply_2(v_toPure_2690_, lean_box(0), v___x_2692_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1(lean_object* v_toPure_2694_, lean_object* v_____do__lift_2695_){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2696_, 0, v_____do__lift_2695_);
v___x_2697_ = lean_apply_2(v_toPure_2694_, lean_box(0), v___x_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2(lean_object* v_toPure_2698_, lean_object* v_____do__lift_2699_){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2700_, 0, v_____do__lift_2699_);
v___x_2701_ = lean_apply_2(v_toPure_2698_, lean_box(0), v___x_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3(lean_object* v_____do__lift_2702_, lean_object* v_i_2703_, lean_object* v_toPure_2704_, lean_object* v_____do__lift_2705_){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2706_, 0, v_____do__lift_2702_);
lean_ctor_set(v___x_2706_, 1, v_i_2703_);
lean_ctor_set(v___x_2706_, 2, v_____do__lift_2705_);
v___x_2707_ = lean_apply_2(v_toPure_2704_, lean_box(0), v___x_2706_);
return v___x_2707_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(lean_object* v_i_2708_, lean_object* v_toPure_2709_, uint8_t v_pu_2710_, lean_object* v_inst_2711_, lean_object* v_f_2712_, lean_object* v_y_2713_, lean_object* v_toBind_2714_, lean_object* v_____do__lift_2715_){
_start:
{
lean_object* v___f_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___f_2716_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3), 4, 3);
lean_closure_set(v___f_2716_, 0, v_____do__lift_2715_);
lean_closure_set(v___f_2716_, 1, v_i_2708_);
lean_closure_set(v___f_2716_, 2, v_toPure_2709_);
v___x_2717_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_2710_, v_inst_2711_, v_f_2712_, v_y_2713_);
v___x_2718_ = lean_apply_4(v_toBind_2714_, lean_box(0), lean_box(0), v___x_2717_, v___f_2716_);
return v___x_2718_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_2708_ = stack[0].m_obj;
lean_object* v_toPure_2709_ = stack[1].m_obj;
uint8_t v_pu_2710_ = stack[2].m_num;
lean_object* v_inst_2711_ = stack[3].m_obj;
lean_object* v_f_2712_ = stack[4].m_obj;
lean_object* v_y_2713_ = stack[5].m_obj;
lean_object* v_toBind_2714_ = stack[6].m_obj;
lean_object* v_____do__lift_2715_ = stack[7].m_obj;
lean_object* v_res_2719_;
v_res_2719_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(v_i_2708_, v_toPure_2709_, v_pu_2710_, v_inst_2711_, v_f_2712_, v_y_2713_, v_toBind_2714_, v_____do__lift_2715_);
stack->m_obj
 = v_res_2719_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed(lean_object* v_i_2720_, lean_object* v_toPure_2721_, lean_object* v_pu_2722_, lean_object* v_inst_2723_, lean_object* v_f_2724_, lean_object* v_y_2725_, lean_object* v_toBind_2726_, lean_object* v_____do__lift_2727_){
_start:
{
uint8_t v_pu_boxed_2728_; lean_object* v_res_2729_; 
v_pu_boxed_2728_ = lean_unbox(v_pu_2722_);
v_res_2729_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(v_i_2720_, v_toPure_2721_, v_pu_boxed_2728_, v_inst_2723_, v_f_2724_, v_y_2725_, v_toBind_2726_, v_____do__lift_2727_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5(lean_object* v_____do__lift_2730_, lean_object* v_i_2731_, lean_object* v_toPure_2732_, lean_object* v_____do__lift_2733_){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2734_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_2734_, 0, v_____do__lift_2730_);
lean_ctor_set(v___x_2734_, 1, v_i_2731_);
lean_ctor_set(v___x_2734_, 2, v_____do__lift_2733_);
v___x_2735_ = lean_apply_2(v_toPure_2732_, lean_box(0), v___x_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6(lean_object* v_i_2736_, lean_object* v_toPure_2737_, lean_object* v_f_2738_, lean_object* v_y_2739_, lean_object* v_toBind_2740_, lean_object* v_____do__lift_2741_){
_start:
{
lean_object* v___f_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___f_2742_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5), 4, 3);
lean_closure_set(v___f_2742_, 0, v_____do__lift_2741_);
lean_closure_set(v___f_2742_, 1, v_i_2736_);
lean_closure_set(v___f_2742_, 2, v_toPure_2737_);
v___x_2743_ = lean_apply_1(v_f_2738_, v_y_2739_);
v___x_2744_ = lean_apply_4(v_toBind_2740_, lean_box(0), lean_box(0), v___x_2743_, v___f_2742_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7(lean_object* v_____do__lift_2745_, lean_object* v_i_2746_, lean_object* v_offset_2747_, lean_object* v_____do__lift_2748_, lean_object* v_toPure_2749_, lean_object* v_____do__lift_2750_){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v___x_2751_, 0, v_____do__lift_2745_);
lean_ctor_set(v___x_2751_, 1, v_i_2746_);
lean_ctor_set(v___x_2751_, 2, v_offset_2747_);
lean_ctor_set(v___x_2751_, 3, v_____do__lift_2748_);
lean_ctor_set(v___x_2751_, 4, v_____do__lift_2750_);
v___x_2752_ = lean_apply_2(v_toPure_2749_, lean_box(0), v___x_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8(lean_object* v_____do__lift_2753_, lean_object* v_i_2754_, lean_object* v_offset_2755_, lean_object* v_toPure_2756_, lean_object* v_inst_2757_, lean_object* v_f_2758_, lean_object* v_ty_2759_, lean_object* v_toBind_2760_, lean_object* v_____do__lift_2761_){
_start:
{
lean_object* v___f_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___f_2762_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7), 6, 5);
lean_closure_set(v___f_2762_, 0, v_____do__lift_2753_);
lean_closure_set(v___f_2762_, 1, v_i_2754_);
lean_closure_set(v___f_2762_, 2, v_offset_2755_);
lean_closure_set(v___f_2762_, 3, v_____do__lift_2761_);
lean_closure_set(v___f_2762_, 4, v_toPure_2756_);
v___x_2763_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2757_, v_f_2758_, v_ty_2759_);
v___x_2764_ = lean_apply_4(v_toBind_2760_, lean_box(0), lean_box(0), v___x_2763_, v___f_2762_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9(lean_object* v_i_2765_, lean_object* v_offset_2766_, lean_object* v_toPure_2767_, lean_object* v_inst_2768_, lean_object* v_f_2769_, lean_object* v_ty_2770_, lean_object* v_toBind_2771_, lean_object* v_y_2772_, lean_object* v_____do__lift_2773_){
_start:
{
lean_object* v___f_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
lean_inc(v_toBind_2771_);
lean_inc(v_f_2769_);
v___f_2774_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8), 9, 8);
lean_closure_set(v___f_2774_, 0, v_____do__lift_2773_);
lean_closure_set(v___f_2774_, 1, v_i_2765_);
lean_closure_set(v___f_2774_, 2, v_offset_2766_);
lean_closure_set(v___f_2774_, 3, v_toPure_2767_);
lean_closure_set(v___f_2774_, 4, v_inst_2768_);
lean_closure_set(v___f_2774_, 5, v_f_2769_);
lean_closure_set(v___f_2774_, 6, v_ty_2770_);
lean_closure_set(v___f_2774_, 7, v_toBind_2771_);
v___x_2775_ = lean_apply_1(v_f_2769_, v_y_2772_);
v___x_2776_ = lean_apply_4(v_toBind_2771_, lean_box(0), lean_box(0), v___x_2775_, v___f_2774_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10(lean_object* v_cidx_2777_, lean_object* v_toPure_2778_, lean_object* v_____do__lift_2779_){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2780_, 0, v_____do__lift_2779_);
lean_ctor_set(v___x_2780_, 1, v_cidx_2777_);
v___x_2781_ = lean_apply_2(v_toPure_2778_, lean_box(0), v___x_2780_);
return v___x_2781_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(lean_object* v_n_2782_, uint8_t v_check_2783_, uint8_t v_persistent_2784_, lean_object* v_toPure_2785_, lean_object* v_____do__lift_2786_){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v___x_2787_, 0, v_____do__lift_2786_);
lean_ctor_set(v___x_2787_, 1, v_n_2782_);
lean_ctor_set_uint8(v___x_2787_, sizeof(void*)*2, v_check_2783_);
lean_ctor_set_uint8(v___x_2787_, sizeof(void*)*2 + 1, v_persistent_2784_);
v___x_2788_ = lean_apply_2(v_toPure_2785_, lean_box(0), v___x_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2782_ = stack[0].m_obj;
uint8_t v_check_2783_ = stack[1].m_num;
uint8_t v_persistent_2784_ = stack[2].m_num;
lean_object* v_toPure_2785_ = stack[3].m_obj;
lean_object* v_____do__lift_2786_ = stack[4].m_obj;
lean_object* v_res_2789_;
v_res_2789_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(v_n_2782_, v_check_2783_, v_persistent_2784_, v_toPure_2785_, v_____do__lift_2786_);
stack->m_obj
 = v_res_2789_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed(lean_object* v_n_2790_, lean_object* v_check_2791_, lean_object* v_persistent_2792_, lean_object* v_toPure_2793_, lean_object* v_____do__lift_2794_){
_start:
{
uint8_t v_check_998__boxed_2795_; uint8_t v_persistent_999__boxed_2796_; lean_object* v_res_2797_; 
v_check_998__boxed_2795_ = lean_unbox(v_check_2791_);
v_persistent_999__boxed_2796_ = lean_unbox(v_persistent_2792_);
v_res_2797_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(v_n_2790_, v_check_998__boxed_2795_, v_persistent_999__boxed_2796_, v_toPure_2793_, v_____do__lift_2794_);
return v_res_2797_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(lean_object* v_n_2798_, uint8_t v_check_2799_, uint8_t v_persistent_2800_, lean_object* v_objs_x3f_2801_, lean_object* v_toPure_2802_, lean_object* v_____do__lift_2803_){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2804_ = lean_alloc_ctor(8, 3, 2);
lean_ctor_set(v___x_2804_, 0, v_____do__lift_2803_);
lean_ctor_set(v___x_2804_, 1, v_n_2798_);
lean_ctor_set(v___x_2804_, 2, v_objs_x3f_2801_);
lean_ctor_set_uint8(v___x_2804_, sizeof(void*)*3, v_check_2799_);
lean_ctor_set_uint8(v___x_2804_, sizeof(void*)*3 + 1, v_persistent_2800_);
v___x_2805_ = lean_apply_2(v_toPure_2802_, lean_box(0), v___x_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2798_ = stack[0].m_obj;
uint8_t v_check_2799_ = stack[1].m_num;
uint8_t v_persistent_2800_ = stack[2].m_num;
lean_object* v_objs_x3f_2801_ = stack[3].m_obj;
lean_object* v_toPure_2802_ = stack[4].m_obj;
lean_object* v_____do__lift_2803_ = stack[5].m_obj;
lean_object* v_res_2806_;
v_res_2806_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(v_n_2798_, v_check_2799_, v_persistent_2800_, v_objs_x3f_2801_, v_toPure_2802_, v_____do__lift_2803_);
stack->m_obj
 = v_res_2806_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed(lean_object* v_n_2807_, lean_object* v_check_2808_, lean_object* v_persistent_2809_, lean_object* v_objs_x3f_2810_, lean_object* v_toPure_2811_, lean_object* v_____do__lift_2812_){
_start:
{
uint8_t v_check_1024__boxed_2813_; uint8_t v_persistent_1025__boxed_2814_; lean_object* v_res_2815_; 
v_check_1024__boxed_2813_ = lean_unbox(v_check_2808_);
v_persistent_1025__boxed_2814_ = lean_unbox(v_persistent_2809_);
v_res_2815_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(v_n_2807_, v_check_1024__boxed_2813_, v_persistent_1025__boxed_2814_, v_objs_x3f_2810_, v_toPure_2811_, v_____do__lift_2812_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13(lean_object* v_toPure_2816_, lean_object* v_____do__lift_2817_){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2818_, 0, v_____do__lift_2817_);
v___x_2819_ = lean_apply_2(v_toPure_2816_, lean_box(0), v___x_2818_);
return v___x_2819_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(uint8_t v_pu_2820_, lean_object* v_m_2821_, lean_object* v_inst_2822_, lean_object* v_inst_2823_, lean_object* v_f_2824_, lean_object* v_decl_2825_){
_start:
{
switch(lean_obj_tag(v_decl_2825_))
{
case 0:
{
lean_object* v_toApplicative_2826_; lean_object* v_toBind_2827_; lean_object* v_toPure_2828_; lean_object* v_decl_2829_; lean_object* v___f_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v_toApplicative_2826_ = lean_ctor_get(v_inst_2823_, 0);
v_toBind_2827_ = lean_ctor_get(v_inst_2823_, 1);
lean_inc(v_toBind_2827_);
v_toPure_2828_ = lean_ctor_get(v_toApplicative_2826_, 1);
v_decl_2829_ = lean_ctor_get(v_decl_2825_, 0);
lean_inc_ref(v_decl_2829_);
lean_dec_ref_known(v_decl_2825_, 1);
lean_inc(v_toPure_2828_);
v___f_2830_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0), 2, 1);
lean_closure_set(v___f_2830_, 0, v_toPure_2828_);
v___x_2831_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_2820_, v_inst_2822_, v_inst_2823_, v_f_2824_, v_decl_2829_);
v___x_2832_ = lean_apply_4(v_toBind_2827_, lean_box(0), lean_box(0), v___x_2831_, v___f_2830_);
return v___x_2832_;
}
case 1:
{
lean_object* v_toApplicative_2833_; lean_object* v_toBind_2834_; lean_object* v_toPure_2835_; lean_object* v_decl_2836_; lean_object* v___f_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v_toApplicative_2833_ = lean_ctor_get(v_inst_2823_, 0);
v_toBind_2834_ = lean_ctor_get(v_inst_2823_, 1);
lean_inc(v_toBind_2834_);
v_toPure_2835_ = lean_ctor_get(v_toApplicative_2833_, 1);
v_decl_2836_ = lean_ctor_get(v_decl_2825_, 0);
lean_inc_ref(v_decl_2836_);
lean_dec_ref_known(v_decl_2825_, 1);
lean_inc(v_toPure_2835_);
v___f_2837_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1), 2, 1);
lean_closure_set(v___f_2837_, 0, v_toPure_2835_);
v___x_2838_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2820_, v_inst_2822_, v_inst_2823_, v_f_2824_, v_decl_2836_);
v___x_2839_ = lean_apply_4(v_toBind_2834_, lean_box(0), lean_box(0), v___x_2838_, v___f_2837_);
return v___x_2839_;
}
case 2:
{
lean_object* v_toApplicative_2840_; lean_object* v_toBind_2841_; lean_object* v_toPure_2842_; lean_object* v_decl_2843_; lean_object* v___f_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v_toApplicative_2840_ = lean_ctor_get(v_inst_2823_, 0);
v_toBind_2841_ = lean_ctor_get(v_inst_2823_, 1);
lean_inc(v_toBind_2841_);
v_toPure_2842_ = lean_ctor_get(v_toApplicative_2840_, 1);
v_decl_2843_ = lean_ctor_get(v_decl_2825_, 0);
lean_inc_ref(v_decl_2843_);
lean_dec_ref_known(v_decl_2825_, 1);
lean_inc(v_toPure_2842_);
v___f_2844_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2), 2, 1);
lean_closure_set(v___f_2844_, 0, v_toPure_2842_);
v___x_2845_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2820_, v_inst_2822_, v_inst_2823_, v_f_2824_, v_decl_2843_);
v___x_2846_ = lean_apply_4(v_toBind_2841_, lean_box(0), lean_box(0), v___x_2845_, v___f_2844_);
return v___x_2846_;
}
case 3:
{
lean_object* v_toApplicative_2847_; lean_object* v_toBind_2848_; lean_object* v_toPure_2849_; lean_object* v_fvarId_2850_; lean_object* v_i_2851_; lean_object* v_y_2852_; lean_object* v___x_2853_; lean_object* v___f_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v_toApplicative_2847_ = lean_ctor_get(v_inst_2823_, 0);
lean_dec(v_inst_2822_);
v_toBind_2848_ = lean_ctor_get(v_inst_2823_, 1);
lean_inc_n(v_toBind_2848_, 2);
v_toPure_2849_ = lean_ctor_get(v_toApplicative_2847_, 1);
lean_inc(v_toPure_2849_);
v_fvarId_2850_ = lean_ctor_get(v_decl_2825_, 0);
lean_inc(v_fvarId_2850_);
v_i_2851_ = lean_ctor_get(v_decl_2825_, 1);
lean_inc(v_i_2851_);
v_y_2852_ = lean_ctor_get(v_decl_2825_, 2);
lean_inc(v_y_2852_);
lean_dec_ref_known(v_decl_2825_, 3);
v___x_2853_ = lean_box(v_pu_2820_);
lean_inc(v_f_2824_);
v___f_2854_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed), 8, 7);
lean_closure_set(v___f_2854_, 0, v_i_2851_);
lean_closure_set(v___f_2854_, 1, v_toPure_2849_);
lean_closure_set(v___f_2854_, 2, v___x_2853_);
lean_closure_set(v___f_2854_, 3, v_inst_2823_);
lean_closure_set(v___f_2854_, 4, v_f_2824_);
lean_closure_set(v___f_2854_, 5, v_y_2852_);
lean_closure_set(v___f_2854_, 6, v_toBind_2848_);
v___x_2855_ = lean_apply_1(v_f_2824_, v_fvarId_2850_);
v___x_2856_ = lean_apply_4(v_toBind_2848_, lean_box(0), lean_box(0), v___x_2855_, v___f_2854_);
return v___x_2856_;
}
case 4:
{
lean_object* v_toApplicative_2857_; lean_object* v_toBind_2858_; lean_object* v_toPure_2859_; lean_object* v_fvarId_2860_; lean_object* v_i_2861_; lean_object* v_y_2862_; lean_object* v___f_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v_toApplicative_2857_ = lean_ctor_get(v_inst_2823_, 0);
lean_inc_ref(v_toApplicative_2857_);
lean_dec(v_inst_2822_);
v_toBind_2858_ = lean_ctor_get(v_inst_2823_, 1);
lean_inc_n(v_toBind_2858_, 2);
lean_dec_ref(v_inst_2823_);
v_toPure_2859_ = lean_ctor_get(v_toApplicative_2857_, 1);
lean_inc(v_toPure_2859_);
lean_dec_ref(v_toApplicative_2857_);
v_fvarId_2860_ = lean_ctor_get(v_decl_2825_, 0);
lean_inc(v_fvarId_2860_);
v_i_2861_ = lean_ctor_get(v_decl_2825_, 1);
lean_inc(v_i_2861_);
v_y_2862_ = lean_ctor_get(v_decl_2825_, 2);
lean_inc(v_y_2862_);
lean_dec_ref_known(v_decl_2825_, 3);
lean_inc(v_f_2824_);
v___f_2863_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6), 6, 5);
lean_closure_set(v___f_2863_, 0, v_i_2861_);
lean_closure_set(v___f_2863_, 1, v_toPure_2859_);
lean_closure_set(v___f_2863_, 2, v_f_2824_);
lean_closure_set(v___f_2863_, 3, v_y_2862_);
lean_closure_set(v___f_2863_, 4, v_toBind_2858_);
v___x_2864_ = lean_apply_1(v_f_2824_, v_fvarId_2860_);
v___x_2865_ = lean_apply_4(v_toBind_2858_, lean_box(0), lean_box(0), v___x_2864_, v___f_2863_);
return v___x_2865_;
}
case 5:
{
lean_object* v_toApplicative_2866_; lean_object* v_toBind_2867_; lean_object* v_toPure_2868_; lean_object* v_fvarId_2869_; lean_object* v_i_2870_; lean_object* v_offset_2871_; lean_object* v_y_2872_; lean_object* v_ty_2873_; lean_object* v___f_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v_toApplicative_2866_ = lean_ctor_get(v_inst_2823_, 0);
lean_dec(v_inst_2822_);
v_toBind_2867_ = lean_ctor_get(v_inst_2823_, 1);
lean_inc_n(v_toBind_2867_, 2);
v_toPure_2868_ = lean_ctor_get(v_toApplicative_2866_, 1);
lean_inc(v_toPure_2868_);
v_fvarId_2869_ = lean_ctor_get(v_decl_2825_, 0);
lean_inc(v_fvarId_2869_);
v_i_2870_ = lean_ctor_get(v_decl_2825_, 1);
lean_inc(v_i_2870_);
v_offset_2871_ = lean_ctor_get(v_decl_2825_, 2);
lean_inc(v_offset_2871_);
v_y_2872_ = lean_ctor_get(v_decl_2825_, 3);
lean_inc(v_y_2872_);
v_ty_2873_ = lean_ctor_get(v_decl_2825_, 4);
lean_inc_ref(v_ty_2873_);
lean_dec_ref_known(v_decl_2825_, 5);
lean_inc(v_f_2824_);
v___f_2874_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9), 9, 8);
lean_closure_set(v___f_2874_, 0, v_i_2870_);
lean_closure_set(v___f_2874_, 1, v_offset_2871_);
lean_closure_set(v___f_2874_, 2, v_toPure_2868_);
lean_closure_set(v___f_2874_, 3, v_inst_2823_);
lean_closure_set(v___f_2874_, 4, v_f_2824_);
lean_closure_set(v___f_2874_, 5, v_ty_2873_);
lean_closure_set(v___f_2874_, 6, v_toBind_2867_);
lean_closure_set(v___f_2874_, 7, v_y_2872_);
v___x_2875_ = lean_apply_1(v_f_2824_, v_fvarId_2869_);
v___x_2876_ = lean_apply_4(v_toBind_2867_, lean_box(0), lean_box(0), v___x_2875_, v___f_2874_);
return v___x_2876_;
}
case 6:
{
lean_object* v_toApplicative_2877_; lean_object* v_toBind_2878_; lean_object* v_toPure_2879_; lean_object* v_fvarId_2880_; lean_object* v_cidx_2881_; lean_object* v___f_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v_toApplicative_2877_ = lean_ctor_get(v_inst_2823_, 0);
lean_inc_ref(v_toApplicative_2877_);
lean_dec(v_inst_2822_);
v_toBind_2878_ = lean_ctor_get(v_inst_2823_, 1);
lean_inc(v_toBind_2878_);
lean_dec_ref(v_inst_2823_);
v_toPure_2879_ = lean_ctor_get(v_toApplicative_2877_, 1);
lean_inc(v_toPure_2879_);
lean_dec_ref(v_toApplicative_2877_);
v_fvarId_2880_ = lean_ctor_get(v_decl_2825_, 0);
lean_inc(v_fvarId_2880_);
v_cidx_2881_ = lean_ctor_get(v_decl_2825_, 1);
lean_inc(v_cidx_2881_);
lean_dec_ref_known(v_decl_2825_, 2);
v___f_2882_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10), 3, 2);
lean_closure_set(v___f_2882_, 0, v_cidx_2881_);
lean_closure_set(v___f_2882_, 1, v_toPure_2879_);
v___x_2883_ = lean_apply_1(v_f_2824_, v_fvarId_2880_);
v___x_2884_ = lean_apply_4(v_toBind_2878_, lean_box(0), lean_box(0), v___x_2883_, v___f_2882_);
return v___x_2884_;
}
case 7:
{
lean_object* v_toApplicative_2885_; lean_object* v_toBind_2886_; lean_object* v_toPure_2887_; lean_object* v_fvarId_2888_; lean_object* v_n_2889_; uint8_t v_check_2890_; uint8_t v_persistent_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___f_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_toApplicative_2885_ = lean_ctor_get(v_inst_2823_, 0);
lean_inc_ref(v_toApplicative_2885_);
lean_dec(v_inst_2822_);
v_toBind_2886_ = lean_ctor_get(v_inst_2823_, 1);
lean_inc(v_toBind_2886_);
lean_dec_ref(v_inst_2823_);
v_toPure_2887_ = lean_ctor_get(v_toApplicative_2885_, 1);
lean_inc(v_toPure_2887_);
lean_dec_ref(v_toApplicative_2885_);
v_fvarId_2888_ = lean_ctor_get(v_decl_2825_, 0);
lean_inc(v_fvarId_2888_);
v_n_2889_ = lean_ctor_get(v_decl_2825_, 1);
lean_inc(v_n_2889_);
v_check_2890_ = lean_ctor_get_uint8(v_decl_2825_, sizeof(void*)*2);
v_persistent_2891_ = lean_ctor_get_uint8(v_decl_2825_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_decl_2825_, 2);
v___x_2892_ = lean_box(v_check_2890_);
v___x_2893_ = lean_box(v_persistent_2891_);
v___f_2894_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed), 5, 4);
lean_closure_set(v___f_2894_, 0, v_n_2889_);
lean_closure_set(v___f_2894_, 1, v___x_2892_);
lean_closure_set(v___f_2894_, 2, v___x_2893_);
lean_closure_set(v___f_2894_, 3, v_toPure_2887_);
v___x_2895_ = lean_apply_1(v_f_2824_, v_fvarId_2888_);
v___x_2896_ = lean_apply_4(v_toBind_2886_, lean_box(0), lean_box(0), v___x_2895_, v___f_2894_);
return v___x_2896_;
}
case 8:
{
lean_object* v_toApplicative_2897_; lean_object* v_toBind_2898_; lean_object* v_toPure_2899_; lean_object* v_fvarId_2900_; lean_object* v_n_2901_; uint8_t v_check_2902_; uint8_t v_persistent_2903_; lean_object* v_objs_x3f_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___f_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v_toApplicative_2897_ = lean_ctor_get(v_inst_2823_, 0);
lean_inc_ref(v_toApplicative_2897_);
lean_dec(v_inst_2822_);
v_toBind_2898_ = lean_ctor_get(v_inst_2823_, 1);
lean_inc(v_toBind_2898_);
lean_dec_ref(v_inst_2823_);
v_toPure_2899_ = lean_ctor_get(v_toApplicative_2897_, 1);
lean_inc(v_toPure_2899_);
lean_dec_ref(v_toApplicative_2897_);
v_fvarId_2900_ = lean_ctor_get(v_decl_2825_, 0);
lean_inc(v_fvarId_2900_);
v_n_2901_ = lean_ctor_get(v_decl_2825_, 1);
lean_inc(v_n_2901_);
v_check_2902_ = lean_ctor_get_uint8(v_decl_2825_, sizeof(void*)*3);
v_persistent_2903_ = lean_ctor_get_uint8(v_decl_2825_, sizeof(void*)*3 + 1);
v_objs_x3f_2904_ = lean_ctor_get(v_decl_2825_, 2);
lean_inc(v_objs_x3f_2904_);
lean_dec_ref_known(v_decl_2825_, 3);
v___x_2905_ = lean_box(v_check_2902_);
v___x_2906_ = lean_box(v_persistent_2903_);
v___f_2907_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed), 6, 5);
lean_closure_set(v___f_2907_, 0, v_n_2901_);
lean_closure_set(v___f_2907_, 1, v___x_2905_);
lean_closure_set(v___f_2907_, 2, v___x_2906_);
lean_closure_set(v___f_2907_, 3, v_objs_x3f_2904_);
lean_closure_set(v___f_2907_, 4, v_toPure_2899_);
v___x_2908_ = lean_apply_1(v_f_2824_, v_fvarId_2900_);
v___x_2909_ = lean_apply_4(v_toBind_2898_, lean_box(0), lean_box(0), v___x_2908_, v___f_2907_);
return v___x_2909_;
}
default: 
{
lean_object* v_toApplicative_2910_; lean_object* v_toBind_2911_; lean_object* v_toPure_2912_; lean_object* v_fvarId_2913_; lean_object* v___f_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v_toApplicative_2910_ = lean_ctor_get(v_inst_2823_, 0);
lean_inc_ref(v_toApplicative_2910_);
lean_dec(v_inst_2822_);
v_toBind_2911_ = lean_ctor_get(v_inst_2823_, 1);
lean_inc(v_toBind_2911_);
lean_dec_ref(v_inst_2823_);
v_toPure_2912_ = lean_ctor_get(v_toApplicative_2910_, 1);
lean_inc(v_toPure_2912_);
lean_dec_ref(v_toApplicative_2910_);
v_fvarId_2913_ = lean_ctor_get(v_decl_2825_, 0);
lean_inc(v_fvarId_2913_);
lean_dec_ref_known(v_decl_2825_, 1);
v___f_2914_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13), 2, 1);
lean_closure_set(v___f_2914_, 0, v_toPure_2912_);
v___x_2915_ = lean_apply_1(v_f_2824_, v_fvarId_2913_);
v___x_2916_ = lean_apply_4(v_toBind_2911_, lean_box(0), lean_box(0), v___x_2915_, v___f_2914_);
return v___x_2916_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2820_ = stack[0].m_num;
lean_object* v_inst_2822_ = stack[2].m_obj;
lean_object* v_inst_2823_ = stack[3].m_obj;
lean_object* v_f_2824_ = stack[4].m_obj;
lean_object* v_decl_2825_ = stack[5].m_obj;
lean_object* v_res_2917_;
v_res_2917_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(v_pu_2820_, lean_box(0), v_inst_2822_, v_inst_2823_, v_f_2824_, v_decl_2825_);
stack->m_obj
 = v_res_2917_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed(lean_object* v_pu_2918_, lean_object* v_m_2919_, lean_object* v_inst_2920_, lean_object* v_inst_2921_, lean_object* v_f_2922_, lean_object* v_decl_2923_){
_start:
{
uint8_t v_pu_boxed_2924_; lean_object* v_res_2925_; 
v_pu_boxed_2924_ = lean_unbox(v_pu_2918_);
v_res_2925_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(v_pu_boxed_2924_, v_m_2919_, v_inst_2920_, v_inst_2921_, v_f_2922_, v_decl_2923_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15(lean_object* v_inst_2926_, lean_object* v_f_2927_, lean_object* v_y_2928_, lean_object* v_____r_2929_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2926_, v_f_2927_, v_y_2928_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16(lean_object* v_f_2931_, lean_object* v_y_2932_, lean_object* v_____r_2933_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = lean_apply_1(v_f_2931_, v_y_2932_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17(lean_object* v_inst_2935_, lean_object* v_f_2936_, lean_object* v_ty_2937_, lean_object* v_____r_2938_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2935_, v_f_2936_, v_ty_2937_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18(lean_object* v_f_2940_, lean_object* v_y_2941_, lean_object* v_toBind_2942_, lean_object* v___f_2943_, lean_object* v_____r_2944_){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = lean_apply_1(v_f_2940_, v_y_2941_);
v___x_2946_ = lean_apply_4(v_toBind_2942_, lean_box(0), lean_box(0), v___x_2945_, v___f_2943_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__19(lean_object* v_m_2947_, lean_object* v_inst_2948_, lean_object* v_f_2949_, lean_object* v_decl_2950_){
_start:
{
switch(lean_obj_tag(v_decl_2950_))
{
case 0:
{
lean_object* v_decl_2951_; lean_object* v___x_2952_; 
v_decl_2951_ = lean_ctor_get(v_decl_2950_, 0);
lean_inc_ref(v_decl_2951_);
lean_dec_ref_known(v_decl_2950_, 1);
v___x_2952_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_2948_, v_f_2949_, v_decl_2951_);
return v___x_2952_;
}
case 1:
{
lean_object* v_decl_2953_; lean_object* v___x_2954_; 
v_decl_2953_ = lean_ctor_get(v_decl_2950_, 0);
lean_inc_ref(v_decl_2953_);
lean_dec_ref_known(v_decl_2950_, 1);
v___x_2954_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2948_, v_f_2949_, v_decl_2953_);
return v___x_2954_;
}
case 2:
{
lean_object* v_decl_2955_; lean_object* v___x_2956_; 
v_decl_2955_ = lean_ctor_get(v_decl_2950_, 0);
lean_inc_ref(v_decl_2955_);
lean_dec_ref_known(v_decl_2950_, 1);
v___x_2956_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2948_, v_f_2949_, v_decl_2955_);
return v___x_2956_;
}
case 3:
{
lean_object* v_toBind_2957_; lean_object* v_fvarId_2958_; lean_object* v_y_2959_; lean_object* v___f_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v_toBind_2957_ = lean_ctor_get(v_inst_2948_, 1);
lean_inc(v_toBind_2957_);
v_fvarId_2958_ = lean_ctor_get(v_decl_2950_, 0);
lean_inc(v_fvarId_2958_);
v_y_2959_ = lean_ctor_get(v_decl_2950_, 2);
lean_inc(v_y_2959_);
lean_dec_ref_known(v_decl_2950_, 3);
lean_inc(v_f_2949_);
v___f_2960_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15), 4, 3);
lean_closure_set(v___f_2960_, 0, v_inst_2948_);
lean_closure_set(v___f_2960_, 1, v_f_2949_);
lean_closure_set(v___f_2960_, 2, v_y_2959_);
v___x_2961_ = lean_apply_1(v_f_2949_, v_fvarId_2958_);
v___x_2962_ = lean_apply_4(v_toBind_2957_, lean_box(0), lean_box(0), v___x_2961_, v___f_2960_);
return v___x_2962_;
}
case 4:
{
lean_object* v_toBind_2963_; lean_object* v_fvarId_2964_; lean_object* v_y_2965_; lean_object* v___f_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v_toBind_2963_ = lean_ctor_get(v_inst_2948_, 1);
lean_inc(v_toBind_2963_);
lean_dec_ref(v_inst_2948_);
v_fvarId_2964_ = lean_ctor_get(v_decl_2950_, 0);
lean_inc(v_fvarId_2964_);
v_y_2965_ = lean_ctor_get(v_decl_2950_, 2);
lean_inc(v_y_2965_);
lean_dec_ref_known(v_decl_2950_, 3);
lean_inc(v_f_2949_);
v___f_2966_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16), 3, 2);
lean_closure_set(v___f_2966_, 0, v_f_2949_);
lean_closure_set(v___f_2966_, 1, v_y_2965_);
v___x_2967_ = lean_apply_1(v_f_2949_, v_fvarId_2964_);
v___x_2968_ = lean_apply_4(v_toBind_2963_, lean_box(0), lean_box(0), v___x_2967_, v___f_2966_);
return v___x_2968_;
}
case 5:
{
lean_object* v_toBind_2969_; lean_object* v_fvarId_2970_; lean_object* v_y_2971_; lean_object* v_ty_2972_; lean_object* v___f_2973_; lean_object* v___f_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v_toBind_2969_ = lean_ctor_get(v_inst_2948_, 1);
lean_inc_n(v_toBind_2969_, 2);
v_fvarId_2970_ = lean_ctor_get(v_decl_2950_, 0);
lean_inc(v_fvarId_2970_);
v_y_2971_ = lean_ctor_get(v_decl_2950_, 3);
lean_inc(v_y_2971_);
v_ty_2972_ = lean_ctor_get(v_decl_2950_, 4);
lean_inc_ref(v_ty_2972_);
lean_dec_ref_known(v_decl_2950_, 5);
lean_inc_n(v_f_2949_, 2);
v___f_2973_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17), 4, 3);
lean_closure_set(v___f_2973_, 0, v_inst_2948_);
lean_closure_set(v___f_2973_, 1, v_f_2949_);
lean_closure_set(v___f_2973_, 2, v_ty_2972_);
v___f_2974_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18), 5, 4);
lean_closure_set(v___f_2974_, 0, v_f_2949_);
lean_closure_set(v___f_2974_, 1, v_y_2971_);
lean_closure_set(v___f_2974_, 2, v_toBind_2969_);
lean_closure_set(v___f_2974_, 3, v___f_2973_);
v___x_2975_ = lean_apply_1(v_f_2949_, v_fvarId_2970_);
v___x_2976_ = lean_apply_4(v_toBind_2969_, lean_box(0), lean_box(0), v___x_2975_, v___f_2974_);
return v___x_2976_;
}
default: 
{
lean_object* v_fvarId_2977_; lean_object* v___x_2978_; 
lean_dec_ref(v_inst_2948_);
v_fvarId_2977_ = lean_ctor_get(v_decl_2950_, 0);
lean_inc(v_fvarId_2977_);
lean_dec_ref(v_decl_2950_);
v___x_2978_ = lean_apply_1(v_f_2949_, v_fvarId_2977_);
return v___x_2978_;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(uint8_t v_pu_2980_){
_start:
{
lean_object* v___x_2981_; lean_object* v___f_2982_; lean_object* v___f_2983_; lean_object* v___x_2984_; 
v___x_2981_ = lean_box(v_pu_2980_);
v___f_2982_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed), 6, 1);
lean_closure_set(v___f_2982_, 0, v___x_2981_);
v___f_2983_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0));
v___x_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___f_2982_);
lean_ctor_set(v___x_2984_, 1, v___f_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2980_ = stack[0].m_num;
lean_object* v_res_2985_;
v_res_2985_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(v_pu_2980_);
stack->m_obj
 = v_res_2985_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___boxed(lean_object* v_pu_2986_){
_start:
{
uint8_t v_pu_boxed_2987_; lean_object* v_res_2988_; 
v_pu_boxed_2987_ = lean_unbox(v_pu_2986_);
v_res_2988_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(v_pu_boxed_2987_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0(lean_object* v_ctorName_2989_, lean_object* v_params_2990_, lean_object* v_toPure_2991_, lean_object* v_____do__lift_2992_){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2993_, 0, v_ctorName_2989_);
lean_ctor_set(v___x_2993_, 1, v_params_2990_);
lean_ctor_set(v___x_2993_, 2, v_____do__lift_2992_);
v___x_2994_ = lean_apply_2(v_toPure_2991_, lean_box(0), v___x_2993_);
return v___x_2994_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(lean_object* v_ctorName_2995_, lean_object* v_toPure_2996_, uint8_t v_pu_2997_, lean_object* v_inst_2998_, lean_object* v_inst_2999_, lean_object* v_f_3000_, lean_object* v_code_3001_, lean_object* v_toBind_3002_, lean_object* v_params_3003_){
_start:
{
lean_object* v___f_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___f_3004_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0), 4, 3);
lean_closure_set(v___f_3004_, 0, v_ctorName_2995_);
lean_closure_set(v___f_3004_, 1, v_params_3003_);
lean_closure_set(v___f_3004_, 2, v_toPure_2996_);
v___x_3005_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2997_, v_inst_2998_, v_inst_2999_, v_f_3000_, v_code_3001_);
v___x_3006_ = lean_apply_4(v_toBind_3002_, lean_box(0), lean_box(0), v___x_3005_, v___f_3004_);
return v___x_3006_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorName_2995_ = stack[0].m_obj;
lean_object* v_toPure_2996_ = stack[1].m_obj;
uint8_t v_pu_2997_ = stack[2].m_num;
lean_object* v_inst_2998_ = stack[3].m_obj;
lean_object* v_inst_2999_ = stack[4].m_obj;
lean_object* v_f_3000_ = stack[5].m_obj;
lean_object* v_code_3001_ = stack[6].m_obj;
lean_object* v_toBind_3002_ = stack[7].m_obj;
lean_object* v_params_3003_ = stack[8].m_obj;
lean_object* v_res_3007_;
v_res_3007_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(v_ctorName_2995_, v_toPure_2996_, v_pu_2997_, v_inst_2998_, v_inst_2999_, v_f_3000_, v_code_3001_, v_toBind_3002_, v_params_3003_);
stack->m_obj
 = v_res_3007_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed(lean_object* v_ctorName_3008_, lean_object* v_toPure_3009_, lean_object* v_pu_3010_, lean_object* v_inst_3011_, lean_object* v_inst_3012_, lean_object* v_f_3013_, lean_object* v_code_3014_, lean_object* v_toBind_3015_, lean_object* v_params_3016_){
_start:
{
uint8_t v_pu_boxed_3017_; lean_object* v_res_3018_; 
v_pu_boxed_3017_ = lean_unbox(v_pu_3010_);
v_res_3018_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(v_ctorName_3008_, v_toPure_3009_, v_pu_boxed_3017_, v_inst_3011_, v_inst_3012_, v_f_3013_, v_code_3014_, v_toBind_3015_, v_params_3016_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2(lean_object* v_info_3019_, lean_object* v_toPure_3020_, lean_object* v_____do__lift_3021_){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3022_, 0, v_info_3019_);
lean_ctor_set(v___x_3022_, 1, v_____do__lift_3021_);
v___x_3023_ = lean_apply_2(v_toPure_3020_, lean_box(0), v___x_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3(lean_object* v_toPure_3024_, lean_object* v_____do__lift_3025_){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3026_, 0, v_____do__lift_3025_);
v___x_3027_ = lean_apply_2(v_toPure_3024_, lean_box(0), v___x_3026_);
return v___x_3027_;
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(uint8_t v_pu_3028_, lean_object* v_m_3029_, lean_object* v_inst_3030_, lean_object* v_inst_3031_, lean_object* v_f_3032_, lean_object* v_alt_3033_){
_start:
{
switch(lean_obj_tag(v_alt_3033_))
{
case 0:
{
lean_object* v_toApplicative_3034_; lean_object* v_toBind_3035_; lean_object* v_toPure_3036_; lean_object* v_ctorName_3037_; lean_object* v_params_3038_; lean_object* v_code_3039_; lean_object* v___x_3040_; lean_object* v___f_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; size_t v_sz_3044_; size_t v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v_toApplicative_3034_ = lean_ctor_get(v_inst_3031_, 0);
v_toBind_3035_ = lean_ctor_get(v_inst_3031_, 1);
lean_inc_n(v_toBind_3035_, 2);
v_toPure_3036_ = lean_ctor_get(v_toApplicative_3034_, 1);
v_ctorName_3037_ = lean_ctor_get(v_alt_3033_, 0);
lean_inc(v_ctorName_3037_);
v_params_3038_ = lean_ctor_get(v_alt_3033_, 1);
lean_inc_ref(v_params_3038_);
v_code_3039_ = lean_ctor_get(v_alt_3033_, 2);
lean_inc_ref(v_code_3039_);
lean_dec_ref_known(v_alt_3033_, 3);
v___x_3040_ = lean_box(v_pu_3028_);
lean_inc(v_f_3032_);
lean_inc_ref_n(v_inst_3031_, 2);
lean_inc(v_inst_3030_);
lean_inc(v_toPure_3036_);
v___f_3041_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed), 9, 8);
lean_closure_set(v___f_3041_, 0, v_ctorName_3037_);
lean_closure_set(v___f_3041_, 1, v_toPure_3036_);
lean_closure_set(v___f_3041_, 2, v___x_3040_);
lean_closure_set(v___f_3041_, 3, v_inst_3030_);
lean_closure_set(v___f_3041_, 4, v_inst_3031_);
lean_closure_set(v___f_3041_, 5, v_f_3032_);
lean_closure_set(v___f_3041_, 6, v_code_3039_);
lean_closure_set(v___f_3041_, 7, v_toBind_3035_);
v___x_3042_ = lean_box(v_pu_3028_);
v___x_3043_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_3043_, 0, lean_box(0));
lean_closure_set(v___x_3043_, 1, v___x_3042_);
lean_closure_set(v___x_3043_, 2, v_inst_3030_);
lean_closure_set(v___x_3043_, 3, v_inst_3031_);
lean_closure_set(v___x_3043_, 4, v_f_3032_);
v_sz_3044_ = lean_array_size(v_params_3038_);
v___x_3045_ = ((size_t)0ULL);
v___x_3046_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3031_, v___x_3043_, v_sz_3044_, v___x_3045_, v_params_3038_);
v___x_3047_ = lean_apply_4(v_toBind_3035_, lean_box(0), lean_box(0), v___x_3046_, v___f_3041_);
return v___x_3047_;
}
case 1:
{
lean_object* v_toApplicative_3048_; lean_object* v_toBind_3049_; lean_object* v_toPure_3050_; lean_object* v_info_3051_; lean_object* v_code_3052_; lean_object* v___f_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v_toApplicative_3048_ = lean_ctor_get(v_inst_3031_, 0);
v_toBind_3049_ = lean_ctor_get(v_inst_3031_, 1);
lean_inc(v_toBind_3049_);
v_toPure_3050_ = lean_ctor_get(v_toApplicative_3048_, 1);
v_info_3051_ = lean_ctor_get(v_alt_3033_, 0);
lean_inc_ref(v_info_3051_);
v_code_3052_ = lean_ctor_get(v_alt_3033_, 1);
lean_inc_ref(v_code_3052_);
lean_dec_ref_known(v_alt_3033_, 2);
lean_inc(v_toPure_3050_);
v___f_3053_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2), 3, 2);
lean_closure_set(v___f_3053_, 0, v_info_3051_);
lean_closure_set(v___f_3053_, 1, v_toPure_3050_);
v___x_3054_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_3028_, v_inst_3030_, v_inst_3031_, v_f_3032_, v_code_3052_);
v___x_3055_ = lean_apply_4(v_toBind_3049_, lean_box(0), lean_box(0), v___x_3054_, v___f_3053_);
return v___x_3055_;
}
default: 
{
lean_object* v_toApplicative_3056_; lean_object* v_toBind_3057_; lean_object* v_toPure_3058_; lean_object* v_code_3059_; lean_object* v___f_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v_toApplicative_3056_ = lean_ctor_get(v_inst_3031_, 0);
v_toBind_3057_ = lean_ctor_get(v_inst_3031_, 1);
lean_inc(v_toBind_3057_);
v_toPure_3058_ = lean_ctor_get(v_toApplicative_3056_, 1);
v_code_3059_ = lean_ctor_get(v_alt_3033_, 0);
lean_inc_ref(v_code_3059_);
lean_dec_ref_known(v_alt_3033_, 1);
lean_inc(v_toPure_3058_);
v___f_3060_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3), 2, 1);
lean_closure_set(v___f_3060_, 0, v_toPure_3058_);
v___x_3061_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_3028_, v_inst_3030_, v_inst_3031_, v_f_3032_, v_code_3059_);
v___x_3062_ = lean_apply_4(v_toBind_3057_, lean_box(0), lean_box(0), v___x_3061_, v___f_3060_);
return v___x_3062_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3028_ = stack[0].m_num;
lean_object* v_inst_3030_ = stack[2].m_obj;
lean_object* v_inst_3031_ = stack[3].m_obj;
lean_object* v_f_3032_ = stack[4].m_obj;
lean_object* v_alt_3033_ = stack[5].m_obj;
lean_object* v_res_3063_;
v_res_3063_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(v_pu_3028_, lean_box(0), v_inst_3030_, v_inst_3031_, v_f_3032_, v_alt_3033_);
stack->m_obj
 = v_res_3063_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed(lean_object* v_pu_3064_, lean_object* v_m_3065_, lean_object* v_inst_3066_, lean_object* v_inst_3067_, lean_object* v_f_3068_, lean_object* v_alt_3069_){
_start:
{
uint8_t v_pu_boxed_3070_; lean_object* v_res_3071_; 
v_pu_boxed_3070_ = lean_unbox(v_pu_3064_);
v_res_3071_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(v_pu_boxed_3070_, v_m_3065_, v_inst_3066_, v_inst_3067_, v_f_3068_, v_alt_3069_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5(lean_object* v_inst_3072_, lean_object* v_f_3073_, lean_object* v_code_3074_, lean_object* v_____r_3075_){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_3072_, v_f_3073_, v_code_3074_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__7(lean_object* v_m_3077_, lean_object* v_inst_3078_, lean_object* v_f_3079_, lean_object* v_alt_3080_){
_start:
{
switch(lean_obj_tag(v_alt_3080_))
{
case 0:
{
lean_object* v_toApplicative_3081_; lean_object* v_toBind_3082_; lean_object* v_params_3083_; lean_object* v_code_3084_; lean_object* v_toPure_3085_; lean_object* v___f_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; uint8_t v___x_3090_; 
v_toApplicative_3081_ = lean_ctor_get(v_inst_3078_, 0);
v_toBind_3082_ = lean_ctor_get(v_inst_3078_, 1);
lean_inc(v_toBind_3082_);
v_params_3083_ = lean_ctor_get(v_alt_3080_, 1);
lean_inc_ref(v_params_3083_);
v_code_3084_ = lean_ctor_get(v_alt_3080_, 2);
lean_inc_ref(v_code_3084_);
lean_dec_ref_known(v_alt_3080_, 3);
v_toPure_3085_ = lean_ctor_get(v_toApplicative_3081_, 1);
lean_inc(v_f_3079_);
lean_inc_ref(v_inst_3078_);
v___f_3086_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5), 4, 3);
lean_closure_set(v___f_3086_, 0, v_inst_3078_);
lean_closure_set(v___f_3086_, 1, v_f_3079_);
lean_closure_set(v___f_3086_, 2, v_code_3084_);
v___x_3087_ = lean_unsigned_to_nat(0u);
v___x_3088_ = lean_array_get_size(v_params_3083_);
v___x_3089_ = lean_box(0);
v___x_3090_ = lean_nat_dec_lt(v___x_3087_, v___x_3088_);
if (v___x_3090_ == 0)
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
lean_inc(v_toPure_3085_);
lean_dec_ref(v_params_3083_);
lean_dec(v_f_3079_);
lean_dec_ref(v_inst_3078_);
v___x_3091_ = lean_apply_2(v_toPure_3085_, lean_box(0), v___x_3089_);
v___x_3092_ = lean_apply_4(v_toBind_3082_, lean_box(0), lean_box(0), v___x_3091_, v___f_3086_);
return v___x_3092_;
}
else
{
lean_object* v___f_3093_; uint8_t v___x_3094_; 
lean_inc_ref(v_inst_3078_);
v___f_3093_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_3093_, 0, v_inst_3078_);
lean_closure_set(v___f_3093_, 1, v_f_3079_);
v___x_3094_ = lean_nat_dec_le(v___x_3088_, v___x_3088_);
if (v___x_3094_ == 0)
{
if (v___x_3090_ == 0)
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
lean_inc(v_toPure_3085_);
lean_dec_ref(v___f_3093_);
lean_dec_ref(v_params_3083_);
lean_dec_ref(v_inst_3078_);
v___x_3095_ = lean_apply_2(v_toPure_3085_, lean_box(0), v___x_3089_);
v___x_3096_ = lean_apply_4(v_toBind_3082_, lean_box(0), lean_box(0), v___x_3095_, v___f_3086_);
return v___x_3096_;
}
else
{
size_t v___x_3097_; size_t v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3097_ = ((size_t)0ULL);
v___x_3098_ = lean_usize_of_nat(v___x_3088_);
v___x_3099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3078_, v___f_3093_, v_params_3083_, v___x_3097_, v___x_3098_, v___x_3089_);
v___x_3100_ = lean_apply_4(v_toBind_3082_, lean_box(0), lean_box(0), v___x_3099_, v___f_3086_);
return v___x_3100_;
}
}
else
{
size_t v___x_3101_; size_t v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3101_ = ((size_t)0ULL);
v___x_3102_ = lean_usize_of_nat(v___x_3088_);
v___x_3103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3078_, v___f_3093_, v_params_3083_, v___x_3101_, v___x_3102_, v___x_3089_);
v___x_3104_ = lean_apply_4(v_toBind_3082_, lean_box(0), lean_box(0), v___x_3103_, v___f_3086_);
return v___x_3104_;
}
}
}
case 1:
{
lean_object* v_code_3105_; lean_object* v___x_3106_; 
v_code_3105_ = lean_ctor_get(v_alt_3080_, 1);
lean_inc_ref(v_code_3105_);
lean_dec_ref_known(v_alt_3080_, 2);
v___x_3106_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_3078_, v_f_3079_, v_code_3105_);
return v___x_3106_;
}
default: 
{
lean_object* v_code_3107_; lean_object* v___x_3108_; 
v_code_3107_ = lean_ctor_get(v_alt_3080_, 0);
lean_inc_ref(v_code_3107_);
lean_dec_ref_known(v_alt_3080_, 1);
v___x_3108_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_3078_, v_f_3079_, v_code_3107_);
return v___x_3108_;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt(uint8_t v_pu_3110_){
_start:
{
lean_object* v___x_3111_; lean_object* v___f_3112_; lean_object* v___f_3113_; lean_object* v___x_3114_; 
v___x_3111_ = lean_box(v_pu_3110_);
v___f_3112_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed), 6, 1);
lean_closure_set(v___f_3112_, 0, v___x_3111_);
v___f_3113_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0));
v___x_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3114_, 0, v___f_3112_);
lean_ctor_set(v___x_3114_, 1, v___f_3113_);
return v___x_3114_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instTraverseFVarAlt_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3110_ = stack[0].m_num;
lean_object* v_res_3115_;
v_res_3115_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt(v_pu_3110_);
stack->m_obj
 = v_res_3115_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___boxed(lean_object* v_pu_3116_){
_start:
{
uint8_t v_pu_boxed_3117_; lean_object* v_res_3118_; 
v_pu_boxed_3117_ = lean_unbox(v_pu_3116_);
v_res_3118_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt(v_pu_boxed_3117_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(lean_object* v_toPure_3121_, lean_object* v_____do__lift_3122_){
_start:
{
if (lean_obj_tag(v_____do__lift_3122_) == 0)
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3123_ = lean_box(0);
v___x_3124_ = lean_apply_2(v_toPure_3121_, lean_box(0), v___x_3123_);
return v___x_3124_;
}
else
{
lean_object* v_val_3125_; uint8_t v___x_3126_; 
v_val_3125_ = lean_ctor_get(v_____do__lift_3122_, 0);
v___x_3126_ = lean_unbox(v_val_3125_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3127_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0));
v___x_3128_ = lean_apply_2(v_toPure_3121_, lean_box(0), v___x_3127_);
return v___x_3128_;
}
else
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3129_ = lean_box(0);
v___x_3130_ = lean_apply_2(v_toPure_3121_, lean_box(0), v___x_3129_);
return v___x_3130_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed(lean_object* v_toPure_3131_, lean_object* v_____do__lift_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(v_toPure_3131_, v_____do__lift_3132_);
lean_dec(v_____do__lift_3132_);
return v_res_3133_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(lean_object* v_toPure_3134_, uint8_t v_____do__lift_3135_){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3136_ = lean_box(v_____do__lift_3135_);
v___x_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
v___x_3138_ = lean_apply_2(v_toPure_3134_, lean_box(0), v___x_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_3134_ = stack[0].m_obj;
uint8_t v_____do__lift_3135_ = stack[1].m_num;
lean_object* v_res_3139_;
v_res_3139_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(v_toPure_3134_, v_____do__lift_3135_);
stack->m_obj
 = v_res_3139_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed(lean_object* v_toPure_3140_, lean_object* v_____do__lift_3141_){
_start:
{
uint8_t v_____do__lift_383__boxed_3142_; lean_object* v_res_3143_; 
v_____do__lift_383__boxed_3142_ = lean_unbox(v_____do__lift_3141_);
v_res_3143_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(v_toPure_3140_, v_____do__lift_383__boxed_3142_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(lean_object* v_inst_3144_, lean_object* v_f_3145_, lean_object* v_fvar_3146_){
_start:
{
lean_object* v_toApplicative_3147_; lean_object* v_toBind_3148_; lean_object* v_toPure_3149_; lean_object* v___x_3150_; lean_object* v___f_3151_; lean_object* v___f_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v_toApplicative_3147_ = lean_ctor_get(v_inst_3144_, 0);
lean_inc_ref(v_toApplicative_3147_);
v_toBind_3148_ = lean_ctor_get(v_inst_3144_, 1);
lean_inc_n(v_toBind_3148_, 2);
lean_dec_ref(v_inst_3144_);
v_toPure_3149_ = lean_ctor_get(v_toApplicative_3147_, 1);
lean_inc_n(v_toPure_3149_, 2);
lean_dec_ref(v_toApplicative_3147_);
v___x_3150_ = lean_apply_1(v_f_3145_, v_fvar_3146_);
v___f_3151_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3151_, 0, v_toPure_3149_);
v___f_3152_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3152_, 0, v_toPure_3149_);
v___x_3153_ = lean_apply_4(v_toBind_3148_, lean_box(0), lean_box(0), v___x_3150_, v___f_3152_);
v___x_3154_ = lean_apply_4(v_toBind_3148_, lean_box(0), lean_box(0), v___x_3153_, v___f_3151_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go(lean_object* v_m_3155_, lean_object* v_inst_3156_, lean_object* v_f_3157_, lean_object* v_fvar_3158_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(v_inst_3156_, v_f_3157_, v_fvar_3158_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(lean_object* v_toPure_3160_, lean_object* v_____do__lift_3161_){
_start:
{
if (lean_obj_tag(v_____do__lift_3161_) == 0)
{
uint8_t v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3162_ = 1;
v___x_3163_ = lean_box(v___x_3162_);
v___x_3164_ = lean_apply_2(v_toPure_3160_, lean_box(0), v___x_3163_);
return v___x_3164_;
}
else
{
uint8_t v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = 0;
v___x_3166_ = lean_box(v___x_3165_);
v___x_3167_ = lean_apply_2(v_toPure_3160_, lean_box(0), v___x_3166_);
return v___x_3167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed(lean_object* v_toPure_3168_, lean_object* v_____do__lift_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(v_toPure_3168_, v_____do__lift_3169_);
lean_dec(v_____do__lift_3169_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg(lean_object* v_inst_3171_, lean_object* v_inst_3172_, lean_object* v_f_3173_, lean_object* v_x_3174_){
_start:
{
lean_object* v_toApplicative_3175_; lean_object* v_toBind_3176_; lean_object* v_forFVarM_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3198_; 
v_toApplicative_3175_ = lean_ctor_get(v_inst_3171_, 0);
v_toBind_3176_ = lean_ctor_get(v_inst_3171_, 1);
lean_inc(v_toBind_3176_);
v_forFVarM_3177_ = lean_ctor_get(v_inst_3172_, 1);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_inst_3172_);
if (v_isSharedCheck_3198_ == 0)
{
lean_object* v_unused_3199_; 
v_unused_3199_ = lean_ctor_get(v_inst_3172_, 0);
lean_dec(v_unused_3199_);
v___x_3179_ = v_inst_3172_;
v_isShared_3180_ = v_isSharedCheck_3198_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_forFVarM_3177_);
lean_dec(v_inst_3172_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3198_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___f_3181_; lean_object* v___f_3182_; lean_object* v___f_3183_; lean_object* v___f_3184_; lean_object* v___f_3185_; lean_object* v___x_3187_; 
lean_inc_ref_n(v_inst_3171_, 5);
v___f_3181_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3181_, 0, v_inst_3171_);
v___f_3182_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3182_, 0, v_inst_3171_);
v___f_3183_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3183_, 0, v_inst_3171_);
v___f_3184_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3184_, 0, v_inst_3171_);
v___f_3185_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3185_, 0, v_inst_3171_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 1, v___f_3182_);
lean_ctor_set(v___x_3179_, 0, v___f_3181_);
v___x_3187_ = v___x_3179_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___f_3181_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v___f_3182_);
v___x_3187_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v_toPure_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___f_3195_; lean_object* v___x_3196_; 
lean_inc_ref_n(v_inst_3171_, 2);
v___x_3188_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3188_, 0, lean_box(0));
lean_closure_set(v___x_3188_, 1, v_inst_3171_);
v___x_3189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3187_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
lean_ctor_set(v___x_3189_, 2, v___f_3183_);
lean_ctor_set(v___x_3189_, 3, v___f_3184_);
lean_ctor_set(v___x_3189_, 4, v___f_3185_);
v___x_3190_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3190_, 0, lean_box(0));
lean_closure_set(v___x_3190_, 1, v_inst_3171_);
v___x_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3189_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
v_toPure_3192_ = lean_ctor_get(v_toApplicative_3175_, 1);
lean_inc(v_toPure_3192_);
v___x_3193_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go), 4, 3);
lean_closure_set(v___x_3193_, 0, lean_box(0));
lean_closure_set(v___x_3193_, 1, v_inst_3171_);
lean_closure_set(v___x_3193_, 2, v_f_3173_);
v___x_3194_ = lean_apply_4(v_forFVarM_3177_, lean_box(0), v___x_3191_, v___x_3193_, v_x_3174_);
v___f_3195_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3195_, 0, v_toPure_3192_);
v___x_3196_ = lean_apply_4(v_toBind_3176_, lean_box(0), lean_box(0), v___x_3194_, v___f_3195_);
return v___x_3196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM(lean_object* v_m_3200_, lean_object* v_00_u03b1_3201_, lean_object* v_inst_3202_, lean_object* v_inst_3203_, lean_object* v_f_3204_, lean_object* v_x_3205_){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = l_Lean_Compiler_LCNF_anyFVarM___redArg(v_inst_3202_, v_inst_3203_, v_f_3204_, v_x_3205_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(lean_object* v_toPure_3207_, lean_object* v_____do__lift_3208_){
_start:
{
if (lean_obj_tag(v_____do__lift_3208_) == 0)
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3209_ = lean_box(0);
v___x_3210_ = lean_apply_2(v_toPure_3207_, lean_box(0), v___x_3209_);
return v___x_3210_;
}
else
{
lean_object* v_val_3211_; uint8_t v___x_3212_; 
v_val_3211_ = lean_ctor_get(v_____do__lift_3208_, 0);
v___x_3212_ = lean_unbox(v_val_3211_);
if (v___x_3212_ == 0)
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = lean_box(0);
v___x_3214_ = lean_apply_2(v_toPure_3207_, lean_box(0), v___x_3213_);
return v___x_3214_;
}
else
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3215_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0));
v___x_3216_ = lean_apply_2(v_toPure_3207_, lean_box(0), v___x_3215_);
return v___x_3216_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed(lean_object* v_toPure_3217_, lean_object* v_____do__lift_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(v_toPure_3217_, v_____do__lift_3218_);
lean_dec(v_____do__lift_3218_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(lean_object* v_inst_3220_, lean_object* v_f_3221_, lean_object* v_fvar_3222_){
_start:
{
lean_object* v_toApplicative_3223_; lean_object* v_toBind_3224_; lean_object* v_toPure_3225_; lean_object* v___x_3226_; lean_object* v___f_3227_; lean_object* v___f_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v_toApplicative_3223_ = lean_ctor_get(v_inst_3220_, 0);
lean_inc_ref(v_toApplicative_3223_);
v_toBind_3224_ = lean_ctor_get(v_inst_3220_, 1);
lean_inc_n(v_toBind_3224_, 2);
lean_dec_ref(v_inst_3220_);
v_toPure_3225_ = lean_ctor_get(v_toApplicative_3223_, 1);
lean_inc_n(v_toPure_3225_, 2);
lean_dec_ref(v_toApplicative_3223_);
v___x_3226_ = lean_apply_1(v_f_3221_, v_fvar_3222_);
v___f_3227_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3227_, 0, v_toPure_3225_);
v___f_3228_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3228_, 0, v_toPure_3225_);
v___x_3229_ = lean_apply_4(v_toBind_3224_, lean_box(0), lean_box(0), v___x_3226_, v___f_3228_);
v___x_3230_ = lean_apply_4(v_toBind_3224_, lean_box(0), lean_box(0), v___x_3229_, v___f_3227_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go(lean_object* v_m_3231_, lean_object* v_inst_3232_, lean_object* v_f_3233_, lean_object* v_fvar_3234_){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(v_inst_3232_, v_f_3233_, v_fvar_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(lean_object* v_toPure_3236_, lean_object* v_____do__lift_3237_){
_start:
{
if (lean_obj_tag(v_____do__lift_3237_) == 1)
{
uint8_t v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3238_ = 1;
v___x_3239_ = lean_box(v___x_3238_);
v___x_3240_ = lean_apply_2(v_toPure_3236_, lean_box(0), v___x_3239_);
return v___x_3240_;
}
else
{
uint8_t v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3241_ = 0;
v___x_3242_ = lean_box(v___x_3241_);
v___x_3243_ = lean_apply_2(v_toPure_3236_, lean_box(0), v___x_3242_);
return v___x_3243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed(lean_object* v_toPure_3244_, lean_object* v_____do__lift_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(v_toPure_3244_, v_____do__lift_3245_);
lean_dec(v_____do__lift_3245_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg(lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_f_3249_, lean_object* v_x_3250_){
_start:
{
lean_object* v_toApplicative_3251_; lean_object* v_toBind_3252_; lean_object* v_forFVarM_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3274_; 
v_toApplicative_3251_ = lean_ctor_get(v_inst_3247_, 0);
v_toBind_3252_ = lean_ctor_get(v_inst_3247_, 1);
lean_inc(v_toBind_3252_);
v_forFVarM_3253_ = lean_ctor_get(v_inst_3248_, 1);
v_isSharedCheck_3274_ = !lean_is_exclusive(v_inst_3248_);
if (v_isSharedCheck_3274_ == 0)
{
lean_object* v_unused_3275_; 
v_unused_3275_ = lean_ctor_get(v_inst_3248_, 0);
lean_dec(v_unused_3275_);
v___x_3255_ = v_inst_3248_;
v_isShared_3256_ = v_isSharedCheck_3274_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_forFVarM_3253_);
lean_dec(v_inst_3248_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3274_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___f_3257_; lean_object* v___f_3258_; lean_object* v___f_3259_; lean_object* v___f_3260_; lean_object* v___f_3261_; lean_object* v___x_3263_; 
lean_inc_ref_n(v_inst_3247_, 5);
v___f_3257_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3257_, 0, v_inst_3247_);
v___f_3258_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3258_, 0, v_inst_3247_);
v___f_3259_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3259_, 0, v_inst_3247_);
v___f_3260_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3260_, 0, v_inst_3247_);
v___f_3261_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3261_, 0, v_inst_3247_);
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 1, v___f_3258_);
lean_ctor_set(v___x_3255_, 0, v___f_3257_);
v___x_3263_ = v___x_3255_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___f_3257_);
lean_ctor_set(v_reuseFailAlloc_3273_, 1, v___f_3258_);
v___x_3263_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v_toPure_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___f_3271_; lean_object* v___x_3272_; 
lean_inc_ref_n(v_inst_3247_, 2);
v___x_3264_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3264_, 0, lean_box(0));
lean_closure_set(v___x_3264_, 1, v_inst_3247_);
v___x_3265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3263_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
lean_ctor_set(v___x_3265_, 2, v___f_3259_);
lean_ctor_set(v___x_3265_, 3, v___f_3260_);
lean_ctor_set(v___x_3265_, 4, v___f_3261_);
v___x_3266_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3266_, 0, lean_box(0));
lean_closure_set(v___x_3266_, 1, v_inst_3247_);
v___x_3267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3265_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
v_toPure_3268_ = lean_ctor_get(v_toApplicative_3251_, 1);
lean_inc(v_toPure_3268_);
v___x_3269_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go), 4, 3);
lean_closure_set(v___x_3269_, 0, lean_box(0));
lean_closure_set(v___x_3269_, 1, v_inst_3247_);
lean_closure_set(v___x_3269_, 2, v_f_3249_);
v___x_3270_ = lean_apply_4(v_forFVarM_3253_, lean_box(0), v___x_3267_, v___x_3269_, v_x_3250_);
v___f_3271_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3271_, 0, v_toPure_3268_);
v___x_3272_ = lean_apply_4(v_toBind_3252_, lean_box(0), lean_box(0), v___x_3270_, v___f_3271_);
return v___x_3272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM(lean_object* v_m_3276_, lean_object* v_00_u03b1_3277_, lean_object* v_inst_3278_, lean_object* v_inst_3279_, lean_object* v_f_3280_, lean_object* v_x_3281_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = l_Lean_Compiler_LCNF_allFVarM___redArg(v_inst_3278_, v_inst_3279_, v_f_3280_, v_x_3281_);
return v___x_3282_;
}
}
uint8_t l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(lean_object* v_f_3283_, lean_object* v_x_3284_){
_start:
{
lean_object* v___x_3285_; uint8_t v___x_3286_; 
v___x_3285_ = lean_apply_1(v_f_3283_, v_x_3284_);
v___x_3286_ = lean_unbox(v___x_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3283_ = stack[0].m_obj;
lean_object* v_x_3284_ = stack[1].m_obj;
uint8_t v_res_3287_;
v_res_3287_ = l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(v_f_3283_, v_x_3284_);
stack->m_num = v_res_3287_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed(lean_object* v_f_3288_, lean_object* v_x_3289_){
_start:
{
uint8_t v_res_3290_; lean_object* v_r_3291_; 
v_res_3290_ = l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(v_f_3288_, v_x_3289_);
v_r_3291_ = lean_box(v_res_3290_);
return v_r_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg(lean_object* v_inst_3311_, lean_object* v_f_3312_, lean_object* v_x_3313_){
_start:
{
lean_object* v___f_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___f_3314_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3314_, 0, v_f_3312_);
v___x_3315_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9));
v___x_3316_ = l_Lean_Compiler_LCNF_anyFVarM___redArg(v___x_3315_, v_inst_3311_, v___f_3314_, v_x_3313_);
return v___x_3316_;
}
}
uint8_t l_Lean_Compiler_LCNF_anyFVar(lean_object* v_00_u03b1_3317_, lean_object* v_inst_3318_, lean_object* v_f_3319_, lean_object* v_x_3320_){
_start:
{
lean_object* v___x_3321_; uint8_t v___x_3322_; 
v___x_3321_ = l_Lean_Compiler_LCNF_anyFVar___redArg(v_inst_3318_, v_f_3319_, v_x_3320_);
v___x_3322_ = lean_unbox(v___x_3321_);
lean_dec(v___x_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_anyFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3318_ = stack[1].m_obj;
lean_object* v_f_3319_ = stack[2].m_obj;
lean_object* v_x_3320_ = stack[3].m_obj;
uint8_t v_res_3323_;
v_res_3323_ = l_Lean_Compiler_LCNF_anyFVar(lean_box(0), v_inst_3318_, v_f_3319_, v_x_3320_);
stack->m_num = v_res_3323_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___boxed(lean_object* v_00_u03b1_3324_, lean_object* v_inst_3325_, lean_object* v_f_3326_, lean_object* v_x_3327_){
_start:
{
uint8_t v_res_3328_; lean_object* v_r_3329_; 
v_res_3328_ = l_Lean_Compiler_LCNF_anyFVar(v_00_u03b1_3324_, v_inst_3325_, v_f_3326_, v_x_3327_);
v_r_3329_ = lean_box(v_res_3328_);
return v_r_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___redArg(lean_object* v_inst_3330_, lean_object* v_f_3331_, lean_object* v_x_3332_){
_start:
{
lean_object* v___f_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___f_3333_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3333_, 0, v_f_3331_);
v___x_3334_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9));
v___x_3335_ = l_Lean_Compiler_LCNF_allFVarM___redArg(v___x_3334_, v_inst_3330_, v___f_3333_, v_x_3332_);
return v___x_3335_;
}
}
uint8_t l_Lean_Compiler_LCNF_allFVar(lean_object* v_00_u03b1_3336_, lean_object* v_inst_3337_, lean_object* v_f_3338_, lean_object* v_x_3339_){
_start:
{
lean_object* v___x_3340_; uint8_t v___x_3341_; 
v___x_3340_ = l_Lean_Compiler_LCNF_allFVar___redArg(v_inst_3337_, v_f_3338_, v_x_3339_);
v___x_3341_ = lean_unbox(v___x_3340_);
lean_dec(v___x_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_allFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3337_ = stack[1].m_obj;
lean_object* v_f_3338_ = stack[2].m_obj;
lean_object* v_x_3339_ = stack[3].m_obj;
uint8_t v_res_3342_;
v_res_3342_ = l_Lean_Compiler_LCNF_allFVar(lean_box(0), v_inst_3337_, v_f_3338_, v_x_3339_);
stack->m_num = v_res_3342_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___boxed(lean_object* v_00_u03b1_3343_, lean_object* v_inst_3344_, lean_object* v_f_3345_, lean_object* v_x_3346_){
_start:
{
uint8_t v_res_3347_; lean_object* v_r_3348_; 
v_res_3347_ = l_Lean_Compiler_LCNF_allFVar(v_00_u03b1_3343_, v_inst_3344_, v_f_3345_, v_x_3346_);
v_r_3348_ = lean_box(v_res_3347_);
return v_r_3348_;
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
