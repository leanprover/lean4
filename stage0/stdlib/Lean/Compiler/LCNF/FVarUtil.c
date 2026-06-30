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
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(uint8_t, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(uint8_t, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0(lean_object* v_toApplicative_1_, lean_object* v_fvarId_2_, lean_object* v_e_3_, lean_object* v_____do__lift_4_){
_start:
{
lean_object* v_toPure_5_; uint8_t v___x_6_; 
v_toPure_5_ = lean_ctor_get(v_toApplicative_1_, 1);
lean_inc(v_toPure_5_);
lean_dec_ref(v_toApplicative_1_);
v___x_6_ = l_Lean_instBEqFVarId_beq(v_fvarId_2_, v_____do__lift_4_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; 
lean_dec_ref(v_e_3_);
v___x_7_ = l_Lean_Expr_fvar___override(v_____do__lift_4_);
v___x_8_ = lean_apply_2(v_toPure_5_, lean_box(0), v___x_7_);
return v___x_8_;
}
else
{
lean_object* v___x_9_; 
lean_dec(v_____do__lift_4_);
v___x_9_ = lean_apply_2(v_toPure_5_, lean_box(0), v_e_3_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0___boxed(lean_object* v_toApplicative_10_, lean_object* v_fvarId_11_, lean_object* v_e_12_, lean_object* v_____do__lift_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0(v_toApplicative_10_, v_fvarId_11_, v_e_12_, v_____do__lift_13_);
lean_dec(v_fvarId_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1(lean_object* v_toApplicative_15_, lean_object* v_____do__lift_16_, lean_object* v_e_17_, lean_object* v_fn_18_, lean_object* v_arg_19_, lean_object* v_____do__lift_20_){
_start:
{
lean_object* v_toPure_21_; uint8_t v___y_23_; size_t v___x_27_; size_t v___x_28_; uint8_t v___x_29_; 
v_toPure_21_ = lean_ctor_get(v_toApplicative_15_, 1);
lean_inc(v_toPure_21_);
lean_dec_ref(v_toApplicative_15_);
v___x_27_ = lean_ptr_addr(v_fn_18_);
v___x_28_ = lean_ptr_addr(v_____do__lift_16_);
v___x_29_ = lean_usize_dec_eq(v___x_27_, v___x_28_);
if (v___x_29_ == 0)
{
v___y_23_ = v___x_29_;
goto v___jp_22_;
}
else
{
size_t v___x_30_; size_t v___x_31_; uint8_t v___x_32_; 
v___x_30_ = lean_ptr_addr(v_arg_19_);
v___x_31_ = lean_ptr_addr(v_____do__lift_20_);
v___x_32_ = lean_usize_dec_eq(v___x_30_, v___x_31_);
v___y_23_ = v___x_32_;
goto v___jp_22_;
}
v___jp_22_:
{
if (v___y_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec_ref(v_e_17_);
v___x_24_ = l_Lean_Expr_app___override(v_____do__lift_16_, v_____do__lift_20_);
v___x_25_ = lean_apply_2(v_toPure_21_, lean_box(0), v___x_24_);
return v___x_25_;
}
else
{
lean_object* v___x_26_; 
lean_dec_ref(v_____do__lift_20_);
lean_dec_ref(v_____do__lift_16_);
v___x_26_ = lean_apply_2(v_toPure_21_, lean_box(0), v_e_17_);
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1___boxed(lean_object* v_toApplicative_33_, lean_object* v_____do__lift_34_, lean_object* v_e_35_, lean_object* v_fn_36_, lean_object* v_arg_37_, lean_object* v_____do__lift_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1(v_toApplicative_33_, v_____do__lift_34_, v_e_35_, v_fn_36_, v_arg_37_, v_____do__lift_38_);
lean_dec_ref(v_arg_37_);
lean_dec_ref(v_fn_36_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3(lean_object* v_toApplicative_40_, lean_object* v_binderName_41_, lean_object* v_____do__lift_42_, uint8_t v_binderInfo_43_, lean_object* v_e_44_, lean_object* v_binderType_45_, lean_object* v_body_46_, lean_object* v_____do__lift_47_){
_start:
{
lean_object* v_toPure_48_; uint8_t v___y_50_; size_t v___x_57_; size_t v___x_58_; uint8_t v___x_59_; 
v_toPure_48_ = lean_ctor_get(v_toApplicative_40_, 1);
lean_inc(v_toPure_48_);
lean_dec_ref(v_toApplicative_40_);
v___x_57_ = lean_ptr_addr(v_binderType_45_);
v___x_58_ = lean_ptr_addr(v_____do__lift_42_);
v___x_59_ = lean_usize_dec_eq(v___x_57_, v___x_58_);
if (v___x_59_ == 0)
{
v___y_50_ = v___x_59_;
goto v___jp_49_;
}
else
{
size_t v___x_60_; size_t v___x_61_; uint8_t v___x_62_; 
v___x_60_ = lean_ptr_addr(v_body_46_);
v___x_61_ = lean_ptr_addr(v_____do__lift_47_);
v___x_62_ = lean_usize_dec_eq(v___x_60_, v___x_61_);
v___y_50_ = v___x_62_;
goto v___jp_49_;
}
v___jp_49_:
{
if (v___y_50_ == 0)
{
lean_object* v___x_51_; lean_object* v___x_52_; 
lean_dec_ref(v_e_44_);
v___x_51_ = l_Lean_Expr_lam___override(v_binderName_41_, v_____do__lift_42_, v_____do__lift_47_, v_binderInfo_43_);
v___x_52_ = lean_apply_2(v_toPure_48_, lean_box(0), v___x_51_);
return v___x_52_;
}
else
{
uint8_t v___x_53_; 
v___x_53_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_43_, v_binderInfo_43_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec_ref(v_e_44_);
v___x_54_ = l_Lean_Expr_lam___override(v_binderName_41_, v_____do__lift_42_, v_____do__lift_47_, v_binderInfo_43_);
v___x_55_ = lean_apply_2(v_toPure_48_, lean_box(0), v___x_54_);
return v___x_55_;
}
else
{
lean_object* v___x_56_; 
lean_dec_ref(v_____do__lift_47_);
lean_dec_ref(v_____do__lift_42_);
lean_dec(v_binderName_41_);
v___x_56_ = lean_apply_2(v_toPure_48_, lean_box(0), v_e_44_);
return v___x_56_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3___boxed(lean_object* v_toApplicative_63_, lean_object* v_binderName_64_, lean_object* v_____do__lift_65_, lean_object* v_binderInfo_66_, lean_object* v_e_67_, lean_object* v_binderType_68_, lean_object* v_body_69_, lean_object* v_____do__lift_70_){
_start:
{
uint8_t v_binderInfo_1027__boxed_71_; lean_object* v_res_72_; 
v_binderInfo_1027__boxed_71_ = lean_unbox(v_binderInfo_66_);
v_res_72_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3(v_toApplicative_63_, v_binderName_64_, v_____do__lift_65_, v_binderInfo_1027__boxed_71_, v_e_67_, v_binderType_68_, v_body_69_, v_____do__lift_70_);
lean_dec_ref(v_body_69_);
lean_dec_ref(v_binderType_68_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5(lean_object* v_toApplicative_73_, lean_object* v_binderName_74_, lean_object* v_____do__lift_75_, uint8_t v_binderInfo_76_, lean_object* v_e_77_, lean_object* v_binderType_78_, lean_object* v_body_79_, lean_object* v_____do__lift_80_){
_start:
{
lean_object* v_toPure_81_; uint8_t v___y_83_; size_t v___x_90_; size_t v___x_91_; uint8_t v___x_92_; 
v_toPure_81_ = lean_ctor_get(v_toApplicative_73_, 1);
lean_inc(v_toPure_81_);
lean_dec_ref(v_toApplicative_73_);
v___x_90_ = lean_ptr_addr(v_binderType_78_);
v___x_91_ = lean_ptr_addr(v_____do__lift_75_);
v___x_92_ = lean_usize_dec_eq(v___x_90_, v___x_91_);
if (v___x_92_ == 0)
{
v___y_83_ = v___x_92_;
goto v___jp_82_;
}
else
{
size_t v___x_93_; size_t v___x_94_; uint8_t v___x_95_; 
v___x_93_ = lean_ptr_addr(v_body_79_);
v___x_94_ = lean_ptr_addr(v_____do__lift_80_);
v___x_95_ = lean_usize_dec_eq(v___x_93_, v___x_94_);
v___y_83_ = v___x_95_;
goto v___jp_82_;
}
v___jp_82_:
{
if (v___y_83_ == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec_ref(v_e_77_);
v___x_84_ = l_Lean_Expr_forallE___override(v_binderName_74_, v_____do__lift_75_, v_____do__lift_80_, v_binderInfo_76_);
v___x_85_ = lean_apply_2(v_toPure_81_, lean_box(0), v___x_84_);
return v___x_85_;
}
else
{
uint8_t v___x_86_; 
v___x_86_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_76_, v_binderInfo_76_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec_ref(v_e_77_);
v___x_87_ = l_Lean_Expr_forallE___override(v_binderName_74_, v_____do__lift_75_, v_____do__lift_80_, v_binderInfo_76_);
v___x_88_ = lean_apply_2(v_toPure_81_, lean_box(0), v___x_87_);
return v___x_88_;
}
else
{
lean_object* v___x_89_; 
lean_dec_ref(v_____do__lift_80_);
lean_dec_ref(v_____do__lift_75_);
lean_dec(v_binderName_74_);
v___x_89_ = lean_apply_2(v_toPure_81_, lean_box(0), v_e_77_);
return v___x_89_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5___boxed(lean_object* v_toApplicative_96_, lean_object* v_binderName_97_, lean_object* v_____do__lift_98_, lean_object* v_binderInfo_99_, lean_object* v_e_100_, lean_object* v_binderType_101_, lean_object* v_body_102_, lean_object* v_____do__lift_103_){
_start:
{
uint8_t v_binderInfo_1073__boxed_104_; lean_object* v_res_105_; 
v_binderInfo_1073__boxed_104_ = lean_unbox(v_binderInfo_99_);
v_res_105_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5(v_toApplicative_96_, v_binderName_97_, v_____do__lift_98_, v_binderInfo_1073__boxed_104_, v_e_100_, v_binderType_101_, v_body_102_, v_____do__lift_103_);
lean_dec_ref(v_body_102_);
lean_dec_ref(v_binderType_101_);
return v_res_105_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_109_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2));
v___x_110_ = lean_unsigned_to_nat(41u);
v___x_111_ = lean_unsigned_to_nat(30u);
v___x_112_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1));
v___x_113_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0));
v___x_114_ = l_mkPanicMessageWithDecl(v___x_113_, v___x_112_, v___x_111_, v___x_110_, v___x_109_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4(lean_object* v_toApplicative_115_, lean_object* v_binderName_116_, uint8_t v_binderInfo_117_, lean_object* v_e_118_, lean_object* v_binderType_119_, lean_object* v_body_120_, lean_object* v_inst_121_, lean_object* v_f_122_, lean_object* v_toBind_123_, lean_object* v_____do__lift_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___f_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_125_ = lean_box(v_binderInfo_117_);
lean_inc_ref(v_body_120_);
v___f_126_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_126_, 0, v_toApplicative_115_);
lean_closure_set(v___f_126_, 1, v_binderName_116_);
lean_closure_set(v___f_126_, 2, v_____do__lift_124_);
lean_closure_set(v___f_126_, 3, v___x_125_);
lean_closure_set(v___f_126_, 4, v_e_118_);
lean_closure_set(v___f_126_, 5, v_binderType_119_);
lean_closure_set(v___f_126_, 6, v_body_120_);
v___x_127_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_121_, v_f_122_, v_body_120_);
v___x_128_ = lean_apply_4(v_toBind_123_, lean_box(0), lean_box(0), v___x_127_, v___f_126_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4___boxed(lean_object* v_toApplicative_129_, lean_object* v_binderName_130_, lean_object* v_binderInfo_131_, lean_object* v_e_132_, lean_object* v_binderType_133_, lean_object* v_body_134_, lean_object* v_inst_135_, lean_object* v_f_136_, lean_object* v_toBind_137_, lean_object* v_____do__lift_138_){
_start:
{
uint8_t v_binderInfo_1152__boxed_139_; lean_object* v_res_140_; 
v_binderInfo_1152__boxed_139_ = lean_unbox(v_binderInfo_131_);
v_res_140_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4(v_toApplicative_129_, v_binderName_130_, v_binderInfo_1152__boxed_139_, v_e_132_, v_binderType_133_, v_body_134_, v_inst_135_, v_f_136_, v_toBind_137_, v_____do__lift_138_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6(lean_object* v_toApplicative_141_, lean_object* v_binderName_142_, uint8_t v_binderInfo_143_, lean_object* v_e_144_, lean_object* v_binderType_145_, lean_object* v_body_146_, lean_object* v_inst_147_, lean_object* v_f_148_, lean_object* v_toBind_149_, lean_object* v_____do__lift_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___f_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_151_ = lean_box(v_binderInfo_143_);
lean_inc_ref(v_body_146_);
v___f_152_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_152_, 0, v_toApplicative_141_);
lean_closure_set(v___f_152_, 1, v_binderName_142_);
lean_closure_set(v___f_152_, 2, v_____do__lift_150_);
lean_closure_set(v___f_152_, 3, v___x_151_);
lean_closure_set(v___f_152_, 4, v_e_144_);
lean_closure_set(v___f_152_, 5, v_binderType_145_);
lean_closure_set(v___f_152_, 6, v_body_146_);
v___x_153_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_147_, v_f_148_, v_body_146_);
v___x_154_ = lean_apply_4(v_toBind_149_, lean_box(0), lean_box(0), v___x_153_, v___f_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6___boxed(lean_object* v_toApplicative_155_, lean_object* v_binderName_156_, lean_object* v_binderInfo_157_, lean_object* v_e_158_, lean_object* v_binderType_159_, lean_object* v_body_160_, lean_object* v_inst_161_, lean_object* v_f_162_, lean_object* v_toBind_163_, lean_object* v_____do__lift_164_){
_start:
{
uint8_t v_binderInfo_1161__boxed_165_; lean_object* v_res_166_; 
v_binderInfo_1161__boxed_165_ = lean_unbox(v_binderInfo_157_);
v_res_166_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6(v_toApplicative_155_, v_binderName_156_, v_binderInfo_1161__boxed_165_, v_e_158_, v_binderType_159_, v_body_160_, v_inst_161_, v_f_162_, v_toBind_163_, v_____do__lift_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(lean_object* v_inst_167_, lean_object* v_f_168_, lean_object* v_e_169_){
_start:
{
uint8_t v___x_170_; 
v___x_170_ = l_Lean_Expr_hasFVar(v_e_169_);
if (v___x_170_ == 0)
{
lean_object* v_toApplicative_171_; lean_object* v_toPure_172_; lean_object* v___x_173_; 
lean_dec(v_f_168_);
v_toApplicative_171_ = lean_ctor_get(v_inst_167_, 0);
lean_inc_ref(v_toApplicative_171_);
lean_dec_ref(v_inst_167_);
v_toPure_172_ = lean_ctor_get(v_toApplicative_171_, 1);
lean_inc(v_toPure_172_);
lean_dec_ref(v_toApplicative_171_);
v___x_173_ = lean_apply_2(v_toPure_172_, lean_box(0), v_e_169_);
return v___x_173_;
}
else
{
switch(lean_obj_tag(v_e_169_))
{
case 1:
{
lean_object* v_fvarId_174_; lean_object* v_toApplicative_175_; lean_object* v_toBind_176_; lean_object* v___f_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_fvarId_174_ = lean_ctor_get(v_e_169_, 0);
lean_inc_n(v_fvarId_174_, 2);
v_toApplicative_175_ = lean_ctor_get(v_inst_167_, 0);
lean_inc_ref(v_toApplicative_175_);
v_toBind_176_ = lean_ctor_get(v_inst_167_, 1);
lean_inc(v_toBind_176_);
lean_dec_ref(v_inst_167_);
v___f_177_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_177_, 0, v_toApplicative_175_);
lean_closure_set(v___f_177_, 1, v_fvarId_174_);
lean_closure_set(v___f_177_, 2, v_e_169_);
v___x_178_ = lean_apply_1(v_f_168_, v_fvarId_174_);
v___x_179_ = lean_apply_4(v_toBind_176_, lean_box(0), lean_box(0), v___x_178_, v___f_177_);
return v___x_179_;
}
case 2:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec_ref_known(v_e_169_, 1);
lean_dec(v_f_168_);
v___x_180_ = l_Lean_instInhabitedExpr;
v___x_181_ = l_instInhabitedOfMonad___redArg(v_inst_167_, v___x_180_);
v___x_182_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3, &l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3);
v___x_183_ = l_panic___redArg(v___x_181_, v___x_182_);
lean_dec(v___x_181_);
return v___x_183_;
}
case 5:
{
lean_object* v_fn_184_; lean_object* v_arg_185_; lean_object* v_toApplicative_186_; lean_object* v_toBind_187_; lean_object* v___f_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_fn_184_ = lean_ctor_get(v_e_169_, 0);
lean_inc_ref_n(v_fn_184_, 2);
v_arg_185_ = lean_ctor_get(v_e_169_, 1);
lean_inc_ref(v_arg_185_);
v_toApplicative_186_ = lean_ctor_get(v_inst_167_, 0);
v_toBind_187_ = lean_ctor_get(v_inst_167_, 1);
lean_inc_n(v_toBind_187_, 2);
lean_inc(v_f_168_);
lean_inc_ref(v_inst_167_);
lean_inc_ref(v_toApplicative_186_);
v___f_188_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__2), 8, 7);
lean_closure_set(v___f_188_, 0, v_toApplicative_186_);
lean_closure_set(v___f_188_, 1, v_e_169_);
lean_closure_set(v___f_188_, 2, v_fn_184_);
lean_closure_set(v___f_188_, 3, v_arg_185_);
lean_closure_set(v___f_188_, 4, v_inst_167_);
lean_closure_set(v___f_188_, 5, v_f_168_);
lean_closure_set(v___f_188_, 6, v_toBind_187_);
v___x_189_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_167_, v_f_168_, v_fn_184_);
v___x_190_ = lean_apply_4(v_toBind_187_, lean_box(0), lean_box(0), v___x_189_, v___f_188_);
return v___x_190_;
}
case 6:
{
lean_object* v_binderName_191_; lean_object* v_binderType_192_; lean_object* v_body_193_; uint8_t v_binderInfo_194_; lean_object* v_toApplicative_195_; lean_object* v_toBind_196_; lean_object* v___x_197_; lean_object* v___f_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_binderName_191_ = lean_ctor_get(v_e_169_, 0);
lean_inc(v_binderName_191_);
v_binderType_192_ = lean_ctor_get(v_e_169_, 1);
lean_inc_ref_n(v_binderType_192_, 2);
v_body_193_ = lean_ctor_get(v_e_169_, 2);
lean_inc_ref(v_body_193_);
v_binderInfo_194_ = lean_ctor_get_uint8(v_e_169_, sizeof(void*)*3 + 8);
v_toApplicative_195_ = lean_ctor_get(v_inst_167_, 0);
v_toBind_196_ = lean_ctor_get(v_inst_167_, 1);
lean_inc_n(v_toBind_196_, 2);
v___x_197_ = lean_box(v_binderInfo_194_);
lean_inc(v_f_168_);
lean_inc_ref(v_inst_167_);
lean_inc_ref(v_toApplicative_195_);
v___f_198_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_198_, 0, v_toApplicative_195_);
lean_closure_set(v___f_198_, 1, v_binderName_191_);
lean_closure_set(v___f_198_, 2, v___x_197_);
lean_closure_set(v___f_198_, 3, v_e_169_);
lean_closure_set(v___f_198_, 4, v_binderType_192_);
lean_closure_set(v___f_198_, 5, v_body_193_);
lean_closure_set(v___f_198_, 6, v_inst_167_);
lean_closure_set(v___f_198_, 7, v_f_168_);
lean_closure_set(v___f_198_, 8, v_toBind_196_);
v___x_199_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_167_, v_f_168_, v_binderType_192_);
v___x_200_ = lean_apply_4(v_toBind_196_, lean_box(0), lean_box(0), v___x_199_, v___f_198_);
return v___x_200_;
}
case 7:
{
lean_object* v_binderName_201_; lean_object* v_binderType_202_; lean_object* v_body_203_; uint8_t v_binderInfo_204_; lean_object* v_toApplicative_205_; lean_object* v_toBind_206_; lean_object* v___x_207_; lean_object* v___f_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_binderName_201_ = lean_ctor_get(v_e_169_, 0);
lean_inc(v_binderName_201_);
v_binderType_202_ = lean_ctor_get(v_e_169_, 1);
lean_inc_ref_n(v_binderType_202_, 2);
v_body_203_ = lean_ctor_get(v_e_169_, 2);
lean_inc_ref(v_body_203_);
v_binderInfo_204_ = lean_ctor_get_uint8(v_e_169_, sizeof(void*)*3 + 8);
v_toApplicative_205_ = lean_ctor_get(v_inst_167_, 0);
v_toBind_206_ = lean_ctor_get(v_inst_167_, 1);
lean_inc_n(v_toBind_206_, 2);
v___x_207_ = lean_box(v_binderInfo_204_);
lean_inc(v_f_168_);
lean_inc_ref(v_inst_167_);
lean_inc_ref(v_toApplicative_205_);
v___f_208_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_208_, 0, v_toApplicative_205_);
lean_closure_set(v___f_208_, 1, v_binderName_201_);
lean_closure_set(v___f_208_, 2, v___x_207_);
lean_closure_set(v___f_208_, 3, v_e_169_);
lean_closure_set(v___f_208_, 4, v_binderType_202_);
lean_closure_set(v___f_208_, 5, v_body_203_);
lean_closure_set(v___f_208_, 6, v_inst_167_);
lean_closure_set(v___f_208_, 7, v_f_168_);
lean_closure_set(v___f_208_, 8, v_toBind_206_);
v___x_209_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_167_, v_f_168_, v_binderType_202_);
v___x_210_ = lean_apply_4(v_toBind_206_, lean_box(0), lean_box(0), v___x_209_, v___f_208_);
return v___x_210_;
}
case 8:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec_ref_known(v_e_169_, 4);
lean_dec(v_f_168_);
v___x_211_ = l_Lean_instInhabitedExpr;
v___x_212_ = l_instInhabitedOfMonad___redArg(v_inst_167_, v___x_211_);
v___x_213_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3, &l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3);
v___x_214_ = l_panic___redArg(v___x_212_, v___x_213_);
lean_dec(v___x_212_);
return v___x_214_;
}
case 11:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec_ref_known(v_e_169_, 3);
lean_dec(v_f_168_);
v___x_215_ = l_Lean_instInhabitedExpr;
v___x_216_ = l_instInhabitedOfMonad___redArg(v_inst_167_, v___x_215_);
v___x_217_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3, &l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3);
v___x_218_ = l_panic___redArg(v___x_216_, v___x_217_);
lean_dec(v___x_216_);
return v___x_218_;
}
default: 
{
lean_object* v_toApplicative_219_; lean_object* v_toPure_220_; lean_object* v___x_221_; 
lean_dec(v_f_168_);
v_toApplicative_219_ = lean_ctor_get(v_inst_167_, 0);
lean_inc_ref(v_toApplicative_219_);
lean_dec_ref(v_inst_167_);
v_toPure_220_ = lean_ctor_get(v_toApplicative_219_, 1);
lean_inc(v_toPure_220_);
lean_dec_ref(v_toApplicative_219_);
v___x_221_ = lean_apply_2(v_toPure_220_, lean_box(0), v_e_169_);
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__2(lean_object* v_toApplicative_222_, lean_object* v_e_223_, lean_object* v_fn_224_, lean_object* v_arg_225_, lean_object* v_inst_226_, lean_object* v_f_227_, lean_object* v_toBind_228_, lean_object* v_____do__lift_229_){
_start:
{
lean_object* v___f_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
lean_inc_ref(v_arg_225_);
v___f_230_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_230_, 0, v_toApplicative_222_);
lean_closure_set(v___f_230_, 1, v_____do__lift_229_);
lean_closure_set(v___f_230_, 2, v_e_223_);
lean_closure_set(v___f_230_, 3, v_fn_224_);
lean_closure_set(v___f_230_, 4, v_arg_225_);
v___x_231_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_226_, v_f_227_, v_arg_225_);
v___x_232_ = lean_apply_4(v_toBind_228_, lean_box(0), lean_box(0), v___x_231_, v___f_230_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM(lean_object* v_m_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_f_236_, lean_object* v_e_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_235_, v_f_236_, v_e_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___boxed(lean_object* v_m_239_, lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_f_242_, lean_object* v_e_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Compiler_LCNF_Expr_mapFVarM(v_m_239_, v_inst_240_, v_inst_241_, v_f_242_, v_e_243_);
lean_dec(v_inst_240_);
return v_res_244_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_246_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2));
v___x_247_ = lean_unsigned_to_nat(40u);
v___x_248_ = lean_unsigned_to_nat(49u);
v___x_249_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0));
v___x_250_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0));
v___x_251_ = l_mkPanicMessageWithDecl(v___x_250_, v___x_249_, v___x_248_, v___x_247_, v___x_246_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__1(lean_object* v_inst_252_, lean_object* v_f_253_, lean_object* v_arg_254_, lean_object* v_____r_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_252_, v_f_253_, v_arg_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(lean_object* v_inst_257_, lean_object* v_f_258_, lean_object* v_e_259_){
_start:
{
lean_object* v_ty_261_; lean_object* v_body_262_; uint8_t v___x_267_; 
v___x_267_ = l_Lean_Expr_hasFVar(v_e_259_);
if (v___x_267_ == 0)
{
lean_object* v_toApplicative_268_; lean_object* v_toPure_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec_ref(v_e_259_);
lean_dec(v_f_258_);
v_toApplicative_268_ = lean_ctor_get(v_inst_257_, 0);
lean_inc_ref(v_toApplicative_268_);
lean_dec_ref(v_inst_257_);
v_toPure_269_ = lean_ctor_get(v_toApplicative_268_, 1);
lean_inc(v_toPure_269_);
lean_dec_ref(v_toApplicative_268_);
v___x_270_ = lean_box(0);
v___x_271_ = lean_apply_2(v_toPure_269_, lean_box(0), v___x_270_);
return v___x_271_;
}
else
{
switch(lean_obj_tag(v_e_259_))
{
case 1:
{
lean_object* v_fvarId_272_; lean_object* v___x_273_; 
lean_dec_ref(v_inst_257_);
v_fvarId_272_ = lean_ctor_get(v_e_259_, 0);
lean_inc(v_fvarId_272_);
lean_dec_ref_known(v_e_259_, 1);
v___x_273_ = lean_apply_1(v_f_258_, v_fvarId_272_);
return v___x_273_;
}
case 2:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec_ref_known(v_e_259_, 1);
lean_dec(v_f_258_);
v___x_274_ = lean_box(0);
v___x_275_ = l_instInhabitedOfMonad___redArg(v_inst_257_, v___x_274_);
v___x_276_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1, &l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1);
v___x_277_ = l_panic___redArg(v___x_275_, v___x_276_);
lean_dec(v___x_275_);
return v___x_277_;
}
case 5:
{
lean_object* v_fn_278_; lean_object* v_arg_279_; lean_object* v_toBind_280_; lean_object* v___f_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_fn_278_ = lean_ctor_get(v_e_259_, 0);
lean_inc_ref(v_fn_278_);
v_arg_279_ = lean_ctor_get(v_e_259_, 1);
lean_inc_ref(v_arg_279_);
lean_dec_ref_known(v_e_259_, 2);
v_toBind_280_ = lean_ctor_get(v_inst_257_, 1);
lean_inc(v_toBind_280_);
lean_inc(v_f_258_);
lean_inc_ref(v_inst_257_);
v___f_281_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_281_, 0, v_inst_257_);
lean_closure_set(v___f_281_, 1, v_f_258_);
lean_closure_set(v___f_281_, 2, v_arg_279_);
v___x_282_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_257_, v_f_258_, v_fn_278_);
v___x_283_ = lean_apply_4(v_toBind_280_, lean_box(0), lean_box(0), v___x_282_, v___f_281_);
return v___x_283_;
}
case 6:
{
lean_object* v_binderType_284_; lean_object* v_body_285_; 
v_binderType_284_ = lean_ctor_get(v_e_259_, 1);
lean_inc_ref(v_binderType_284_);
v_body_285_ = lean_ctor_get(v_e_259_, 2);
lean_inc_ref(v_body_285_);
lean_dec_ref_known(v_e_259_, 3);
v_ty_261_ = v_binderType_284_;
v_body_262_ = v_body_285_;
goto v___jp_260_;
}
case 7:
{
lean_object* v_binderType_286_; lean_object* v_body_287_; 
v_binderType_286_ = lean_ctor_get(v_e_259_, 1);
lean_inc_ref(v_binderType_286_);
v_body_287_ = lean_ctor_get(v_e_259_, 2);
lean_inc_ref(v_body_287_);
lean_dec_ref_known(v_e_259_, 3);
v_ty_261_ = v_binderType_286_;
v_body_262_ = v_body_287_;
goto v___jp_260_;
}
case 8:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
lean_dec_ref_known(v_e_259_, 4);
lean_dec(v_f_258_);
v___x_288_ = lean_box(0);
v___x_289_ = l_instInhabitedOfMonad___redArg(v_inst_257_, v___x_288_);
v___x_290_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1, &l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1);
v___x_291_ = l_panic___redArg(v___x_289_, v___x_290_);
lean_dec(v___x_289_);
return v___x_291_;
}
case 11:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec_ref_known(v_e_259_, 3);
lean_dec(v_f_258_);
v___x_292_ = lean_box(0);
v___x_293_ = l_instInhabitedOfMonad___redArg(v_inst_257_, v___x_292_);
v___x_294_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1, &l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1);
v___x_295_ = l_panic___redArg(v___x_293_, v___x_294_);
lean_dec(v___x_293_);
return v___x_295_;
}
default: 
{
lean_object* v_toApplicative_296_; lean_object* v_toPure_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec_ref(v_e_259_);
lean_dec(v_f_258_);
v_toApplicative_296_ = lean_ctor_get(v_inst_257_, 0);
lean_inc_ref(v_toApplicative_296_);
lean_dec_ref(v_inst_257_);
v_toPure_297_ = lean_ctor_get(v_toApplicative_296_, 1);
lean_inc(v_toPure_297_);
lean_dec_ref(v_toApplicative_296_);
v___x_298_ = lean_box(0);
v___x_299_ = lean_apply_2(v_toPure_297_, lean_box(0), v___x_298_);
return v___x_299_;
}
}
}
v___jp_260_:
{
lean_object* v_toBind_263_; lean_object* v___f_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_toBind_263_ = lean_ctor_get(v_inst_257_, 1);
lean_inc(v_toBind_263_);
lean_inc(v_f_258_);
lean_inc_ref(v_inst_257_);
v___f_264_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_264_, 0, v_inst_257_);
lean_closure_set(v___f_264_, 1, v_f_258_);
lean_closure_set(v___f_264_, 2, v_body_262_);
v___x_265_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_257_, v_f_258_, v_ty_261_);
v___x_266_ = lean_apply_4(v_toBind_263_, lean_box(0), lean_box(0), v___x_265_, v___f_264_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__0(lean_object* v_inst_300_, lean_object* v_f_301_, lean_object* v_body_302_, lean_object* v_____r_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_300_, v_f_301_, v_body_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM(lean_object* v_m_305_, lean_object* v_inst_306_, lean_object* v_f_307_, lean_object* v_e_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_306_, v_f_307_, v_e_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0(lean_object* v_m_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_312_, v___y_313_, v___y_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0___boxed(lean_object* v_m_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0(v_m_316_, v_inst_317_, v_inst_318_, v___y_319_, v___y_320_);
lean_dec(v_inst_317_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__1(lean_object* v_m_322_, lean_object* v_inst_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_323_, v___y_324_, v___y_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__0(lean_object* v_arg_333_, lean_object* v_toPure_334_, lean_object* v_____do__lift_335_){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(v_arg_333_, v_____do__lift_335_);
v___x_337_ = lean_apply_2(v_toPure_334_, lean_box(0), v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1(uint8_t v_pu_338_, lean_object* v_arg_339_, lean_object* v_toPure_340_, lean_object* v_____do__lift_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_338_, v_arg_339_, v_____do__lift_341_);
v___x_343_ = lean_apply_2(v_toPure_340_, lean_box(0), v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1___boxed(lean_object* v_pu_344_, lean_object* v_arg_345_, lean_object* v_toPure_346_, lean_object* v_____do__lift_347_){
_start:
{
uint8_t v_pu_boxed_348_; lean_object* v_res_349_; 
v_pu_boxed_348_ = lean_unbox(v_pu_344_);
v_res_349_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1(v_pu_boxed_348_, v_arg_345_, v_toPure_346_, v_____do__lift_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(uint8_t v_pu_350_, lean_object* v_inst_351_, lean_object* v_f_352_, lean_object* v_arg_353_){
_start:
{
switch(lean_obj_tag(v_arg_353_))
{
case 0:
{
lean_object* v_toApplicative_354_; lean_object* v_toPure_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_toApplicative_354_ = lean_ctor_get(v_inst_351_, 0);
lean_inc_ref(v_toApplicative_354_);
lean_dec(v_f_352_);
lean_dec_ref(v_inst_351_);
v_toPure_355_ = lean_ctor_get(v_toApplicative_354_, 1);
lean_inc(v_toPure_355_);
lean_dec_ref(v_toApplicative_354_);
v___x_356_ = lean_box(0);
v___x_357_ = lean_apply_2(v_toPure_355_, lean_box(0), v___x_356_);
return v___x_357_;
}
case 1:
{
lean_object* v_toApplicative_358_; lean_object* v_toBind_359_; lean_object* v_toPure_360_; lean_object* v_fvarId_361_; lean_object* v___f_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_toApplicative_358_ = lean_ctor_get(v_inst_351_, 0);
lean_inc_ref(v_toApplicative_358_);
v_toBind_359_ = lean_ctor_get(v_inst_351_, 1);
lean_inc(v_toBind_359_);
lean_dec_ref(v_inst_351_);
v_toPure_360_ = lean_ctor_get(v_toApplicative_358_, 1);
lean_inc(v_toPure_360_);
lean_dec_ref(v_toApplicative_358_);
v_fvarId_361_ = lean_ctor_get(v_arg_353_, 0);
lean_inc(v_fvarId_361_);
v___f_362_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_362_, 0, v_arg_353_);
lean_closure_set(v___f_362_, 1, v_toPure_360_);
v___x_363_ = lean_apply_1(v_f_352_, v_fvarId_361_);
v___x_364_ = lean_apply_4(v_toBind_359_, lean_box(0), lean_box(0), v___x_363_, v___f_362_);
return v___x_364_;
}
default: 
{
lean_object* v_toApplicative_365_; lean_object* v_toBind_366_; lean_object* v_toPure_367_; lean_object* v_expr_368_; lean_object* v___x_369_; lean_object* v___f_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_toApplicative_365_ = lean_ctor_get(v_inst_351_, 0);
v_toBind_366_ = lean_ctor_get(v_inst_351_, 1);
lean_inc(v_toBind_366_);
v_toPure_367_ = lean_ctor_get(v_toApplicative_365_, 1);
v_expr_368_ = lean_ctor_get(v_arg_353_, 0);
lean_inc_ref(v_expr_368_);
v___x_369_ = lean_box(v_pu_350_);
lean_inc(v_toPure_367_);
v___f_370_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_370_, 0, v___x_369_);
lean_closure_set(v___f_370_, 1, v_arg_353_);
lean_closure_set(v___f_370_, 2, v_toPure_367_);
v___x_371_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_351_, v_f_352_, v_expr_368_);
v___x_372_ = lean_apply_4(v_toBind_366_, lean_box(0), lean_box(0), v___x_371_, v___f_370_);
return v___x_372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___boxed(lean_object* v_pu_373_, lean_object* v_inst_374_, lean_object* v_f_375_, lean_object* v_arg_376_){
_start:
{
uint8_t v_pu_boxed_377_; lean_object* v_res_378_; 
v_pu_boxed_377_ = lean_unbox(v_pu_373_);
v_res_378_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_boxed_377_, v_inst_374_, v_f_375_, v_arg_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM(lean_object* v_m_379_, uint8_t v_pu_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_f_383_, lean_object* v_arg_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_380_, v_inst_382_, v_f_383_, v_arg_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___boxed(lean_object* v_m_386_, lean_object* v_pu_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_f_390_, lean_object* v_arg_391_){
_start:
{
uint8_t v_pu_boxed_392_; lean_object* v_res_393_; 
v_pu_boxed_392_ = lean_unbox(v_pu_387_);
v_res_393_ = l_Lean_Compiler_LCNF_Arg_mapFVarM(v_m_386_, v_pu_boxed_392_, v_inst_388_, v_inst_389_, v_f_390_, v_arg_391_);
lean_dec(v_inst_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(lean_object* v_inst_394_, lean_object* v_f_395_, lean_object* v_arg_396_){
_start:
{
switch(lean_obj_tag(v_arg_396_))
{
case 0:
{
lean_object* v_toApplicative_397_; lean_object* v_toPure_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_toApplicative_397_ = lean_ctor_get(v_inst_394_, 0);
lean_inc_ref(v_toApplicative_397_);
lean_dec(v_f_395_);
lean_dec_ref(v_inst_394_);
v_toPure_398_ = lean_ctor_get(v_toApplicative_397_, 1);
lean_inc(v_toPure_398_);
lean_dec_ref(v_toApplicative_397_);
v___x_399_ = lean_box(0);
v___x_400_ = lean_apply_2(v_toPure_398_, lean_box(0), v___x_399_);
return v___x_400_;
}
case 1:
{
lean_object* v_fvarId_401_; lean_object* v___x_402_; 
lean_dec_ref(v_inst_394_);
v_fvarId_401_ = lean_ctor_get(v_arg_396_, 0);
lean_inc(v_fvarId_401_);
lean_dec_ref_known(v_arg_396_, 1);
v___x_402_ = lean_apply_1(v_f_395_, v_fvarId_401_);
return v___x_402_;
}
default: 
{
lean_object* v_expr_403_; lean_object* v___x_404_; 
v_expr_403_ = lean_ctor_get(v_arg_396_, 0);
lean_inc_ref(v_expr_403_);
lean_dec_ref_known(v_arg_396_, 1);
v___x_404_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_394_, v_f_395_, v_expr_403_);
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM(lean_object* v_m_405_, uint8_t v_pu_406_, lean_object* v_inst_407_, lean_object* v_f_408_, lean_object* v_arg_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_407_, v_f_408_, v_arg_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___boxed(lean_object* v_m_411_, lean_object* v_pu_412_, lean_object* v_inst_413_, lean_object* v_f_414_, lean_object* v_arg_415_){
_start:
{
uint8_t v_pu_boxed_416_; lean_object* v_res_417_; 
v_pu_boxed_416_ = lean_unbox(v_pu_412_);
v_res_417_ = l_Lean_Compiler_LCNF_Arg_forFVarM(v_m_411_, v_pu_boxed_416_, v_inst_413_, v_f_414_, v_arg_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0(uint8_t v_pu_418_, lean_object* v_m_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_418_, v_inst_421_, v___y_422_, v___y_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0___boxed(lean_object* v_pu_425_, lean_object* v_m_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
uint8_t v_pu_boxed_431_; lean_object* v_res_432_; 
v_pu_boxed_431_ = lean_unbox(v_pu_425_);
v_res_432_ = l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0(v_pu_boxed_431_, v_m_426_, v_inst_427_, v_inst_428_, v___y_429_, v___y_430_);
lean_dec(v_inst_427_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__1(lean_object* v_m_433_, lean_object* v_inst_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_434_, v___y_435_, v___y_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg(uint8_t v_pu_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___f_441_; lean_object* v___f_442_; lean_object* v___x_443_; 
v___x_440_ = lean_box(v_pu_439_);
v___f_441_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_441_, 0, v___x_440_);
v___f_442_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarArg___closed__0));
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v___f_441_);
lean_ctor_set(v___x_443_, 1, v___f_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___boxed(lean_object* v_pu_444_){
_start:
{
uint8_t v_pu_boxed_445_; lean_object* v_res_446_; 
v_pu_boxed_445_ = lean_unbox(v_pu_444_);
v_res_446_ = l_Lean_Compiler_LCNF_instTraverseFVarArg(v_pu_boxed_445_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0(uint8_t v_pu_447_, lean_object* v_inst_448_, lean_object* v_f_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_447_, v_inst_448_, v_f_449_, v___y_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_452_, lean_object* v_inst_453_, lean_object* v_f_454_, lean_object* v___y_455_){
_start:
{
uint8_t v_pu_boxed_456_; lean_object* v_res_457_; 
v_pu_boxed_456_ = lean_unbox(v_pu_452_);
v_res_457_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0(v_pu_boxed_456_, v_inst_453_, v_f_454_, v___y_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1(uint8_t v_pu_458_, lean_object* v_e_459_, lean_object* v_toPure_460_, lean_object* v_____do__lift_461_){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_458_, v_e_459_, v_____do__lift_461_);
v___x_463_ = lean_apply_2(v_toPure_460_, lean_box(0), v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1___boxed(lean_object* v_pu_464_, lean_object* v_e_465_, lean_object* v_toPure_466_, lean_object* v_____do__lift_467_){
_start:
{
uint8_t v_pu_boxed_468_; lean_object* v_res_469_; 
v_pu_boxed_468_ = lean_unbox(v_pu_464_);
v_res_469_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1(v_pu_boxed_468_, v_e_465_, v_toPure_466_, v_____do__lift_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(uint8_t v_pu_470_, lean_object* v_e_471_, lean_object* v_toPure_472_, lean_object* v_____do__lift_473_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_470_, v_e_471_, v_____do__lift_473_);
v___x_475_ = lean_apply_2(v_toPure_472_, lean_box(0), v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed(lean_object* v_pu_476_, lean_object* v_e_477_, lean_object* v_toPure_478_, lean_object* v_____do__lift_479_){
_start:
{
uint8_t v_pu_boxed_480_; lean_object* v_res_481_; 
v_pu_boxed_480_ = lean_unbox(v_pu_476_);
v_res_481_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(v_pu_boxed_480_, v_e_477_, v_toPure_478_, v_____do__lift_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7(uint8_t v_pu_482_, lean_object* v_e_483_, lean_object* v_____do__lift_484_, lean_object* v_toPure_485_, lean_object* v_____do__lift_486_){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_482_, v_e_483_, v_____do__lift_484_, v_____do__lift_486_);
v___x_488_ = lean_apply_2(v_toPure_485_, lean_box(0), v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7___boxed(lean_object* v_pu_489_, lean_object* v_e_490_, lean_object* v_____do__lift_491_, lean_object* v_toPure_492_, lean_object* v_____do__lift_493_){
_start:
{
uint8_t v_pu_boxed_494_; lean_object* v_res_495_; 
v_pu_boxed_494_ = lean_unbox(v_pu_489_);
v_res_495_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7(v_pu_boxed_494_, v_e_490_, v_____do__lift_491_, v_toPure_492_, v_____do__lift_493_);
lean_dec(v_e_490_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3(uint8_t v_pu_496_, lean_object* v_e_497_, lean_object* v_toPure_498_, lean_object* v_args_499_, lean_object* v_inst_500_, lean_object* v___f_501_, lean_object* v_toBind_502_, lean_object* v_____do__lift_503_){
_start:
{
lean_object* v___x_504_; lean_object* v___f_505_; size_t v_sz_506_; size_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_504_ = lean_box(v_pu_496_);
v___f_505_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7___boxed), 5, 4);
lean_closure_set(v___f_505_, 0, v___x_504_);
lean_closure_set(v___f_505_, 1, v_e_497_);
lean_closure_set(v___f_505_, 2, v_____do__lift_503_);
lean_closure_set(v___f_505_, 3, v_toPure_498_);
v_sz_506_ = lean_array_size(v_args_499_);
v___x_507_ = ((size_t)0ULL);
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_500_, v___f_501_, v_sz_506_, v___x_507_, v_args_499_);
v___x_509_ = lean_apply_4(v_toBind_502_, lean_box(0), lean_box(0), v___x_508_, v___f_505_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3___boxed(lean_object* v_pu_510_, lean_object* v_e_511_, lean_object* v_toPure_512_, lean_object* v_args_513_, lean_object* v_inst_514_, lean_object* v___f_515_, lean_object* v_toBind_516_, lean_object* v_____do__lift_517_){
_start:
{
uint8_t v_pu_boxed_518_; lean_object* v_res_519_; 
v_pu_boxed_518_ = lean_unbox(v_pu_510_);
v_res_519_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3(v_pu_boxed_518_, v_e_511_, v_toPure_512_, v_args_513_, v_inst_514_, v___f_515_, v_toBind_516_, v_____do__lift_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8(uint8_t v_pu_520_, lean_object* v_e_521_, lean_object* v_n_522_, lean_object* v_toPure_523_, lean_object* v_____do__lift_524_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_520_, v_e_521_, v_n_522_, v_____do__lift_524_);
v___x_526_ = lean_apply_2(v_toPure_523_, lean_box(0), v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8___boxed(lean_object* v_pu_527_, lean_object* v_e_528_, lean_object* v_n_529_, lean_object* v_toPure_530_, lean_object* v_____do__lift_531_){
_start:
{
uint8_t v_pu_boxed_532_; lean_object* v_res_533_; 
v_pu_boxed_532_ = lean_unbox(v_pu_527_);
v_res_533_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8(v_pu_boxed_532_, v_e_528_, v_n_529_, v_toPure_530_, v_____do__lift_531_);
lean_dec(v_e_528_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(uint8_t v_pu_534_, lean_object* v_e_535_, lean_object* v_____do__lift_536_, lean_object* v_i_537_, uint8_t v_updateHeader_538_, lean_object* v_toPure_539_, lean_object* v_____do__lift_540_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_534_, v_e_535_, v_____do__lift_536_, v_i_537_, v_updateHeader_538_, v_____do__lift_540_);
v___x_542_ = lean_apply_2(v_toPure_539_, lean_box(0), v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed(lean_object* v_pu_543_, lean_object* v_e_544_, lean_object* v_____do__lift_545_, lean_object* v_i_546_, lean_object* v_updateHeader_547_, lean_object* v_toPure_548_, lean_object* v_____do__lift_549_){
_start:
{
uint8_t v_pu_boxed_550_; uint8_t v_updateHeader_627__boxed_551_; lean_object* v_res_552_; 
v_pu_boxed_550_ = lean_unbox(v_pu_543_);
v_updateHeader_627__boxed_551_ = lean_unbox(v_updateHeader_547_);
v_res_552_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(v_pu_boxed_550_, v_e_544_, v_____do__lift_545_, v_i_546_, v_updateHeader_627__boxed_551_, v_toPure_548_, v_____do__lift_549_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(uint8_t v_pu_553_, lean_object* v_e_554_, lean_object* v_i_555_, uint8_t v_updateHeader_556_, lean_object* v_toPure_557_, lean_object* v_args_558_, lean_object* v_inst_559_, lean_object* v___f_560_, lean_object* v_toBind_561_, lean_object* v_____do__lift_562_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___f_565_; size_t v_sz_566_; size_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_563_ = lean_box(v_pu_553_);
v___x_564_ = lean_box(v_updateHeader_556_);
v___f_565_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_565_, 0, v___x_563_);
lean_closure_set(v___f_565_, 1, v_e_554_);
lean_closure_set(v___f_565_, 2, v_____do__lift_562_);
lean_closure_set(v___f_565_, 3, v_i_555_);
lean_closure_set(v___f_565_, 4, v___x_564_);
lean_closure_set(v___f_565_, 5, v_toPure_557_);
v_sz_566_ = lean_array_size(v_args_558_);
v___x_567_ = ((size_t)0ULL);
v___x_568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_559_, v___f_560_, v_sz_566_, v___x_567_, v_args_558_);
v___x_569_ = lean_apply_4(v_toBind_561_, lean_box(0), lean_box(0), v___x_568_, v___f_565_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed(lean_object* v_pu_570_, lean_object* v_e_571_, lean_object* v_i_572_, lean_object* v_updateHeader_573_, lean_object* v_toPure_574_, lean_object* v_args_575_, lean_object* v_inst_576_, lean_object* v___f_577_, lean_object* v_toBind_578_, lean_object* v_____do__lift_579_){
_start:
{
uint8_t v_pu_boxed_580_; uint8_t v_updateHeader_642__boxed_581_; lean_object* v_res_582_; 
v_pu_boxed_580_ = lean_unbox(v_pu_570_);
v_updateHeader_642__boxed_581_ = lean_unbox(v_updateHeader_573_);
v_res_582_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(v_pu_boxed_580_, v_e_571_, v_i_572_, v_updateHeader_642__boxed_581_, v_toPure_574_, v_args_575_, v_inst_576_, v___f_577_, v_toBind_578_, v_____do__lift_579_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6(uint8_t v_pu_583_, lean_object* v_e_584_, lean_object* v_ty_585_, lean_object* v_toPure_586_, lean_object* v_____do__lift_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_583_, v_e_584_, v_ty_585_, v_____do__lift_587_);
v___x_589_ = lean_apply_2(v_toPure_586_, lean_box(0), v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6___boxed(lean_object* v_pu_590_, lean_object* v_e_591_, lean_object* v_ty_592_, lean_object* v_toPure_593_, lean_object* v_____do__lift_594_){
_start:
{
uint8_t v_pu_boxed_595_; lean_object* v_res_596_; 
v_pu_boxed_595_ = lean_unbox(v_pu_590_);
v_res_596_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6(v_pu_boxed_595_, v_e_591_, v_ty_592_, v_toPure_593_, v_____do__lift_594_);
lean_dec(v_e_591_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9(uint8_t v_pu_597_, lean_object* v_e_598_, lean_object* v_toPure_599_, lean_object* v_____do__lift_600_){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_597_, v_e_598_, v_____do__lift_600_);
v___x_602_ = lean_apply_2(v_toPure_599_, lean_box(0), v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9___boxed(lean_object* v_pu_603_, lean_object* v_e_604_, lean_object* v_toPure_605_, lean_object* v_____do__lift_606_){
_start:
{
uint8_t v_pu_boxed_607_; lean_object* v_res_608_; 
v_pu_boxed_607_ = lean_unbox(v_pu_603_);
v_res_608_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9(v_pu_boxed_607_, v_e_604_, v_toPure_605_, v_____do__lift_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10(uint8_t v_pu_609_, lean_object* v_e_610_, lean_object* v_toPure_611_, lean_object* v_____do__lift_612_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_609_, v_e_610_, v_____do__lift_612_);
v___x_614_ = lean_apply_2(v_toPure_611_, lean_box(0), v___x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10___boxed(lean_object* v_pu_615_, lean_object* v_e_616_, lean_object* v_toPure_617_, lean_object* v_____do__lift_618_){
_start:
{
uint8_t v_pu_boxed_619_; lean_object* v_res_620_; 
v_pu_boxed_619_ = lean_unbox(v_pu_615_);
v_res_620_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10(v_pu_boxed_619_, v_e_616_, v_toPure_617_, v_____do__lift_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(uint8_t v_pu_621_, lean_object* v_inst_622_, lean_object* v_f_623_, lean_object* v_e_624_){
_start:
{
lean_object* v_toApplicative_625_; lean_object* v_toBind_626_; lean_object* v_toPure_627_; lean_object* v___x_628_; lean_object* v___f_629_; lean_object* v___x_630_; lean_object* v___f_631_; lean_object* v_args_633_; lean_object* v___x_638_; lean_object* v___f_639_; lean_object* v_fvarId_641_; 
v_toApplicative_625_ = lean_ctor_get(v_inst_622_, 0);
v_toBind_626_ = lean_ctor_get(v_inst_622_, 1);
lean_inc(v_toBind_626_);
v_toPure_627_ = lean_ctor_get(v_toApplicative_625_, 1);
v___x_628_ = lean_box(v_pu_621_);
lean_inc(v_f_623_);
lean_inc_ref(v_inst_622_);
v___f_629_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_629_, 0, v___x_628_);
lean_closure_set(v___f_629_, 1, v_inst_622_);
lean_closure_set(v___f_629_, 2, v_f_623_);
v___x_630_ = lean_box(v_pu_621_);
lean_inc_n(v_toPure_627_, 2);
lean_inc_n(v_e_624_, 2);
v___f_631_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_631_, 0, v___x_630_);
lean_closure_set(v___f_631_, 1, v_e_624_);
lean_closure_set(v___f_631_, 2, v_toPure_627_);
v___x_638_ = lean_box(v_pu_621_);
v___f_639_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_639_, 0, v___x_638_);
lean_closure_set(v___f_639_, 1, v_e_624_);
lean_closure_set(v___f_639_, 2, v_toPure_627_);
switch(lean_obj_tag(v_e_624_))
{
case 2:
{
lean_object* v_struct_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec_ref(v___f_631_);
lean_dec_ref(v___f_629_);
lean_dec_ref(v_inst_622_);
v_struct_644_ = lean_ctor_get(v_e_624_, 2);
lean_inc(v_struct_644_);
lean_dec_ref_known(v_e_624_, 3);
v___x_645_ = lean_apply_1(v_f_623_, v_struct_644_);
v___x_646_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_645_, v___f_639_);
return v___x_646_;
}
case 3:
{
lean_object* v_args_647_; size_t v_sz_648_; size_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
lean_dec_ref(v___f_639_);
lean_dec(v_f_623_);
v_args_647_ = lean_ctor_get(v_e_624_, 2);
lean_inc_ref(v_args_647_);
lean_dec_ref_known(v_e_624_, 3);
v_sz_648_ = lean_array_size(v_args_647_);
v___x_649_ = ((size_t)0ULL);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_622_, v___f_629_, v_sz_648_, v___x_649_, v_args_647_);
v___x_651_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_650_, v___f_631_);
return v___x_651_;
}
case 4:
{
lean_object* v_fvarId_652_; lean_object* v_args_653_; lean_object* v___x_654_; lean_object* v___f_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
lean_inc(v_toPure_627_);
lean_dec_ref(v___f_639_);
lean_dec_ref(v___f_631_);
v_fvarId_652_ = lean_ctor_get(v_e_624_, 0);
lean_inc(v_fvarId_652_);
v_args_653_ = lean_ctor_get(v_e_624_, 1);
lean_inc_ref(v_args_653_);
v___x_654_ = lean_box(v_pu_621_);
lean_inc(v_toBind_626_);
v___f_655_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_655_, 0, v___x_654_);
lean_closure_set(v___f_655_, 1, v_e_624_);
lean_closure_set(v___f_655_, 2, v_toPure_627_);
lean_closure_set(v___f_655_, 3, v_args_653_);
lean_closure_set(v___f_655_, 4, v_inst_622_);
lean_closure_set(v___f_655_, 5, v___f_629_);
lean_closure_set(v___f_655_, 6, v_toBind_626_);
v___x_656_ = lean_apply_1(v_f_623_, v_fvarId_652_);
v___x_657_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_656_, v___f_655_);
return v___x_657_;
}
case 5:
{
lean_object* v_args_658_; size_t v_sz_659_; size_t v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec_ref(v___f_639_);
lean_dec(v_f_623_);
v_args_658_ = lean_ctor_get(v_e_624_, 1);
lean_inc_ref(v_args_658_);
lean_dec_ref_known(v_e_624_, 2);
v_sz_659_ = lean_array_size(v_args_658_);
v___x_660_ = ((size_t)0ULL);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_622_, v___f_629_, v_sz_659_, v___x_660_, v_args_658_);
v___x_662_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_661_, v___f_631_);
return v___x_662_;
}
case 6:
{
lean_object* v_var_663_; 
lean_dec_ref(v___f_631_);
lean_dec_ref(v___f_629_);
lean_dec_ref(v_inst_622_);
v_var_663_ = lean_ctor_get(v_e_624_, 1);
lean_inc(v_var_663_);
lean_dec_ref_known(v_e_624_, 2);
v_fvarId_641_ = v_var_663_;
goto v___jp_640_;
}
case 7:
{
lean_object* v_var_664_; 
lean_dec_ref(v___f_631_);
lean_dec_ref(v___f_629_);
lean_dec_ref(v_inst_622_);
v_var_664_ = lean_ctor_get(v_e_624_, 1);
lean_inc(v_var_664_);
lean_dec_ref_known(v_e_624_, 2);
v_fvarId_641_ = v_var_664_;
goto v___jp_640_;
}
case 8:
{
lean_object* v_var_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec_ref(v___f_631_);
lean_dec_ref(v___f_629_);
lean_dec_ref(v_inst_622_);
v_var_665_ = lean_ctor_get(v_e_624_, 2);
lean_inc(v_var_665_);
lean_dec_ref_known(v_e_624_, 3);
v___x_666_ = lean_apply_1(v_f_623_, v_var_665_);
v___x_667_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_666_, v___f_639_);
return v___x_667_;
}
case 9:
{
lean_object* v_args_668_; 
lean_dec_ref(v___f_639_);
lean_dec(v_f_623_);
v_args_668_ = lean_ctor_get(v_e_624_, 1);
lean_inc_ref(v_args_668_);
lean_dec_ref_known(v_e_624_, 2);
v_args_633_ = v_args_668_;
goto v___jp_632_;
}
case 10:
{
lean_object* v_args_669_; 
lean_dec_ref(v___f_639_);
lean_dec(v_f_623_);
v_args_669_ = lean_ctor_get(v_e_624_, 1);
lean_inc_ref(v_args_669_);
lean_dec_ref_known(v_e_624_, 2);
v_args_633_ = v_args_669_;
goto v___jp_632_;
}
case 11:
{
lean_object* v_n_670_; lean_object* v_var_671_; lean_object* v___x_672_; lean_object* v___f_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
lean_inc(v_toPure_627_);
lean_dec_ref(v___f_639_);
lean_dec_ref(v___f_631_);
lean_dec_ref(v___f_629_);
lean_dec_ref(v_inst_622_);
v_n_670_ = lean_ctor_get(v_e_624_, 0);
lean_inc(v_n_670_);
v_var_671_ = lean_ctor_get(v_e_624_, 1);
lean_inc(v_var_671_);
v___x_672_ = lean_box(v_pu_621_);
v___f_673_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_673_, 0, v___x_672_);
lean_closure_set(v___f_673_, 1, v_e_624_);
lean_closure_set(v___f_673_, 2, v_n_670_);
lean_closure_set(v___f_673_, 3, v_toPure_627_);
v___x_674_ = lean_apply_1(v_f_623_, v_var_671_);
v___x_675_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_674_, v___f_673_);
return v___x_675_;
}
case 12:
{
lean_object* v_var_676_; lean_object* v_i_677_; uint8_t v_updateHeader_678_; lean_object* v_args_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___f_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
lean_inc(v_toPure_627_);
lean_dec_ref(v___f_639_);
lean_dec_ref(v___f_631_);
v_var_676_ = lean_ctor_get(v_e_624_, 0);
lean_inc(v_var_676_);
v_i_677_ = lean_ctor_get(v_e_624_, 1);
lean_inc_ref(v_i_677_);
v_updateHeader_678_ = lean_ctor_get_uint8(v_e_624_, sizeof(void*)*3);
v_args_679_ = lean_ctor_get(v_e_624_, 2);
lean_inc_ref(v_args_679_);
v___x_680_ = lean_box(v_pu_621_);
v___x_681_ = lean_box(v_updateHeader_678_);
lean_inc(v_toBind_626_);
v___f_682_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_682_, 0, v___x_680_);
lean_closure_set(v___f_682_, 1, v_e_624_);
lean_closure_set(v___f_682_, 2, v_i_677_);
lean_closure_set(v___f_682_, 3, v___x_681_);
lean_closure_set(v___f_682_, 4, v_toPure_627_);
lean_closure_set(v___f_682_, 5, v_args_679_);
lean_closure_set(v___f_682_, 6, v_inst_622_);
lean_closure_set(v___f_682_, 7, v___f_629_);
lean_closure_set(v___f_682_, 8, v_toBind_626_);
v___x_683_ = lean_apply_1(v_f_623_, v_var_676_);
v___x_684_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_683_, v___f_682_);
return v___x_684_;
}
case 13:
{
lean_object* v_ty_685_; lean_object* v_fvarId_686_; lean_object* v___x_687_; lean_object* v___f_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
lean_inc(v_toPure_627_);
lean_dec_ref(v___f_639_);
lean_dec_ref(v___f_631_);
lean_dec_ref(v___f_629_);
lean_dec_ref(v_inst_622_);
v_ty_685_ = lean_ctor_get(v_e_624_, 0);
lean_inc_ref(v_ty_685_);
v_fvarId_686_ = lean_ctor_get(v_e_624_, 1);
lean_inc(v_fvarId_686_);
v___x_687_ = lean_box(v_pu_621_);
v___f_688_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6___boxed), 5, 4);
lean_closure_set(v___f_688_, 0, v___x_687_);
lean_closure_set(v___f_688_, 1, v_e_624_);
lean_closure_set(v___f_688_, 2, v_ty_685_);
lean_closure_set(v___f_688_, 3, v_toPure_627_);
v___x_689_ = lean_apply_1(v_f_623_, v_fvarId_686_);
v___x_690_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_689_, v___f_688_);
return v___x_690_;
}
case 14:
{
lean_object* v_fvarId_691_; lean_object* v___x_692_; lean_object* v___f_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
lean_inc(v_toPure_627_);
lean_dec_ref(v___f_639_);
lean_dec_ref(v___f_631_);
lean_dec_ref(v___f_629_);
lean_dec_ref(v_inst_622_);
v_fvarId_691_ = lean_ctor_get(v_e_624_, 0);
lean_inc(v_fvarId_691_);
v___x_692_ = lean_box(v_pu_621_);
v___f_693_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9___boxed), 4, 3);
lean_closure_set(v___f_693_, 0, v___x_692_);
lean_closure_set(v___f_693_, 1, v_e_624_);
lean_closure_set(v___f_693_, 2, v_toPure_627_);
v___x_694_ = lean_apply_1(v_f_623_, v_fvarId_691_);
v___x_695_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_694_, v___f_693_);
return v___x_695_;
}
case 15:
{
lean_object* v_fvarId_696_; lean_object* v___x_697_; lean_object* v___f_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
lean_inc(v_toPure_627_);
lean_dec_ref(v___f_639_);
lean_dec_ref(v___f_631_);
lean_dec_ref(v___f_629_);
lean_dec_ref(v_inst_622_);
v_fvarId_696_ = lean_ctor_get(v_e_624_, 0);
lean_inc(v_fvarId_696_);
v___x_697_ = lean_box(v_pu_621_);
v___f_698_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10___boxed), 4, 3);
lean_closure_set(v___f_698_, 0, v___x_697_);
lean_closure_set(v___f_698_, 1, v_e_624_);
lean_closure_set(v___f_698_, 2, v_toPure_627_);
v___x_699_ = lean_apply_1(v_f_623_, v_fvarId_696_);
v___x_700_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_699_, v___f_698_);
return v___x_700_;
}
default: 
{
lean_object* v___x_701_; 
lean_inc(v_toPure_627_);
lean_dec_ref(v___f_639_);
lean_dec_ref(v___f_631_);
lean_dec_ref(v___f_629_);
lean_dec(v_toBind_626_);
lean_dec(v_f_623_);
lean_dec_ref(v_inst_622_);
v___x_701_ = lean_apply_2(v_toPure_627_, lean_box(0), v_e_624_);
return v___x_701_;
}
}
v___jp_632_:
{
size_t v_sz_634_; size_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_sz_634_ = lean_array_size(v_args_633_);
v___x_635_ = ((size_t)0ULL);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_622_, v___f_629_, v_sz_634_, v___x_635_, v_args_633_);
v___x_637_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_636_, v___f_631_);
return v___x_637_;
}
v___jp_640_:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_apply_1(v_f_623_, v_fvarId_641_);
v___x_643_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_642_, v___f_639_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___boxed(lean_object* v_pu_702_, lean_object* v_inst_703_, lean_object* v_f_704_, lean_object* v_e_705_){
_start:
{
uint8_t v_pu_boxed_706_; lean_object* v_res_707_; 
v_pu_boxed_706_ = lean_unbox(v_pu_702_);
v_res_707_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_boxed_706_, v_inst_703_, v_f_704_, v_e_705_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM(lean_object* v_m_708_, uint8_t v_pu_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_f_712_, lean_object* v_e_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_709_, v_inst_711_, v_f_712_, v_e_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___boxed(lean_object* v_m_715_, lean_object* v_pu_716_, lean_object* v_inst_717_, lean_object* v_inst_718_, lean_object* v_f_719_, lean_object* v_e_720_){
_start:
{
uint8_t v_pu_boxed_721_; lean_object* v_res_722_; 
v_pu_boxed_721_ = lean_unbox(v_pu_716_);
v_res_722_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM(v_m_715_, v_pu_boxed_721_, v_inst_717_, v_inst_718_, v_f_719_, v_e_720_);
lean_dec(v_inst_717_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0(lean_object* v_inst_723_, lean_object* v_f_724_, lean_object* v_x_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_723_, v_f_724_, v___y_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3(lean_object* v_args_728_, lean_object* v_toPure_729_, lean_object* v_inst_730_, lean_object* v___f_731_, lean_object* v_____r_732_){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = lean_array_get_size(v_args_728_);
v___x_735_ = lean_box(0);
v___x_736_ = lean_nat_dec_lt(v___x_733_, v___x_734_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
lean_dec(v___f_731_);
lean_dec_ref(v_inst_730_);
lean_dec_ref(v_args_728_);
v___x_737_ = lean_apply_2(v_toPure_729_, lean_box(0), v___x_735_);
return v___x_737_;
}
else
{
uint8_t v___x_738_; 
v___x_738_ = lean_nat_dec_le(v___x_734_, v___x_734_);
if (v___x_738_ == 0)
{
if (v___x_736_ == 0)
{
lean_object* v___x_739_; 
lean_dec(v___f_731_);
lean_dec_ref(v_inst_730_);
lean_dec_ref(v_args_728_);
v___x_739_ = lean_apply_2(v_toPure_729_, lean_box(0), v___x_735_);
return v___x_739_;
}
else
{
size_t v___x_740_; size_t v___x_741_; lean_object* v___x_742_; 
lean_dec(v_toPure_729_);
v___x_740_ = ((size_t)0ULL);
v___x_741_ = lean_usize_of_nat(v___x_734_);
v___x_742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_730_, v___f_731_, v_args_728_, v___x_740_, v___x_741_, v___x_735_);
return v___x_742_;
}
}
else
{
size_t v___x_743_; size_t v___x_744_; lean_object* v___x_745_; 
lean_dec(v_toPure_729_);
v___x_743_ = ((size_t)0ULL);
v___x_744_ = lean_usize_of_nat(v___x_734_);
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_730_, v___f_731_, v_args_728_, v___x_743_, v___x_744_, v___x_735_);
return v___x_745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(lean_object* v_inst_746_, lean_object* v_f_747_, lean_object* v_e_748_){
_start:
{
lean_object* v_toApplicative_749_; lean_object* v_toBind_750_; lean_object* v_toPure_751_; lean_object* v___f_752_; lean_object* v_args_754_; 
v_toApplicative_749_ = lean_ctor_get(v_inst_746_, 0);
v_toBind_750_ = lean_ctor_get(v_inst_746_, 1);
v_toPure_751_ = lean_ctor_get(v_toApplicative_749_, 1);
lean_inc(v_f_747_);
lean_inc_ref(v_inst_746_);
v___f_752_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_752_, 0, v_inst_746_);
lean_closure_set(v___f_752_, 1, v_f_747_);
switch(lean_obj_tag(v_e_748_))
{
case 2:
{
lean_object* v_struct_768_; lean_object* v___x_769_; 
lean_dec_ref(v___f_752_);
lean_dec_ref(v_inst_746_);
v_struct_768_ = lean_ctor_get(v_e_748_, 2);
lean_inc(v_struct_768_);
lean_dec_ref_known(v_e_748_, 3);
v___x_769_ = lean_apply_1(v_f_747_, v_struct_768_);
return v___x_769_;
}
case 3:
{
lean_object* v_args_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
lean_dec(v_f_747_);
v_args_770_ = lean_ctor_get(v_e_748_, 2);
lean_inc_ref(v_args_770_);
lean_dec_ref_known(v_e_748_, 3);
v___x_771_ = lean_unsigned_to_nat(0u);
v___x_772_ = lean_array_get_size(v_args_770_);
v___x_773_ = lean_box(0);
v___x_774_ = lean_nat_dec_lt(v___x_771_, v___x_772_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
lean_inc(v_toPure_751_);
lean_dec_ref(v_args_770_);
lean_dec_ref(v___f_752_);
lean_dec_ref(v_inst_746_);
v___x_775_ = lean_apply_2(v_toPure_751_, lean_box(0), v___x_773_);
return v___x_775_;
}
else
{
uint8_t v___x_776_; 
v___x_776_ = lean_nat_dec_le(v___x_772_, v___x_772_);
if (v___x_776_ == 0)
{
if (v___x_774_ == 0)
{
lean_object* v___x_777_; 
lean_inc(v_toPure_751_);
lean_dec_ref(v_args_770_);
lean_dec_ref(v___f_752_);
lean_dec_ref(v_inst_746_);
v___x_777_ = lean_apply_2(v_toPure_751_, lean_box(0), v___x_773_);
return v___x_777_;
}
else
{
size_t v___x_778_; size_t v___x_779_; lean_object* v___x_780_; 
v___x_778_ = ((size_t)0ULL);
v___x_779_ = lean_usize_of_nat(v___x_772_);
v___x_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_746_, v___f_752_, v_args_770_, v___x_778_, v___x_779_, v___x_773_);
return v___x_780_;
}
}
else
{
size_t v___x_781_; size_t v___x_782_; lean_object* v___x_783_; 
v___x_781_ = ((size_t)0ULL);
v___x_782_ = lean_usize_of_nat(v___x_772_);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_746_, v___f_752_, v_args_770_, v___x_781_, v___x_782_, v___x_773_);
return v___x_783_;
}
}
}
case 4:
{
lean_object* v_fvarId_784_; lean_object* v_args_785_; lean_object* v___f_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_inc(v_toPure_751_);
lean_inc(v_toBind_750_);
v_fvarId_784_ = lean_ctor_get(v_e_748_, 0);
lean_inc(v_fvarId_784_);
v_args_785_ = lean_ctor_get(v_e_748_, 1);
lean_inc_ref(v_args_785_);
lean_dec_ref_known(v_e_748_, 2);
v___f_786_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3), 5, 4);
lean_closure_set(v___f_786_, 0, v_args_785_);
lean_closure_set(v___f_786_, 1, v_toPure_751_);
lean_closure_set(v___f_786_, 2, v_inst_746_);
lean_closure_set(v___f_786_, 3, v___f_752_);
v___x_787_ = lean_apply_1(v_f_747_, v_fvarId_784_);
v___x_788_ = lean_apply_4(v_toBind_750_, lean_box(0), lean_box(0), v___x_787_, v___f_786_);
return v___x_788_;
}
case 5:
{
lean_object* v_args_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
lean_dec(v_f_747_);
v_args_789_ = lean_ctor_get(v_e_748_, 1);
lean_inc_ref(v_args_789_);
lean_dec_ref_known(v_e_748_, 2);
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = lean_array_get_size(v_args_789_);
v___x_792_ = lean_box(0);
v___x_793_ = lean_nat_dec_lt(v___x_790_, v___x_791_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
lean_inc(v_toPure_751_);
lean_dec_ref(v_args_789_);
lean_dec_ref(v___f_752_);
lean_dec_ref(v_inst_746_);
v___x_794_ = lean_apply_2(v_toPure_751_, lean_box(0), v___x_792_);
return v___x_794_;
}
else
{
uint8_t v___x_795_; 
v___x_795_ = lean_nat_dec_le(v___x_791_, v___x_791_);
if (v___x_795_ == 0)
{
if (v___x_793_ == 0)
{
lean_object* v___x_796_; 
lean_inc(v_toPure_751_);
lean_dec_ref(v_args_789_);
lean_dec_ref(v___f_752_);
lean_dec_ref(v_inst_746_);
v___x_796_ = lean_apply_2(v_toPure_751_, lean_box(0), v___x_792_);
return v___x_796_;
}
else
{
size_t v___x_797_; size_t v___x_798_; lean_object* v___x_799_; 
v___x_797_ = ((size_t)0ULL);
v___x_798_ = lean_usize_of_nat(v___x_791_);
v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_746_, v___f_752_, v_args_789_, v___x_797_, v___x_798_, v___x_792_);
return v___x_799_;
}
}
else
{
size_t v___x_800_; size_t v___x_801_; lean_object* v___x_802_; 
v___x_800_ = ((size_t)0ULL);
v___x_801_ = lean_usize_of_nat(v___x_791_);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_746_, v___f_752_, v_args_789_, v___x_800_, v___x_801_, v___x_792_);
return v___x_802_;
}
}
}
case 6:
{
lean_object* v_var_803_; lean_object* v___x_804_; 
lean_dec_ref(v___f_752_);
lean_dec_ref(v_inst_746_);
v_var_803_ = lean_ctor_get(v_e_748_, 1);
lean_inc(v_var_803_);
lean_dec_ref_known(v_e_748_, 2);
v___x_804_ = lean_apply_1(v_f_747_, v_var_803_);
return v___x_804_;
}
case 7:
{
lean_object* v_var_805_; lean_object* v___x_806_; 
lean_dec_ref(v___f_752_);
lean_dec_ref(v_inst_746_);
v_var_805_ = lean_ctor_get(v_e_748_, 1);
lean_inc(v_var_805_);
lean_dec_ref_known(v_e_748_, 2);
v___x_806_ = lean_apply_1(v_f_747_, v_var_805_);
return v___x_806_;
}
case 8:
{
lean_object* v_var_807_; lean_object* v___x_808_; 
lean_dec_ref(v___f_752_);
lean_dec_ref(v_inst_746_);
v_var_807_ = lean_ctor_get(v_e_748_, 2);
lean_inc(v_var_807_);
lean_dec_ref_known(v_e_748_, 3);
v___x_808_ = lean_apply_1(v_f_747_, v_var_807_);
return v___x_808_;
}
case 9:
{
lean_object* v_args_809_; 
lean_dec(v_f_747_);
v_args_809_ = lean_ctor_get(v_e_748_, 1);
lean_inc_ref(v_args_809_);
lean_dec_ref_known(v_e_748_, 2);
v_args_754_ = v_args_809_;
goto v___jp_753_;
}
case 10:
{
lean_object* v_args_810_; 
lean_dec(v_f_747_);
v_args_810_ = lean_ctor_get(v_e_748_, 1);
lean_inc_ref(v_args_810_);
lean_dec_ref_known(v_e_748_, 2);
v_args_754_ = v_args_810_;
goto v___jp_753_;
}
case 11:
{
lean_object* v_var_811_; lean_object* v___x_812_; 
lean_dec_ref(v___f_752_);
lean_dec_ref(v_inst_746_);
v_var_811_ = lean_ctor_get(v_e_748_, 1);
lean_inc(v_var_811_);
lean_dec_ref_known(v_e_748_, 2);
v___x_812_ = lean_apply_1(v_f_747_, v_var_811_);
return v___x_812_;
}
case 12:
{
lean_object* v_var_813_; lean_object* v_args_814_; lean_object* v___f_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_inc(v_toPure_751_);
lean_inc(v_toBind_750_);
v_var_813_ = lean_ctor_get(v_e_748_, 0);
lean_inc(v_var_813_);
v_args_814_ = lean_ctor_get(v_e_748_, 2);
lean_inc_ref(v_args_814_);
lean_dec_ref_known(v_e_748_, 3);
v___f_815_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3), 5, 4);
lean_closure_set(v___f_815_, 0, v_args_814_);
lean_closure_set(v___f_815_, 1, v_toPure_751_);
lean_closure_set(v___f_815_, 2, v_inst_746_);
lean_closure_set(v___f_815_, 3, v___f_752_);
v___x_816_ = lean_apply_1(v_f_747_, v_var_813_);
v___x_817_ = lean_apply_4(v_toBind_750_, lean_box(0), lean_box(0), v___x_816_, v___f_815_);
return v___x_817_;
}
case 13:
{
lean_object* v_fvarId_818_; lean_object* v___x_819_; 
lean_dec_ref(v___f_752_);
lean_dec_ref(v_inst_746_);
v_fvarId_818_ = lean_ctor_get(v_e_748_, 1);
lean_inc(v_fvarId_818_);
lean_dec_ref_known(v_e_748_, 2);
v___x_819_ = lean_apply_1(v_f_747_, v_fvarId_818_);
return v___x_819_;
}
case 14:
{
lean_object* v_fvarId_820_; lean_object* v___x_821_; 
lean_dec_ref(v___f_752_);
lean_dec_ref(v_inst_746_);
v_fvarId_820_ = lean_ctor_get(v_e_748_, 0);
lean_inc(v_fvarId_820_);
lean_dec_ref_known(v_e_748_, 1);
v___x_821_ = lean_apply_1(v_f_747_, v_fvarId_820_);
return v___x_821_;
}
case 15:
{
lean_object* v_fvarId_822_; lean_object* v___x_823_; 
lean_dec_ref(v___f_752_);
lean_dec_ref(v_inst_746_);
v_fvarId_822_ = lean_ctor_get(v_e_748_, 0);
lean_inc(v_fvarId_822_);
lean_dec_ref_known(v_e_748_, 1);
v___x_823_ = lean_apply_1(v_f_747_, v_fvarId_822_);
return v___x_823_;
}
default: 
{
lean_object* v___x_824_; lean_object* v___x_825_; 
lean_inc(v_toPure_751_);
lean_dec_ref(v___f_752_);
lean_dec(v_e_748_);
lean_dec(v_f_747_);
lean_dec_ref(v_inst_746_);
v___x_824_ = lean_box(0);
v___x_825_ = lean_apply_2(v_toPure_751_, lean_box(0), v___x_824_);
return v___x_825_;
}
}
v___jp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_array_get_size(v_args_754_);
v___x_757_ = lean_box(0);
v___x_758_ = lean_nat_dec_lt(v___x_755_, v___x_756_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; 
lean_inc(v_toPure_751_);
lean_dec_ref(v_args_754_);
lean_dec_ref(v___f_752_);
lean_dec_ref(v_inst_746_);
v___x_759_ = lean_apply_2(v_toPure_751_, lean_box(0), v___x_757_);
return v___x_759_;
}
else
{
uint8_t v___x_760_; 
v___x_760_ = lean_nat_dec_le(v___x_756_, v___x_756_);
if (v___x_760_ == 0)
{
if (v___x_758_ == 0)
{
lean_object* v___x_761_; 
lean_inc(v_toPure_751_);
lean_dec_ref(v_args_754_);
lean_dec_ref(v___f_752_);
lean_dec_ref(v_inst_746_);
v___x_761_ = lean_apply_2(v_toPure_751_, lean_box(0), v___x_757_);
return v___x_761_;
}
else
{
size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; 
v___x_762_ = ((size_t)0ULL);
v___x_763_ = lean_usize_of_nat(v___x_756_);
v___x_764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_746_, v___f_752_, v_args_754_, v___x_762_, v___x_763_, v___x_757_);
return v___x_764_;
}
}
else
{
size_t v___x_765_; size_t v___x_766_; lean_object* v___x_767_; 
v___x_765_ = ((size_t)0ULL);
v___x_766_ = lean_usize_of_nat(v___x_756_);
v___x_767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_746_, v___f_752_, v_args_754_, v___x_765_, v___x_766_, v___x_757_);
return v___x_767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM(lean_object* v_m_826_, uint8_t v_pu_827_, lean_object* v_inst_828_, lean_object* v_f_829_, lean_object* v_e_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_828_, v_f_829_, v_e_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___boxed(lean_object* v_m_832_, lean_object* v_pu_833_, lean_object* v_inst_834_, lean_object* v_f_835_, lean_object* v_e_836_){
_start:
{
uint8_t v_pu_boxed_837_; lean_object* v_res_838_; 
v_pu_boxed_837_ = lean_unbox(v_pu_833_);
v_res_838_ = l_Lean_Compiler_LCNF_LetValue_forFVarM(v_m_832_, v_pu_boxed_837_, v_inst_834_, v_f_835_, v_e_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(uint8_t v_pu_839_, lean_object* v_m_840_, lean_object* v_inst_841_, lean_object* v_inst_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_839_, v_inst_842_, v___y_843_, v___y_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0___boxed(lean_object* v_pu_846_, lean_object* v_m_847_, lean_object* v_inst_848_, lean_object* v_inst_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
uint8_t v_pu_boxed_852_; lean_object* v_res_853_; 
v_pu_boxed_852_ = lean_unbox(v_pu_846_);
v_res_853_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(v_pu_boxed_852_, v_m_847_, v_inst_848_, v_inst_849_, v___y_850_, v___y_851_);
lean_dec(v_inst_848_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__1(lean_object* v_m_854_, lean_object* v_inst_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_855_, v___y_856_, v___y_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue(uint8_t v_pu_860_){
_start:
{
lean_object* v___x_861_; lean_object* v___f_862_; lean_object* v___f_863_; lean_object* v___x_864_; 
v___x_861_ = lean_box(v_pu_860_);
v___f_862_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0___boxed), 6, 1);
lean_closure_set(v___f_862_, 0, v___x_861_);
v___f_863_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarLetValue___closed__0));
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v___f_862_);
lean_ctor_set(v___x_864_, 1, v___f_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___boxed(lean_object* v_pu_865_){
_start:
{
uint8_t v_pu_boxed_866_; lean_object* v_res_867_; 
v_pu_boxed_866_ = lean_unbox(v_pu_865_);
v_res_867_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue(v_pu_boxed_866_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(uint8_t v_pu_868_, lean_object* v_decl_869_, lean_object* v_____do__lift_870_, lean_object* v_inst_871_, lean_object* v_____do__lift_872_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_873_ = lean_box(v_pu_868_);
v___x_874_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_874_, 0, v___x_873_);
lean_closure_set(v___x_874_, 1, v_decl_869_);
lean_closure_set(v___x_874_, 2, v_____do__lift_870_);
lean_closure_set(v___x_874_, 3, v_____do__lift_872_);
v___x_875_ = lean_apply_2(v_inst_871_, lean_box(0), v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_876_, lean_object* v_decl_877_, lean_object* v_____do__lift_878_, lean_object* v_inst_879_, lean_object* v_____do__lift_880_){
_start:
{
uint8_t v_pu_boxed_881_; lean_object* v_res_882_; 
v_pu_boxed_881_ = lean_unbox(v_pu_876_);
v_res_882_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(v_pu_boxed_881_, v_decl_877_, v_____do__lift_878_, v_inst_879_, v_____do__lift_880_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(uint8_t v_pu_883_, lean_object* v_decl_884_, lean_object* v_inst_885_, lean_object* v_inst_886_, lean_object* v_f_887_, lean_object* v_value_888_, lean_object* v_toBind_889_, lean_object* v_____do__lift_890_){
_start:
{
lean_object* v___x_891_; lean_object* v___f_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_891_ = lean_box(v_pu_883_);
v___f_892_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_892_, 0, v___x_891_);
lean_closure_set(v___f_892_, 1, v_decl_884_);
lean_closure_set(v___f_892_, 2, v_____do__lift_890_);
lean_closure_set(v___f_892_, 3, v_inst_885_);
v___x_893_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_883_, v_inst_886_, v_f_887_, v_value_888_);
v___x_894_ = lean_apply_4(v_toBind_889_, lean_box(0), lean_box(0), v___x_893_, v___f_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1___boxed(lean_object* v_pu_895_, lean_object* v_decl_896_, lean_object* v_inst_897_, lean_object* v_inst_898_, lean_object* v_f_899_, lean_object* v_value_900_, lean_object* v_toBind_901_, lean_object* v_____do__lift_902_){
_start:
{
uint8_t v_pu_boxed_903_; lean_object* v_res_904_; 
v_pu_boxed_903_ = lean_unbox(v_pu_895_);
v_res_904_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(v_pu_boxed_903_, v_decl_896_, v_inst_897_, v_inst_898_, v_f_899_, v_value_900_, v_toBind_901_, v_____do__lift_902_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(uint8_t v_pu_905_, lean_object* v_inst_906_, lean_object* v_inst_907_, lean_object* v_f_908_, lean_object* v_decl_909_){
_start:
{
lean_object* v_toBind_910_; lean_object* v_type_911_; lean_object* v_value_912_; lean_object* v___x_913_; lean_object* v___f_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v_toBind_910_ = lean_ctor_get(v_inst_907_, 1);
lean_inc_n(v_toBind_910_, 2);
v_type_911_ = lean_ctor_get(v_decl_909_, 2);
lean_inc_ref(v_type_911_);
v_value_912_ = lean_ctor_get(v_decl_909_, 3);
lean_inc(v_value_912_);
v___x_913_ = lean_box(v_pu_905_);
lean_inc(v_f_908_);
lean_inc_ref(v_inst_907_);
v___f_914_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_914_, 0, v___x_913_);
lean_closure_set(v___f_914_, 1, v_decl_909_);
lean_closure_set(v___f_914_, 2, v_inst_906_);
lean_closure_set(v___f_914_, 3, v_inst_907_);
lean_closure_set(v___f_914_, 4, v_f_908_);
lean_closure_set(v___f_914_, 5, v_value_912_);
lean_closure_set(v___f_914_, 6, v_toBind_910_);
v___x_915_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_907_, v_f_908_, v_type_911_);
v___x_916_ = lean_apply_4(v_toBind_910_, lean_box(0), lean_box(0), v___x_915_, v___f_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___boxed(lean_object* v_pu_917_, lean_object* v_inst_918_, lean_object* v_inst_919_, lean_object* v_f_920_, lean_object* v_decl_921_){
_start:
{
uint8_t v_pu_boxed_922_; lean_object* v_res_923_; 
v_pu_boxed_922_ = lean_unbox(v_pu_917_);
v_res_923_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_boxed_922_, v_inst_918_, v_inst_919_, v_f_920_, v_decl_921_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM(lean_object* v_m_924_, uint8_t v_pu_925_, lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_f_928_, lean_object* v_decl_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_925_, v_inst_926_, v_inst_927_, v_f_928_, v_decl_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___boxed(lean_object* v_m_931_, lean_object* v_pu_932_, lean_object* v_inst_933_, lean_object* v_inst_934_, lean_object* v_f_935_, lean_object* v_decl_936_){
_start:
{
uint8_t v_pu_boxed_937_; lean_object* v_res_938_; 
v_pu_boxed_937_ = lean_unbox(v_pu_932_);
v_res_938_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM(v_m_931_, v_pu_boxed_937_, v_inst_933_, v_inst_934_, v_f_935_, v_decl_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg___lam__0(lean_object* v_inst_939_, lean_object* v_f_940_, lean_object* v_value_941_, lean_object* v_____r_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_939_, v_f_940_, v_value_941_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(lean_object* v_inst_944_, lean_object* v_f_945_, lean_object* v_decl_946_){
_start:
{
lean_object* v_toBind_947_; lean_object* v_type_948_; lean_object* v_value_949_; lean_object* v___f_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_toBind_947_ = lean_ctor_get(v_inst_944_, 1);
lean_inc(v_toBind_947_);
v_type_948_ = lean_ctor_get(v_decl_946_, 2);
lean_inc_ref(v_type_948_);
v_value_949_ = lean_ctor_get(v_decl_946_, 3);
lean_inc(v_value_949_);
lean_dec_ref(v_decl_946_);
lean_inc(v_f_945_);
lean_inc_ref(v_inst_944_);
v___f_950_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_950_, 0, v_inst_944_);
lean_closure_set(v___f_950_, 1, v_f_945_);
lean_closure_set(v___f_950_, 2, v_value_949_);
v___x_951_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_944_, v_f_945_, v_type_948_);
v___x_952_ = lean_apply_4(v_toBind_947_, lean_box(0), lean_box(0), v___x_951_, v___f_950_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM(lean_object* v_m_953_, uint8_t v_pu_954_, lean_object* v_inst_955_, lean_object* v_f_956_, lean_object* v_decl_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_955_, v_f_956_, v_decl_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___boxed(lean_object* v_m_959_, lean_object* v_pu_960_, lean_object* v_inst_961_, lean_object* v_f_962_, lean_object* v_decl_963_){
_start:
{
uint8_t v_pu_boxed_964_; lean_object* v_res_965_; 
v_pu_boxed_964_ = lean_unbox(v_pu_960_);
v_res_965_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM(v_m_959_, v_pu_boxed_964_, v_inst_961_, v_f_962_, v_decl_963_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(uint8_t v_pu_966_, lean_object* v_m_967_, lean_object* v_inst_968_, lean_object* v_inst_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_966_, v_inst_968_, v_inst_969_, v___y_970_, v___y_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0___boxed(lean_object* v_pu_973_, lean_object* v_m_974_, lean_object* v_inst_975_, lean_object* v_inst_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
uint8_t v_pu_boxed_979_; lean_object* v_res_980_; 
v_pu_boxed_979_ = lean_unbox(v_pu_973_);
v_res_980_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(v_pu_boxed_979_, v_m_974_, v_inst_975_, v_inst_976_, v___y_977_, v___y_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__1(lean_object* v_m_981_, lean_object* v_inst_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_982_, v___y_983_, v___y_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(uint8_t v_pu_987_){
_start:
{
lean_object* v___x_988_; lean_object* v___f_989_; lean_object* v___f_990_; lean_object* v___x_991_; 
v___x_988_ = lean_box(v_pu_987_);
v___f_989_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0___boxed), 6, 1);
lean_closure_set(v___f_989_, 0, v___x_988_);
v___f_990_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___closed__0));
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v___f_989_);
lean_ctor_set(v___x_991_, 1, v___f_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___boxed(lean_object* v_pu_992_){
_start:
{
uint8_t v_pu_boxed_993_; lean_object* v_res_994_; 
v_pu_boxed_993_ = lean_unbox(v_pu_992_);
v_res_994_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(v_pu_boxed_993_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(uint8_t v_pu_995_, lean_object* v_param_996_, lean_object* v_inst_997_, lean_object* v_____do__lift_998_){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = lean_box(v_pu_995_);
v___x_1000_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_1000_, 0, v___x_999_);
lean_closure_set(v___x_1000_, 1, v_param_996_);
lean_closure_set(v___x_1000_, 2, v_____do__lift_998_);
v___x_1001_ = lean_apply_2(v_inst_997_, lean_box(0), v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_1002_, lean_object* v_param_1003_, lean_object* v_inst_1004_, lean_object* v_____do__lift_1005_){
_start:
{
uint8_t v_pu_boxed_1006_; lean_object* v_res_1007_; 
v_pu_boxed_1006_ = lean_unbox(v_pu_1002_);
v_res_1007_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(v_pu_boxed_1006_, v_param_1003_, v_inst_1004_, v_____do__lift_1005_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(uint8_t v_pu_1008_, lean_object* v_inst_1009_, lean_object* v_inst_1010_, lean_object* v_f_1011_, lean_object* v_param_1012_){
_start:
{
lean_object* v_toBind_1013_; lean_object* v_type_1014_; lean_object* v___x_1015_; lean_object* v___f_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_toBind_1013_ = lean_ctor_get(v_inst_1010_, 1);
lean_inc(v_toBind_1013_);
v_type_1014_ = lean_ctor_get(v_param_1012_, 2);
lean_inc_ref(v_type_1014_);
v___x_1015_ = lean_box(v_pu_1008_);
v___f_1016_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1016_, 0, v___x_1015_);
lean_closure_set(v___f_1016_, 1, v_param_1012_);
lean_closure_set(v___f_1016_, 2, v_inst_1009_);
v___x_1017_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1010_, v_f_1011_, v_type_1014_);
v___x_1018_ = lean_apply_4(v_toBind_1013_, lean_box(0), lean_box(0), v___x_1017_, v___f_1016_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___boxed(lean_object* v_pu_1019_, lean_object* v_inst_1020_, lean_object* v_inst_1021_, lean_object* v_f_1022_, lean_object* v_param_1023_){
_start:
{
uint8_t v_pu_boxed_1024_; lean_object* v_res_1025_; 
v_pu_boxed_1024_ = lean_unbox(v_pu_1019_);
v_res_1025_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(v_pu_boxed_1024_, v_inst_1020_, v_inst_1021_, v_f_1022_, v_param_1023_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM(lean_object* v_m_1026_, uint8_t v_pu_1027_, lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_f_1030_, lean_object* v_param_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(v_pu_1027_, v_inst_1028_, v_inst_1029_, v_f_1030_, v_param_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___boxed(lean_object* v_m_1033_, lean_object* v_pu_1034_, lean_object* v_inst_1035_, lean_object* v_inst_1036_, lean_object* v_f_1037_, lean_object* v_param_1038_){
_start:
{
uint8_t v_pu_boxed_1039_; lean_object* v_res_1040_; 
v_pu_boxed_1039_ = lean_unbox(v_pu_1034_);
v_res_1040_ = l_Lean_Compiler_LCNF_Param_mapFVarM(v_m_1033_, v_pu_boxed_1039_, v_inst_1035_, v_inst_1036_, v_f_1037_, v_param_1038_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___redArg(lean_object* v_inst_1041_, lean_object* v_f_1042_, lean_object* v_param_1043_){
_start:
{
lean_object* v_type_1044_; lean_object* v___x_1045_; 
v_type_1044_ = lean_ctor_get(v_param_1043_, 2);
lean_inc_ref(v_type_1044_);
lean_dec_ref(v_param_1043_);
v___x_1045_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_1041_, v_f_1042_, v_type_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM(lean_object* v_m_1046_, uint8_t v_pu_1047_, lean_object* v_inst_1048_, lean_object* v_f_1049_, lean_object* v_param_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_1048_, v_f_1049_, v_param_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___boxed(lean_object* v_m_1052_, lean_object* v_pu_1053_, lean_object* v_inst_1054_, lean_object* v_f_1055_, lean_object* v_param_1056_){
_start:
{
uint8_t v_pu_boxed_1057_; lean_object* v_res_1058_; 
v_pu_boxed_1057_ = lean_unbox(v_pu_1053_);
v_res_1058_ = l_Lean_Compiler_LCNF_Param_forFVarM(v_m_1052_, v_pu_boxed_1057_, v_inst_1054_, v_f_1055_, v_param_1056_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(uint8_t v_pu_1059_, lean_object* v_m_1060_, lean_object* v_inst_1061_, lean_object* v_inst_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(v_pu_1059_, v_inst_1061_, v_inst_1062_, v___y_1063_, v___y_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0___boxed(lean_object* v_pu_1066_, lean_object* v_m_1067_, lean_object* v_inst_1068_, lean_object* v_inst_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
uint8_t v_pu_boxed_1072_; lean_object* v_res_1073_; 
v_pu_boxed_1072_ = lean_unbox(v_pu_1066_);
v_res_1073_ = l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(v_pu_boxed_1072_, v_m_1067_, v_inst_1068_, v_inst_1069_, v___y_1070_, v___y_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__1(lean_object* v_m_1074_, lean_object* v_inst_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_1075_, v___y_1076_, v___y_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam(uint8_t v_pu_1080_){
_start:
{
lean_object* v___x_1081_; lean_object* v___f_1082_; lean_object* v___f_1083_; lean_object* v___x_1084_; 
v___x_1081_ = lean_box(v_pu_1080_);
v___f_1082_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1082_, 0, v___x_1081_);
v___f_1083_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarParam___closed__0));
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___f_1082_);
lean_ctor_set(v___x_1084_, 1, v___f_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___boxed(lean_object* v_pu_1085_){
_start:
{
uint8_t v_pu_boxed_1086_; lean_object* v_res_1087_; 
v_pu_boxed_1086_ = lean_unbox(v_pu_1085_);
v_res_1087_ = l_Lean_Compiler_LCNF_instTraverseFVarParam(v_pu_boxed_1086_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0(lean_object* v_decl_1088_, lean_object* v_toPure_1089_, lean_object* v_c_1090_, lean_object* v_k_1091_, lean_object* v_decl_1092_, lean_object* v_____do__lift_1093_){
_start:
{
uint8_t v___y_1095_; size_t v___x_1099_; size_t v___x_1100_; uint8_t v___x_1101_; 
v___x_1099_ = lean_ptr_addr(v_k_1091_);
v___x_1100_ = lean_ptr_addr(v_____do__lift_1093_);
v___x_1101_ = lean_usize_dec_eq(v___x_1099_, v___x_1100_);
if (v___x_1101_ == 0)
{
v___y_1095_ = v___x_1101_;
goto v___jp_1094_;
}
else
{
size_t v___x_1102_; size_t v___x_1103_; uint8_t v___x_1104_; 
v___x_1102_ = lean_ptr_addr(v_decl_1092_);
v___x_1103_ = lean_ptr_addr(v_decl_1088_);
v___x_1104_ = lean_usize_dec_eq(v___x_1102_, v___x_1103_);
v___y_1095_ = v___x_1104_;
goto v___jp_1094_;
}
v___jp_1094_:
{
if (v___y_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec_ref(v_c_1090_);
v___x_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1096_, 0, v_decl_1088_);
lean_ctor_set(v___x_1096_, 1, v_____do__lift_1093_);
v___x_1097_ = lean_apply_2(v_toPure_1089_, lean_box(0), v___x_1096_);
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; 
lean_dec_ref(v_____do__lift_1093_);
lean_dec_ref(v_decl_1088_);
v___x_1098_ = lean_apply_2(v_toPure_1089_, lean_box(0), v_c_1090_);
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed(lean_object* v_decl_1105_, lean_object* v_toPure_1106_, lean_object* v_c_1107_, lean_object* v_k_1108_, lean_object* v_decl_1109_, lean_object* v_____do__lift_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0(v_decl_1105_, v_toPure_1106_, v_c_1107_, v_k_1108_, v_decl_1109_, v_____do__lift_1110_);
lean_dec_ref(v_decl_1109_);
lean_dec_ref(v_k_1108_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(lean_object* v_____do__lift_1112_, lean_object* v_i_1113_, lean_object* v_____do__lift_1114_, lean_object* v_toPure_1115_, lean_object* v_y_1116_, lean_object* v_k_1117_, lean_object* v_c_1118_, lean_object* v_fvarId_1119_, lean_object* v_____do__lift_1120_){
_start:
{
uint8_t v___y_1122_; size_t v___x_1136_; size_t v___x_1137_; uint8_t v___x_1138_; 
v___x_1136_ = lean_ptr_addr(v_fvarId_1119_);
v___x_1137_ = lean_ptr_addr(v_____do__lift_1112_);
v___x_1138_ = lean_usize_dec_eq(v___x_1136_, v___x_1137_);
if (v___x_1138_ == 0)
{
v___y_1122_ = v___x_1138_;
goto v___jp_1121_;
}
else
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_nat_dec_eq(v_i_1113_, v_i_1113_);
v___y_1122_ = v___x_1139_;
goto v___jp_1121_;
}
v___jp_1121_:
{
if (v___y_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_dec_ref(v_c_1118_);
v___x_1123_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1123_, 0, v_____do__lift_1112_);
lean_ctor_set(v___x_1123_, 1, v_i_1113_);
lean_ctor_set(v___x_1123_, 2, v_____do__lift_1114_);
lean_ctor_set(v___x_1123_, 3, v_____do__lift_1120_);
v___x_1124_ = lean_apply_2(v_toPure_1115_, lean_box(0), v___x_1123_);
return v___x_1124_;
}
else
{
size_t v___x_1125_; size_t v___x_1126_; uint8_t v___x_1127_; 
v___x_1125_ = lean_ptr_addr(v_y_1116_);
v___x_1126_ = lean_ptr_addr(v_____do__lift_1114_);
v___x_1127_ = lean_usize_dec_eq(v___x_1125_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_dec_ref(v_c_1118_);
v___x_1128_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1128_, 0, v_____do__lift_1112_);
lean_ctor_set(v___x_1128_, 1, v_i_1113_);
lean_ctor_set(v___x_1128_, 2, v_____do__lift_1114_);
lean_ctor_set(v___x_1128_, 3, v_____do__lift_1120_);
v___x_1129_ = lean_apply_2(v_toPure_1115_, lean_box(0), v___x_1128_);
return v___x_1129_;
}
else
{
size_t v___x_1130_; size_t v___x_1131_; uint8_t v___x_1132_; 
v___x_1130_ = lean_ptr_addr(v_k_1117_);
v___x_1131_ = lean_ptr_addr(v_____do__lift_1120_);
v___x_1132_ = lean_usize_dec_eq(v___x_1130_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec_ref(v_c_1118_);
v___x_1133_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1133_, 0, v_____do__lift_1112_);
lean_ctor_set(v___x_1133_, 1, v_i_1113_);
lean_ctor_set(v___x_1133_, 2, v_____do__lift_1114_);
lean_ctor_set(v___x_1133_, 3, v_____do__lift_1120_);
v___x_1134_ = lean_apply_2(v_toPure_1115_, lean_box(0), v___x_1133_);
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; 
lean_dec_ref(v_____do__lift_1120_);
lean_dec(v_____do__lift_1114_);
lean_dec(v_i_1113_);
lean_dec(v_____do__lift_1112_);
v___x_1135_ = lean_apply_2(v_toPure_1115_, lean_box(0), v_c_1118_);
return v___x_1135_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed(lean_object* v_____do__lift_1140_, lean_object* v_i_1141_, lean_object* v_____do__lift_1142_, lean_object* v_toPure_1143_, lean_object* v_y_1144_, lean_object* v_k_1145_, lean_object* v_c_1146_, lean_object* v_fvarId_1147_, lean_object* v_____do__lift_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(v_____do__lift_1140_, v_i_1141_, v_____do__lift_1142_, v_toPure_1143_, v_y_1144_, v_k_1145_, v_c_1146_, v_fvarId_1147_, v_____do__lift_1148_);
lean_dec(v_fvarId_1147_);
lean_dec_ref(v_k_1145_);
lean_dec(v_y_1144_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(lean_object* v_fvarId_1150_, lean_object* v_toPure_1151_, lean_object* v_c_1152_, lean_object* v_____do__lift_1153_){
_start:
{
uint8_t v___x_1154_; 
v___x_1154_ = l_Lean_instBEqFVarId_beq(v_fvarId_1150_, v_____do__lift_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_dec_ref(v_c_1152_);
v___x_1155_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_____do__lift_1153_);
v___x_1156_ = lean_apply_2(v_toPure_1151_, lean_box(0), v___x_1155_);
return v___x_1156_;
}
else
{
lean_object* v___x_1157_; 
lean_dec(v_____do__lift_1153_);
v___x_1157_ = lean_apply_2(v_toPure_1151_, lean_box(0), v_c_1152_);
return v___x_1157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed(lean_object* v_fvarId_1158_, lean_object* v_toPure_1159_, lean_object* v_c_1160_, lean_object* v_____do__lift_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(v_fvarId_1158_, v_toPure_1159_, v_c_1160_, v_____do__lift_1161_);
lean_dec(v_fvarId_1158_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27(lean_object* v_____do__lift_1163_, lean_object* v_cidx_1164_, lean_object* v_toPure_1165_, lean_object* v_k_1166_, lean_object* v_c_1167_, lean_object* v_fvarId_1168_, lean_object* v_____do__lift_1169_){
_start:
{
uint8_t v___y_1171_; size_t v___x_1180_; size_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1180_ = lean_ptr_addr(v_fvarId_1168_);
v___x_1181_ = lean_ptr_addr(v_____do__lift_1163_);
v___x_1182_ = lean_usize_dec_eq(v___x_1180_, v___x_1181_);
if (v___x_1182_ == 0)
{
v___y_1171_ = v___x_1182_;
goto v___jp_1170_;
}
else
{
uint8_t v___x_1183_; 
v___x_1183_ = lean_nat_dec_eq(v_cidx_1164_, v_cidx_1164_);
v___y_1171_ = v___x_1183_;
goto v___jp_1170_;
}
v___jp_1170_:
{
if (v___y_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_dec_ref(v_c_1167_);
v___x_1172_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1172_, 0, v_____do__lift_1163_);
lean_ctor_set(v___x_1172_, 1, v_cidx_1164_);
lean_ctor_set(v___x_1172_, 2, v_____do__lift_1169_);
v___x_1173_ = lean_apply_2(v_toPure_1165_, lean_box(0), v___x_1172_);
return v___x_1173_;
}
else
{
size_t v___x_1174_; size_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1174_ = lean_ptr_addr(v_k_1166_);
v___x_1175_ = lean_ptr_addr(v_____do__lift_1169_);
v___x_1176_ = lean_usize_dec_eq(v___x_1174_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec_ref(v_c_1167_);
v___x_1177_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1177_, 0, v_____do__lift_1163_);
lean_ctor_set(v___x_1177_, 1, v_cidx_1164_);
lean_ctor_set(v___x_1177_, 2, v_____do__lift_1169_);
v___x_1178_ = lean_apply_2(v_toPure_1165_, lean_box(0), v___x_1177_);
return v___x_1178_;
}
else
{
lean_object* v___x_1179_; 
lean_dec_ref(v_____do__lift_1169_);
lean_dec(v_cidx_1164_);
lean_dec(v_____do__lift_1163_);
v___x_1179_ = lean_apply_2(v_toPure_1165_, lean_box(0), v_c_1167_);
return v___x_1179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27___boxed(lean_object* v_____do__lift_1184_, lean_object* v_cidx_1185_, lean_object* v_toPure_1186_, lean_object* v_k_1187_, lean_object* v_c_1188_, lean_object* v_fvarId_1189_, lean_object* v_____do__lift_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27(v_____do__lift_1184_, v_cidx_1185_, v_toPure_1186_, v_k_1187_, v_c_1188_, v_fvarId_1189_, v_____do__lift_1190_);
lean_dec(v_fvarId_1189_);
lean_dec_ref(v_k_1187_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(lean_object* v_____do__lift_1192_, lean_object* v_n_1193_, uint8_t v_check_1194_, uint8_t v_persistent_1195_, lean_object* v_toPure_1196_, lean_object* v_k_1197_, lean_object* v_c_1198_, lean_object* v_fvarId_1199_, lean_object* v_____do__lift_1200_){
_start:
{
uint8_t v___y_1202_; size_t v___x_1211_; size_t v___x_1212_; uint8_t v___x_1213_; 
v___x_1211_ = lean_ptr_addr(v_fvarId_1199_);
v___x_1212_ = lean_ptr_addr(v_____do__lift_1192_);
v___x_1213_ = lean_usize_dec_eq(v___x_1211_, v___x_1212_);
if (v___x_1213_ == 0)
{
v___y_1202_ = v___x_1213_;
goto v___jp_1201_;
}
else
{
uint8_t v___x_1214_; 
v___x_1214_ = lean_nat_dec_eq(v_n_1193_, v_n_1193_);
v___y_1202_ = v___x_1214_;
goto v___jp_1201_;
}
v___jp_1201_:
{
if (v___y_1202_ == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_dec_ref(v_c_1198_);
v___x_1203_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1203_, 0, v_____do__lift_1192_);
lean_ctor_set(v___x_1203_, 1, v_n_1193_);
lean_ctor_set(v___x_1203_, 2, v_____do__lift_1200_);
lean_ctor_set_uint8(v___x_1203_, sizeof(void*)*3, v_check_1194_);
lean_ctor_set_uint8(v___x_1203_, sizeof(void*)*3 + 1, v_persistent_1195_);
v___x_1204_ = lean_apply_2(v_toPure_1196_, lean_box(0), v___x_1203_);
return v___x_1204_;
}
else
{
size_t v___x_1205_; size_t v___x_1206_; uint8_t v___x_1207_; 
v___x_1205_ = lean_ptr_addr(v_k_1197_);
v___x_1206_ = lean_ptr_addr(v_____do__lift_1200_);
v___x_1207_ = lean_usize_dec_eq(v___x_1205_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec_ref(v_c_1198_);
v___x_1208_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1208_, 0, v_____do__lift_1192_);
lean_ctor_set(v___x_1208_, 1, v_n_1193_);
lean_ctor_set(v___x_1208_, 2, v_____do__lift_1200_);
lean_ctor_set_uint8(v___x_1208_, sizeof(void*)*3, v_check_1194_);
lean_ctor_set_uint8(v___x_1208_, sizeof(void*)*3 + 1, v_persistent_1195_);
v___x_1209_ = lean_apply_2(v_toPure_1196_, lean_box(0), v___x_1208_);
return v___x_1209_;
}
else
{
lean_object* v___x_1210_; 
lean_dec_ref(v_____do__lift_1200_);
lean_dec(v_n_1193_);
lean_dec(v_____do__lift_1192_);
v___x_1210_ = lean_apply_2(v_toPure_1196_, lean_box(0), v_c_1198_);
return v___x_1210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29___boxed(lean_object* v_____do__lift_1215_, lean_object* v_n_1216_, lean_object* v_check_1217_, lean_object* v_persistent_1218_, lean_object* v_toPure_1219_, lean_object* v_k_1220_, lean_object* v_c_1221_, lean_object* v_fvarId_1222_, lean_object* v_____do__lift_1223_){
_start:
{
uint8_t v_check_1824__boxed_1224_; uint8_t v_persistent_1825__boxed_1225_; lean_object* v_res_1226_; 
v_check_1824__boxed_1224_ = lean_unbox(v_check_1217_);
v_persistent_1825__boxed_1225_ = lean_unbox(v_persistent_1218_);
v_res_1226_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(v_____do__lift_1215_, v_n_1216_, v_check_1824__boxed_1224_, v_persistent_1825__boxed_1225_, v_toPure_1219_, v_k_1220_, v_c_1221_, v_fvarId_1222_, v_____do__lift_1223_);
lean_dec(v_fvarId_1222_);
lean_dec_ref(v_k_1220_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(lean_object* v_____do__lift_1227_, lean_object* v_i_1228_, lean_object* v_offset_1229_, lean_object* v_____do__lift_1230_, lean_object* v_____do__lift_1231_, lean_object* v_toPure_1232_, lean_object* v_y_1233_, lean_object* v_ty_1234_, lean_object* v_k_1235_, lean_object* v_c_1236_, lean_object* v_fvarId_1237_, lean_object* v_____do__lift_1238_){
_start:
{
uint8_t v___y_1240_; size_t v___x_1262_; size_t v___x_1263_; uint8_t v___x_1264_; 
v___x_1262_ = lean_ptr_addr(v_fvarId_1237_);
v___x_1263_ = lean_ptr_addr(v_____do__lift_1227_);
v___x_1264_ = lean_usize_dec_eq(v___x_1262_, v___x_1263_);
if (v___x_1264_ == 0)
{
v___y_1240_ = v___x_1264_;
goto v___jp_1239_;
}
else
{
uint8_t v___x_1265_; 
v___x_1265_ = lean_nat_dec_eq(v_i_1228_, v_i_1228_);
v___y_1240_ = v___x_1265_;
goto v___jp_1239_;
}
v___jp_1239_:
{
if (v___y_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_dec_ref(v_c_1236_);
v___x_1241_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1241_, 0, v_____do__lift_1227_);
lean_ctor_set(v___x_1241_, 1, v_i_1228_);
lean_ctor_set(v___x_1241_, 2, v_offset_1229_);
lean_ctor_set(v___x_1241_, 3, v_____do__lift_1230_);
lean_ctor_set(v___x_1241_, 4, v_____do__lift_1231_);
lean_ctor_set(v___x_1241_, 5, v_____do__lift_1238_);
v___x_1242_ = lean_apply_2(v_toPure_1232_, lean_box(0), v___x_1241_);
return v___x_1242_;
}
else
{
uint8_t v___x_1243_; 
v___x_1243_ = lean_nat_dec_eq(v_offset_1229_, v_offset_1229_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec_ref(v_c_1236_);
v___x_1244_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1244_, 0, v_____do__lift_1227_);
lean_ctor_set(v___x_1244_, 1, v_i_1228_);
lean_ctor_set(v___x_1244_, 2, v_offset_1229_);
lean_ctor_set(v___x_1244_, 3, v_____do__lift_1230_);
lean_ctor_set(v___x_1244_, 4, v_____do__lift_1231_);
lean_ctor_set(v___x_1244_, 5, v_____do__lift_1238_);
v___x_1245_ = lean_apply_2(v_toPure_1232_, lean_box(0), v___x_1244_);
return v___x_1245_;
}
else
{
size_t v___x_1246_; size_t v___x_1247_; uint8_t v___x_1248_; 
v___x_1246_ = lean_ptr_addr(v_y_1233_);
v___x_1247_ = lean_ptr_addr(v_____do__lift_1230_);
v___x_1248_ = lean_usize_dec_eq(v___x_1246_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_dec_ref(v_c_1236_);
v___x_1249_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1249_, 0, v_____do__lift_1227_);
lean_ctor_set(v___x_1249_, 1, v_i_1228_);
lean_ctor_set(v___x_1249_, 2, v_offset_1229_);
lean_ctor_set(v___x_1249_, 3, v_____do__lift_1230_);
lean_ctor_set(v___x_1249_, 4, v_____do__lift_1231_);
lean_ctor_set(v___x_1249_, 5, v_____do__lift_1238_);
v___x_1250_ = lean_apply_2(v_toPure_1232_, lean_box(0), v___x_1249_);
return v___x_1250_;
}
else
{
size_t v___x_1251_; size_t v___x_1252_; uint8_t v___x_1253_; 
v___x_1251_ = lean_ptr_addr(v_ty_1234_);
v___x_1252_ = lean_ptr_addr(v_____do__lift_1231_);
v___x_1253_ = lean_usize_dec_eq(v___x_1251_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_dec_ref(v_c_1236_);
v___x_1254_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1254_, 0, v_____do__lift_1227_);
lean_ctor_set(v___x_1254_, 1, v_i_1228_);
lean_ctor_set(v___x_1254_, 2, v_offset_1229_);
lean_ctor_set(v___x_1254_, 3, v_____do__lift_1230_);
lean_ctor_set(v___x_1254_, 4, v_____do__lift_1231_);
lean_ctor_set(v___x_1254_, 5, v_____do__lift_1238_);
v___x_1255_ = lean_apply_2(v_toPure_1232_, lean_box(0), v___x_1254_);
return v___x_1255_;
}
else
{
size_t v___x_1256_; size_t v___x_1257_; uint8_t v___x_1258_; 
v___x_1256_ = lean_ptr_addr(v_k_1235_);
v___x_1257_ = lean_ptr_addr(v_____do__lift_1238_);
v___x_1258_ = lean_usize_dec_eq(v___x_1256_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec_ref(v_c_1236_);
v___x_1259_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1259_, 0, v_____do__lift_1227_);
lean_ctor_set(v___x_1259_, 1, v_i_1228_);
lean_ctor_set(v___x_1259_, 2, v_offset_1229_);
lean_ctor_set(v___x_1259_, 3, v_____do__lift_1230_);
lean_ctor_set(v___x_1259_, 4, v_____do__lift_1231_);
lean_ctor_set(v___x_1259_, 5, v_____do__lift_1238_);
v___x_1260_ = lean_apply_2(v_toPure_1232_, lean_box(0), v___x_1259_);
return v___x_1260_;
}
else
{
lean_object* v___x_1261_; 
lean_dec_ref(v_____do__lift_1238_);
lean_dec_ref(v_____do__lift_1231_);
lean_dec(v_____do__lift_1230_);
lean_dec(v_offset_1229_);
lean_dec(v_i_1228_);
lean_dec(v_____do__lift_1227_);
v___x_1261_ = lean_apply_2(v_toPure_1232_, lean_box(0), v_c_1236_);
return v___x_1261_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed(lean_object* v_____do__lift_1266_, lean_object* v_i_1267_, lean_object* v_offset_1268_, lean_object* v_____do__lift_1269_, lean_object* v_____do__lift_1270_, lean_object* v_toPure_1271_, lean_object* v_y_1272_, lean_object* v_ty_1273_, lean_object* v_k_1274_, lean_object* v_c_1275_, lean_object* v_fvarId_1276_, lean_object* v_____do__lift_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(v_____do__lift_1266_, v_i_1267_, v_offset_1268_, v_____do__lift_1269_, v_____do__lift_1270_, v_toPure_1271_, v_y_1272_, v_ty_1273_, v_k_1274_, v_c_1275_, v_fvarId_1276_, v_____do__lift_1277_);
lean_dec(v_fvarId_1276_);
lean_dec_ref(v_k_1274_);
lean_dec_ref(v_ty_1273_);
lean_dec(v_y_1272_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(uint8_t v_pu_1279_, lean_object* v_decl_1280_, lean_object* v_____do__lift_1281_, lean_object* v_params_1282_, lean_object* v_inst_1283_, lean_object* v_toBind_1284_, lean_object* v___f_1285_, lean_object* v_____do__lift_1286_){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1287_ = lean_box(v_pu_1279_);
v___x_1288_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed), 10, 5);
lean_closure_set(v___x_1288_, 0, v___x_1287_);
lean_closure_set(v___x_1288_, 1, v_decl_1280_);
lean_closure_set(v___x_1288_, 2, v_____do__lift_1281_);
lean_closure_set(v___x_1288_, 3, v_params_1282_);
lean_closure_set(v___x_1288_, 4, v_____do__lift_1286_);
v___x_1289_ = lean_apply_2(v_inst_1283_, lean_box(0), v___x_1288_);
v___x_1290_ = lean_apply_4(v_toBind_1284_, lean_box(0), lean_box(0), v___x_1289_, v___f_1285_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed(lean_object* v_pu_1291_, lean_object* v_decl_1292_, lean_object* v_____do__lift_1293_, lean_object* v_params_1294_, lean_object* v_inst_1295_, lean_object* v_toBind_1296_, lean_object* v___f_1297_, lean_object* v_____do__lift_1298_){
_start:
{
uint8_t v_pu_boxed_1299_; lean_object* v_res_1300_; 
v_pu_boxed_1299_ = lean_unbox(v_pu_1291_);
v_res_1300_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(v_pu_boxed_1299_, v_decl_1292_, v_____do__lift_1293_, v_params_1294_, v_inst_1295_, v_toBind_1296_, v___f_1297_, v_____do__lift_1298_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(lean_object* v_____do__lift_1301_, lean_object* v_toPure_1302_, lean_object* v_c_1303_, lean_object* v_fvarId_1304_, lean_object* v_args_1305_, lean_object* v_____do__lift_1306_){
_start:
{
uint8_t v___y_1308_; uint8_t v___x_1312_; 
v___x_1312_ = l_Lean_instBEqFVarId_beq(v_fvarId_1304_, v_____do__lift_1301_);
if (v___x_1312_ == 0)
{
v___y_1308_ = v___x_1312_;
goto v___jp_1307_;
}
else
{
size_t v___x_1313_; size_t v___x_1314_; uint8_t v___x_1315_; 
v___x_1313_ = lean_ptr_addr(v_args_1305_);
v___x_1314_ = lean_ptr_addr(v_____do__lift_1306_);
v___x_1315_ = lean_usize_dec_eq(v___x_1313_, v___x_1314_);
v___y_1308_ = v___x_1315_;
goto v___jp_1307_;
}
v___jp_1307_:
{
if (v___y_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec_ref(v_c_1303_);
v___x_1309_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1309_, 0, v_____do__lift_1301_);
lean_ctor_set(v___x_1309_, 1, v_____do__lift_1306_);
v___x_1310_ = lean_apply_2(v_toPure_1302_, lean_box(0), v___x_1309_);
return v___x_1310_;
}
else
{
lean_object* v___x_1311_; 
lean_dec_ref(v_____do__lift_1306_);
lean_dec(v_____do__lift_1301_);
v___x_1311_ = lean_apply_2(v_toPure_1302_, lean_box(0), v_c_1303_);
return v___x_1311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed(lean_object* v_____do__lift_1316_, lean_object* v_toPure_1317_, lean_object* v_c_1318_, lean_object* v_fvarId_1319_, lean_object* v_args_1320_, lean_object* v_____do__lift_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(v_____do__lift_1316_, v_toPure_1317_, v_c_1318_, v_fvarId_1319_, v_args_1320_, v_____do__lift_1321_);
lean_dec_ref(v_args_1320_);
lean_dec(v_fvarId_1319_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(lean_object* v_toPure_1323_, lean_object* v_c_1324_, lean_object* v_fvarId_1325_, lean_object* v_args_1326_, uint8_t v_pu_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_f_1330_, lean_object* v_toBind_1331_, lean_object* v_____do__lift_1332_){
_start:
{
lean_object* v___f_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; size_t v_sz_1336_; size_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_inc_ref(v_args_1326_);
v___f_1333_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed), 6, 5);
lean_closure_set(v___f_1333_, 0, v_____do__lift_1332_);
lean_closure_set(v___f_1333_, 1, v_toPure_1323_);
lean_closure_set(v___f_1333_, 2, v_c_1324_);
lean_closure_set(v___f_1333_, 3, v_fvarId_1325_);
lean_closure_set(v___f_1333_, 4, v_args_1326_);
v___x_1334_ = lean_box(v_pu_1327_);
lean_inc_ref(v_inst_1329_);
v___x_1335_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Arg_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_1335_, 0, lean_box(0));
lean_closure_set(v___x_1335_, 1, v___x_1334_);
lean_closure_set(v___x_1335_, 2, v_inst_1328_);
lean_closure_set(v___x_1335_, 3, v_inst_1329_);
lean_closure_set(v___x_1335_, 4, v_f_1330_);
v_sz_1336_ = lean_array_size(v_args_1326_);
v___x_1337_ = ((size_t)0ULL);
v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1329_, v___x_1335_, v_sz_1336_, v___x_1337_, v_args_1326_);
v___x_1339_ = lean_apply_4(v_toBind_1331_, lean_box(0), lean_box(0), v___x_1338_, v___f_1333_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed(lean_object* v_toPure_1340_, lean_object* v_c_1341_, lean_object* v_fvarId_1342_, lean_object* v_args_1343_, lean_object* v_pu_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_f_1347_, lean_object* v_toBind_1348_, lean_object* v_____do__lift_1349_){
_start:
{
uint8_t v_pu_boxed_1350_; lean_object* v_res_1351_; 
v_pu_boxed_1350_ = lean_unbox(v_pu_1344_);
v_res_1351_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(v_toPure_1340_, v_c_1341_, v_fvarId_1342_, v_args_1343_, v_pu_boxed_1350_, v_inst_1345_, v_inst_1346_, v_f_1347_, v_toBind_1348_, v_____do__lift_1349_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(lean_object* v_typeName_1352_, lean_object* v_____do__lift_1353_, lean_object* v_____do__lift_1354_, lean_object* v_toPure_1355_, lean_object* v_discr_1356_, lean_object* v_c_1357_, lean_object* v_alts_1358_, lean_object* v_resultType_1359_, lean_object* v_____do__lift_1360_){
_start:
{
uint8_t v___y_1366_; size_t v___x_1369_; size_t v___x_1370_; uint8_t v___x_1371_; 
v___x_1369_ = lean_ptr_addr(v_alts_1358_);
v___x_1370_ = lean_ptr_addr(v_____do__lift_1360_);
v___x_1371_ = lean_usize_dec_eq(v___x_1369_, v___x_1370_);
if (v___x_1371_ == 0)
{
v___y_1366_ = v___x_1371_;
goto v___jp_1365_;
}
else
{
size_t v___x_1372_; size_t v___x_1373_; uint8_t v___x_1374_; 
v___x_1372_ = lean_ptr_addr(v_resultType_1359_);
v___x_1373_ = lean_ptr_addr(v_____do__lift_1353_);
v___x_1374_ = lean_usize_dec_eq(v___x_1372_, v___x_1373_);
v___y_1366_ = v___x_1374_;
goto v___jp_1365_;
}
v___jp_1361_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1362_, 0, v_typeName_1352_);
lean_ctor_set(v___x_1362_, 1, v_____do__lift_1353_);
lean_ctor_set(v___x_1362_, 2, v_____do__lift_1354_);
lean_ctor_set(v___x_1362_, 3, v_____do__lift_1360_);
v___x_1363_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
v___x_1364_ = lean_apply_2(v_toPure_1355_, lean_box(0), v___x_1363_);
return v___x_1364_;
}
v___jp_1365_:
{
if (v___y_1366_ == 0)
{
lean_dec_ref(v_c_1357_);
goto v___jp_1361_;
}
else
{
uint8_t v___x_1367_; 
v___x_1367_ = l_Lean_instBEqFVarId_beq(v_discr_1356_, v_____do__lift_1354_);
if (v___x_1367_ == 0)
{
lean_dec_ref(v_c_1357_);
goto v___jp_1361_;
}
else
{
lean_object* v___x_1368_; 
lean_dec_ref(v_____do__lift_1360_);
lean_dec(v_____do__lift_1354_);
lean_dec_ref(v_____do__lift_1353_);
lean_dec(v_typeName_1352_);
v___x_1368_ = lean_apply_2(v_toPure_1355_, lean_box(0), v_c_1357_);
return v___x_1368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed(lean_object* v_typeName_1375_, lean_object* v_____do__lift_1376_, lean_object* v_____do__lift_1377_, lean_object* v_toPure_1378_, lean_object* v_discr_1379_, lean_object* v_c_1380_, lean_object* v_alts_1381_, lean_object* v_resultType_1382_, lean_object* v_____do__lift_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(v_typeName_1375_, v_____do__lift_1376_, v_____do__lift_1377_, v_toPure_1378_, v_discr_1379_, v_c_1380_, v_alts_1381_, v_resultType_1382_, v_____do__lift_1383_);
lean_dec_ref(v_resultType_1382_);
lean_dec_ref(v_alts_1381_);
lean_dec(v_discr_1379_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13(lean_object* v_typeName_1385_, lean_object* v_____do__lift_1386_, lean_object* v_toPure_1387_, lean_object* v_discr_1388_, lean_object* v_c_1389_, lean_object* v_alts_1390_, lean_object* v_resultType_1391_, lean_object* v_inst_1392_, lean_object* v___f_1393_, lean_object* v_toBind_1394_, lean_object* v_____do__lift_1395_){
_start:
{
lean_object* v___f_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_inc_ref(v_alts_1390_);
v___f_1396_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed), 9, 8);
lean_closure_set(v___f_1396_, 0, v_typeName_1385_);
lean_closure_set(v___f_1396_, 1, v_____do__lift_1386_);
lean_closure_set(v___f_1396_, 2, v_____do__lift_1395_);
lean_closure_set(v___f_1396_, 3, v_toPure_1387_);
lean_closure_set(v___f_1396_, 4, v_discr_1388_);
lean_closure_set(v___f_1396_, 5, v_c_1389_);
lean_closure_set(v___f_1396_, 6, v_alts_1390_);
lean_closure_set(v___f_1396_, 7, v_resultType_1391_);
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_1392_, v___f_1393_, v___x_1397_, v_alts_1390_);
v___x_1399_ = lean_apply_4(v_toBind_1394_, lean_box(0), lean_box(0), v___x_1398_, v___f_1396_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14(lean_object* v_typeName_1400_, lean_object* v_toPure_1401_, lean_object* v_discr_1402_, lean_object* v_c_1403_, lean_object* v_alts_1404_, lean_object* v_resultType_1405_, lean_object* v_inst_1406_, lean_object* v___f_1407_, lean_object* v_toBind_1408_, lean_object* v_f_1409_, lean_object* v_____do__lift_1410_){
_start:
{
lean_object* v___f_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
lean_inc(v_toBind_1408_);
lean_inc(v_discr_1402_);
v___f_1411_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13), 11, 10);
lean_closure_set(v___f_1411_, 0, v_typeName_1400_);
lean_closure_set(v___f_1411_, 1, v_____do__lift_1410_);
lean_closure_set(v___f_1411_, 2, v_toPure_1401_);
lean_closure_set(v___f_1411_, 3, v_discr_1402_);
lean_closure_set(v___f_1411_, 4, v_c_1403_);
lean_closure_set(v___f_1411_, 5, v_alts_1404_);
lean_closure_set(v___f_1411_, 6, v_resultType_1405_);
lean_closure_set(v___f_1411_, 7, v_inst_1406_);
lean_closure_set(v___f_1411_, 8, v___f_1407_);
lean_closure_set(v___f_1411_, 9, v_toBind_1408_);
v___x_1412_ = lean_apply_1(v_f_1409_, v_discr_1402_);
v___x_1413_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1412_, v___f_1411_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(lean_object* v_____do__lift_1414_, lean_object* v_n_1415_, uint8_t v_check_1416_, uint8_t v_persistent_1417_, lean_object* v_objs_x3f_1418_, lean_object* v_toPure_1419_, lean_object* v_k_1420_, lean_object* v_c_1421_, lean_object* v_fvarId_1422_, lean_object* v_____do__lift_1423_){
_start:
{
uint8_t v___y_1425_; size_t v___x_1438_; size_t v___x_1439_; uint8_t v___x_1440_; 
v___x_1438_ = lean_ptr_addr(v_fvarId_1422_);
v___x_1439_ = lean_ptr_addr(v_____do__lift_1414_);
v___x_1440_ = lean_usize_dec_eq(v___x_1438_, v___x_1439_);
if (v___x_1440_ == 0)
{
v___y_1425_ = v___x_1440_;
goto v___jp_1424_;
}
else
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_nat_dec_eq(v_n_1415_, v_n_1415_);
v___y_1425_ = v___x_1441_;
goto v___jp_1424_;
}
v___jp_1424_:
{
if (v___y_1425_ == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec_ref(v_c_1421_);
v___x_1426_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1426_, 0, v_____do__lift_1414_);
lean_ctor_set(v___x_1426_, 1, v_n_1415_);
lean_ctor_set(v___x_1426_, 2, v_objs_x3f_1418_);
lean_ctor_set(v___x_1426_, 3, v_____do__lift_1423_);
lean_ctor_set_uint8(v___x_1426_, sizeof(void*)*4, v_check_1416_);
lean_ctor_set_uint8(v___x_1426_, sizeof(void*)*4 + 1, v_persistent_1417_);
v___x_1427_ = lean_apply_2(v_toPure_1419_, lean_box(0), v___x_1426_);
return v___x_1427_;
}
else
{
size_t v___x_1428_; uint8_t v___x_1429_; 
v___x_1428_ = lean_ptr_addr(v_objs_x3f_1418_);
v___x_1429_ = lean_usize_dec_eq(v___x_1428_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec_ref(v_c_1421_);
v___x_1430_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1430_, 0, v_____do__lift_1414_);
lean_ctor_set(v___x_1430_, 1, v_n_1415_);
lean_ctor_set(v___x_1430_, 2, v_objs_x3f_1418_);
lean_ctor_set(v___x_1430_, 3, v_____do__lift_1423_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*4, v_check_1416_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*4 + 1, v_persistent_1417_);
v___x_1431_ = lean_apply_2(v_toPure_1419_, lean_box(0), v___x_1430_);
return v___x_1431_;
}
else
{
size_t v___x_1432_; size_t v___x_1433_; uint8_t v___x_1434_; 
v___x_1432_ = lean_ptr_addr(v_k_1420_);
v___x_1433_ = lean_ptr_addr(v_____do__lift_1423_);
v___x_1434_ = lean_usize_dec_eq(v___x_1432_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec_ref(v_c_1421_);
v___x_1435_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1435_, 0, v_____do__lift_1414_);
lean_ctor_set(v___x_1435_, 1, v_n_1415_);
lean_ctor_set(v___x_1435_, 2, v_objs_x3f_1418_);
lean_ctor_set(v___x_1435_, 3, v_____do__lift_1423_);
lean_ctor_set_uint8(v___x_1435_, sizeof(void*)*4, v_check_1416_);
lean_ctor_set_uint8(v___x_1435_, sizeof(void*)*4 + 1, v_persistent_1417_);
v___x_1436_ = lean_apply_2(v_toPure_1419_, lean_box(0), v___x_1435_);
return v___x_1436_;
}
else
{
lean_object* v___x_1437_; 
lean_dec_ref(v_____do__lift_1423_);
lean_dec(v_objs_x3f_1418_);
lean_dec(v_n_1415_);
lean_dec(v_____do__lift_1414_);
v___x_1437_ = lean_apply_2(v_toPure_1419_, lean_box(0), v_c_1421_);
return v___x_1437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed(lean_object* v_____do__lift_1442_, lean_object* v_n_1443_, lean_object* v_check_1444_, lean_object* v_persistent_1445_, lean_object* v_objs_x3f_1446_, lean_object* v_toPure_1447_, lean_object* v_k_1448_, lean_object* v_c_1449_, lean_object* v_fvarId_1450_, lean_object* v_____do__lift_1451_){
_start:
{
uint8_t v_check_2130__boxed_1452_; uint8_t v_persistent_2131__boxed_1453_; lean_object* v_res_1454_; 
v_check_2130__boxed_1452_ = lean_unbox(v_check_1444_);
v_persistent_2131__boxed_1453_ = lean_unbox(v_persistent_1445_);
v_res_1454_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(v_____do__lift_1442_, v_n_1443_, v_check_2130__boxed_1452_, v_persistent_2131__boxed_1453_, v_objs_x3f_1446_, v_toPure_1447_, v_k_1448_, v_c_1449_, v_fvarId_1450_, v_____do__lift_1451_);
lean_dec(v_fvarId_1450_);
lean_dec_ref(v_k_1448_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(lean_object* v_decl_1455_, lean_object* v_toPure_1456_, lean_object* v_c_1457_, lean_object* v_k_1458_, lean_object* v_decl_1459_, lean_object* v_____do__lift_1460_){
_start:
{
uint8_t v___y_1462_; size_t v___x_1466_; size_t v___x_1467_; uint8_t v___x_1468_; 
v___x_1466_ = lean_ptr_addr(v_k_1458_);
v___x_1467_ = lean_ptr_addr(v_____do__lift_1460_);
v___x_1468_ = lean_usize_dec_eq(v___x_1466_, v___x_1467_);
if (v___x_1468_ == 0)
{
v___y_1462_ = v___x_1468_;
goto v___jp_1461_;
}
else
{
size_t v___x_1469_; size_t v___x_1470_; uint8_t v___x_1471_; 
v___x_1469_ = lean_ptr_addr(v_decl_1459_);
v___x_1470_ = lean_ptr_addr(v_decl_1455_);
v___x_1471_ = lean_usize_dec_eq(v___x_1469_, v___x_1470_);
v___y_1462_ = v___x_1471_;
goto v___jp_1461_;
}
v___jp_1461_:
{
if (v___y_1462_ == 0)
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_dec_ref(v_c_1457_);
v___x_1463_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1463_, 0, v_decl_1455_);
lean_ctor_set(v___x_1463_, 1, v_____do__lift_1460_);
v___x_1464_ = lean_apply_2(v_toPure_1456_, lean_box(0), v___x_1463_);
return v___x_1464_;
}
else
{
lean_object* v___x_1465_; 
lean_dec_ref(v_____do__lift_1460_);
lean_dec_ref(v_decl_1455_);
v___x_1465_ = lean_apply_2(v_toPure_1456_, lean_box(0), v_c_1457_);
return v___x_1465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed(lean_object* v_decl_1472_, lean_object* v_toPure_1473_, lean_object* v_c_1474_, lean_object* v_k_1475_, lean_object* v_decl_1476_, lean_object* v_____do__lift_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(v_decl_1472_, v_toPure_1473_, v_c_1474_, v_k_1475_, v_decl_1476_, v_____do__lift_1477_);
lean_dec_ref(v_decl_1476_);
lean_dec_ref(v_k_1475_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(lean_object* v_decl_1479_, lean_object* v_toPure_1480_, lean_object* v_c_1481_, lean_object* v_k_1482_, lean_object* v_decl_1483_, lean_object* v_____do__lift_1484_){
_start:
{
uint8_t v___y_1486_; size_t v___x_1490_; size_t v___x_1491_; uint8_t v___x_1492_; 
v___x_1490_ = lean_ptr_addr(v_k_1482_);
v___x_1491_ = lean_ptr_addr(v_____do__lift_1484_);
v___x_1492_ = lean_usize_dec_eq(v___x_1490_, v___x_1491_);
if (v___x_1492_ == 0)
{
v___y_1486_ = v___x_1492_;
goto v___jp_1485_;
}
else
{
size_t v___x_1493_; size_t v___x_1494_; uint8_t v___x_1495_; 
v___x_1493_ = lean_ptr_addr(v_decl_1483_);
v___x_1494_ = lean_ptr_addr(v_decl_1479_);
v___x_1495_ = lean_usize_dec_eq(v___x_1493_, v___x_1494_);
v___y_1486_ = v___x_1495_;
goto v___jp_1485_;
}
v___jp_1485_:
{
if (v___y_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_dec_ref(v_c_1481_);
v___x_1487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1487_, 0, v_decl_1479_);
lean_ctor_set(v___x_1487_, 1, v_____do__lift_1484_);
v___x_1488_ = lean_apply_2(v_toPure_1480_, lean_box(0), v___x_1487_);
return v___x_1488_;
}
else
{
lean_object* v___x_1489_; 
lean_dec_ref(v_____do__lift_1484_);
lean_dec_ref(v_decl_1479_);
v___x_1489_ = lean_apply_2(v_toPure_1480_, lean_box(0), v_c_1481_);
return v___x_1489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed(lean_object* v_decl_1496_, lean_object* v_toPure_1497_, lean_object* v_c_1498_, lean_object* v_k_1499_, lean_object* v_decl_1500_, lean_object* v_____do__lift_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(v_decl_1496_, v_toPure_1497_, v_c_1498_, v_k_1499_, v_decl_1500_, v_____do__lift_1501_);
lean_dec_ref(v_decl_1500_);
lean_dec_ref(v_k_1499_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(lean_object* v_____do__lift_1503_, lean_object* v_i_1504_, lean_object* v_____do__lift_1505_, lean_object* v_toPure_1506_, lean_object* v_y_1507_, lean_object* v_k_1508_, lean_object* v_c_1509_, lean_object* v_fvarId_1510_, lean_object* v_____do__lift_1511_){
_start:
{
uint8_t v___y_1513_; size_t v___x_1527_; size_t v___x_1528_; uint8_t v___x_1529_; 
v___x_1527_ = lean_ptr_addr(v_fvarId_1510_);
v___x_1528_ = lean_ptr_addr(v_____do__lift_1503_);
v___x_1529_ = lean_usize_dec_eq(v___x_1527_, v___x_1528_);
if (v___x_1529_ == 0)
{
v___y_1513_ = v___x_1529_;
goto v___jp_1512_;
}
else
{
uint8_t v___x_1530_; 
v___x_1530_ = lean_nat_dec_eq(v_i_1504_, v_i_1504_);
v___y_1513_ = v___x_1530_;
goto v___jp_1512_;
}
v___jp_1512_:
{
if (v___y_1513_ == 0)
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_dec_ref(v_c_1509_);
v___x_1514_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1514_, 0, v_____do__lift_1503_);
lean_ctor_set(v___x_1514_, 1, v_i_1504_);
lean_ctor_set(v___x_1514_, 2, v_____do__lift_1505_);
lean_ctor_set(v___x_1514_, 3, v_____do__lift_1511_);
v___x_1515_ = lean_apply_2(v_toPure_1506_, lean_box(0), v___x_1514_);
return v___x_1515_;
}
else
{
size_t v___x_1516_; size_t v___x_1517_; uint8_t v___x_1518_; 
v___x_1516_ = lean_ptr_addr(v_y_1507_);
v___x_1517_ = lean_ptr_addr(v_____do__lift_1505_);
v___x_1518_ = lean_usize_dec_eq(v___x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_dec_ref(v_c_1509_);
v___x_1519_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1519_, 0, v_____do__lift_1503_);
lean_ctor_set(v___x_1519_, 1, v_i_1504_);
lean_ctor_set(v___x_1519_, 2, v_____do__lift_1505_);
lean_ctor_set(v___x_1519_, 3, v_____do__lift_1511_);
v___x_1520_ = lean_apply_2(v_toPure_1506_, lean_box(0), v___x_1519_);
return v___x_1520_;
}
else
{
size_t v___x_1521_; size_t v___x_1522_; uint8_t v___x_1523_; 
v___x_1521_ = lean_ptr_addr(v_k_1508_);
v___x_1522_ = lean_ptr_addr(v_____do__lift_1511_);
v___x_1523_ = lean_usize_dec_eq(v___x_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec_ref(v_c_1509_);
v___x_1524_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1524_, 0, v_____do__lift_1503_);
lean_ctor_set(v___x_1524_, 1, v_i_1504_);
lean_ctor_set(v___x_1524_, 2, v_____do__lift_1505_);
lean_ctor_set(v___x_1524_, 3, v_____do__lift_1511_);
v___x_1525_ = lean_apply_2(v_toPure_1506_, lean_box(0), v___x_1524_);
return v___x_1525_;
}
else
{
lean_object* v___x_1526_; 
lean_dec_ref(v_____do__lift_1511_);
lean_dec(v_____do__lift_1505_);
lean_dec(v_i_1504_);
lean_dec(v_____do__lift_1503_);
v___x_1526_ = lean_apply_2(v_toPure_1506_, lean_box(0), v_c_1509_);
return v___x_1526_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed(lean_object* v_____do__lift_1531_, lean_object* v_i_1532_, lean_object* v_____do__lift_1533_, lean_object* v_toPure_1534_, lean_object* v_y_1535_, lean_object* v_k_1536_, lean_object* v_c_1537_, lean_object* v_fvarId_1538_, lean_object* v_____do__lift_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(v_____do__lift_1531_, v_i_1532_, v_____do__lift_1533_, v_toPure_1534_, v_y_1535_, v_k_1536_, v_c_1537_, v_fvarId_1538_, v_____do__lift_1539_);
lean_dec(v_fvarId_1538_);
lean_dec_ref(v_k_1536_);
lean_dec(v_y_1535_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(lean_object* v_____do__lift_1541_, lean_object* v_toPure_1542_, lean_object* v_c_1543_, lean_object* v_fvarId_1544_, lean_object* v_k_1545_, lean_object* v_____do__lift_1546_){
_start:
{
uint8_t v___y_1548_; size_t v___x_1552_; size_t v___x_1553_; uint8_t v___x_1554_; 
v___x_1552_ = lean_ptr_addr(v_fvarId_1544_);
v___x_1553_ = lean_ptr_addr(v_____do__lift_1541_);
v___x_1554_ = lean_usize_dec_eq(v___x_1552_, v___x_1553_);
if (v___x_1554_ == 0)
{
v___y_1548_ = v___x_1554_;
goto v___jp_1547_;
}
else
{
size_t v___x_1555_; size_t v___x_1556_; uint8_t v___x_1557_; 
v___x_1555_ = lean_ptr_addr(v_k_1545_);
v___x_1556_ = lean_ptr_addr(v_____do__lift_1546_);
v___x_1557_ = lean_usize_dec_eq(v___x_1555_, v___x_1556_);
v___y_1548_ = v___x_1557_;
goto v___jp_1547_;
}
v___jp_1547_:
{
if (v___y_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
lean_dec_ref(v_c_1543_);
v___x_1549_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_1549_, 0, v_____do__lift_1541_);
lean_ctor_set(v___x_1549_, 1, v_____do__lift_1546_);
v___x_1550_ = lean_apply_2(v_toPure_1542_, lean_box(0), v___x_1549_);
return v___x_1550_;
}
else
{
lean_object* v___x_1551_; 
lean_dec_ref(v_____do__lift_1546_);
lean_dec(v_____do__lift_1541_);
v___x_1551_ = lean_apply_2(v_toPure_1542_, lean_box(0), v_c_1543_);
return v___x_1551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed(lean_object* v_____do__lift_1558_, lean_object* v_toPure_1559_, lean_object* v_c_1560_, lean_object* v_fvarId_1561_, lean_object* v_k_1562_, lean_object* v_____do__lift_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(v_____do__lift_1558_, v_toPure_1559_, v_c_1560_, v_fvarId_1561_, v_k_1562_, v_____do__lift_1563_);
lean_dec_ref(v_k_1562_);
lean_dec(v_fvarId_1561_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(lean_object* v_type_1565_, lean_object* v_toPure_1566_, lean_object* v_c_1567_, lean_object* v_____do__lift_1568_){
_start:
{
size_t v___x_1569_; size_t v___x_1570_; uint8_t v___x_1571_; 
v___x_1569_ = lean_ptr_addr(v_type_1565_);
v___x_1570_ = lean_ptr_addr(v_____do__lift_1568_);
v___x_1571_ = lean_usize_dec_eq(v___x_1569_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
lean_dec_ref(v_c_1567_);
v___x_1572_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1572_, 0, v_____do__lift_1568_);
v___x_1573_ = lean_apply_2(v_toPure_1566_, lean_box(0), v___x_1572_);
return v___x_1573_;
}
else
{
lean_object* v___x_1574_; 
lean_dec_ref(v_____do__lift_1568_);
v___x_1574_ = lean_apply_2(v_toPure_1566_, lean_box(0), v_c_1567_);
return v___x_1574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed(lean_object* v_type_1575_, lean_object* v_toPure_1576_, lean_object* v_c_1577_, lean_object* v_____do__lift_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(v_type_1575_, v_toPure_1576_, v_c_1577_, v_____do__lift_1578_);
lean_dec_ref(v_type_1575_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(lean_object* v_toPure_1580_, lean_object* v_c_1581_, lean_object* v_k_1582_, lean_object* v_decl_1583_, uint8_t v_pu_1584_, lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_f_1587_, lean_object* v_toBind_1588_, lean_object* v_decl_1589_){
_start:
{
lean_object* v___f_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_inc_ref(v_k_1582_);
v___f_1590_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1590_, 0, v_decl_1589_);
lean_closure_set(v___f_1590_, 1, v_toPure_1580_);
lean_closure_set(v___f_1590_, 2, v_c_1581_);
lean_closure_set(v___f_1590_, 3, v_k_1582_);
lean_closure_set(v___f_1590_, 4, v_decl_1583_);
v___x_1591_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1584_, v_inst_1585_, v_inst_1586_, v_f_1587_, v_k_1582_);
v___x_1592_ = lean_apply_4(v_toBind_1588_, lean_box(0), lean_box(0), v___x_1591_, v___f_1590_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed(lean_object* v_toPure_1593_, lean_object* v_c_1594_, lean_object* v_k_1595_, lean_object* v_decl_1596_, lean_object* v_pu_1597_, lean_object* v_inst_1598_, lean_object* v_inst_1599_, lean_object* v_f_1600_, lean_object* v_toBind_1601_, lean_object* v_decl_1602_){
_start:
{
uint8_t v_pu_boxed_1603_; lean_object* v_res_1604_; 
v_pu_boxed_1603_ = lean_unbox(v_pu_1597_);
v_res_1604_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(v_toPure_1593_, v_c_1594_, v_k_1595_, v_decl_1596_, v_pu_boxed_1603_, v_inst_1598_, v_inst_1599_, v_f_1600_, v_toBind_1601_, v_decl_1602_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(lean_object* v_toPure_1605_, lean_object* v_c_1606_, lean_object* v_k_1607_, lean_object* v_decl_1608_, uint8_t v_pu_1609_, lean_object* v_inst_1610_, lean_object* v_inst_1611_, lean_object* v_f_1612_, lean_object* v_toBind_1613_, lean_object* v_decl_1614_){
_start:
{
lean_object* v___f_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_inc_ref(v_k_1607_);
v___f_1615_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_1615_, 0, v_decl_1614_);
lean_closure_set(v___f_1615_, 1, v_toPure_1605_);
lean_closure_set(v___f_1615_, 2, v_c_1606_);
lean_closure_set(v___f_1615_, 3, v_k_1607_);
lean_closure_set(v___f_1615_, 4, v_decl_1608_);
v___x_1616_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1609_, v_inst_1610_, v_inst_1611_, v_f_1612_, v_k_1607_);
v___x_1617_ = lean_apply_4(v_toBind_1613_, lean_box(0), lean_box(0), v___x_1616_, v___f_1615_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed(lean_object* v_toPure_1618_, lean_object* v_c_1619_, lean_object* v_k_1620_, lean_object* v_decl_1621_, lean_object* v_pu_1622_, lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_f_1625_, lean_object* v_toBind_1626_, lean_object* v_decl_1627_){
_start:
{
uint8_t v_pu_boxed_1628_; lean_object* v_res_1629_; 
v_pu_boxed_1628_ = lean_unbox(v_pu_1622_);
v_res_1629_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(v_toPure_1618_, v_c_1619_, v_k_1620_, v_decl_1621_, v_pu_boxed_1628_, v_inst_1623_, v_inst_1624_, v_f_1625_, v_toBind_1626_, v_decl_1627_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(uint8_t v_pu_1630_, lean_object* v_decl_1631_, lean_object* v_params_1632_, lean_object* v_inst_1633_, lean_object* v_toBind_1634_, lean_object* v___f_1635_, lean_object* v_inst_1636_, lean_object* v_f_1637_, lean_object* v_value_1638_, lean_object* v_____do__lift_1639_){
_start:
{
lean_object* v___x_1640_; lean_object* v___f_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1640_ = lean_box(v_pu_1630_);
lean_inc(v_toBind_1634_);
lean_inc(v_inst_1633_);
v___f_1641_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_1641_, 0, v___x_1640_);
lean_closure_set(v___f_1641_, 1, v_decl_1631_);
lean_closure_set(v___f_1641_, 2, v_____do__lift_1639_);
lean_closure_set(v___f_1641_, 3, v_params_1632_);
lean_closure_set(v___f_1641_, 4, v_inst_1633_);
lean_closure_set(v___f_1641_, 5, v_toBind_1634_);
lean_closure_set(v___f_1641_, 6, v___f_1635_);
v___x_1642_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1630_, v_inst_1633_, v_inst_1636_, v_f_1637_, v_value_1638_);
v___x_1643_ = lean_apply_4(v_toBind_1634_, lean_box(0), lean_box(0), v___x_1642_, v___f_1641_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed(lean_object* v_pu_1644_, lean_object* v_decl_1645_, lean_object* v_params_1646_, lean_object* v_inst_1647_, lean_object* v_toBind_1648_, lean_object* v___f_1649_, lean_object* v_inst_1650_, lean_object* v_f_1651_, lean_object* v_value_1652_, lean_object* v_____do__lift_1653_){
_start:
{
uint8_t v_pu_boxed_1654_; lean_object* v_res_1655_; 
v_pu_boxed_1654_ = lean_unbox(v_pu_1644_);
v_res_1655_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(v_pu_boxed_1654_, v_decl_1645_, v_params_1646_, v_inst_1647_, v_toBind_1648_, v___f_1649_, v_inst_1650_, v_f_1651_, v_value_1652_, v_____do__lift_1653_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(uint8_t v_pu_1656_, lean_object* v_decl_1657_, lean_object* v_inst_1658_, lean_object* v_toBind_1659_, lean_object* v___f_1660_, lean_object* v_inst_1661_, lean_object* v_f_1662_, lean_object* v_value_1663_, lean_object* v_type_1664_, lean_object* v_params_1665_){
_start:
{
lean_object* v___x_1666_; lean_object* v___f_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1666_ = lean_box(v_pu_1656_);
lean_inc(v_f_1662_);
lean_inc_ref(v_inst_1661_);
lean_inc(v_toBind_1659_);
v___f_1667_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed), 10, 9);
lean_closure_set(v___f_1667_, 0, v___x_1666_);
lean_closure_set(v___f_1667_, 1, v_decl_1657_);
lean_closure_set(v___f_1667_, 2, v_params_1665_);
lean_closure_set(v___f_1667_, 3, v_inst_1658_);
lean_closure_set(v___f_1667_, 4, v_toBind_1659_);
lean_closure_set(v___f_1667_, 5, v___f_1660_);
lean_closure_set(v___f_1667_, 6, v_inst_1661_);
lean_closure_set(v___f_1667_, 7, v_f_1662_);
lean_closure_set(v___f_1667_, 8, v_value_1663_);
v___x_1668_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1661_, v_f_1662_, v_type_1664_);
v___x_1669_ = lean_apply_4(v_toBind_1659_, lean_box(0), lean_box(0), v___x_1668_, v___f_1667_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed(lean_object* v_pu_1670_, lean_object* v_decl_1671_, lean_object* v_inst_1672_, lean_object* v_toBind_1673_, lean_object* v___f_1674_, lean_object* v_inst_1675_, lean_object* v_f_1676_, lean_object* v_value_1677_, lean_object* v_type_1678_, lean_object* v_params_1679_){
_start:
{
uint8_t v_pu_boxed_1680_; lean_object* v_res_1681_; 
v_pu_boxed_1680_ = lean_unbox(v_pu_1670_);
v_res_1681_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(v_pu_boxed_1680_, v_decl_1671_, v_inst_1672_, v_toBind_1673_, v___f_1674_, v_inst_1675_, v_f_1676_, v_value_1677_, v_type_1678_, v_params_1679_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(lean_object* v_toPure_1682_, lean_object* v_c_1683_, lean_object* v_k_1684_, lean_object* v_decl_1685_, uint8_t v_pu_1686_, lean_object* v_inst_1687_, lean_object* v_inst_1688_, lean_object* v_f_1689_, lean_object* v_toBind_1690_, lean_object* v_decl_1691_){
_start:
{
lean_object* v___f_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
lean_inc_ref(v_k_1684_);
v___f_1692_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_1692_, 0, v_decl_1691_);
lean_closure_set(v___f_1692_, 1, v_toPure_1682_);
lean_closure_set(v___f_1692_, 2, v_c_1683_);
lean_closure_set(v___f_1692_, 3, v_k_1684_);
lean_closure_set(v___f_1692_, 4, v_decl_1685_);
v___x_1693_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1686_, v_inst_1687_, v_inst_1688_, v_f_1689_, v_k_1684_);
v___x_1694_ = lean_apply_4(v_toBind_1690_, lean_box(0), lean_box(0), v___x_1693_, v___f_1692_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed(lean_object* v_toPure_1695_, lean_object* v_c_1696_, lean_object* v_k_1697_, lean_object* v_decl_1698_, lean_object* v_pu_1699_, lean_object* v_inst_1700_, lean_object* v_inst_1701_, lean_object* v_f_1702_, lean_object* v_toBind_1703_, lean_object* v_decl_1704_){
_start:
{
uint8_t v_pu_boxed_1705_; lean_object* v_res_1706_; 
v_pu_boxed_1705_ = lean_unbox(v_pu_1699_);
v_res_1706_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(v_toPure_1695_, v_c_1696_, v_k_1697_, v_decl_1698_, v_pu_boxed_1705_, v_inst_1700_, v_inst_1701_, v_f_1702_, v_toBind_1703_, v_decl_1704_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed(lean_object* v_pu_1707_, lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_f_1710_, lean_object* v_x_1711_){
_start:
{
uint8_t v_pu_boxed_1712_; lean_object* v_res_1713_; 
v_pu_boxed_1712_ = lean_unbox(v_pu_1707_);
v_res_1713_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(v_pu_boxed_1712_, v_inst_1708_, v_inst_1709_, v_f_1710_, v_x_1711_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(lean_object* v_____do__lift_1714_, lean_object* v_i_1715_, lean_object* v_toPure_1716_, lean_object* v_y_1717_, lean_object* v_k_1718_, lean_object* v_c_1719_, lean_object* v_fvarId_1720_, uint8_t v_pu_1721_, lean_object* v_inst_1722_, lean_object* v_inst_1723_, lean_object* v_f_1724_, lean_object* v_toBind_1725_, lean_object* v_____do__lift_1726_){
_start:
{
lean_object* v___f_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_inc_ref(v_k_1718_);
v___f_1727_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed), 9, 8);
lean_closure_set(v___f_1727_, 0, v_____do__lift_1714_);
lean_closure_set(v___f_1727_, 1, v_i_1715_);
lean_closure_set(v___f_1727_, 2, v_____do__lift_1726_);
lean_closure_set(v___f_1727_, 3, v_toPure_1716_);
lean_closure_set(v___f_1727_, 4, v_y_1717_);
lean_closure_set(v___f_1727_, 5, v_k_1718_);
lean_closure_set(v___f_1727_, 6, v_c_1719_);
lean_closure_set(v___f_1727_, 7, v_fvarId_1720_);
v___x_1728_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1721_, v_inst_1722_, v_inst_1723_, v_f_1724_, v_k_1718_);
v___x_1729_ = lean_apply_4(v_toBind_1725_, lean_box(0), lean_box(0), v___x_1728_, v___f_1727_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed(lean_object* v_____do__lift_1730_, lean_object* v_i_1731_, lean_object* v_toPure_1732_, lean_object* v_y_1733_, lean_object* v_k_1734_, lean_object* v_c_1735_, lean_object* v_fvarId_1736_, lean_object* v_pu_1737_, lean_object* v_inst_1738_, lean_object* v_inst_1739_, lean_object* v_f_1740_, lean_object* v_toBind_1741_, lean_object* v_____do__lift_1742_){
_start:
{
uint8_t v_pu_boxed_1743_; lean_object* v_res_1744_; 
v_pu_boxed_1743_ = lean_unbox(v_pu_1737_);
v_res_1744_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(v_____do__lift_1730_, v_i_1731_, v_toPure_1732_, v_y_1733_, v_k_1734_, v_c_1735_, v_fvarId_1736_, v_pu_boxed_1743_, v_inst_1738_, v_inst_1739_, v_f_1740_, v_toBind_1741_, v_____do__lift_1742_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(lean_object* v_i_1745_, lean_object* v_toPure_1746_, lean_object* v_y_1747_, lean_object* v_k_1748_, lean_object* v_c_1749_, lean_object* v_fvarId_1750_, uint8_t v_pu_1751_, lean_object* v_inst_1752_, lean_object* v_inst_1753_, lean_object* v_f_1754_, lean_object* v_toBind_1755_, lean_object* v_____do__lift_1756_){
_start:
{
lean_object* v___x_1757_; lean_object* v___f_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1757_ = lean_box(v_pu_1751_);
lean_inc(v_toBind_1755_);
lean_inc(v_f_1754_);
lean_inc_ref(v_inst_1753_);
lean_inc(v_y_1747_);
v___f_1758_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed), 13, 12);
lean_closure_set(v___f_1758_, 0, v_____do__lift_1756_);
lean_closure_set(v___f_1758_, 1, v_i_1745_);
lean_closure_set(v___f_1758_, 2, v_toPure_1746_);
lean_closure_set(v___f_1758_, 3, v_y_1747_);
lean_closure_set(v___f_1758_, 4, v_k_1748_);
lean_closure_set(v___f_1758_, 5, v_c_1749_);
lean_closure_set(v___f_1758_, 6, v_fvarId_1750_);
lean_closure_set(v___f_1758_, 7, v___x_1757_);
lean_closure_set(v___f_1758_, 8, v_inst_1752_);
lean_closure_set(v___f_1758_, 9, v_inst_1753_);
lean_closure_set(v___f_1758_, 10, v_f_1754_);
lean_closure_set(v___f_1758_, 11, v_toBind_1755_);
v___x_1759_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_1751_, v_inst_1753_, v_f_1754_, v_y_1747_);
v___x_1760_ = lean_apply_4(v_toBind_1755_, lean_box(0), lean_box(0), v___x_1759_, v___f_1758_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed(lean_object* v_i_1761_, lean_object* v_toPure_1762_, lean_object* v_y_1763_, lean_object* v_k_1764_, lean_object* v_c_1765_, lean_object* v_fvarId_1766_, lean_object* v_pu_1767_, lean_object* v_inst_1768_, lean_object* v_inst_1769_, lean_object* v_f_1770_, lean_object* v_toBind_1771_, lean_object* v_____do__lift_1772_){
_start:
{
uint8_t v_pu_boxed_1773_; lean_object* v_res_1774_; 
v_pu_boxed_1773_ = lean_unbox(v_pu_1767_);
v_res_1774_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(v_i_1761_, v_toPure_1762_, v_y_1763_, v_k_1764_, v_c_1765_, v_fvarId_1766_, v_pu_boxed_1773_, v_inst_1768_, v_inst_1769_, v_f_1770_, v_toBind_1771_, v_____do__lift_1772_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(lean_object* v_____do__lift_1775_, lean_object* v_i_1776_, lean_object* v_toPure_1777_, lean_object* v_y_1778_, lean_object* v_k_1779_, lean_object* v_c_1780_, lean_object* v_fvarId_1781_, uint8_t v_pu_1782_, lean_object* v_inst_1783_, lean_object* v_inst_1784_, lean_object* v_f_1785_, lean_object* v_toBind_1786_, lean_object* v_____do__lift_1787_){
_start:
{
lean_object* v___f_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_inc_ref(v_k_1779_);
v___f_1788_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed), 9, 8);
lean_closure_set(v___f_1788_, 0, v_____do__lift_1775_);
lean_closure_set(v___f_1788_, 1, v_i_1776_);
lean_closure_set(v___f_1788_, 2, v_____do__lift_1787_);
lean_closure_set(v___f_1788_, 3, v_toPure_1777_);
lean_closure_set(v___f_1788_, 4, v_y_1778_);
lean_closure_set(v___f_1788_, 5, v_k_1779_);
lean_closure_set(v___f_1788_, 6, v_c_1780_);
lean_closure_set(v___f_1788_, 7, v_fvarId_1781_);
v___x_1789_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1782_, v_inst_1783_, v_inst_1784_, v_f_1785_, v_k_1779_);
v___x_1790_ = lean_apply_4(v_toBind_1786_, lean_box(0), lean_box(0), v___x_1789_, v___f_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed(lean_object* v_____do__lift_1791_, lean_object* v_i_1792_, lean_object* v_toPure_1793_, lean_object* v_y_1794_, lean_object* v_k_1795_, lean_object* v_c_1796_, lean_object* v_fvarId_1797_, lean_object* v_pu_1798_, lean_object* v_inst_1799_, lean_object* v_inst_1800_, lean_object* v_f_1801_, lean_object* v_toBind_1802_, lean_object* v_____do__lift_1803_){
_start:
{
uint8_t v_pu_boxed_1804_; lean_object* v_res_1805_; 
v_pu_boxed_1804_ = lean_unbox(v_pu_1798_);
v_res_1805_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(v_____do__lift_1791_, v_i_1792_, v_toPure_1793_, v_y_1794_, v_k_1795_, v_c_1796_, v_fvarId_1797_, v_pu_boxed_1804_, v_inst_1799_, v_inst_1800_, v_f_1801_, v_toBind_1802_, v_____do__lift_1803_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(lean_object* v_i_1806_, lean_object* v_toPure_1807_, lean_object* v_y_1808_, lean_object* v_k_1809_, lean_object* v_c_1810_, lean_object* v_fvarId_1811_, uint8_t v_pu_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_f_1815_, lean_object* v_toBind_1816_, lean_object* v_____do__lift_1817_){
_start:
{
lean_object* v___x_1818_; lean_object* v___f_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1818_ = lean_box(v_pu_1812_);
lean_inc(v_toBind_1816_);
lean_inc(v_f_1815_);
lean_inc(v_y_1808_);
v___f_1819_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed), 13, 12);
lean_closure_set(v___f_1819_, 0, v_____do__lift_1817_);
lean_closure_set(v___f_1819_, 1, v_i_1806_);
lean_closure_set(v___f_1819_, 2, v_toPure_1807_);
lean_closure_set(v___f_1819_, 3, v_y_1808_);
lean_closure_set(v___f_1819_, 4, v_k_1809_);
lean_closure_set(v___f_1819_, 5, v_c_1810_);
lean_closure_set(v___f_1819_, 6, v_fvarId_1811_);
lean_closure_set(v___f_1819_, 7, v___x_1818_);
lean_closure_set(v___f_1819_, 8, v_inst_1813_);
lean_closure_set(v___f_1819_, 9, v_inst_1814_);
lean_closure_set(v___f_1819_, 10, v_f_1815_);
lean_closure_set(v___f_1819_, 11, v_toBind_1816_);
v___x_1820_ = lean_apply_1(v_f_1815_, v_y_1808_);
v___x_1821_ = lean_apply_4(v_toBind_1816_, lean_box(0), lean_box(0), v___x_1820_, v___f_1819_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed(lean_object* v_i_1822_, lean_object* v_toPure_1823_, lean_object* v_y_1824_, lean_object* v_k_1825_, lean_object* v_c_1826_, lean_object* v_fvarId_1827_, lean_object* v_pu_1828_, lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_f_1831_, lean_object* v_toBind_1832_, lean_object* v_____do__lift_1833_){
_start:
{
uint8_t v_pu_boxed_1834_; lean_object* v_res_1835_; 
v_pu_boxed_1834_ = lean_unbox(v_pu_1828_);
v_res_1835_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(v_i_1822_, v_toPure_1823_, v_y_1824_, v_k_1825_, v_c_1826_, v_fvarId_1827_, v_pu_boxed_1834_, v_inst_1829_, v_inst_1830_, v_f_1831_, v_toBind_1832_, v_____do__lift_1833_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(lean_object* v_____do__lift_1836_, lean_object* v_i_1837_, lean_object* v_offset_1838_, lean_object* v_____do__lift_1839_, lean_object* v_toPure_1840_, lean_object* v_y_1841_, lean_object* v_ty_1842_, lean_object* v_k_1843_, lean_object* v_c_1844_, lean_object* v_fvarId_1845_, uint8_t v_pu_1846_, lean_object* v_inst_1847_, lean_object* v_inst_1848_, lean_object* v_f_1849_, lean_object* v_toBind_1850_, lean_object* v_____do__lift_1851_){
_start:
{
lean_object* v___f_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
lean_inc_ref(v_k_1843_);
v___f_1852_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed), 12, 11);
lean_closure_set(v___f_1852_, 0, v_____do__lift_1836_);
lean_closure_set(v___f_1852_, 1, v_i_1837_);
lean_closure_set(v___f_1852_, 2, v_offset_1838_);
lean_closure_set(v___f_1852_, 3, v_____do__lift_1839_);
lean_closure_set(v___f_1852_, 4, v_____do__lift_1851_);
lean_closure_set(v___f_1852_, 5, v_toPure_1840_);
lean_closure_set(v___f_1852_, 6, v_y_1841_);
lean_closure_set(v___f_1852_, 7, v_ty_1842_);
lean_closure_set(v___f_1852_, 8, v_k_1843_);
lean_closure_set(v___f_1852_, 9, v_c_1844_);
lean_closure_set(v___f_1852_, 10, v_fvarId_1845_);
v___x_1853_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1846_, v_inst_1847_, v_inst_1848_, v_f_1849_, v_k_1843_);
v___x_1854_ = lean_apply_4(v_toBind_1850_, lean_box(0), lean_box(0), v___x_1853_, v___f_1852_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed(lean_object* v_____do__lift_1855_, lean_object* v_i_1856_, lean_object* v_offset_1857_, lean_object* v_____do__lift_1858_, lean_object* v_toPure_1859_, lean_object* v_y_1860_, lean_object* v_ty_1861_, lean_object* v_k_1862_, lean_object* v_c_1863_, lean_object* v_fvarId_1864_, lean_object* v_pu_1865_, lean_object* v_inst_1866_, lean_object* v_inst_1867_, lean_object* v_f_1868_, lean_object* v_toBind_1869_, lean_object* v_____do__lift_1870_){
_start:
{
uint8_t v_pu_boxed_1871_; lean_object* v_res_1872_; 
v_pu_boxed_1871_ = lean_unbox(v_pu_1865_);
v_res_1872_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(v_____do__lift_1855_, v_i_1856_, v_offset_1857_, v_____do__lift_1858_, v_toPure_1859_, v_y_1860_, v_ty_1861_, v_k_1862_, v_c_1863_, v_fvarId_1864_, v_pu_boxed_1871_, v_inst_1866_, v_inst_1867_, v_f_1868_, v_toBind_1869_, v_____do__lift_1870_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(lean_object* v_____do__lift_1873_, lean_object* v_i_1874_, lean_object* v_offset_1875_, lean_object* v_toPure_1876_, lean_object* v_y_1877_, lean_object* v_ty_1878_, lean_object* v_k_1879_, lean_object* v_c_1880_, lean_object* v_fvarId_1881_, uint8_t v_pu_1882_, lean_object* v_inst_1883_, lean_object* v_inst_1884_, lean_object* v_f_1885_, lean_object* v_toBind_1886_, lean_object* v_____do__lift_1887_){
_start:
{
lean_object* v___x_1888_; lean_object* v___f_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1888_ = lean_box(v_pu_1882_);
lean_inc(v_toBind_1886_);
lean_inc(v_f_1885_);
lean_inc_ref(v_inst_1884_);
lean_inc_ref(v_ty_1878_);
v___f_1889_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed), 16, 15);
lean_closure_set(v___f_1889_, 0, v_____do__lift_1873_);
lean_closure_set(v___f_1889_, 1, v_i_1874_);
lean_closure_set(v___f_1889_, 2, v_offset_1875_);
lean_closure_set(v___f_1889_, 3, v_____do__lift_1887_);
lean_closure_set(v___f_1889_, 4, v_toPure_1876_);
lean_closure_set(v___f_1889_, 5, v_y_1877_);
lean_closure_set(v___f_1889_, 6, v_ty_1878_);
lean_closure_set(v___f_1889_, 7, v_k_1879_);
lean_closure_set(v___f_1889_, 8, v_c_1880_);
lean_closure_set(v___f_1889_, 9, v_fvarId_1881_);
lean_closure_set(v___f_1889_, 10, v___x_1888_);
lean_closure_set(v___f_1889_, 11, v_inst_1883_);
lean_closure_set(v___f_1889_, 12, v_inst_1884_);
lean_closure_set(v___f_1889_, 13, v_f_1885_);
lean_closure_set(v___f_1889_, 14, v_toBind_1886_);
v___x_1890_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1884_, v_f_1885_, v_ty_1878_);
v___x_1891_ = lean_apply_4(v_toBind_1886_, lean_box(0), lean_box(0), v___x_1890_, v___f_1889_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed(lean_object* v_____do__lift_1892_, lean_object* v_i_1893_, lean_object* v_offset_1894_, lean_object* v_toPure_1895_, lean_object* v_y_1896_, lean_object* v_ty_1897_, lean_object* v_k_1898_, lean_object* v_c_1899_, lean_object* v_fvarId_1900_, lean_object* v_pu_1901_, lean_object* v_inst_1902_, lean_object* v_inst_1903_, lean_object* v_f_1904_, lean_object* v_toBind_1905_, lean_object* v_____do__lift_1906_){
_start:
{
uint8_t v_pu_boxed_1907_; lean_object* v_res_1908_; 
v_pu_boxed_1907_ = lean_unbox(v_pu_1901_);
v_res_1908_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(v_____do__lift_1892_, v_i_1893_, v_offset_1894_, v_toPure_1895_, v_y_1896_, v_ty_1897_, v_k_1898_, v_c_1899_, v_fvarId_1900_, v_pu_boxed_1907_, v_inst_1902_, v_inst_1903_, v_f_1904_, v_toBind_1905_, v_____do__lift_1906_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(lean_object* v_i_1909_, lean_object* v_offset_1910_, lean_object* v_toPure_1911_, lean_object* v_y_1912_, lean_object* v_ty_1913_, lean_object* v_k_1914_, lean_object* v_c_1915_, lean_object* v_fvarId_1916_, uint8_t v_pu_1917_, lean_object* v_inst_1918_, lean_object* v_inst_1919_, lean_object* v_f_1920_, lean_object* v_toBind_1921_, lean_object* v_____do__lift_1922_){
_start:
{
lean_object* v___x_1923_; lean_object* v___f_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1923_ = lean_box(v_pu_1917_);
lean_inc(v_toBind_1921_);
lean_inc(v_f_1920_);
lean_inc(v_y_1912_);
v___f_1924_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed), 15, 14);
lean_closure_set(v___f_1924_, 0, v_____do__lift_1922_);
lean_closure_set(v___f_1924_, 1, v_i_1909_);
lean_closure_set(v___f_1924_, 2, v_offset_1910_);
lean_closure_set(v___f_1924_, 3, v_toPure_1911_);
lean_closure_set(v___f_1924_, 4, v_y_1912_);
lean_closure_set(v___f_1924_, 5, v_ty_1913_);
lean_closure_set(v___f_1924_, 6, v_k_1914_);
lean_closure_set(v___f_1924_, 7, v_c_1915_);
lean_closure_set(v___f_1924_, 8, v_fvarId_1916_);
lean_closure_set(v___f_1924_, 9, v___x_1923_);
lean_closure_set(v___f_1924_, 10, v_inst_1918_);
lean_closure_set(v___f_1924_, 11, v_inst_1919_);
lean_closure_set(v___f_1924_, 12, v_f_1920_);
lean_closure_set(v___f_1924_, 13, v_toBind_1921_);
v___x_1925_ = lean_apply_1(v_f_1920_, v_y_1912_);
v___x_1926_ = lean_apply_4(v_toBind_1921_, lean_box(0), lean_box(0), v___x_1925_, v___f_1924_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed(lean_object* v_i_1927_, lean_object* v_offset_1928_, lean_object* v_toPure_1929_, lean_object* v_y_1930_, lean_object* v_ty_1931_, lean_object* v_k_1932_, lean_object* v_c_1933_, lean_object* v_fvarId_1934_, lean_object* v_pu_1935_, lean_object* v_inst_1936_, lean_object* v_inst_1937_, lean_object* v_f_1938_, lean_object* v_toBind_1939_, lean_object* v_____do__lift_1940_){
_start:
{
uint8_t v_pu_boxed_1941_; lean_object* v_res_1942_; 
v_pu_boxed_1941_ = lean_unbox(v_pu_1935_);
v_res_1942_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(v_i_1927_, v_offset_1928_, v_toPure_1929_, v_y_1930_, v_ty_1931_, v_k_1932_, v_c_1933_, v_fvarId_1934_, v_pu_boxed_1941_, v_inst_1936_, v_inst_1937_, v_f_1938_, v_toBind_1939_, v_____do__lift_1940_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(lean_object* v_cidx_1943_, lean_object* v_toPure_1944_, lean_object* v_k_1945_, lean_object* v_c_1946_, lean_object* v_fvarId_1947_, uint8_t v_pu_1948_, lean_object* v_inst_1949_, lean_object* v_inst_1950_, lean_object* v_f_1951_, lean_object* v_toBind_1952_, lean_object* v_____do__lift_1953_){
_start:
{
lean_object* v___f_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
lean_inc_ref(v_k_1945_);
v___f_1954_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27___boxed), 7, 6);
lean_closure_set(v___f_1954_, 0, v_____do__lift_1953_);
lean_closure_set(v___f_1954_, 1, v_cidx_1943_);
lean_closure_set(v___f_1954_, 2, v_toPure_1944_);
lean_closure_set(v___f_1954_, 3, v_k_1945_);
lean_closure_set(v___f_1954_, 4, v_c_1946_);
lean_closure_set(v___f_1954_, 5, v_fvarId_1947_);
v___x_1955_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1948_, v_inst_1949_, v_inst_1950_, v_f_1951_, v_k_1945_);
v___x_1956_ = lean_apply_4(v_toBind_1952_, lean_box(0), lean_box(0), v___x_1955_, v___f_1954_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed(lean_object* v_cidx_1957_, lean_object* v_toPure_1958_, lean_object* v_k_1959_, lean_object* v_c_1960_, lean_object* v_fvarId_1961_, lean_object* v_pu_1962_, lean_object* v_inst_1963_, lean_object* v_inst_1964_, lean_object* v_f_1965_, lean_object* v_toBind_1966_, lean_object* v_____do__lift_1967_){
_start:
{
uint8_t v_pu_boxed_1968_; lean_object* v_res_1969_; 
v_pu_boxed_1968_ = lean_unbox(v_pu_1962_);
v_res_1969_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(v_cidx_1957_, v_toPure_1958_, v_k_1959_, v_c_1960_, v_fvarId_1961_, v_pu_boxed_1968_, v_inst_1963_, v_inst_1964_, v_f_1965_, v_toBind_1966_, v_____do__lift_1967_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(lean_object* v_n_1970_, uint8_t v_check_1971_, uint8_t v_persistent_1972_, lean_object* v_toPure_1973_, lean_object* v_k_1974_, lean_object* v_c_1975_, lean_object* v_fvarId_1976_, uint8_t v_pu_1977_, lean_object* v_inst_1978_, lean_object* v_inst_1979_, lean_object* v_f_1980_, lean_object* v_toBind_1981_, lean_object* v_____do__lift_1982_){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___f_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1983_ = lean_box(v_check_1971_);
v___x_1984_ = lean_box(v_persistent_1972_);
lean_inc_ref(v_k_1974_);
v___f_1985_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29___boxed), 9, 8);
lean_closure_set(v___f_1985_, 0, v_____do__lift_1982_);
lean_closure_set(v___f_1985_, 1, v_n_1970_);
lean_closure_set(v___f_1985_, 2, v___x_1983_);
lean_closure_set(v___f_1985_, 3, v___x_1984_);
lean_closure_set(v___f_1985_, 4, v_toPure_1973_);
lean_closure_set(v___f_1985_, 5, v_k_1974_);
lean_closure_set(v___f_1985_, 6, v_c_1975_);
lean_closure_set(v___f_1985_, 7, v_fvarId_1976_);
v___x_1986_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1977_, v_inst_1978_, v_inst_1979_, v_f_1980_, v_k_1974_);
v___x_1987_ = lean_apply_4(v_toBind_1981_, lean_box(0), lean_box(0), v___x_1986_, v___f_1985_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed(lean_object* v_n_1988_, lean_object* v_check_1989_, lean_object* v_persistent_1990_, lean_object* v_toPure_1991_, lean_object* v_k_1992_, lean_object* v_c_1993_, lean_object* v_fvarId_1994_, lean_object* v_pu_1995_, lean_object* v_inst_1996_, lean_object* v_inst_1997_, lean_object* v_f_1998_, lean_object* v_toBind_1999_, lean_object* v_____do__lift_2000_){
_start:
{
uint8_t v_check_2471__boxed_2001_; uint8_t v_persistent_2472__boxed_2002_; uint8_t v_pu_boxed_2003_; lean_object* v_res_2004_; 
v_check_2471__boxed_2001_ = lean_unbox(v_check_1989_);
v_persistent_2472__boxed_2002_ = lean_unbox(v_persistent_1990_);
v_pu_boxed_2003_ = lean_unbox(v_pu_1995_);
v_res_2004_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(v_n_1988_, v_check_2471__boxed_2001_, v_persistent_2472__boxed_2002_, v_toPure_1991_, v_k_1992_, v_c_1993_, v_fvarId_1994_, v_pu_boxed_2003_, v_inst_1996_, v_inst_1997_, v_f_1998_, v_toBind_1999_, v_____do__lift_2000_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(lean_object* v_n_2005_, uint8_t v_check_2006_, uint8_t v_persistent_2007_, lean_object* v_objs_x3f_2008_, lean_object* v_toPure_2009_, lean_object* v_k_2010_, lean_object* v_c_2011_, lean_object* v_fvarId_2012_, uint8_t v_pu_2013_, lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_f_2016_, lean_object* v_toBind_2017_, lean_object* v_____do__lift_2018_){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___f_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2019_ = lean_box(v_check_2006_);
v___x_2020_ = lean_box(v_persistent_2007_);
lean_inc_ref(v_k_2010_);
v___f_2021_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed), 10, 9);
lean_closure_set(v___f_2021_, 0, v_____do__lift_2018_);
lean_closure_set(v___f_2021_, 1, v_n_2005_);
lean_closure_set(v___f_2021_, 2, v___x_2019_);
lean_closure_set(v___f_2021_, 3, v___x_2020_);
lean_closure_set(v___f_2021_, 4, v_objs_x3f_2008_);
lean_closure_set(v___f_2021_, 5, v_toPure_2009_);
lean_closure_set(v___f_2021_, 6, v_k_2010_);
lean_closure_set(v___f_2021_, 7, v_c_2011_);
lean_closure_set(v___f_2021_, 8, v_fvarId_2012_);
v___x_2022_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2013_, v_inst_2014_, v_inst_2015_, v_f_2016_, v_k_2010_);
v___x_2023_ = lean_apply_4(v_toBind_2017_, lean_box(0), lean_box(0), v___x_2022_, v___f_2021_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed(lean_object* v_n_2024_, lean_object* v_check_2025_, lean_object* v_persistent_2026_, lean_object* v_objs_x3f_2027_, lean_object* v_toPure_2028_, lean_object* v_k_2029_, lean_object* v_c_2030_, lean_object* v_fvarId_2031_, lean_object* v_pu_2032_, lean_object* v_inst_2033_, lean_object* v_inst_2034_, lean_object* v_f_2035_, lean_object* v_toBind_2036_, lean_object* v_____do__lift_2037_){
_start:
{
uint8_t v_check_2482__boxed_2038_; uint8_t v_persistent_2483__boxed_2039_; uint8_t v_pu_boxed_2040_; lean_object* v_res_2041_; 
v_check_2482__boxed_2038_ = lean_unbox(v_check_2025_);
v_persistent_2483__boxed_2039_ = lean_unbox(v_persistent_2026_);
v_pu_boxed_2040_ = lean_unbox(v_pu_2032_);
v_res_2041_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(v_n_2024_, v_check_2482__boxed_2038_, v_persistent_2483__boxed_2039_, v_objs_x3f_2027_, v_toPure_2028_, v_k_2029_, v_c_2030_, v_fvarId_2031_, v_pu_boxed_2040_, v_inst_2033_, v_inst_2034_, v_f_2035_, v_toBind_2036_, v_____do__lift_2037_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(lean_object* v_toPure_2042_, lean_object* v_c_2043_, lean_object* v_fvarId_2044_, lean_object* v_k_2045_, uint8_t v_pu_2046_, lean_object* v_inst_2047_, lean_object* v_inst_2048_, lean_object* v_f_2049_, lean_object* v_toBind_2050_, lean_object* v_____do__lift_2051_){
_start:
{
lean_object* v___f_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
lean_inc_ref(v_k_2045_);
v___f_2052_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed), 6, 5);
lean_closure_set(v___f_2052_, 0, v_____do__lift_2051_);
lean_closure_set(v___f_2052_, 1, v_toPure_2042_);
lean_closure_set(v___f_2052_, 2, v_c_2043_);
lean_closure_set(v___f_2052_, 3, v_fvarId_2044_);
lean_closure_set(v___f_2052_, 4, v_k_2045_);
v___x_2053_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2046_, v_inst_2047_, v_inst_2048_, v_f_2049_, v_k_2045_);
v___x_2054_ = lean_apply_4(v_toBind_2050_, lean_box(0), lean_box(0), v___x_2053_, v___f_2052_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed(lean_object* v_toPure_2055_, lean_object* v_c_2056_, lean_object* v_fvarId_2057_, lean_object* v_k_2058_, lean_object* v_pu_2059_, lean_object* v_inst_2060_, lean_object* v_inst_2061_, lean_object* v_f_2062_, lean_object* v_toBind_2063_, lean_object* v_____do__lift_2064_){
_start:
{
uint8_t v_pu_boxed_2065_; lean_object* v_res_2066_; 
v_pu_boxed_2065_ = lean_unbox(v_pu_2059_);
v_res_2066_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(v_toPure_2055_, v_c_2056_, v_fvarId_2057_, v_k_2058_, v_pu_boxed_2065_, v_inst_2060_, v_inst_2061_, v_f_2062_, v_toBind_2063_, v_____do__lift_2064_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(uint8_t v_pu_2067_, lean_object* v_inst_2068_, lean_object* v_inst_2069_, lean_object* v_f_2070_, lean_object* v_c_2071_){
_start:
{
switch(lean_obj_tag(v_c_2071_))
{
case 0:
{
lean_object* v_toApplicative_2072_; lean_object* v_toBind_2073_; lean_object* v_toPure_2074_; lean_object* v_decl_2075_; lean_object* v_k_2076_; lean_object* v___x_2077_; lean_object* v___f_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v_toApplicative_2072_ = lean_ctor_get(v_inst_2069_, 0);
v_toBind_2073_ = lean_ctor_get(v_inst_2069_, 1);
lean_inc_n(v_toBind_2073_, 2);
v_toPure_2074_ = lean_ctor_get(v_toApplicative_2072_, 1);
v_decl_2075_ = lean_ctor_get(v_c_2071_, 0);
lean_inc_ref_n(v_decl_2075_, 2);
v_k_2076_ = lean_ctor_get(v_c_2071_, 1);
lean_inc_ref(v_k_2076_);
v___x_2077_ = lean_box(v_pu_2067_);
lean_inc(v_f_2070_);
lean_inc_ref(v_inst_2069_);
lean_inc(v_inst_2068_);
lean_inc(v_toPure_2074_);
v___f_2078_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_2078_, 0, v_toPure_2074_);
lean_closure_set(v___f_2078_, 1, v_c_2071_);
lean_closure_set(v___f_2078_, 2, v_k_2076_);
lean_closure_set(v___f_2078_, 3, v_decl_2075_);
lean_closure_set(v___f_2078_, 4, v___x_2077_);
lean_closure_set(v___f_2078_, 5, v_inst_2068_);
lean_closure_set(v___f_2078_, 6, v_inst_2069_);
lean_closure_set(v___f_2078_, 7, v_f_2070_);
lean_closure_set(v___f_2078_, 8, v_toBind_2073_);
v___x_2079_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_2067_, v_inst_2068_, v_inst_2069_, v_f_2070_, v_decl_2075_);
v___x_2080_ = lean_apply_4(v_toBind_2073_, lean_box(0), lean_box(0), v___x_2079_, v___f_2078_);
return v___x_2080_;
}
case 1:
{
lean_object* v_toApplicative_2081_; lean_object* v_decl_2082_; lean_object* v_toBind_2083_; lean_object* v_toPure_2084_; lean_object* v_k_2085_; lean_object* v_params_2086_; lean_object* v_type_2087_; lean_object* v_value_2088_; lean_object* v___x_2089_; lean_object* v___f_2090_; lean_object* v___x_2091_; lean_object* v___f_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; size_t v_sz_2095_; size_t v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_toApplicative_2081_ = lean_ctor_get(v_inst_2069_, 0);
v_decl_2082_ = lean_ctor_get(v_c_2071_, 0);
lean_inc_ref_n(v_decl_2082_, 2);
v_toBind_2083_ = lean_ctor_get(v_inst_2069_, 1);
lean_inc_n(v_toBind_2083_, 3);
v_toPure_2084_ = lean_ctor_get(v_toApplicative_2081_, 1);
v_k_2085_ = lean_ctor_get(v_c_2071_, 1);
lean_inc_ref(v_k_2085_);
v_params_2086_ = lean_ctor_get(v_decl_2082_, 2);
lean_inc_ref(v_params_2086_);
v_type_2087_ = lean_ctor_get(v_decl_2082_, 3);
lean_inc_ref(v_type_2087_);
v_value_2088_ = lean_ctor_get(v_decl_2082_, 4);
lean_inc_ref(v_value_2088_);
v___x_2089_ = lean_box(v_pu_2067_);
lean_inc_n(v_f_2070_, 2);
lean_inc_ref_n(v_inst_2069_, 3);
lean_inc_n(v_inst_2068_, 2);
lean_inc(v_toPure_2084_);
v___f_2090_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_2090_, 0, v_toPure_2084_);
lean_closure_set(v___f_2090_, 1, v_c_2071_);
lean_closure_set(v___f_2090_, 2, v_k_2085_);
lean_closure_set(v___f_2090_, 3, v_decl_2082_);
lean_closure_set(v___f_2090_, 4, v___x_2089_);
lean_closure_set(v___f_2090_, 5, v_inst_2068_);
lean_closure_set(v___f_2090_, 6, v_inst_2069_);
lean_closure_set(v___f_2090_, 7, v_f_2070_);
lean_closure_set(v___f_2090_, 8, v_toBind_2083_);
v___x_2091_ = lean_box(v_pu_2067_);
v___f_2092_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_2092_, 0, v___x_2091_);
lean_closure_set(v___f_2092_, 1, v_decl_2082_);
lean_closure_set(v___f_2092_, 2, v_inst_2068_);
lean_closure_set(v___f_2092_, 3, v_toBind_2083_);
lean_closure_set(v___f_2092_, 4, v___f_2090_);
lean_closure_set(v___f_2092_, 5, v_inst_2069_);
lean_closure_set(v___f_2092_, 6, v_f_2070_);
lean_closure_set(v___f_2092_, 7, v_value_2088_);
lean_closure_set(v___f_2092_, 8, v_type_2087_);
v___x_2093_ = lean_box(v_pu_2067_);
v___x_2094_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2094_, 0, lean_box(0));
lean_closure_set(v___x_2094_, 1, v___x_2093_);
lean_closure_set(v___x_2094_, 2, v_inst_2068_);
lean_closure_set(v___x_2094_, 3, v_inst_2069_);
lean_closure_set(v___x_2094_, 4, v_f_2070_);
v_sz_2095_ = lean_array_size(v_params_2086_);
v___x_2096_ = ((size_t)0ULL);
v___x_2097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2069_, v___x_2094_, v_sz_2095_, v___x_2096_, v_params_2086_);
v___x_2098_ = lean_apply_4(v_toBind_2083_, lean_box(0), lean_box(0), v___x_2097_, v___f_2092_);
return v___x_2098_;
}
case 2:
{
lean_object* v_toApplicative_2099_; lean_object* v_decl_2100_; lean_object* v_toBind_2101_; lean_object* v_toPure_2102_; lean_object* v_k_2103_; lean_object* v_params_2104_; lean_object* v_type_2105_; lean_object* v_value_2106_; lean_object* v___x_2107_; lean_object* v___f_2108_; lean_object* v___x_2109_; lean_object* v___f_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; size_t v_sz_2113_; size_t v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v_toApplicative_2099_ = lean_ctor_get(v_inst_2069_, 0);
v_decl_2100_ = lean_ctor_get(v_c_2071_, 0);
lean_inc_ref_n(v_decl_2100_, 2);
v_toBind_2101_ = lean_ctor_get(v_inst_2069_, 1);
lean_inc_n(v_toBind_2101_, 3);
v_toPure_2102_ = lean_ctor_get(v_toApplicative_2099_, 1);
v_k_2103_ = lean_ctor_get(v_c_2071_, 1);
lean_inc_ref(v_k_2103_);
v_params_2104_ = lean_ctor_get(v_decl_2100_, 2);
lean_inc_ref(v_params_2104_);
v_type_2105_ = lean_ctor_get(v_decl_2100_, 3);
lean_inc_ref(v_type_2105_);
v_value_2106_ = lean_ctor_get(v_decl_2100_, 4);
lean_inc_ref(v_value_2106_);
v___x_2107_ = lean_box(v_pu_2067_);
lean_inc_n(v_f_2070_, 2);
lean_inc_ref_n(v_inst_2069_, 3);
lean_inc_n(v_inst_2068_, 2);
lean_inc(v_toPure_2102_);
v___f_2108_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed), 10, 9);
lean_closure_set(v___f_2108_, 0, v_toPure_2102_);
lean_closure_set(v___f_2108_, 1, v_c_2071_);
lean_closure_set(v___f_2108_, 2, v_k_2103_);
lean_closure_set(v___f_2108_, 3, v_decl_2100_);
lean_closure_set(v___f_2108_, 4, v___x_2107_);
lean_closure_set(v___f_2108_, 5, v_inst_2068_);
lean_closure_set(v___f_2108_, 6, v_inst_2069_);
lean_closure_set(v___f_2108_, 7, v_f_2070_);
lean_closure_set(v___f_2108_, 8, v_toBind_2101_);
v___x_2109_ = lean_box(v_pu_2067_);
v___f_2110_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_2110_, 0, v___x_2109_);
lean_closure_set(v___f_2110_, 1, v_decl_2100_);
lean_closure_set(v___f_2110_, 2, v_inst_2068_);
lean_closure_set(v___f_2110_, 3, v_toBind_2101_);
lean_closure_set(v___f_2110_, 4, v___f_2108_);
lean_closure_set(v___f_2110_, 5, v_inst_2069_);
lean_closure_set(v___f_2110_, 6, v_f_2070_);
lean_closure_set(v___f_2110_, 7, v_value_2106_);
lean_closure_set(v___f_2110_, 8, v_type_2105_);
v___x_2111_ = lean_box(v_pu_2067_);
v___x_2112_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2112_, 0, lean_box(0));
lean_closure_set(v___x_2112_, 1, v___x_2111_);
lean_closure_set(v___x_2112_, 2, v_inst_2068_);
lean_closure_set(v___x_2112_, 3, v_inst_2069_);
lean_closure_set(v___x_2112_, 4, v_f_2070_);
v_sz_2113_ = lean_array_size(v_params_2104_);
v___x_2114_ = ((size_t)0ULL);
v___x_2115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2069_, v___x_2112_, v_sz_2113_, v___x_2114_, v_params_2104_);
v___x_2116_ = lean_apply_4(v_toBind_2101_, lean_box(0), lean_box(0), v___x_2115_, v___f_2110_);
return v___x_2116_;
}
case 3:
{
lean_object* v_toApplicative_2117_; lean_object* v_toBind_2118_; lean_object* v_toPure_2119_; lean_object* v_fvarId_2120_; lean_object* v_args_2121_; lean_object* v___x_2122_; lean_object* v___f_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v_toApplicative_2117_ = lean_ctor_get(v_inst_2069_, 0);
v_toBind_2118_ = lean_ctor_get(v_inst_2069_, 1);
lean_inc_n(v_toBind_2118_, 2);
v_toPure_2119_ = lean_ctor_get(v_toApplicative_2117_, 1);
lean_inc(v_toPure_2119_);
v_fvarId_2120_ = lean_ctor_get(v_c_2071_, 0);
lean_inc_n(v_fvarId_2120_, 2);
v_args_2121_ = lean_ctor_get(v_c_2071_, 1);
lean_inc_ref(v_args_2121_);
v___x_2122_ = lean_box(v_pu_2067_);
lean_inc(v_f_2070_);
v___f_2123_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_2123_, 0, v_toPure_2119_);
lean_closure_set(v___f_2123_, 1, v_c_2071_);
lean_closure_set(v___f_2123_, 2, v_fvarId_2120_);
lean_closure_set(v___f_2123_, 3, v_args_2121_);
lean_closure_set(v___f_2123_, 4, v___x_2122_);
lean_closure_set(v___f_2123_, 5, v_inst_2068_);
lean_closure_set(v___f_2123_, 6, v_inst_2069_);
lean_closure_set(v___f_2123_, 7, v_f_2070_);
lean_closure_set(v___f_2123_, 8, v_toBind_2118_);
v___x_2124_ = lean_apply_1(v_f_2070_, v_fvarId_2120_);
v___x_2125_ = lean_apply_4(v_toBind_2118_, lean_box(0), lean_box(0), v___x_2124_, v___f_2123_);
return v___x_2125_;
}
case 4:
{
lean_object* v_toApplicative_2126_; lean_object* v_cases_2127_; lean_object* v_toBind_2128_; lean_object* v_toPure_2129_; lean_object* v_typeName_2130_; lean_object* v_resultType_2131_; lean_object* v_discr_2132_; lean_object* v_alts_2133_; lean_object* v___x_2134_; lean_object* v___f_2135_; lean_object* v___f_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v_toApplicative_2126_ = lean_ctor_get(v_inst_2069_, 0);
v_cases_2127_ = lean_ctor_get(v_c_2071_, 0);
v_toBind_2128_ = lean_ctor_get(v_inst_2069_, 1);
lean_inc_n(v_toBind_2128_, 2);
v_toPure_2129_ = lean_ctor_get(v_toApplicative_2126_, 1);
v_typeName_2130_ = lean_ctor_get(v_cases_2127_, 0);
lean_inc(v_typeName_2130_);
v_resultType_2131_ = lean_ctor_get(v_cases_2127_, 1);
lean_inc_ref_n(v_resultType_2131_, 2);
v_discr_2132_ = lean_ctor_get(v_cases_2127_, 2);
lean_inc(v_discr_2132_);
v_alts_2133_ = lean_ctor_get(v_cases_2127_, 3);
lean_inc_ref(v_alts_2133_);
v___x_2134_ = lean_box(v_pu_2067_);
lean_inc_n(v_f_2070_, 2);
lean_inc_ref_n(v_inst_2069_, 2);
v___f_2135_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed), 5, 4);
lean_closure_set(v___f_2135_, 0, v___x_2134_);
lean_closure_set(v___f_2135_, 1, v_inst_2068_);
lean_closure_set(v___f_2135_, 2, v_inst_2069_);
lean_closure_set(v___f_2135_, 3, v_f_2070_);
lean_inc(v_toPure_2129_);
v___f_2136_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14), 11, 10);
lean_closure_set(v___f_2136_, 0, v_typeName_2130_);
lean_closure_set(v___f_2136_, 1, v_toPure_2129_);
lean_closure_set(v___f_2136_, 2, v_discr_2132_);
lean_closure_set(v___f_2136_, 3, v_c_2071_);
lean_closure_set(v___f_2136_, 4, v_alts_2133_);
lean_closure_set(v___f_2136_, 5, v_resultType_2131_);
lean_closure_set(v___f_2136_, 6, v_inst_2069_);
lean_closure_set(v___f_2136_, 7, v___f_2135_);
lean_closure_set(v___f_2136_, 8, v_toBind_2128_);
lean_closure_set(v___f_2136_, 9, v_f_2070_);
v___x_2137_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2069_, v_f_2070_, v_resultType_2131_);
v___x_2138_ = lean_apply_4(v_toBind_2128_, lean_box(0), lean_box(0), v___x_2137_, v___f_2136_);
return v___x_2138_;
}
case 5:
{
lean_object* v_toApplicative_2139_; lean_object* v_toBind_2140_; lean_object* v_toPure_2141_; lean_object* v_fvarId_2142_; lean_object* v___f_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v_toApplicative_2139_ = lean_ctor_get(v_inst_2069_, 0);
lean_inc_ref(v_toApplicative_2139_);
lean_dec(v_inst_2068_);
v_toBind_2140_ = lean_ctor_get(v_inst_2069_, 1);
lean_inc(v_toBind_2140_);
lean_dec_ref(v_inst_2069_);
v_toPure_2141_ = lean_ctor_get(v_toApplicative_2139_, 1);
lean_inc(v_toPure_2141_);
lean_dec_ref(v_toApplicative_2139_);
v_fvarId_2142_ = lean_ctor_get(v_c_2071_, 0);
lean_inc_n(v_fvarId_2142_, 2);
v___f_2143_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed), 4, 3);
lean_closure_set(v___f_2143_, 0, v_fvarId_2142_);
lean_closure_set(v___f_2143_, 1, v_toPure_2141_);
lean_closure_set(v___f_2143_, 2, v_c_2071_);
v___x_2144_ = lean_apply_1(v_f_2070_, v_fvarId_2142_);
v___x_2145_ = lean_apply_4(v_toBind_2140_, lean_box(0), lean_box(0), v___x_2144_, v___f_2143_);
return v___x_2145_;
}
case 6:
{
lean_object* v_toApplicative_2146_; lean_object* v_toBind_2147_; lean_object* v_toPure_2148_; lean_object* v_type_2149_; lean_object* v___f_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v_toApplicative_2146_ = lean_ctor_get(v_inst_2069_, 0);
lean_dec(v_inst_2068_);
v_toBind_2147_ = lean_ctor_get(v_inst_2069_, 1);
lean_inc(v_toBind_2147_);
v_toPure_2148_ = lean_ctor_get(v_toApplicative_2146_, 1);
v_type_2149_ = lean_ctor_get(v_c_2071_, 0);
lean_inc_ref_n(v_type_2149_, 2);
lean_inc(v_toPure_2148_);
v___f_2150_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed), 4, 3);
lean_closure_set(v___f_2150_, 0, v_type_2149_);
lean_closure_set(v___f_2150_, 1, v_toPure_2148_);
lean_closure_set(v___f_2150_, 2, v_c_2071_);
v___x_2151_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2069_, v_f_2070_, v_type_2149_);
v___x_2152_ = lean_apply_4(v_toBind_2147_, lean_box(0), lean_box(0), v___x_2151_, v___f_2150_);
return v___x_2152_;
}
case 7:
{
lean_object* v_toApplicative_2153_; lean_object* v_toBind_2154_; lean_object* v_toPure_2155_; lean_object* v_fvarId_2156_; lean_object* v_i_2157_; lean_object* v_y_2158_; lean_object* v_k_2159_; lean_object* v___x_2160_; lean_object* v___f_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v_toApplicative_2153_ = lean_ctor_get(v_inst_2069_, 0);
v_toBind_2154_ = lean_ctor_get(v_inst_2069_, 1);
lean_inc_n(v_toBind_2154_, 2);
v_toPure_2155_ = lean_ctor_get(v_toApplicative_2153_, 1);
lean_inc(v_toPure_2155_);
v_fvarId_2156_ = lean_ctor_get(v_c_2071_, 0);
lean_inc_n(v_fvarId_2156_, 2);
v_i_2157_ = lean_ctor_get(v_c_2071_, 1);
lean_inc(v_i_2157_);
v_y_2158_ = lean_ctor_get(v_c_2071_, 2);
lean_inc(v_y_2158_);
v_k_2159_ = lean_ctor_get(v_c_2071_, 3);
lean_inc_ref(v_k_2159_);
v___x_2160_ = lean_box(v_pu_2067_);
lean_inc(v_f_2070_);
v___f_2161_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed), 12, 11);
lean_closure_set(v___f_2161_, 0, v_i_2157_);
lean_closure_set(v___f_2161_, 1, v_toPure_2155_);
lean_closure_set(v___f_2161_, 2, v_y_2158_);
lean_closure_set(v___f_2161_, 3, v_k_2159_);
lean_closure_set(v___f_2161_, 4, v_c_2071_);
lean_closure_set(v___f_2161_, 5, v_fvarId_2156_);
lean_closure_set(v___f_2161_, 6, v___x_2160_);
lean_closure_set(v___f_2161_, 7, v_inst_2068_);
lean_closure_set(v___f_2161_, 8, v_inst_2069_);
lean_closure_set(v___f_2161_, 9, v_f_2070_);
lean_closure_set(v___f_2161_, 10, v_toBind_2154_);
v___x_2162_ = lean_apply_1(v_f_2070_, v_fvarId_2156_);
v___x_2163_ = lean_apply_4(v_toBind_2154_, lean_box(0), lean_box(0), v___x_2162_, v___f_2161_);
return v___x_2163_;
}
case 8:
{
lean_object* v_toApplicative_2164_; lean_object* v_toBind_2165_; lean_object* v_toPure_2166_; lean_object* v_fvarId_2167_; lean_object* v_i_2168_; lean_object* v_y_2169_; lean_object* v_k_2170_; lean_object* v___x_2171_; lean_object* v___f_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_toApplicative_2164_ = lean_ctor_get(v_inst_2069_, 0);
v_toBind_2165_ = lean_ctor_get(v_inst_2069_, 1);
lean_inc_n(v_toBind_2165_, 2);
v_toPure_2166_ = lean_ctor_get(v_toApplicative_2164_, 1);
lean_inc(v_toPure_2166_);
v_fvarId_2167_ = lean_ctor_get(v_c_2071_, 0);
lean_inc_n(v_fvarId_2167_, 2);
v_i_2168_ = lean_ctor_get(v_c_2071_, 1);
lean_inc(v_i_2168_);
v_y_2169_ = lean_ctor_get(v_c_2071_, 2);
lean_inc(v_y_2169_);
v_k_2170_ = lean_ctor_get(v_c_2071_, 3);
lean_inc_ref(v_k_2170_);
v___x_2171_ = lean_box(v_pu_2067_);
lean_inc(v_f_2070_);
v___f_2172_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed), 12, 11);
lean_closure_set(v___f_2172_, 0, v_i_2168_);
lean_closure_set(v___f_2172_, 1, v_toPure_2166_);
lean_closure_set(v___f_2172_, 2, v_y_2169_);
lean_closure_set(v___f_2172_, 3, v_k_2170_);
lean_closure_set(v___f_2172_, 4, v_c_2071_);
lean_closure_set(v___f_2172_, 5, v_fvarId_2167_);
lean_closure_set(v___f_2172_, 6, v___x_2171_);
lean_closure_set(v___f_2172_, 7, v_inst_2068_);
lean_closure_set(v___f_2172_, 8, v_inst_2069_);
lean_closure_set(v___f_2172_, 9, v_f_2070_);
lean_closure_set(v___f_2172_, 10, v_toBind_2165_);
v___x_2173_ = lean_apply_1(v_f_2070_, v_fvarId_2167_);
v___x_2174_ = lean_apply_4(v_toBind_2165_, lean_box(0), lean_box(0), v___x_2173_, v___f_2172_);
return v___x_2174_;
}
case 9:
{
lean_object* v_toApplicative_2175_; lean_object* v_toBind_2176_; lean_object* v_toPure_2177_; lean_object* v_fvarId_2178_; lean_object* v_i_2179_; lean_object* v_offset_2180_; lean_object* v_y_2181_; lean_object* v_ty_2182_; lean_object* v_k_2183_; lean_object* v___x_2184_; lean_object* v___f_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v_toApplicative_2175_ = lean_ctor_get(v_inst_2069_, 0);
v_toBind_2176_ = lean_ctor_get(v_inst_2069_, 1);
lean_inc_n(v_toBind_2176_, 2);
v_toPure_2177_ = lean_ctor_get(v_toApplicative_2175_, 1);
lean_inc(v_toPure_2177_);
v_fvarId_2178_ = lean_ctor_get(v_c_2071_, 0);
lean_inc_n(v_fvarId_2178_, 2);
v_i_2179_ = lean_ctor_get(v_c_2071_, 1);
lean_inc(v_i_2179_);
v_offset_2180_ = lean_ctor_get(v_c_2071_, 2);
lean_inc(v_offset_2180_);
v_y_2181_ = lean_ctor_get(v_c_2071_, 3);
lean_inc(v_y_2181_);
v_ty_2182_ = lean_ctor_get(v_c_2071_, 4);
lean_inc_ref(v_ty_2182_);
v_k_2183_ = lean_ctor_get(v_c_2071_, 5);
lean_inc_ref(v_k_2183_);
v___x_2184_ = lean_box(v_pu_2067_);
lean_inc(v_f_2070_);
v___f_2185_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed), 14, 13);
lean_closure_set(v___f_2185_, 0, v_i_2179_);
lean_closure_set(v___f_2185_, 1, v_offset_2180_);
lean_closure_set(v___f_2185_, 2, v_toPure_2177_);
lean_closure_set(v___f_2185_, 3, v_y_2181_);
lean_closure_set(v___f_2185_, 4, v_ty_2182_);
lean_closure_set(v___f_2185_, 5, v_k_2183_);
lean_closure_set(v___f_2185_, 6, v_c_2071_);
lean_closure_set(v___f_2185_, 7, v_fvarId_2178_);
lean_closure_set(v___f_2185_, 8, v___x_2184_);
lean_closure_set(v___f_2185_, 9, v_inst_2068_);
lean_closure_set(v___f_2185_, 10, v_inst_2069_);
lean_closure_set(v___f_2185_, 11, v_f_2070_);
lean_closure_set(v___f_2185_, 12, v_toBind_2176_);
v___x_2186_ = lean_apply_1(v_f_2070_, v_fvarId_2178_);
v___x_2187_ = lean_apply_4(v_toBind_2176_, lean_box(0), lean_box(0), v___x_2186_, v___f_2185_);
return v___x_2187_;
}
case 10:
{
lean_object* v_toApplicative_2188_; lean_object* v_toBind_2189_; lean_object* v_toPure_2190_; lean_object* v_fvarId_2191_; lean_object* v_cidx_2192_; lean_object* v_k_2193_; lean_object* v___x_2194_; lean_object* v___f_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v_toApplicative_2188_ = lean_ctor_get(v_inst_2069_, 0);
v_toBind_2189_ = lean_ctor_get(v_inst_2069_, 1);
lean_inc_n(v_toBind_2189_, 2);
v_toPure_2190_ = lean_ctor_get(v_toApplicative_2188_, 1);
lean_inc(v_toPure_2190_);
v_fvarId_2191_ = lean_ctor_get(v_c_2071_, 0);
lean_inc_n(v_fvarId_2191_, 2);
v_cidx_2192_ = lean_ctor_get(v_c_2071_, 1);
lean_inc(v_cidx_2192_);
v_k_2193_ = lean_ctor_get(v_c_2071_, 2);
lean_inc_ref(v_k_2193_);
v___x_2194_ = lean_box(v_pu_2067_);
lean_inc(v_f_2070_);
v___f_2195_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed), 11, 10);
lean_closure_set(v___f_2195_, 0, v_cidx_2192_);
lean_closure_set(v___f_2195_, 1, v_toPure_2190_);
lean_closure_set(v___f_2195_, 2, v_k_2193_);
lean_closure_set(v___f_2195_, 3, v_c_2071_);
lean_closure_set(v___f_2195_, 4, v_fvarId_2191_);
lean_closure_set(v___f_2195_, 5, v___x_2194_);
lean_closure_set(v___f_2195_, 6, v_inst_2068_);
lean_closure_set(v___f_2195_, 7, v_inst_2069_);
lean_closure_set(v___f_2195_, 8, v_f_2070_);
lean_closure_set(v___f_2195_, 9, v_toBind_2189_);
v___x_2196_ = lean_apply_1(v_f_2070_, v_fvarId_2191_);
v___x_2197_ = lean_apply_4(v_toBind_2189_, lean_box(0), lean_box(0), v___x_2196_, v___f_2195_);
return v___x_2197_;
}
case 11:
{
lean_object* v_toApplicative_2198_; lean_object* v_toBind_2199_; lean_object* v_toPure_2200_; lean_object* v_fvarId_2201_; lean_object* v_n_2202_; uint8_t v_check_2203_; uint8_t v_persistent_2204_; lean_object* v_k_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___f_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v_toApplicative_2198_ = lean_ctor_get(v_inst_2069_, 0);
v_toBind_2199_ = lean_ctor_get(v_inst_2069_, 1);
lean_inc_n(v_toBind_2199_, 2);
v_toPure_2200_ = lean_ctor_get(v_toApplicative_2198_, 1);
lean_inc(v_toPure_2200_);
v_fvarId_2201_ = lean_ctor_get(v_c_2071_, 0);
lean_inc_n(v_fvarId_2201_, 2);
v_n_2202_ = lean_ctor_get(v_c_2071_, 1);
lean_inc(v_n_2202_);
v_check_2203_ = lean_ctor_get_uint8(v_c_2071_, sizeof(void*)*3);
v_persistent_2204_ = lean_ctor_get_uint8(v_c_2071_, sizeof(void*)*3 + 1);
v_k_2205_ = lean_ctor_get(v_c_2071_, 2);
lean_inc_ref(v_k_2205_);
v___x_2206_ = lean_box(v_check_2203_);
v___x_2207_ = lean_box(v_persistent_2204_);
v___x_2208_ = lean_box(v_pu_2067_);
lean_inc(v_f_2070_);
v___f_2209_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed), 13, 12);
lean_closure_set(v___f_2209_, 0, v_n_2202_);
lean_closure_set(v___f_2209_, 1, v___x_2206_);
lean_closure_set(v___f_2209_, 2, v___x_2207_);
lean_closure_set(v___f_2209_, 3, v_toPure_2200_);
lean_closure_set(v___f_2209_, 4, v_k_2205_);
lean_closure_set(v___f_2209_, 5, v_c_2071_);
lean_closure_set(v___f_2209_, 6, v_fvarId_2201_);
lean_closure_set(v___f_2209_, 7, v___x_2208_);
lean_closure_set(v___f_2209_, 8, v_inst_2068_);
lean_closure_set(v___f_2209_, 9, v_inst_2069_);
lean_closure_set(v___f_2209_, 10, v_f_2070_);
lean_closure_set(v___f_2209_, 11, v_toBind_2199_);
v___x_2210_ = lean_apply_1(v_f_2070_, v_fvarId_2201_);
v___x_2211_ = lean_apply_4(v_toBind_2199_, lean_box(0), lean_box(0), v___x_2210_, v___f_2209_);
return v___x_2211_;
}
case 12:
{
lean_object* v_toApplicative_2212_; lean_object* v_toBind_2213_; lean_object* v_toPure_2214_; lean_object* v_fvarId_2215_; lean_object* v_n_2216_; uint8_t v_check_2217_; uint8_t v_persistent_2218_; lean_object* v_objs_x3f_2219_; lean_object* v_k_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___f_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v_toApplicative_2212_ = lean_ctor_get(v_inst_2069_, 0);
v_toBind_2213_ = lean_ctor_get(v_inst_2069_, 1);
lean_inc_n(v_toBind_2213_, 2);
v_toPure_2214_ = lean_ctor_get(v_toApplicative_2212_, 1);
lean_inc(v_toPure_2214_);
v_fvarId_2215_ = lean_ctor_get(v_c_2071_, 0);
lean_inc_n(v_fvarId_2215_, 2);
v_n_2216_ = lean_ctor_get(v_c_2071_, 1);
lean_inc(v_n_2216_);
v_check_2217_ = lean_ctor_get_uint8(v_c_2071_, sizeof(void*)*4);
v_persistent_2218_ = lean_ctor_get_uint8(v_c_2071_, sizeof(void*)*4 + 1);
v_objs_x3f_2219_ = lean_ctor_get(v_c_2071_, 2);
lean_inc(v_objs_x3f_2219_);
v_k_2220_ = lean_ctor_get(v_c_2071_, 3);
lean_inc_ref(v_k_2220_);
v___x_2221_ = lean_box(v_check_2217_);
v___x_2222_ = lean_box(v_persistent_2218_);
v___x_2223_ = lean_box(v_pu_2067_);
lean_inc(v_f_2070_);
v___f_2224_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed), 14, 13);
lean_closure_set(v___f_2224_, 0, v_n_2216_);
lean_closure_set(v___f_2224_, 1, v___x_2221_);
lean_closure_set(v___f_2224_, 2, v___x_2222_);
lean_closure_set(v___f_2224_, 3, v_objs_x3f_2219_);
lean_closure_set(v___f_2224_, 4, v_toPure_2214_);
lean_closure_set(v___f_2224_, 5, v_k_2220_);
lean_closure_set(v___f_2224_, 6, v_c_2071_);
lean_closure_set(v___f_2224_, 7, v_fvarId_2215_);
lean_closure_set(v___f_2224_, 8, v___x_2223_);
lean_closure_set(v___f_2224_, 9, v_inst_2068_);
lean_closure_set(v___f_2224_, 10, v_inst_2069_);
lean_closure_set(v___f_2224_, 11, v_f_2070_);
lean_closure_set(v___f_2224_, 12, v_toBind_2213_);
v___x_2225_ = lean_apply_1(v_f_2070_, v_fvarId_2215_);
v___x_2226_ = lean_apply_4(v_toBind_2213_, lean_box(0), lean_box(0), v___x_2225_, v___f_2224_);
return v___x_2226_;
}
default: 
{
lean_object* v_toApplicative_2227_; lean_object* v_toBind_2228_; lean_object* v_toPure_2229_; lean_object* v_fvarId_2230_; lean_object* v_k_2231_; lean_object* v___x_2232_; lean_object* v___f_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_toApplicative_2227_ = lean_ctor_get(v_inst_2069_, 0);
v_toBind_2228_ = lean_ctor_get(v_inst_2069_, 1);
lean_inc_n(v_toBind_2228_, 2);
v_toPure_2229_ = lean_ctor_get(v_toApplicative_2227_, 1);
lean_inc(v_toPure_2229_);
v_fvarId_2230_ = lean_ctor_get(v_c_2071_, 0);
lean_inc_n(v_fvarId_2230_, 2);
v_k_2231_ = lean_ctor_get(v_c_2071_, 1);
lean_inc_ref(v_k_2231_);
v___x_2232_ = lean_box(v_pu_2067_);
lean_inc(v_f_2070_);
v___f_2233_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed), 10, 9);
lean_closure_set(v___f_2233_, 0, v_toPure_2229_);
lean_closure_set(v___f_2233_, 1, v_c_2071_);
lean_closure_set(v___f_2233_, 2, v_fvarId_2230_);
lean_closure_set(v___f_2233_, 3, v_k_2231_);
lean_closure_set(v___f_2233_, 4, v___x_2232_);
lean_closure_set(v___f_2233_, 5, v_inst_2068_);
lean_closure_set(v___f_2233_, 6, v_inst_2069_);
lean_closure_set(v___f_2233_, 7, v_f_2070_);
lean_closure_set(v___f_2233_, 8, v_toBind_2228_);
v___x_2234_ = lean_apply_1(v_f_2070_, v_fvarId_2230_);
v___x_2235_ = lean_apply_4(v_toBind_2228_, lean_box(0), lean_box(0), v___x_2234_, v___f_2233_);
return v___x_2235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed(lean_object* v_pu_2236_, lean_object* v_inst_2237_, lean_object* v_inst_2238_, lean_object* v_f_2239_, lean_object* v_c_2240_){
_start:
{
uint8_t v_pu_boxed_2241_; lean_object* v_res_2242_; 
v_pu_boxed_2241_ = lean_unbox(v_pu_2236_);
v_res_2242_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_boxed_2241_, v_inst_2237_, v_inst_2238_, v_f_2239_, v_c_2240_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(uint8_t v_pu_2243_, lean_object* v_inst_2244_, lean_object* v_inst_2245_, lean_object* v_f_2246_, lean_object* v_x_2247_){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2248_ = lean_box(v_pu_2243_);
lean_inc_ref(v_inst_2245_);
v___x_2249_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed), 5, 4);
lean_closure_set(v___x_2249_, 0, v___x_2248_);
lean_closure_set(v___x_2249_, 1, v_inst_2244_);
lean_closure_set(v___x_2249_, 2, v_inst_2245_);
lean_closure_set(v___x_2249_, 3, v_f_2246_);
v___x_2250_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg(v_inst_2245_, v_x_2247_, v___x_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM(lean_object* v_m_2251_, uint8_t v_pu_2252_, lean_object* v_inst_2253_, lean_object* v_inst_2254_, lean_object* v_f_2255_, lean_object* v_c_2256_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2252_, v_inst_2253_, v_inst_2254_, v_f_2255_, v_c_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___boxed(lean_object* v_m_2258_, lean_object* v_pu_2259_, lean_object* v_inst_2260_, lean_object* v_inst_2261_, lean_object* v_f_2262_, lean_object* v_c_2263_){
_start:
{
uint8_t v_pu_boxed_2264_; lean_object* v_res_2265_; 
v_pu_boxed_2264_ = lean_unbox(v_pu_2259_);
v_res_2265_ = l_Lean_Compiler_LCNF_Code_mapFVarM(v_m_2258_, v_pu_boxed_2264_, v_inst_2260_, v_inst_2261_, v_f_2262_, v_c_2263_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1(lean_object* v_inst_2266_, lean_object* v_f_2267_, lean_object* v_type_2268_, lean_object* v_toBind_2269_, lean_object* v___f_2270_, lean_object* v_____r_2271_){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2266_, v_f_2267_, v_type_2268_);
v___x_2273_ = lean_apply_4(v_toBind_2269_, lean_box(0), lean_box(0), v___x_2272_, v___f_2270_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12(lean_object* v_inst_2274_, lean_object* v_f_2275_, lean_object* v_ty_2276_, lean_object* v_toBind_2277_, lean_object* v___f_2278_, lean_object* v_____r_2279_){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2274_, v_f_2275_, v_ty_2276_);
v___x_2281_ = lean_apply_4(v_toBind_2277_, lean_box(0), lean_box(0), v___x_2280_, v___f_2278_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4(lean_object* v_args_2282_, lean_object* v_toApplicative_2283_, lean_object* v_inst_2284_, lean_object* v___f_2285_, lean_object* v_____r_2286_){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; 
v___x_2287_ = lean_unsigned_to_nat(0u);
v___x_2288_ = lean_array_get_size(v_args_2282_);
v___x_2289_ = lean_box(0);
v___x_2290_ = lean_nat_dec_lt(v___x_2287_, v___x_2288_);
if (v___x_2290_ == 0)
{
lean_object* v_toPure_2291_; lean_object* v___x_2292_; 
lean_dec(v___f_2285_);
lean_dec_ref(v_inst_2284_);
lean_dec_ref(v_args_2282_);
v_toPure_2291_ = lean_ctor_get(v_toApplicative_2283_, 1);
lean_inc(v_toPure_2291_);
lean_dec_ref(v_toApplicative_2283_);
v___x_2292_ = lean_apply_2(v_toPure_2291_, lean_box(0), v___x_2289_);
return v___x_2292_;
}
else
{
uint8_t v___x_2293_; 
v___x_2293_ = lean_nat_dec_le(v___x_2288_, v___x_2288_);
if (v___x_2293_ == 0)
{
if (v___x_2290_ == 0)
{
lean_object* v_toPure_2294_; lean_object* v___x_2295_; 
lean_dec(v___f_2285_);
lean_dec_ref(v_inst_2284_);
lean_dec_ref(v_args_2282_);
v_toPure_2294_ = lean_ctor_get(v_toApplicative_2283_, 1);
lean_inc(v_toPure_2294_);
lean_dec_ref(v_toApplicative_2283_);
v___x_2295_ = lean_apply_2(v_toPure_2294_, lean_box(0), v___x_2289_);
return v___x_2295_;
}
else
{
size_t v___x_2296_; size_t v___x_2297_; lean_object* v___x_2298_; 
lean_dec_ref(v_toApplicative_2283_);
v___x_2296_ = ((size_t)0ULL);
v___x_2297_ = lean_usize_of_nat(v___x_2288_);
v___x_2298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2284_, v___f_2285_, v_args_2282_, v___x_2296_, v___x_2297_, v___x_2289_);
return v___x_2298_;
}
}
else
{
size_t v___x_2299_; size_t v___x_2300_; lean_object* v___x_2301_; 
lean_dec_ref(v_toApplicative_2283_);
v___x_2299_ = ((size_t)0ULL);
v___x_2300_ = lean_usize_of_nat(v___x_2288_);
v___x_2301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2284_, v___f_2285_, v_args_2282_, v___x_2299_, v___x_2300_, v___x_2289_);
return v___x_2301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3(lean_object* v_inst_2302_, lean_object* v_f_2303_, lean_object* v_x_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_2302_, v_f_2303_, v___y_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10(lean_object* v_inst_2307_, lean_object* v_f_2308_, lean_object* v_y_2309_, lean_object* v_toBind_2310_, lean_object* v___f_2311_, lean_object* v_____r_2312_){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2307_, v_f_2308_, v_y_2309_);
v___x_2314_ = lean_apply_4(v_toBind_2310_, lean_box(0), lean_box(0), v___x_2313_, v___f_2311_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11(lean_object* v_f_2315_, lean_object* v_y_2316_, lean_object* v_toBind_2317_, lean_object* v___f_2318_, lean_object* v_____r_2319_){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = lean_apply_1(v_f_2315_, v_y_2316_);
v___x_2321_ = lean_apply_4(v_toBind_2317_, lean_box(0), lean_box(0), v___x_2320_, v___f_2318_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7(lean_object* v_f_2322_, lean_object* v_discr_2323_, lean_object* v_toBind_2324_, lean_object* v___f_2325_, lean_object* v_____r_2326_){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = lean_apply_1(v_f_2322_, v_discr_2323_);
v___x_2328_ = lean_apply_4(v_toBind_2324_, lean_box(0), lean_box(0), v___x_2327_, v___f_2325_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6(lean_object* v_alts_2329_, lean_object* v_toApplicative_2330_, lean_object* v_inst_2331_, lean_object* v___f_2332_, lean_object* v_____r_2333_){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2334_ = lean_unsigned_to_nat(0u);
v___x_2335_ = lean_array_get_size(v_alts_2329_);
v___x_2336_ = lean_box(0);
v___x_2337_ = lean_nat_dec_lt(v___x_2334_, v___x_2335_);
if (v___x_2337_ == 0)
{
lean_object* v_toPure_2338_; lean_object* v___x_2339_; 
lean_dec(v___f_2332_);
lean_dec_ref(v_inst_2331_);
lean_dec_ref(v_alts_2329_);
v_toPure_2338_ = lean_ctor_get(v_toApplicative_2330_, 1);
lean_inc(v_toPure_2338_);
lean_dec_ref(v_toApplicative_2330_);
v___x_2339_ = lean_apply_2(v_toPure_2338_, lean_box(0), v___x_2336_);
return v___x_2339_;
}
else
{
uint8_t v___x_2340_; 
v___x_2340_ = lean_nat_dec_le(v___x_2335_, v___x_2335_);
if (v___x_2340_ == 0)
{
if (v___x_2337_ == 0)
{
lean_object* v_toPure_2341_; lean_object* v___x_2342_; 
lean_dec(v___f_2332_);
lean_dec_ref(v_inst_2331_);
lean_dec_ref(v_alts_2329_);
v_toPure_2341_ = lean_ctor_get(v_toApplicative_2330_, 1);
lean_inc(v_toPure_2341_);
lean_dec_ref(v_toApplicative_2330_);
v___x_2342_ = lean_apply_2(v_toPure_2341_, lean_box(0), v___x_2336_);
return v___x_2342_;
}
else
{
size_t v___x_2343_; size_t v___x_2344_; lean_object* v___x_2345_; 
lean_dec_ref(v_toApplicative_2330_);
v___x_2343_ = ((size_t)0ULL);
v___x_2344_ = lean_usize_of_nat(v___x_2335_);
v___x_2345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2331_, v___f_2332_, v_alts_2329_, v___x_2343_, v___x_2344_, v___x_2336_);
return v___x_2345_;
}
}
else
{
size_t v___x_2346_; size_t v___x_2347_; lean_object* v___x_2348_; 
lean_dec_ref(v_toApplicative_2330_);
v___x_2346_ = ((size_t)0ULL);
v___x_2347_ = lean_usize_of_nat(v___x_2335_);
v___x_2348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2331_, v___f_2332_, v_alts_2329_, v___x_2346_, v___x_2347_, v___x_2336_);
return v___x_2348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8(lean_object* v_inst_2349_, lean_object* v_f_2350_, lean_object* v_x_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2349_, v_f_2350_, v___y_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5(lean_object* v_inst_2354_, lean_object* v_f_2355_, lean_object* v_x_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg), 3, 2);
lean_closure_set(v___x_2358_, 0, v_inst_2354_);
lean_closure_set(v___x_2358_, 1, v_f_2355_);
v___x_2359_ = l_Lean_Compiler_LCNF_Alt_forCodeM___redArg(v___y_2357_, v___x_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2(lean_object* v_inst_2360_, lean_object* v_f_2361_, lean_object* v_value_2362_, lean_object* v_toBind_2363_, lean_object* v___f_2364_, lean_object* v_____r_2365_){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2360_, v_f_2361_, v_value_2362_);
v___x_2367_ = lean_apply_4(v_toBind_2363_, lean_box(0), lean_box(0), v___x_2366_, v___f_2364_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg(lean_object* v_inst_2368_, lean_object* v_f_2369_, lean_object* v_c_2370_){
_start:
{
switch(lean_obj_tag(v_c_2370_))
{
case 0:
{
lean_object* v_toBind_2371_; lean_object* v_decl_2372_; lean_object* v_k_2373_; lean_object* v___f_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v_toBind_2371_ = lean_ctor_get(v_inst_2368_, 1);
lean_inc(v_toBind_2371_);
v_decl_2372_ = lean_ctor_get(v_c_2370_, 0);
lean_inc_ref(v_decl_2372_);
v_k_2373_ = lean_ctor_get(v_c_2370_, 1);
lean_inc_ref(v_k_2373_);
lean_dec_ref_known(v_c_2370_, 2);
lean_inc(v_f_2369_);
lean_inc_ref(v_inst_2368_);
v___f_2374_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2374_, 0, v_inst_2368_);
lean_closure_set(v___f_2374_, 1, v_f_2369_);
lean_closure_set(v___f_2374_, 2, v_k_2373_);
v___x_2375_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_2368_, v_f_2369_, v_decl_2372_);
v___x_2376_ = lean_apply_4(v_toBind_2371_, lean_box(0), lean_box(0), v___x_2375_, v___f_2374_);
return v___x_2376_;
}
case 3:
{
lean_object* v_toApplicative_2377_; lean_object* v_toBind_2378_; lean_object* v_fvarId_2379_; lean_object* v_args_2380_; lean_object* v___f_2381_; lean_object* v___f_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_toApplicative_2377_ = lean_ctor_get(v_inst_2368_, 0);
lean_inc_ref(v_toApplicative_2377_);
v_toBind_2378_ = lean_ctor_get(v_inst_2368_, 1);
lean_inc(v_toBind_2378_);
v_fvarId_2379_ = lean_ctor_get(v_c_2370_, 0);
lean_inc(v_fvarId_2379_);
v_args_2380_ = lean_ctor_get(v_c_2370_, 1);
lean_inc_ref(v_args_2380_);
lean_dec_ref_known(v_c_2370_, 2);
lean_inc(v_f_2369_);
lean_inc_ref(v_inst_2368_);
v___f_2381_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8), 4, 2);
lean_closure_set(v___f_2381_, 0, v_inst_2368_);
lean_closure_set(v___f_2381_, 1, v_f_2369_);
v___f_2382_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2382_, 0, v_args_2380_);
lean_closure_set(v___f_2382_, 1, v_toApplicative_2377_);
lean_closure_set(v___f_2382_, 2, v_inst_2368_);
lean_closure_set(v___f_2382_, 3, v___f_2381_);
v___x_2383_ = lean_apply_1(v_f_2369_, v_fvarId_2379_);
v___x_2384_ = lean_apply_4(v_toBind_2378_, lean_box(0), lean_box(0), v___x_2383_, v___f_2382_);
return v___x_2384_;
}
case 4:
{
lean_object* v_cases_2385_; lean_object* v_toApplicative_2386_; lean_object* v_toBind_2387_; lean_object* v_resultType_2388_; lean_object* v_discr_2389_; lean_object* v_alts_2390_; lean_object* v___f_2391_; lean_object* v___f_2392_; lean_object* v___f_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v_cases_2385_ = lean_ctor_get(v_c_2370_, 0);
lean_inc_ref(v_cases_2385_);
lean_dec_ref_known(v_c_2370_, 1);
v_toApplicative_2386_ = lean_ctor_get(v_inst_2368_, 0);
v_toBind_2387_ = lean_ctor_get(v_inst_2368_, 1);
lean_inc_n(v_toBind_2387_, 2);
v_resultType_2388_ = lean_ctor_get(v_cases_2385_, 1);
lean_inc_ref(v_resultType_2388_);
v_discr_2389_ = lean_ctor_get(v_cases_2385_, 2);
lean_inc(v_discr_2389_);
v_alts_2390_ = lean_ctor_get(v_cases_2385_, 3);
lean_inc_ref(v_alts_2390_);
lean_dec_ref(v_cases_2385_);
lean_inc_n(v_f_2369_, 2);
lean_inc_ref_n(v_inst_2368_, 2);
v___f_2391_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5), 4, 2);
lean_closure_set(v___f_2391_, 0, v_inst_2368_);
lean_closure_set(v___f_2391_, 1, v_f_2369_);
lean_inc_ref(v_toApplicative_2386_);
v___f_2392_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6), 5, 4);
lean_closure_set(v___f_2392_, 0, v_alts_2390_);
lean_closure_set(v___f_2392_, 1, v_toApplicative_2386_);
lean_closure_set(v___f_2392_, 2, v_inst_2368_);
lean_closure_set(v___f_2392_, 3, v___f_2391_);
v___f_2393_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7), 5, 4);
lean_closure_set(v___f_2393_, 0, v_f_2369_);
lean_closure_set(v___f_2393_, 1, v_discr_2389_);
lean_closure_set(v___f_2393_, 2, v_toBind_2387_);
lean_closure_set(v___f_2393_, 3, v___f_2392_);
v___x_2394_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2368_, v_f_2369_, v_resultType_2388_);
v___x_2395_ = lean_apply_4(v_toBind_2387_, lean_box(0), lean_box(0), v___x_2394_, v___f_2393_);
return v___x_2395_;
}
case 5:
{
lean_object* v_fvarId_2396_; lean_object* v___x_2397_; 
lean_dec_ref(v_inst_2368_);
v_fvarId_2396_ = lean_ctor_get(v_c_2370_, 0);
lean_inc(v_fvarId_2396_);
lean_dec_ref_known(v_c_2370_, 1);
v___x_2397_ = lean_apply_1(v_f_2369_, v_fvarId_2396_);
return v___x_2397_;
}
case 6:
{
lean_object* v_type_2398_; lean_object* v___x_2399_; 
v_type_2398_ = lean_ctor_get(v_c_2370_, 0);
lean_inc_ref(v_type_2398_);
lean_dec_ref_known(v_c_2370_, 1);
v___x_2399_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2368_, v_f_2369_, v_type_2398_);
return v___x_2399_;
}
case 7:
{
lean_object* v_toBind_2400_; lean_object* v_fvarId_2401_; lean_object* v_y_2402_; lean_object* v_k_2403_; lean_object* v___f_2404_; lean_object* v___f_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v_toBind_2400_ = lean_ctor_get(v_inst_2368_, 1);
lean_inc_n(v_toBind_2400_, 2);
v_fvarId_2401_ = lean_ctor_get(v_c_2370_, 0);
lean_inc(v_fvarId_2401_);
v_y_2402_ = lean_ctor_get(v_c_2370_, 2);
lean_inc(v_y_2402_);
v_k_2403_ = lean_ctor_get(v_c_2370_, 3);
lean_inc_ref(v_k_2403_);
lean_dec_ref_known(v_c_2370_, 4);
lean_inc_n(v_f_2369_, 2);
lean_inc_ref(v_inst_2368_);
v___f_2404_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2404_, 0, v_inst_2368_);
lean_closure_set(v___f_2404_, 1, v_f_2369_);
lean_closure_set(v___f_2404_, 2, v_k_2403_);
v___f_2405_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10), 6, 5);
lean_closure_set(v___f_2405_, 0, v_inst_2368_);
lean_closure_set(v___f_2405_, 1, v_f_2369_);
lean_closure_set(v___f_2405_, 2, v_y_2402_);
lean_closure_set(v___f_2405_, 3, v_toBind_2400_);
lean_closure_set(v___f_2405_, 4, v___f_2404_);
v___x_2406_ = lean_apply_1(v_f_2369_, v_fvarId_2401_);
v___x_2407_ = lean_apply_4(v_toBind_2400_, lean_box(0), lean_box(0), v___x_2406_, v___f_2405_);
return v___x_2407_;
}
case 8:
{
lean_object* v_toBind_2408_; lean_object* v_fvarId_2409_; lean_object* v_y_2410_; lean_object* v_k_2411_; lean_object* v___f_2412_; lean_object* v___f_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v_toBind_2408_ = lean_ctor_get(v_inst_2368_, 1);
lean_inc_n(v_toBind_2408_, 2);
v_fvarId_2409_ = lean_ctor_get(v_c_2370_, 0);
lean_inc(v_fvarId_2409_);
v_y_2410_ = lean_ctor_get(v_c_2370_, 2);
lean_inc(v_y_2410_);
v_k_2411_ = lean_ctor_get(v_c_2370_, 3);
lean_inc_ref(v_k_2411_);
lean_dec_ref_known(v_c_2370_, 4);
lean_inc_n(v_f_2369_, 2);
v___f_2412_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2412_, 0, v_inst_2368_);
lean_closure_set(v___f_2412_, 1, v_f_2369_);
lean_closure_set(v___f_2412_, 2, v_k_2411_);
v___f_2413_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11), 5, 4);
lean_closure_set(v___f_2413_, 0, v_f_2369_);
lean_closure_set(v___f_2413_, 1, v_y_2410_);
lean_closure_set(v___f_2413_, 2, v_toBind_2408_);
lean_closure_set(v___f_2413_, 3, v___f_2412_);
v___x_2414_ = lean_apply_1(v_f_2369_, v_fvarId_2409_);
v___x_2415_ = lean_apply_4(v_toBind_2408_, lean_box(0), lean_box(0), v___x_2414_, v___f_2413_);
return v___x_2415_;
}
case 9:
{
lean_object* v_toBind_2416_; lean_object* v_fvarId_2417_; lean_object* v_y_2418_; lean_object* v_ty_2419_; lean_object* v_k_2420_; lean_object* v___f_2421_; lean_object* v___f_2422_; lean_object* v___f_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v_toBind_2416_ = lean_ctor_get(v_inst_2368_, 1);
lean_inc_n(v_toBind_2416_, 3);
v_fvarId_2417_ = lean_ctor_get(v_c_2370_, 0);
lean_inc(v_fvarId_2417_);
v_y_2418_ = lean_ctor_get(v_c_2370_, 3);
lean_inc(v_y_2418_);
v_ty_2419_ = lean_ctor_get(v_c_2370_, 4);
lean_inc_ref(v_ty_2419_);
v_k_2420_ = lean_ctor_get(v_c_2370_, 5);
lean_inc_ref(v_k_2420_);
lean_dec_ref_known(v_c_2370_, 6);
lean_inc_n(v_f_2369_, 3);
lean_inc_ref(v_inst_2368_);
v___f_2421_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2421_, 0, v_inst_2368_);
lean_closure_set(v___f_2421_, 1, v_f_2369_);
lean_closure_set(v___f_2421_, 2, v_k_2420_);
v___f_2422_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12), 6, 5);
lean_closure_set(v___f_2422_, 0, v_inst_2368_);
lean_closure_set(v___f_2422_, 1, v_f_2369_);
lean_closure_set(v___f_2422_, 2, v_ty_2419_);
lean_closure_set(v___f_2422_, 3, v_toBind_2416_);
lean_closure_set(v___f_2422_, 4, v___f_2421_);
v___f_2423_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11), 5, 4);
lean_closure_set(v___f_2423_, 0, v_f_2369_);
lean_closure_set(v___f_2423_, 1, v_y_2418_);
lean_closure_set(v___f_2423_, 2, v_toBind_2416_);
lean_closure_set(v___f_2423_, 3, v___f_2422_);
v___x_2424_ = lean_apply_1(v_f_2369_, v_fvarId_2417_);
v___x_2425_ = lean_apply_4(v_toBind_2416_, lean_box(0), lean_box(0), v___x_2424_, v___f_2423_);
return v___x_2425_;
}
case 10:
{
lean_object* v_toBind_2426_; lean_object* v_fvarId_2427_; lean_object* v_k_2428_; lean_object* v___f_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_toBind_2426_ = lean_ctor_get(v_inst_2368_, 1);
lean_inc(v_toBind_2426_);
v_fvarId_2427_ = lean_ctor_get(v_c_2370_, 0);
lean_inc(v_fvarId_2427_);
v_k_2428_ = lean_ctor_get(v_c_2370_, 2);
lean_inc_ref(v_k_2428_);
lean_dec_ref_known(v_c_2370_, 3);
lean_inc(v_f_2369_);
v___f_2429_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2429_, 0, v_inst_2368_);
lean_closure_set(v___f_2429_, 1, v_f_2369_);
lean_closure_set(v___f_2429_, 2, v_k_2428_);
v___x_2430_ = lean_apply_1(v_f_2369_, v_fvarId_2427_);
v___x_2431_ = lean_apply_4(v_toBind_2426_, lean_box(0), lean_box(0), v___x_2430_, v___f_2429_);
return v___x_2431_;
}
case 11:
{
lean_object* v_toBind_2432_; lean_object* v_fvarId_2433_; lean_object* v_k_2434_; lean_object* v___f_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v_toBind_2432_ = lean_ctor_get(v_inst_2368_, 1);
lean_inc(v_toBind_2432_);
v_fvarId_2433_ = lean_ctor_get(v_c_2370_, 0);
lean_inc(v_fvarId_2433_);
v_k_2434_ = lean_ctor_get(v_c_2370_, 2);
lean_inc_ref(v_k_2434_);
lean_dec_ref_known(v_c_2370_, 3);
lean_inc(v_f_2369_);
v___f_2435_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2435_, 0, v_inst_2368_);
lean_closure_set(v___f_2435_, 1, v_f_2369_);
lean_closure_set(v___f_2435_, 2, v_k_2434_);
v___x_2436_ = lean_apply_1(v_f_2369_, v_fvarId_2433_);
v___x_2437_ = lean_apply_4(v_toBind_2432_, lean_box(0), lean_box(0), v___x_2436_, v___f_2435_);
return v___x_2437_;
}
case 12:
{
lean_object* v_toBind_2438_; lean_object* v_fvarId_2439_; lean_object* v_k_2440_; lean_object* v___f_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v_toBind_2438_ = lean_ctor_get(v_inst_2368_, 1);
lean_inc(v_toBind_2438_);
v_fvarId_2439_ = lean_ctor_get(v_c_2370_, 0);
lean_inc(v_fvarId_2439_);
v_k_2440_ = lean_ctor_get(v_c_2370_, 3);
lean_inc_ref(v_k_2440_);
lean_dec_ref_known(v_c_2370_, 4);
lean_inc(v_f_2369_);
v___f_2441_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2441_, 0, v_inst_2368_);
lean_closure_set(v___f_2441_, 1, v_f_2369_);
lean_closure_set(v___f_2441_, 2, v_k_2440_);
v___x_2442_ = lean_apply_1(v_f_2369_, v_fvarId_2439_);
v___x_2443_ = lean_apply_4(v_toBind_2438_, lean_box(0), lean_box(0), v___x_2442_, v___f_2441_);
return v___x_2443_;
}
case 13:
{
lean_object* v_toBind_2444_; lean_object* v_fvarId_2445_; lean_object* v_k_2446_; lean_object* v___f_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v_toBind_2444_ = lean_ctor_get(v_inst_2368_, 1);
lean_inc(v_toBind_2444_);
v_fvarId_2445_ = lean_ctor_get(v_c_2370_, 0);
lean_inc(v_fvarId_2445_);
v_k_2446_ = lean_ctor_get(v_c_2370_, 1);
lean_inc_ref(v_k_2446_);
lean_dec_ref_known(v_c_2370_, 2);
lean_inc(v_f_2369_);
v___f_2447_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2447_, 0, v_inst_2368_);
lean_closure_set(v___f_2447_, 1, v_f_2369_);
lean_closure_set(v___f_2447_, 2, v_k_2446_);
v___x_2448_ = lean_apply_1(v_f_2369_, v_fvarId_2445_);
v___x_2449_ = lean_apply_4(v_toBind_2444_, lean_box(0), lean_box(0), v___x_2448_, v___f_2447_);
return v___x_2449_;
}
default: 
{
lean_object* v_decl_2450_; lean_object* v_toApplicative_2451_; lean_object* v_toBind_2452_; lean_object* v_k_2453_; lean_object* v_params_2454_; lean_object* v_type_2455_; lean_object* v_value_2456_; lean_object* v___f_2457_; lean_object* v___f_2458_; lean_object* v___f_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; 
v_decl_2450_ = lean_ctor_get(v_c_2370_, 0);
lean_inc_ref(v_decl_2450_);
v_toApplicative_2451_ = lean_ctor_get(v_inst_2368_, 0);
v_toBind_2452_ = lean_ctor_get(v_inst_2368_, 1);
lean_inc_n(v_toBind_2452_, 3);
v_k_2453_ = lean_ctor_get(v_c_2370_, 1);
lean_inc_ref(v_k_2453_);
lean_dec_ref(v_c_2370_);
v_params_2454_ = lean_ctor_get(v_decl_2450_, 2);
lean_inc_ref(v_params_2454_);
v_type_2455_ = lean_ctor_get(v_decl_2450_, 3);
lean_inc_ref(v_type_2455_);
v_value_2456_ = lean_ctor_get(v_decl_2450_, 4);
lean_inc_ref(v_value_2456_);
lean_dec_ref(v_decl_2450_);
lean_inc_n(v_f_2369_, 3);
lean_inc_ref_n(v_inst_2368_, 3);
v___f_2457_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2457_, 0, v_inst_2368_);
lean_closure_set(v___f_2457_, 1, v_f_2369_);
lean_closure_set(v___f_2457_, 2, v_k_2453_);
v___f_2458_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2458_, 0, v_inst_2368_);
lean_closure_set(v___f_2458_, 1, v_f_2369_);
lean_closure_set(v___f_2458_, 2, v_value_2456_);
lean_closure_set(v___f_2458_, 3, v_toBind_2452_);
lean_closure_set(v___f_2458_, 4, v___f_2457_);
v___f_2459_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2459_, 0, v_inst_2368_);
lean_closure_set(v___f_2459_, 1, v_f_2369_);
lean_closure_set(v___f_2459_, 2, v_type_2455_);
lean_closure_set(v___f_2459_, 3, v_toBind_2452_);
lean_closure_set(v___f_2459_, 4, v___f_2458_);
v___x_2460_ = lean_unsigned_to_nat(0u);
v___x_2461_ = lean_array_get_size(v_params_2454_);
v___x_2462_ = lean_box(0);
v___x_2463_ = lean_nat_dec_lt(v___x_2460_, v___x_2461_);
if (v___x_2463_ == 0)
{
lean_object* v_toPure_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
lean_inc_ref(v_toApplicative_2451_);
lean_dec_ref(v_params_2454_);
lean_dec(v_f_2369_);
lean_dec_ref(v_inst_2368_);
v_toPure_2464_ = lean_ctor_get(v_toApplicative_2451_, 1);
lean_inc(v_toPure_2464_);
lean_dec_ref(v_toApplicative_2451_);
v___x_2465_ = lean_apply_2(v_toPure_2464_, lean_box(0), v___x_2462_);
v___x_2466_ = lean_apply_4(v_toBind_2452_, lean_box(0), lean_box(0), v___x_2465_, v___f_2459_);
return v___x_2466_;
}
else
{
lean_object* v___f_2467_; uint8_t v___x_2468_; 
lean_inc_ref(v_inst_2368_);
v___f_2467_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2467_, 0, v_inst_2368_);
lean_closure_set(v___f_2467_, 1, v_f_2369_);
v___x_2468_ = lean_nat_dec_le(v___x_2461_, v___x_2461_);
if (v___x_2468_ == 0)
{
if (v___x_2463_ == 0)
{
lean_object* v_toPure_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
lean_inc_ref(v_toApplicative_2451_);
lean_dec_ref(v___f_2467_);
lean_dec_ref(v_params_2454_);
lean_dec_ref(v_inst_2368_);
v_toPure_2469_ = lean_ctor_get(v_toApplicative_2451_, 1);
lean_inc(v_toPure_2469_);
lean_dec_ref(v_toApplicative_2451_);
v___x_2470_ = lean_apply_2(v_toPure_2469_, lean_box(0), v___x_2462_);
v___x_2471_ = lean_apply_4(v_toBind_2452_, lean_box(0), lean_box(0), v___x_2470_, v___f_2459_);
return v___x_2471_;
}
else
{
size_t v___x_2472_; size_t v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2472_ = ((size_t)0ULL);
v___x_2473_ = lean_usize_of_nat(v___x_2461_);
v___x_2474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2368_, v___f_2467_, v_params_2454_, v___x_2472_, v___x_2473_, v___x_2462_);
v___x_2475_ = lean_apply_4(v_toBind_2452_, lean_box(0), lean_box(0), v___x_2474_, v___f_2459_);
return v___x_2475_;
}
}
else
{
size_t v___x_2476_; size_t v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2476_ = ((size_t)0ULL);
v___x_2477_ = lean_usize_of_nat(v___x_2461_);
v___x_2478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2368_, v___f_2467_, v_params_2454_, v___x_2476_, v___x_2477_, v___x_2462_);
v___x_2479_ = lean_apply_4(v_toBind_2452_, lean_box(0), lean_box(0), v___x_2478_, v___f_2459_);
return v___x_2479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0(lean_object* v_inst_2480_, lean_object* v_f_2481_, lean_object* v_k_2482_, lean_object* v_____r_2483_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2480_, v_f_2481_, v_k_2482_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM(lean_object* v_m_2485_, uint8_t v_pu_2486_, lean_object* v_inst_2487_, lean_object* v_f_2488_, lean_object* v_c_2489_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2487_, v_f_2488_, v_c_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___boxed(lean_object* v_m_2491_, lean_object* v_pu_2492_, lean_object* v_inst_2493_, lean_object* v_f_2494_, lean_object* v_c_2495_){
_start:
{
uint8_t v_pu_boxed_2496_; lean_object* v_res_2497_; 
v_pu_boxed_2496_ = lean_unbox(v_pu_2492_);
v_res_2497_ = l_Lean_Compiler_LCNF_Code_forFVarM(v_m_2491_, v_pu_boxed_2496_, v_inst_2493_, v_f_2494_, v_c_2495_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(uint8_t v_pu_2498_, lean_object* v_m_2499_, lean_object* v_inst_2500_, lean_object* v_inst_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2498_, v_inst_2500_, v_inst_2501_, v___y_2502_, v___y_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed(lean_object* v_pu_2505_, lean_object* v_m_2506_, lean_object* v_inst_2507_, lean_object* v_inst_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
uint8_t v_pu_boxed_2511_; lean_object* v_res_2512_; 
v_pu_boxed_2511_ = lean_unbox(v_pu_2505_);
v_res_2512_ = l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(v_pu_boxed_2511_, v_m_2506_, v_inst_2507_, v_inst_2508_, v___y_2509_, v___y_2510_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__1(lean_object* v_m_2513_, lean_object* v_inst_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2514_, v___y_2515_, v___y_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode(uint8_t v_pu_2519_){
_start:
{
lean_object* v___x_2520_; lean_object* v___f_2521_; lean_object* v___f_2522_; lean_object* v___x_2523_; 
v___x_2520_ = lean_box(v_pu_2519_);
v___f_2521_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2521_, 0, v___x_2520_);
v___f_2522_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0));
v___x_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___f_2521_);
lean_ctor_set(v___x_2523_, 1, v___f_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___boxed(lean_object* v_pu_2524_){
_start:
{
uint8_t v_pu_boxed_2525_; lean_object* v_res_2526_; 
v_pu_boxed_2525_ = lean_unbox(v_pu_2524_);
v_res_2526_ = l_Lean_Compiler_LCNF_instTraverseFVarCode(v_pu_boxed_2525_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(uint8_t v_pu_2527_, lean_object* v_decl_2528_, lean_object* v_____do__lift_2529_, lean_object* v_params_2530_, lean_object* v_inst_2531_, lean_object* v_____do__lift_2532_){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = lean_box(v_pu_2527_);
v___x_2534_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed), 10, 5);
lean_closure_set(v___x_2534_, 0, v___x_2533_);
lean_closure_set(v___x_2534_, 1, v_decl_2528_);
lean_closure_set(v___x_2534_, 2, v_____do__lift_2529_);
lean_closure_set(v___x_2534_, 3, v_params_2530_);
lean_closure_set(v___x_2534_, 4, v_____do__lift_2532_);
v___x_2535_ = lean_apply_2(v_inst_2531_, lean_box(0), v___x_2534_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_2536_, lean_object* v_decl_2537_, lean_object* v_____do__lift_2538_, lean_object* v_params_2539_, lean_object* v_inst_2540_, lean_object* v_____do__lift_2541_){
_start:
{
uint8_t v_pu_boxed_2542_; lean_object* v_res_2543_; 
v_pu_boxed_2542_ = lean_unbox(v_pu_2536_);
v_res_2543_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(v_pu_boxed_2542_, v_decl_2537_, v_____do__lift_2538_, v_params_2539_, v_inst_2540_, v_____do__lift_2541_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(uint8_t v_pu_2544_, lean_object* v_decl_2545_, lean_object* v_params_2546_, lean_object* v_inst_2547_, lean_object* v_inst_2548_, lean_object* v_f_2549_, lean_object* v_value_2550_, lean_object* v_toBind_2551_, lean_object* v_____do__lift_2552_){
_start:
{
lean_object* v___x_2553_; lean_object* v___f_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2553_ = lean_box(v_pu_2544_);
lean_inc(v_inst_2547_);
v___f_2554_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2554_, 0, v___x_2553_);
lean_closure_set(v___f_2554_, 1, v_decl_2545_);
lean_closure_set(v___f_2554_, 2, v_____do__lift_2552_);
lean_closure_set(v___f_2554_, 3, v_params_2546_);
lean_closure_set(v___f_2554_, 4, v_inst_2547_);
v___x_2555_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2544_, v_inst_2547_, v_inst_2548_, v_f_2549_, v_value_2550_);
v___x_2556_ = lean_apply_4(v_toBind_2551_, lean_box(0), lean_box(0), v___x_2555_, v___f_2554_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed(lean_object* v_pu_2557_, lean_object* v_decl_2558_, lean_object* v_params_2559_, lean_object* v_inst_2560_, lean_object* v_inst_2561_, lean_object* v_f_2562_, lean_object* v_value_2563_, lean_object* v_toBind_2564_, lean_object* v_____do__lift_2565_){
_start:
{
uint8_t v_pu_boxed_2566_; lean_object* v_res_2567_; 
v_pu_boxed_2566_ = lean_unbox(v_pu_2557_);
v_res_2567_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(v_pu_boxed_2566_, v_decl_2558_, v_params_2559_, v_inst_2560_, v_inst_2561_, v_f_2562_, v_value_2563_, v_toBind_2564_, v_____do__lift_2565_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(uint8_t v_pu_2568_, lean_object* v_decl_2569_, lean_object* v_inst_2570_, lean_object* v_inst_2571_, lean_object* v_f_2572_, lean_object* v_value_2573_, lean_object* v_toBind_2574_, lean_object* v_type_2575_, lean_object* v_params_2576_){
_start:
{
lean_object* v___x_2577_; lean_object* v___f_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2577_ = lean_box(v_pu_2568_);
lean_inc(v_toBind_2574_);
lean_inc(v_f_2572_);
lean_inc_ref(v_inst_2571_);
v___f_2578_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2578_, 0, v___x_2577_);
lean_closure_set(v___f_2578_, 1, v_decl_2569_);
lean_closure_set(v___f_2578_, 2, v_params_2576_);
lean_closure_set(v___f_2578_, 3, v_inst_2570_);
lean_closure_set(v___f_2578_, 4, v_inst_2571_);
lean_closure_set(v___f_2578_, 5, v_f_2572_);
lean_closure_set(v___f_2578_, 6, v_value_2573_);
lean_closure_set(v___f_2578_, 7, v_toBind_2574_);
v___x_2579_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2571_, v_f_2572_, v_type_2575_);
v___x_2580_ = lean_apply_4(v_toBind_2574_, lean_box(0), lean_box(0), v___x_2579_, v___f_2578_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed(lean_object* v_pu_2581_, lean_object* v_decl_2582_, lean_object* v_inst_2583_, lean_object* v_inst_2584_, lean_object* v_f_2585_, lean_object* v_value_2586_, lean_object* v_toBind_2587_, lean_object* v_type_2588_, lean_object* v_params_2589_){
_start:
{
uint8_t v_pu_boxed_2590_; lean_object* v_res_2591_; 
v_pu_boxed_2590_ = lean_unbox(v_pu_2581_);
v_res_2591_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(v_pu_boxed_2590_, v_decl_2582_, v_inst_2583_, v_inst_2584_, v_f_2585_, v_value_2586_, v_toBind_2587_, v_type_2588_, v_params_2589_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(uint8_t v_pu_2592_, lean_object* v_inst_2593_, lean_object* v_inst_2594_, lean_object* v_f_2595_, lean_object* v_decl_2596_){
_start:
{
lean_object* v_toBind_2597_; lean_object* v_params_2598_; lean_object* v_type_2599_; lean_object* v_value_2600_; lean_object* v___x_2601_; lean_object* v___f_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; size_t v_sz_2605_; size_t v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v_toBind_2597_ = lean_ctor_get(v_inst_2594_, 1);
lean_inc_n(v_toBind_2597_, 2);
v_params_2598_ = lean_ctor_get(v_decl_2596_, 2);
lean_inc_ref(v_params_2598_);
v_type_2599_ = lean_ctor_get(v_decl_2596_, 3);
lean_inc_ref(v_type_2599_);
v_value_2600_ = lean_ctor_get(v_decl_2596_, 4);
lean_inc_ref(v_value_2600_);
v___x_2601_ = lean_box(v_pu_2592_);
lean_inc(v_f_2595_);
lean_inc_ref_n(v_inst_2594_, 2);
lean_inc(v_inst_2593_);
v___f_2602_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2602_, 0, v___x_2601_);
lean_closure_set(v___f_2602_, 1, v_decl_2596_);
lean_closure_set(v___f_2602_, 2, v_inst_2593_);
lean_closure_set(v___f_2602_, 3, v_inst_2594_);
lean_closure_set(v___f_2602_, 4, v_f_2595_);
lean_closure_set(v___f_2602_, 5, v_value_2600_);
lean_closure_set(v___f_2602_, 6, v_toBind_2597_);
lean_closure_set(v___f_2602_, 7, v_type_2599_);
v___x_2603_ = lean_box(v_pu_2592_);
v___x_2604_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2604_, 0, lean_box(0));
lean_closure_set(v___x_2604_, 1, v___x_2603_);
lean_closure_set(v___x_2604_, 2, v_inst_2593_);
lean_closure_set(v___x_2604_, 3, v_inst_2594_);
lean_closure_set(v___x_2604_, 4, v_f_2595_);
v_sz_2605_ = lean_array_size(v_params_2598_);
v___x_2606_ = ((size_t)0ULL);
v___x_2607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2594_, v___x_2604_, v_sz_2605_, v___x_2606_, v_params_2598_);
v___x_2608_ = lean_apply_4(v_toBind_2597_, lean_box(0), lean_box(0), v___x_2607_, v___f_2602_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___boxed(lean_object* v_pu_2609_, lean_object* v_inst_2610_, lean_object* v_inst_2611_, lean_object* v_f_2612_, lean_object* v_decl_2613_){
_start:
{
uint8_t v_pu_boxed_2614_; lean_object* v_res_2615_; 
v_pu_boxed_2614_ = lean_unbox(v_pu_2609_);
v_res_2615_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_boxed_2614_, v_inst_2610_, v_inst_2611_, v_f_2612_, v_decl_2613_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM(lean_object* v_m_2616_, uint8_t v_pu_2617_, lean_object* v_inst_2618_, lean_object* v_inst_2619_, lean_object* v_f_2620_, lean_object* v_decl_2621_){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2617_, v_inst_2618_, v_inst_2619_, v_f_2620_, v_decl_2621_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___boxed(lean_object* v_m_2623_, lean_object* v_pu_2624_, lean_object* v_inst_2625_, lean_object* v_inst_2626_, lean_object* v_f_2627_, lean_object* v_decl_2628_){
_start:
{
uint8_t v_pu_boxed_2629_; lean_object* v_res_2630_; 
v_pu_boxed_2629_ = lean_unbox(v_pu_2624_);
v_res_2630_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM(v_m_2623_, v_pu_boxed_2629_, v_inst_2625_, v_inst_2626_, v_f_2627_, v_decl_2628_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0(lean_object* v_inst_2631_, lean_object* v_f_2632_, lean_object* v_value_2633_, lean_object* v_____r_2634_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2631_, v_f_2632_, v_value_2633_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1(lean_object* v_inst_2636_, lean_object* v_f_2637_, lean_object* v_type_2638_, lean_object* v_toBind_2639_, lean_object* v___f_2640_, lean_object* v_____r_2641_){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2636_, v_f_2637_, v_type_2638_);
v___x_2643_ = lean_apply_4(v_toBind_2639_, lean_box(0), lean_box(0), v___x_2642_, v___f_2640_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2(lean_object* v_inst_2644_, lean_object* v_f_2645_, lean_object* v_x_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_2644_, v_f_2645_, v___y_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(lean_object* v_inst_2649_, lean_object* v_f_2650_, lean_object* v_decl_2651_){
_start:
{
lean_object* v_toApplicative_2652_; lean_object* v_toBind_2653_; lean_object* v_params_2654_; lean_object* v_type_2655_; lean_object* v_value_2656_; lean_object* v___f_2657_; lean_object* v___f_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; uint8_t v___x_2662_; 
v_toApplicative_2652_ = lean_ctor_get(v_inst_2649_, 0);
v_toBind_2653_ = lean_ctor_get(v_inst_2649_, 1);
lean_inc_n(v_toBind_2653_, 2);
v_params_2654_ = lean_ctor_get(v_decl_2651_, 2);
lean_inc_ref(v_params_2654_);
v_type_2655_ = lean_ctor_get(v_decl_2651_, 3);
lean_inc_ref(v_type_2655_);
v_value_2656_ = lean_ctor_get(v_decl_2651_, 4);
lean_inc_ref(v_value_2656_);
lean_dec_ref(v_decl_2651_);
lean_inc_n(v_f_2650_, 2);
lean_inc_ref_n(v_inst_2649_, 2);
v___f_2657_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2657_, 0, v_inst_2649_);
lean_closure_set(v___f_2657_, 1, v_f_2650_);
lean_closure_set(v___f_2657_, 2, v_value_2656_);
v___f_2658_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2658_, 0, v_inst_2649_);
lean_closure_set(v___f_2658_, 1, v_f_2650_);
lean_closure_set(v___f_2658_, 2, v_type_2655_);
lean_closure_set(v___f_2658_, 3, v_toBind_2653_);
lean_closure_set(v___f_2658_, 4, v___f_2657_);
v___x_2659_ = lean_unsigned_to_nat(0u);
v___x_2660_ = lean_array_get_size(v_params_2654_);
v___x_2661_ = lean_box(0);
v___x_2662_ = lean_nat_dec_lt(v___x_2659_, v___x_2660_);
if (v___x_2662_ == 0)
{
lean_object* v_toPure_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
lean_inc_ref(v_toApplicative_2652_);
lean_dec_ref(v_params_2654_);
lean_dec(v_f_2650_);
lean_dec_ref(v_inst_2649_);
v_toPure_2663_ = lean_ctor_get(v_toApplicative_2652_, 1);
lean_inc(v_toPure_2663_);
lean_dec_ref(v_toApplicative_2652_);
v___x_2664_ = lean_apply_2(v_toPure_2663_, lean_box(0), v___x_2661_);
v___x_2665_ = lean_apply_4(v_toBind_2653_, lean_box(0), lean_box(0), v___x_2664_, v___f_2658_);
return v___x_2665_;
}
else
{
lean_object* v___f_2666_; uint8_t v___x_2667_; 
lean_inc_ref(v_inst_2649_);
v___f_2666_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_2666_, 0, v_inst_2649_);
lean_closure_set(v___f_2666_, 1, v_f_2650_);
v___x_2667_ = lean_nat_dec_le(v___x_2660_, v___x_2660_);
if (v___x_2667_ == 0)
{
if (v___x_2662_ == 0)
{
lean_object* v_toPure_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
lean_inc_ref(v_toApplicative_2652_);
lean_dec_ref(v___f_2666_);
lean_dec_ref(v_params_2654_);
lean_dec_ref(v_inst_2649_);
v_toPure_2668_ = lean_ctor_get(v_toApplicative_2652_, 1);
lean_inc(v_toPure_2668_);
lean_dec_ref(v_toApplicative_2652_);
v___x_2669_ = lean_apply_2(v_toPure_2668_, lean_box(0), v___x_2661_);
v___x_2670_ = lean_apply_4(v_toBind_2653_, lean_box(0), lean_box(0), v___x_2669_, v___f_2658_);
return v___x_2670_;
}
else
{
size_t v___x_2671_; size_t v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2671_ = ((size_t)0ULL);
v___x_2672_ = lean_usize_of_nat(v___x_2660_);
v___x_2673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2649_, v___f_2666_, v_params_2654_, v___x_2671_, v___x_2672_, v___x_2661_);
v___x_2674_ = lean_apply_4(v_toBind_2653_, lean_box(0), lean_box(0), v___x_2673_, v___f_2658_);
return v___x_2674_;
}
}
else
{
size_t v___x_2675_; size_t v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2675_ = ((size_t)0ULL);
v___x_2676_ = lean_usize_of_nat(v___x_2660_);
v___x_2677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2649_, v___f_2666_, v_params_2654_, v___x_2675_, v___x_2676_, v___x_2661_);
v___x_2678_ = lean_apply_4(v_toBind_2653_, lean_box(0), lean_box(0), v___x_2677_, v___f_2658_);
return v___x_2678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM(lean_object* v_m_2679_, uint8_t v_pu_2680_, lean_object* v_inst_2681_, lean_object* v_f_2682_, lean_object* v_decl_2683_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2681_, v_f_2682_, v_decl_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___boxed(lean_object* v_m_2685_, lean_object* v_pu_2686_, lean_object* v_inst_2687_, lean_object* v_f_2688_, lean_object* v_decl_2689_){
_start:
{
uint8_t v_pu_boxed_2690_; lean_object* v_res_2691_; 
v_pu_boxed_2690_ = lean_unbox(v_pu_2686_);
v_res_2691_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM(v_m_2685_, v_pu_boxed_2690_, v_inst_2687_, v_f_2688_, v_decl_2689_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(uint8_t v_pu_2692_, lean_object* v_m_2693_, lean_object* v_inst_2694_, lean_object* v_inst_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2692_, v_inst_2694_, v_inst_2695_, v___y_2696_, v___y_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed(lean_object* v_pu_2699_, lean_object* v_m_2700_, lean_object* v_inst_2701_, lean_object* v_inst_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
uint8_t v_pu_boxed_2705_; lean_object* v_res_2706_; 
v_pu_boxed_2705_ = lean_unbox(v_pu_2699_);
v_res_2706_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(v_pu_boxed_2705_, v_m_2700_, v_inst_2701_, v_inst_2702_, v___y_2703_, v___y_2704_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__1(lean_object* v_m_2707_, lean_object* v_inst_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2708_, v___y_2709_, v___y_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(uint8_t v_pu_2713_){
_start:
{
lean_object* v___x_2714_; lean_object* v___f_2715_; lean_object* v___f_2716_; lean_object* v___x_2717_; 
v___x_2714_ = lean_box(v_pu_2713_);
v___f_2715_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2715_, 0, v___x_2714_);
v___f_2716_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0));
v___x_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___f_2715_);
lean_ctor_set(v___x_2717_, 1, v___f_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___boxed(lean_object* v_pu_2718_){
_start:
{
uint8_t v_pu_boxed_2719_; lean_object* v_res_2720_; 
v_pu_boxed_2719_ = lean_unbox(v_pu_2718_);
v_res_2720_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(v_pu_boxed_2719_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0(lean_object* v_toPure_2721_, lean_object* v_____do__lift_2722_){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2723_, 0, v_____do__lift_2722_);
v___x_2724_ = lean_apply_2(v_toPure_2721_, lean_box(0), v___x_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1(lean_object* v_toPure_2725_, lean_object* v_____do__lift_2726_){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2727_, 0, v_____do__lift_2726_);
v___x_2728_ = lean_apply_2(v_toPure_2725_, lean_box(0), v___x_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2(lean_object* v_toPure_2729_, lean_object* v_____do__lift_2730_){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2731_, 0, v_____do__lift_2730_);
v___x_2732_ = lean_apply_2(v_toPure_2729_, lean_box(0), v___x_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3(lean_object* v_____do__lift_2733_, lean_object* v_i_2734_, lean_object* v_toPure_2735_, lean_object* v_____do__lift_2736_){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2737_, 0, v_____do__lift_2733_);
lean_ctor_set(v___x_2737_, 1, v_i_2734_);
lean_ctor_set(v___x_2737_, 2, v_____do__lift_2736_);
v___x_2738_ = lean_apply_2(v_toPure_2735_, lean_box(0), v___x_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(lean_object* v_i_2739_, lean_object* v_toPure_2740_, uint8_t v_pu_2741_, lean_object* v_inst_2742_, lean_object* v_f_2743_, lean_object* v_y_2744_, lean_object* v_toBind_2745_, lean_object* v_____do__lift_2746_){
_start:
{
lean_object* v___f_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___f_2747_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3), 4, 3);
lean_closure_set(v___f_2747_, 0, v_____do__lift_2746_);
lean_closure_set(v___f_2747_, 1, v_i_2739_);
lean_closure_set(v___f_2747_, 2, v_toPure_2740_);
v___x_2748_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_2741_, v_inst_2742_, v_f_2743_, v_y_2744_);
v___x_2749_ = lean_apply_4(v_toBind_2745_, lean_box(0), lean_box(0), v___x_2748_, v___f_2747_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed(lean_object* v_i_2750_, lean_object* v_toPure_2751_, lean_object* v_pu_2752_, lean_object* v_inst_2753_, lean_object* v_f_2754_, lean_object* v_y_2755_, lean_object* v_toBind_2756_, lean_object* v_____do__lift_2757_){
_start:
{
uint8_t v_pu_boxed_2758_; lean_object* v_res_2759_; 
v_pu_boxed_2758_ = lean_unbox(v_pu_2752_);
v_res_2759_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(v_i_2750_, v_toPure_2751_, v_pu_boxed_2758_, v_inst_2753_, v_f_2754_, v_y_2755_, v_toBind_2756_, v_____do__lift_2757_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5(lean_object* v_____do__lift_2760_, lean_object* v_i_2761_, lean_object* v_toPure_2762_, lean_object* v_____do__lift_2763_){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_2764_, 0, v_____do__lift_2760_);
lean_ctor_set(v___x_2764_, 1, v_i_2761_);
lean_ctor_set(v___x_2764_, 2, v_____do__lift_2763_);
v___x_2765_ = lean_apply_2(v_toPure_2762_, lean_box(0), v___x_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6(lean_object* v_i_2766_, lean_object* v_toPure_2767_, lean_object* v_f_2768_, lean_object* v_y_2769_, lean_object* v_toBind_2770_, lean_object* v_____do__lift_2771_){
_start:
{
lean_object* v___f_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___f_2772_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5), 4, 3);
lean_closure_set(v___f_2772_, 0, v_____do__lift_2771_);
lean_closure_set(v___f_2772_, 1, v_i_2766_);
lean_closure_set(v___f_2772_, 2, v_toPure_2767_);
v___x_2773_ = lean_apply_1(v_f_2768_, v_y_2769_);
v___x_2774_ = lean_apply_4(v_toBind_2770_, lean_box(0), lean_box(0), v___x_2773_, v___f_2772_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7(lean_object* v_____do__lift_2775_, lean_object* v_i_2776_, lean_object* v_offset_2777_, lean_object* v_____do__lift_2778_, lean_object* v_toPure_2779_, lean_object* v_____do__lift_2780_){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v___x_2781_, 0, v_____do__lift_2775_);
lean_ctor_set(v___x_2781_, 1, v_i_2776_);
lean_ctor_set(v___x_2781_, 2, v_offset_2777_);
lean_ctor_set(v___x_2781_, 3, v_____do__lift_2778_);
lean_ctor_set(v___x_2781_, 4, v_____do__lift_2780_);
v___x_2782_ = lean_apply_2(v_toPure_2779_, lean_box(0), v___x_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8(lean_object* v_____do__lift_2783_, lean_object* v_i_2784_, lean_object* v_offset_2785_, lean_object* v_toPure_2786_, lean_object* v_inst_2787_, lean_object* v_f_2788_, lean_object* v_ty_2789_, lean_object* v_toBind_2790_, lean_object* v_____do__lift_2791_){
_start:
{
lean_object* v___f_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___f_2792_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7), 6, 5);
lean_closure_set(v___f_2792_, 0, v_____do__lift_2783_);
lean_closure_set(v___f_2792_, 1, v_i_2784_);
lean_closure_set(v___f_2792_, 2, v_offset_2785_);
lean_closure_set(v___f_2792_, 3, v_____do__lift_2791_);
lean_closure_set(v___f_2792_, 4, v_toPure_2786_);
v___x_2793_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2787_, v_f_2788_, v_ty_2789_);
v___x_2794_ = lean_apply_4(v_toBind_2790_, lean_box(0), lean_box(0), v___x_2793_, v___f_2792_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9(lean_object* v_i_2795_, lean_object* v_offset_2796_, lean_object* v_toPure_2797_, lean_object* v_inst_2798_, lean_object* v_f_2799_, lean_object* v_ty_2800_, lean_object* v_toBind_2801_, lean_object* v_y_2802_, lean_object* v_____do__lift_2803_){
_start:
{
lean_object* v___f_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
lean_inc(v_toBind_2801_);
lean_inc(v_f_2799_);
v___f_2804_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8), 9, 8);
lean_closure_set(v___f_2804_, 0, v_____do__lift_2803_);
lean_closure_set(v___f_2804_, 1, v_i_2795_);
lean_closure_set(v___f_2804_, 2, v_offset_2796_);
lean_closure_set(v___f_2804_, 3, v_toPure_2797_);
lean_closure_set(v___f_2804_, 4, v_inst_2798_);
lean_closure_set(v___f_2804_, 5, v_f_2799_);
lean_closure_set(v___f_2804_, 6, v_ty_2800_);
lean_closure_set(v___f_2804_, 7, v_toBind_2801_);
v___x_2805_ = lean_apply_1(v_f_2799_, v_y_2802_);
v___x_2806_ = lean_apply_4(v_toBind_2801_, lean_box(0), lean_box(0), v___x_2805_, v___f_2804_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10(lean_object* v_cidx_2807_, lean_object* v_toPure_2808_, lean_object* v_____do__lift_2809_){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2810_, 0, v_____do__lift_2809_);
lean_ctor_set(v___x_2810_, 1, v_cidx_2807_);
v___x_2811_ = lean_apply_2(v_toPure_2808_, lean_box(0), v___x_2810_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(lean_object* v_n_2812_, uint8_t v_check_2813_, uint8_t v_persistent_2814_, lean_object* v_toPure_2815_, lean_object* v_____do__lift_2816_){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v___x_2817_, 0, v_____do__lift_2816_);
lean_ctor_set(v___x_2817_, 1, v_n_2812_);
lean_ctor_set_uint8(v___x_2817_, sizeof(void*)*2, v_check_2813_);
lean_ctor_set_uint8(v___x_2817_, sizeof(void*)*2 + 1, v_persistent_2814_);
v___x_2818_ = lean_apply_2(v_toPure_2815_, lean_box(0), v___x_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed(lean_object* v_n_2819_, lean_object* v_check_2820_, lean_object* v_persistent_2821_, lean_object* v_toPure_2822_, lean_object* v_____do__lift_2823_){
_start:
{
uint8_t v_check_923__boxed_2824_; uint8_t v_persistent_924__boxed_2825_; lean_object* v_res_2826_; 
v_check_923__boxed_2824_ = lean_unbox(v_check_2820_);
v_persistent_924__boxed_2825_ = lean_unbox(v_persistent_2821_);
v_res_2826_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(v_n_2819_, v_check_923__boxed_2824_, v_persistent_924__boxed_2825_, v_toPure_2822_, v_____do__lift_2823_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(lean_object* v_n_2827_, uint8_t v_check_2828_, uint8_t v_persistent_2829_, lean_object* v_objs_x3f_2830_, lean_object* v_toPure_2831_, lean_object* v_____do__lift_2832_){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_alloc_ctor(8, 3, 2);
lean_ctor_set(v___x_2833_, 0, v_____do__lift_2832_);
lean_ctor_set(v___x_2833_, 1, v_n_2827_);
lean_ctor_set(v___x_2833_, 2, v_objs_x3f_2830_);
lean_ctor_set_uint8(v___x_2833_, sizeof(void*)*3, v_check_2828_);
lean_ctor_set_uint8(v___x_2833_, sizeof(void*)*3 + 1, v_persistent_2829_);
v___x_2834_ = lean_apply_2(v_toPure_2831_, lean_box(0), v___x_2833_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed(lean_object* v_n_2835_, lean_object* v_check_2836_, lean_object* v_persistent_2837_, lean_object* v_objs_x3f_2838_, lean_object* v_toPure_2839_, lean_object* v_____do__lift_2840_){
_start:
{
uint8_t v_check_939__boxed_2841_; uint8_t v_persistent_940__boxed_2842_; lean_object* v_res_2843_; 
v_check_939__boxed_2841_ = lean_unbox(v_check_2836_);
v_persistent_940__boxed_2842_ = lean_unbox(v_persistent_2837_);
v_res_2843_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(v_n_2835_, v_check_939__boxed_2841_, v_persistent_940__boxed_2842_, v_objs_x3f_2838_, v_toPure_2839_, v_____do__lift_2840_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13(lean_object* v_toPure_2844_, lean_object* v_____do__lift_2845_){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2846_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2846_, 0, v_____do__lift_2845_);
v___x_2847_ = lean_apply_2(v_toPure_2844_, lean_box(0), v___x_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(uint8_t v_pu_2848_, lean_object* v_m_2849_, lean_object* v_inst_2850_, lean_object* v_inst_2851_, lean_object* v_f_2852_, lean_object* v_decl_2853_){
_start:
{
switch(lean_obj_tag(v_decl_2853_))
{
case 0:
{
lean_object* v_toApplicative_2854_; lean_object* v_toBind_2855_; lean_object* v_toPure_2856_; lean_object* v_decl_2857_; lean_object* v___f_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v_toApplicative_2854_ = lean_ctor_get(v_inst_2851_, 0);
v_toBind_2855_ = lean_ctor_get(v_inst_2851_, 1);
lean_inc(v_toBind_2855_);
v_toPure_2856_ = lean_ctor_get(v_toApplicative_2854_, 1);
v_decl_2857_ = lean_ctor_get(v_decl_2853_, 0);
lean_inc_ref(v_decl_2857_);
lean_dec_ref_known(v_decl_2853_, 1);
lean_inc(v_toPure_2856_);
v___f_2858_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0), 2, 1);
lean_closure_set(v___f_2858_, 0, v_toPure_2856_);
v___x_2859_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_2848_, v_inst_2850_, v_inst_2851_, v_f_2852_, v_decl_2857_);
v___x_2860_ = lean_apply_4(v_toBind_2855_, lean_box(0), lean_box(0), v___x_2859_, v___f_2858_);
return v___x_2860_;
}
case 1:
{
lean_object* v_toApplicative_2861_; lean_object* v_toBind_2862_; lean_object* v_toPure_2863_; lean_object* v_decl_2864_; lean_object* v___f_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v_toApplicative_2861_ = lean_ctor_get(v_inst_2851_, 0);
v_toBind_2862_ = lean_ctor_get(v_inst_2851_, 1);
lean_inc(v_toBind_2862_);
v_toPure_2863_ = lean_ctor_get(v_toApplicative_2861_, 1);
v_decl_2864_ = lean_ctor_get(v_decl_2853_, 0);
lean_inc_ref(v_decl_2864_);
lean_dec_ref_known(v_decl_2853_, 1);
lean_inc(v_toPure_2863_);
v___f_2865_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1), 2, 1);
lean_closure_set(v___f_2865_, 0, v_toPure_2863_);
v___x_2866_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2848_, v_inst_2850_, v_inst_2851_, v_f_2852_, v_decl_2864_);
v___x_2867_ = lean_apply_4(v_toBind_2862_, lean_box(0), lean_box(0), v___x_2866_, v___f_2865_);
return v___x_2867_;
}
case 2:
{
lean_object* v_toApplicative_2868_; lean_object* v_toBind_2869_; lean_object* v_toPure_2870_; lean_object* v_decl_2871_; lean_object* v___f_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v_toApplicative_2868_ = lean_ctor_get(v_inst_2851_, 0);
v_toBind_2869_ = lean_ctor_get(v_inst_2851_, 1);
lean_inc(v_toBind_2869_);
v_toPure_2870_ = lean_ctor_get(v_toApplicative_2868_, 1);
v_decl_2871_ = lean_ctor_get(v_decl_2853_, 0);
lean_inc_ref(v_decl_2871_);
lean_dec_ref_known(v_decl_2853_, 1);
lean_inc(v_toPure_2870_);
v___f_2872_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2), 2, 1);
lean_closure_set(v___f_2872_, 0, v_toPure_2870_);
v___x_2873_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2848_, v_inst_2850_, v_inst_2851_, v_f_2852_, v_decl_2871_);
v___x_2874_ = lean_apply_4(v_toBind_2869_, lean_box(0), lean_box(0), v___x_2873_, v___f_2872_);
return v___x_2874_;
}
case 3:
{
lean_object* v_toApplicative_2875_; lean_object* v_toBind_2876_; lean_object* v_toPure_2877_; lean_object* v_fvarId_2878_; lean_object* v_i_2879_; lean_object* v_y_2880_; lean_object* v___x_2881_; lean_object* v___f_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v_toApplicative_2875_ = lean_ctor_get(v_inst_2851_, 0);
lean_dec(v_inst_2850_);
v_toBind_2876_ = lean_ctor_get(v_inst_2851_, 1);
lean_inc_n(v_toBind_2876_, 2);
v_toPure_2877_ = lean_ctor_get(v_toApplicative_2875_, 1);
lean_inc(v_toPure_2877_);
v_fvarId_2878_ = lean_ctor_get(v_decl_2853_, 0);
lean_inc(v_fvarId_2878_);
v_i_2879_ = lean_ctor_get(v_decl_2853_, 1);
lean_inc(v_i_2879_);
v_y_2880_ = lean_ctor_get(v_decl_2853_, 2);
lean_inc(v_y_2880_);
lean_dec_ref_known(v_decl_2853_, 3);
v___x_2881_ = lean_box(v_pu_2848_);
lean_inc(v_f_2852_);
v___f_2882_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed), 8, 7);
lean_closure_set(v___f_2882_, 0, v_i_2879_);
lean_closure_set(v___f_2882_, 1, v_toPure_2877_);
lean_closure_set(v___f_2882_, 2, v___x_2881_);
lean_closure_set(v___f_2882_, 3, v_inst_2851_);
lean_closure_set(v___f_2882_, 4, v_f_2852_);
lean_closure_set(v___f_2882_, 5, v_y_2880_);
lean_closure_set(v___f_2882_, 6, v_toBind_2876_);
v___x_2883_ = lean_apply_1(v_f_2852_, v_fvarId_2878_);
v___x_2884_ = lean_apply_4(v_toBind_2876_, lean_box(0), lean_box(0), v___x_2883_, v___f_2882_);
return v___x_2884_;
}
case 4:
{
lean_object* v_toApplicative_2885_; lean_object* v_toBind_2886_; lean_object* v_toPure_2887_; lean_object* v_fvarId_2888_; lean_object* v_i_2889_; lean_object* v_y_2890_; lean_object* v___f_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v_toApplicative_2885_ = lean_ctor_get(v_inst_2851_, 0);
lean_inc_ref(v_toApplicative_2885_);
lean_dec(v_inst_2850_);
v_toBind_2886_ = lean_ctor_get(v_inst_2851_, 1);
lean_inc_n(v_toBind_2886_, 2);
lean_dec_ref(v_inst_2851_);
v_toPure_2887_ = lean_ctor_get(v_toApplicative_2885_, 1);
lean_inc(v_toPure_2887_);
lean_dec_ref(v_toApplicative_2885_);
v_fvarId_2888_ = lean_ctor_get(v_decl_2853_, 0);
lean_inc(v_fvarId_2888_);
v_i_2889_ = lean_ctor_get(v_decl_2853_, 1);
lean_inc(v_i_2889_);
v_y_2890_ = lean_ctor_get(v_decl_2853_, 2);
lean_inc(v_y_2890_);
lean_dec_ref_known(v_decl_2853_, 3);
lean_inc(v_f_2852_);
v___f_2891_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6), 6, 5);
lean_closure_set(v___f_2891_, 0, v_i_2889_);
lean_closure_set(v___f_2891_, 1, v_toPure_2887_);
lean_closure_set(v___f_2891_, 2, v_f_2852_);
lean_closure_set(v___f_2891_, 3, v_y_2890_);
lean_closure_set(v___f_2891_, 4, v_toBind_2886_);
v___x_2892_ = lean_apply_1(v_f_2852_, v_fvarId_2888_);
v___x_2893_ = lean_apply_4(v_toBind_2886_, lean_box(0), lean_box(0), v___x_2892_, v___f_2891_);
return v___x_2893_;
}
case 5:
{
lean_object* v_toApplicative_2894_; lean_object* v_toBind_2895_; lean_object* v_toPure_2896_; lean_object* v_fvarId_2897_; lean_object* v_i_2898_; lean_object* v_offset_2899_; lean_object* v_y_2900_; lean_object* v_ty_2901_; lean_object* v___f_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
v_toApplicative_2894_ = lean_ctor_get(v_inst_2851_, 0);
lean_dec(v_inst_2850_);
v_toBind_2895_ = lean_ctor_get(v_inst_2851_, 1);
lean_inc_n(v_toBind_2895_, 2);
v_toPure_2896_ = lean_ctor_get(v_toApplicative_2894_, 1);
lean_inc(v_toPure_2896_);
v_fvarId_2897_ = lean_ctor_get(v_decl_2853_, 0);
lean_inc(v_fvarId_2897_);
v_i_2898_ = lean_ctor_get(v_decl_2853_, 1);
lean_inc(v_i_2898_);
v_offset_2899_ = lean_ctor_get(v_decl_2853_, 2);
lean_inc(v_offset_2899_);
v_y_2900_ = lean_ctor_get(v_decl_2853_, 3);
lean_inc(v_y_2900_);
v_ty_2901_ = lean_ctor_get(v_decl_2853_, 4);
lean_inc_ref(v_ty_2901_);
lean_dec_ref_known(v_decl_2853_, 5);
lean_inc(v_f_2852_);
v___f_2902_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9), 9, 8);
lean_closure_set(v___f_2902_, 0, v_i_2898_);
lean_closure_set(v___f_2902_, 1, v_offset_2899_);
lean_closure_set(v___f_2902_, 2, v_toPure_2896_);
lean_closure_set(v___f_2902_, 3, v_inst_2851_);
lean_closure_set(v___f_2902_, 4, v_f_2852_);
lean_closure_set(v___f_2902_, 5, v_ty_2901_);
lean_closure_set(v___f_2902_, 6, v_toBind_2895_);
lean_closure_set(v___f_2902_, 7, v_y_2900_);
v___x_2903_ = lean_apply_1(v_f_2852_, v_fvarId_2897_);
v___x_2904_ = lean_apply_4(v_toBind_2895_, lean_box(0), lean_box(0), v___x_2903_, v___f_2902_);
return v___x_2904_;
}
case 6:
{
lean_object* v_toApplicative_2905_; lean_object* v_toBind_2906_; lean_object* v_toPure_2907_; lean_object* v_fvarId_2908_; lean_object* v_cidx_2909_; lean_object* v___f_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v_toApplicative_2905_ = lean_ctor_get(v_inst_2851_, 0);
lean_inc_ref(v_toApplicative_2905_);
lean_dec(v_inst_2850_);
v_toBind_2906_ = lean_ctor_get(v_inst_2851_, 1);
lean_inc(v_toBind_2906_);
lean_dec_ref(v_inst_2851_);
v_toPure_2907_ = lean_ctor_get(v_toApplicative_2905_, 1);
lean_inc(v_toPure_2907_);
lean_dec_ref(v_toApplicative_2905_);
v_fvarId_2908_ = lean_ctor_get(v_decl_2853_, 0);
lean_inc(v_fvarId_2908_);
v_cidx_2909_ = lean_ctor_get(v_decl_2853_, 1);
lean_inc(v_cidx_2909_);
lean_dec_ref_known(v_decl_2853_, 2);
v___f_2910_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10), 3, 2);
lean_closure_set(v___f_2910_, 0, v_cidx_2909_);
lean_closure_set(v___f_2910_, 1, v_toPure_2907_);
v___x_2911_ = lean_apply_1(v_f_2852_, v_fvarId_2908_);
v___x_2912_ = lean_apply_4(v_toBind_2906_, lean_box(0), lean_box(0), v___x_2911_, v___f_2910_);
return v___x_2912_;
}
case 7:
{
lean_object* v_toApplicative_2913_; lean_object* v_toBind_2914_; lean_object* v_toPure_2915_; lean_object* v_fvarId_2916_; lean_object* v_n_2917_; uint8_t v_check_2918_; uint8_t v_persistent_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___f_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v_toApplicative_2913_ = lean_ctor_get(v_inst_2851_, 0);
lean_inc_ref(v_toApplicative_2913_);
lean_dec(v_inst_2850_);
v_toBind_2914_ = lean_ctor_get(v_inst_2851_, 1);
lean_inc(v_toBind_2914_);
lean_dec_ref(v_inst_2851_);
v_toPure_2915_ = lean_ctor_get(v_toApplicative_2913_, 1);
lean_inc(v_toPure_2915_);
lean_dec_ref(v_toApplicative_2913_);
v_fvarId_2916_ = lean_ctor_get(v_decl_2853_, 0);
lean_inc(v_fvarId_2916_);
v_n_2917_ = lean_ctor_get(v_decl_2853_, 1);
lean_inc(v_n_2917_);
v_check_2918_ = lean_ctor_get_uint8(v_decl_2853_, sizeof(void*)*2);
v_persistent_2919_ = lean_ctor_get_uint8(v_decl_2853_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_decl_2853_, 2);
v___x_2920_ = lean_box(v_check_2918_);
v___x_2921_ = lean_box(v_persistent_2919_);
v___f_2922_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed), 5, 4);
lean_closure_set(v___f_2922_, 0, v_n_2917_);
lean_closure_set(v___f_2922_, 1, v___x_2920_);
lean_closure_set(v___f_2922_, 2, v___x_2921_);
lean_closure_set(v___f_2922_, 3, v_toPure_2915_);
v___x_2923_ = lean_apply_1(v_f_2852_, v_fvarId_2916_);
v___x_2924_ = lean_apply_4(v_toBind_2914_, lean_box(0), lean_box(0), v___x_2923_, v___f_2922_);
return v___x_2924_;
}
case 8:
{
lean_object* v_toApplicative_2925_; lean_object* v_toBind_2926_; lean_object* v_toPure_2927_; lean_object* v_fvarId_2928_; lean_object* v_n_2929_; uint8_t v_check_2930_; uint8_t v_persistent_2931_; lean_object* v_objs_x3f_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___f_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v_toApplicative_2925_ = lean_ctor_get(v_inst_2851_, 0);
lean_inc_ref(v_toApplicative_2925_);
lean_dec(v_inst_2850_);
v_toBind_2926_ = lean_ctor_get(v_inst_2851_, 1);
lean_inc(v_toBind_2926_);
lean_dec_ref(v_inst_2851_);
v_toPure_2927_ = lean_ctor_get(v_toApplicative_2925_, 1);
lean_inc(v_toPure_2927_);
lean_dec_ref(v_toApplicative_2925_);
v_fvarId_2928_ = lean_ctor_get(v_decl_2853_, 0);
lean_inc(v_fvarId_2928_);
v_n_2929_ = lean_ctor_get(v_decl_2853_, 1);
lean_inc(v_n_2929_);
v_check_2930_ = lean_ctor_get_uint8(v_decl_2853_, sizeof(void*)*3);
v_persistent_2931_ = lean_ctor_get_uint8(v_decl_2853_, sizeof(void*)*3 + 1);
v_objs_x3f_2932_ = lean_ctor_get(v_decl_2853_, 2);
lean_inc(v_objs_x3f_2932_);
lean_dec_ref_known(v_decl_2853_, 3);
v___x_2933_ = lean_box(v_check_2930_);
v___x_2934_ = lean_box(v_persistent_2931_);
v___f_2935_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed), 6, 5);
lean_closure_set(v___f_2935_, 0, v_n_2929_);
lean_closure_set(v___f_2935_, 1, v___x_2933_);
lean_closure_set(v___f_2935_, 2, v___x_2934_);
lean_closure_set(v___f_2935_, 3, v_objs_x3f_2932_);
lean_closure_set(v___f_2935_, 4, v_toPure_2927_);
v___x_2936_ = lean_apply_1(v_f_2852_, v_fvarId_2928_);
v___x_2937_ = lean_apply_4(v_toBind_2926_, lean_box(0), lean_box(0), v___x_2936_, v___f_2935_);
return v___x_2937_;
}
default: 
{
lean_object* v_toApplicative_2938_; lean_object* v_toBind_2939_; lean_object* v_toPure_2940_; lean_object* v_fvarId_2941_; lean_object* v___f_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v_toApplicative_2938_ = lean_ctor_get(v_inst_2851_, 0);
lean_inc_ref(v_toApplicative_2938_);
lean_dec(v_inst_2850_);
v_toBind_2939_ = lean_ctor_get(v_inst_2851_, 1);
lean_inc(v_toBind_2939_);
lean_dec_ref(v_inst_2851_);
v_toPure_2940_ = lean_ctor_get(v_toApplicative_2938_, 1);
lean_inc(v_toPure_2940_);
lean_dec_ref(v_toApplicative_2938_);
v_fvarId_2941_ = lean_ctor_get(v_decl_2853_, 0);
lean_inc(v_fvarId_2941_);
lean_dec_ref_known(v_decl_2853_, 1);
v___f_2942_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13), 2, 1);
lean_closure_set(v___f_2942_, 0, v_toPure_2940_);
v___x_2943_ = lean_apply_1(v_f_2852_, v_fvarId_2941_);
v___x_2944_ = lean_apply_4(v_toBind_2939_, lean_box(0), lean_box(0), v___x_2943_, v___f_2942_);
return v___x_2944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed(lean_object* v_pu_2945_, lean_object* v_m_2946_, lean_object* v_inst_2947_, lean_object* v_inst_2948_, lean_object* v_f_2949_, lean_object* v_decl_2950_){
_start:
{
uint8_t v_pu_boxed_2951_; lean_object* v_res_2952_; 
v_pu_boxed_2951_ = lean_unbox(v_pu_2945_);
v_res_2952_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(v_pu_boxed_2951_, v_m_2946_, v_inst_2947_, v_inst_2948_, v_f_2949_, v_decl_2950_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15(lean_object* v_inst_2953_, lean_object* v_f_2954_, lean_object* v_y_2955_, lean_object* v_____r_2956_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2953_, v_f_2954_, v_y_2955_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16(lean_object* v_f_2958_, lean_object* v_y_2959_, lean_object* v_____r_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_apply_1(v_f_2958_, v_y_2959_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17(lean_object* v_inst_2962_, lean_object* v_f_2963_, lean_object* v_ty_2964_, lean_object* v_____r_2965_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2962_, v_f_2963_, v_ty_2964_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18(lean_object* v_f_2967_, lean_object* v_y_2968_, lean_object* v_toBind_2969_, lean_object* v___f_2970_, lean_object* v_____r_2971_){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = lean_apply_1(v_f_2967_, v_y_2968_);
v___x_2973_ = lean_apply_4(v_toBind_2969_, lean_box(0), lean_box(0), v___x_2972_, v___f_2970_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__19(lean_object* v_m_2974_, lean_object* v_inst_2975_, lean_object* v_f_2976_, lean_object* v_decl_2977_){
_start:
{
switch(lean_obj_tag(v_decl_2977_))
{
case 0:
{
lean_object* v_decl_2978_; lean_object* v___x_2979_; 
v_decl_2978_ = lean_ctor_get(v_decl_2977_, 0);
lean_inc_ref(v_decl_2978_);
lean_dec_ref_known(v_decl_2977_, 1);
v___x_2979_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_2975_, v_f_2976_, v_decl_2978_);
return v___x_2979_;
}
case 1:
{
lean_object* v_decl_2980_; lean_object* v___x_2981_; 
v_decl_2980_ = lean_ctor_get(v_decl_2977_, 0);
lean_inc_ref(v_decl_2980_);
lean_dec_ref_known(v_decl_2977_, 1);
v___x_2981_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2975_, v_f_2976_, v_decl_2980_);
return v___x_2981_;
}
case 2:
{
lean_object* v_decl_2982_; lean_object* v___x_2983_; 
v_decl_2982_ = lean_ctor_get(v_decl_2977_, 0);
lean_inc_ref(v_decl_2982_);
lean_dec_ref_known(v_decl_2977_, 1);
v___x_2983_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2975_, v_f_2976_, v_decl_2982_);
return v___x_2983_;
}
case 3:
{
lean_object* v_toBind_2984_; lean_object* v_fvarId_2985_; lean_object* v_y_2986_; lean_object* v___f_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v_toBind_2984_ = lean_ctor_get(v_inst_2975_, 1);
lean_inc(v_toBind_2984_);
v_fvarId_2985_ = lean_ctor_get(v_decl_2977_, 0);
lean_inc(v_fvarId_2985_);
v_y_2986_ = lean_ctor_get(v_decl_2977_, 2);
lean_inc(v_y_2986_);
lean_dec_ref_known(v_decl_2977_, 3);
lean_inc(v_f_2976_);
v___f_2987_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15), 4, 3);
lean_closure_set(v___f_2987_, 0, v_inst_2975_);
lean_closure_set(v___f_2987_, 1, v_f_2976_);
lean_closure_set(v___f_2987_, 2, v_y_2986_);
v___x_2988_ = lean_apply_1(v_f_2976_, v_fvarId_2985_);
v___x_2989_ = lean_apply_4(v_toBind_2984_, lean_box(0), lean_box(0), v___x_2988_, v___f_2987_);
return v___x_2989_;
}
case 4:
{
lean_object* v_toBind_2990_; lean_object* v_fvarId_2991_; lean_object* v_y_2992_; lean_object* v___f_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v_toBind_2990_ = lean_ctor_get(v_inst_2975_, 1);
lean_inc(v_toBind_2990_);
lean_dec_ref(v_inst_2975_);
v_fvarId_2991_ = lean_ctor_get(v_decl_2977_, 0);
lean_inc(v_fvarId_2991_);
v_y_2992_ = lean_ctor_get(v_decl_2977_, 2);
lean_inc(v_y_2992_);
lean_dec_ref_known(v_decl_2977_, 3);
lean_inc(v_f_2976_);
v___f_2993_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16), 3, 2);
lean_closure_set(v___f_2993_, 0, v_f_2976_);
lean_closure_set(v___f_2993_, 1, v_y_2992_);
v___x_2994_ = lean_apply_1(v_f_2976_, v_fvarId_2991_);
v___x_2995_ = lean_apply_4(v_toBind_2990_, lean_box(0), lean_box(0), v___x_2994_, v___f_2993_);
return v___x_2995_;
}
case 5:
{
lean_object* v_toBind_2996_; lean_object* v_fvarId_2997_; lean_object* v_y_2998_; lean_object* v_ty_2999_; lean_object* v___f_3000_; lean_object* v___f_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v_toBind_2996_ = lean_ctor_get(v_inst_2975_, 1);
lean_inc_n(v_toBind_2996_, 2);
v_fvarId_2997_ = lean_ctor_get(v_decl_2977_, 0);
lean_inc(v_fvarId_2997_);
v_y_2998_ = lean_ctor_get(v_decl_2977_, 3);
lean_inc(v_y_2998_);
v_ty_2999_ = lean_ctor_get(v_decl_2977_, 4);
lean_inc_ref(v_ty_2999_);
lean_dec_ref_known(v_decl_2977_, 5);
lean_inc_n(v_f_2976_, 2);
v___f_3000_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17), 4, 3);
lean_closure_set(v___f_3000_, 0, v_inst_2975_);
lean_closure_set(v___f_3000_, 1, v_f_2976_);
lean_closure_set(v___f_3000_, 2, v_ty_2999_);
v___f_3001_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18), 5, 4);
lean_closure_set(v___f_3001_, 0, v_f_2976_);
lean_closure_set(v___f_3001_, 1, v_y_2998_);
lean_closure_set(v___f_3001_, 2, v_toBind_2996_);
lean_closure_set(v___f_3001_, 3, v___f_3000_);
v___x_3002_ = lean_apply_1(v_f_2976_, v_fvarId_2997_);
v___x_3003_ = lean_apply_4(v_toBind_2996_, lean_box(0), lean_box(0), v___x_3002_, v___f_3001_);
return v___x_3003_;
}
default: 
{
lean_object* v_fvarId_3004_; lean_object* v___x_3005_; 
lean_dec_ref(v_inst_2975_);
v_fvarId_3004_ = lean_ctor_get(v_decl_2977_, 0);
lean_inc(v_fvarId_3004_);
lean_dec_ref(v_decl_2977_);
v___x_3005_ = lean_apply_1(v_f_2976_, v_fvarId_3004_);
return v___x_3005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(uint8_t v_pu_3007_){
_start:
{
lean_object* v___x_3008_; lean_object* v___f_3009_; lean_object* v___f_3010_; lean_object* v___x_3011_; 
v___x_3008_ = lean_box(v_pu_3007_);
v___f_3009_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed), 6, 1);
lean_closure_set(v___f_3009_, 0, v___x_3008_);
v___f_3010_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0));
v___x_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___f_3009_);
lean_ctor_set(v___x_3011_, 1, v___f_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___boxed(lean_object* v_pu_3012_){
_start:
{
uint8_t v_pu_boxed_3013_; lean_object* v_res_3014_; 
v_pu_boxed_3013_ = lean_unbox(v_pu_3012_);
v_res_3014_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(v_pu_boxed_3013_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0(lean_object* v_ctorName_3015_, lean_object* v_params_3016_, lean_object* v_toPure_3017_, lean_object* v_____do__lift_3018_){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3019_, 0, v_ctorName_3015_);
lean_ctor_set(v___x_3019_, 1, v_params_3016_);
lean_ctor_set(v___x_3019_, 2, v_____do__lift_3018_);
v___x_3020_ = lean_apply_2(v_toPure_3017_, lean_box(0), v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(lean_object* v_ctorName_3021_, lean_object* v_toPure_3022_, uint8_t v_pu_3023_, lean_object* v_inst_3024_, lean_object* v_inst_3025_, lean_object* v_f_3026_, lean_object* v_code_3027_, lean_object* v_toBind_3028_, lean_object* v_params_3029_){
_start:
{
lean_object* v___f_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___f_3030_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0), 4, 3);
lean_closure_set(v___f_3030_, 0, v_ctorName_3021_);
lean_closure_set(v___f_3030_, 1, v_params_3029_);
lean_closure_set(v___f_3030_, 2, v_toPure_3022_);
v___x_3031_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_3023_, v_inst_3024_, v_inst_3025_, v_f_3026_, v_code_3027_);
v___x_3032_ = lean_apply_4(v_toBind_3028_, lean_box(0), lean_box(0), v___x_3031_, v___f_3030_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed(lean_object* v_ctorName_3033_, lean_object* v_toPure_3034_, lean_object* v_pu_3035_, lean_object* v_inst_3036_, lean_object* v_inst_3037_, lean_object* v_f_3038_, lean_object* v_code_3039_, lean_object* v_toBind_3040_, lean_object* v_params_3041_){
_start:
{
uint8_t v_pu_boxed_3042_; lean_object* v_res_3043_; 
v_pu_boxed_3042_ = lean_unbox(v_pu_3035_);
v_res_3043_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(v_ctorName_3033_, v_toPure_3034_, v_pu_boxed_3042_, v_inst_3036_, v_inst_3037_, v_f_3038_, v_code_3039_, v_toBind_3040_, v_params_3041_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2(lean_object* v_info_3044_, lean_object* v_toPure_3045_, lean_object* v_____do__lift_3046_){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3047_, 0, v_info_3044_);
lean_ctor_set(v___x_3047_, 1, v_____do__lift_3046_);
v___x_3048_ = lean_apply_2(v_toPure_3045_, lean_box(0), v___x_3047_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3(lean_object* v_toPure_3049_, lean_object* v_____do__lift_3050_){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3051_, 0, v_____do__lift_3050_);
v___x_3052_ = lean_apply_2(v_toPure_3049_, lean_box(0), v___x_3051_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(uint8_t v_pu_3053_, lean_object* v_m_3054_, lean_object* v_inst_3055_, lean_object* v_inst_3056_, lean_object* v_f_3057_, lean_object* v_alt_3058_){
_start:
{
switch(lean_obj_tag(v_alt_3058_))
{
case 0:
{
lean_object* v_toApplicative_3059_; lean_object* v_toBind_3060_; lean_object* v_toPure_3061_; lean_object* v_ctorName_3062_; lean_object* v_params_3063_; lean_object* v_code_3064_; lean_object* v___x_3065_; lean_object* v___f_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; size_t v_sz_3069_; size_t v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v_toApplicative_3059_ = lean_ctor_get(v_inst_3056_, 0);
v_toBind_3060_ = lean_ctor_get(v_inst_3056_, 1);
lean_inc_n(v_toBind_3060_, 2);
v_toPure_3061_ = lean_ctor_get(v_toApplicative_3059_, 1);
v_ctorName_3062_ = lean_ctor_get(v_alt_3058_, 0);
lean_inc(v_ctorName_3062_);
v_params_3063_ = lean_ctor_get(v_alt_3058_, 1);
lean_inc_ref(v_params_3063_);
v_code_3064_ = lean_ctor_get(v_alt_3058_, 2);
lean_inc_ref(v_code_3064_);
lean_dec_ref_known(v_alt_3058_, 3);
v___x_3065_ = lean_box(v_pu_3053_);
lean_inc(v_f_3057_);
lean_inc_ref_n(v_inst_3056_, 2);
lean_inc(v_inst_3055_);
lean_inc(v_toPure_3061_);
v___f_3066_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed), 9, 8);
lean_closure_set(v___f_3066_, 0, v_ctorName_3062_);
lean_closure_set(v___f_3066_, 1, v_toPure_3061_);
lean_closure_set(v___f_3066_, 2, v___x_3065_);
lean_closure_set(v___f_3066_, 3, v_inst_3055_);
lean_closure_set(v___f_3066_, 4, v_inst_3056_);
lean_closure_set(v___f_3066_, 5, v_f_3057_);
lean_closure_set(v___f_3066_, 6, v_code_3064_);
lean_closure_set(v___f_3066_, 7, v_toBind_3060_);
v___x_3067_ = lean_box(v_pu_3053_);
v___x_3068_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_3068_, 0, lean_box(0));
lean_closure_set(v___x_3068_, 1, v___x_3067_);
lean_closure_set(v___x_3068_, 2, v_inst_3055_);
lean_closure_set(v___x_3068_, 3, v_inst_3056_);
lean_closure_set(v___x_3068_, 4, v_f_3057_);
v_sz_3069_ = lean_array_size(v_params_3063_);
v___x_3070_ = ((size_t)0ULL);
v___x_3071_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3056_, v___x_3068_, v_sz_3069_, v___x_3070_, v_params_3063_);
v___x_3072_ = lean_apply_4(v_toBind_3060_, lean_box(0), lean_box(0), v___x_3071_, v___f_3066_);
return v___x_3072_;
}
case 1:
{
lean_object* v_toApplicative_3073_; lean_object* v_toBind_3074_; lean_object* v_toPure_3075_; lean_object* v_info_3076_; lean_object* v_code_3077_; lean_object* v___f_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v_toApplicative_3073_ = lean_ctor_get(v_inst_3056_, 0);
v_toBind_3074_ = lean_ctor_get(v_inst_3056_, 1);
lean_inc(v_toBind_3074_);
v_toPure_3075_ = lean_ctor_get(v_toApplicative_3073_, 1);
v_info_3076_ = lean_ctor_get(v_alt_3058_, 0);
lean_inc_ref(v_info_3076_);
v_code_3077_ = lean_ctor_get(v_alt_3058_, 1);
lean_inc_ref(v_code_3077_);
lean_dec_ref_known(v_alt_3058_, 2);
lean_inc(v_toPure_3075_);
v___f_3078_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2), 3, 2);
lean_closure_set(v___f_3078_, 0, v_info_3076_);
lean_closure_set(v___f_3078_, 1, v_toPure_3075_);
v___x_3079_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_3053_, v_inst_3055_, v_inst_3056_, v_f_3057_, v_code_3077_);
v___x_3080_ = lean_apply_4(v_toBind_3074_, lean_box(0), lean_box(0), v___x_3079_, v___f_3078_);
return v___x_3080_;
}
default: 
{
lean_object* v_toApplicative_3081_; lean_object* v_toBind_3082_; lean_object* v_toPure_3083_; lean_object* v_code_3084_; lean_object* v___f_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v_toApplicative_3081_ = lean_ctor_get(v_inst_3056_, 0);
v_toBind_3082_ = lean_ctor_get(v_inst_3056_, 1);
lean_inc(v_toBind_3082_);
v_toPure_3083_ = lean_ctor_get(v_toApplicative_3081_, 1);
v_code_3084_ = lean_ctor_get(v_alt_3058_, 0);
lean_inc_ref(v_code_3084_);
lean_dec_ref_known(v_alt_3058_, 1);
lean_inc(v_toPure_3083_);
v___f_3085_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3), 2, 1);
lean_closure_set(v___f_3085_, 0, v_toPure_3083_);
v___x_3086_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_3053_, v_inst_3055_, v_inst_3056_, v_f_3057_, v_code_3084_);
v___x_3087_ = lean_apply_4(v_toBind_3082_, lean_box(0), lean_box(0), v___x_3086_, v___f_3085_);
return v___x_3087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed(lean_object* v_pu_3088_, lean_object* v_m_3089_, lean_object* v_inst_3090_, lean_object* v_inst_3091_, lean_object* v_f_3092_, lean_object* v_alt_3093_){
_start:
{
uint8_t v_pu_boxed_3094_; lean_object* v_res_3095_; 
v_pu_boxed_3094_ = lean_unbox(v_pu_3088_);
v_res_3095_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(v_pu_boxed_3094_, v_m_3089_, v_inst_3090_, v_inst_3091_, v_f_3092_, v_alt_3093_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5(lean_object* v_inst_3096_, lean_object* v_f_3097_, lean_object* v_code_3098_, lean_object* v_____r_3099_){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_3096_, v_f_3097_, v_code_3098_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__7(lean_object* v_m_3101_, lean_object* v_inst_3102_, lean_object* v_f_3103_, lean_object* v_alt_3104_){
_start:
{
switch(lean_obj_tag(v_alt_3104_))
{
case 0:
{
lean_object* v_toApplicative_3105_; lean_object* v_toBind_3106_; lean_object* v_params_3107_; lean_object* v_code_3108_; lean_object* v___f_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; uint8_t v___x_3113_; 
v_toApplicative_3105_ = lean_ctor_get(v_inst_3102_, 0);
v_toBind_3106_ = lean_ctor_get(v_inst_3102_, 1);
lean_inc(v_toBind_3106_);
v_params_3107_ = lean_ctor_get(v_alt_3104_, 1);
lean_inc_ref(v_params_3107_);
v_code_3108_ = lean_ctor_get(v_alt_3104_, 2);
lean_inc_ref(v_code_3108_);
lean_dec_ref_known(v_alt_3104_, 3);
lean_inc(v_f_3103_);
lean_inc_ref(v_inst_3102_);
v___f_3109_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5), 4, 3);
lean_closure_set(v___f_3109_, 0, v_inst_3102_);
lean_closure_set(v___f_3109_, 1, v_f_3103_);
lean_closure_set(v___f_3109_, 2, v_code_3108_);
v___x_3110_ = lean_unsigned_to_nat(0u);
v___x_3111_ = lean_array_get_size(v_params_3107_);
v___x_3112_ = lean_box(0);
v___x_3113_ = lean_nat_dec_lt(v___x_3110_, v___x_3111_);
if (v___x_3113_ == 0)
{
lean_object* v_toPure_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
lean_inc_ref(v_toApplicative_3105_);
lean_dec_ref(v_params_3107_);
lean_dec(v_f_3103_);
lean_dec_ref(v_inst_3102_);
v_toPure_3114_ = lean_ctor_get(v_toApplicative_3105_, 1);
lean_inc(v_toPure_3114_);
lean_dec_ref(v_toApplicative_3105_);
v___x_3115_ = lean_apply_2(v_toPure_3114_, lean_box(0), v___x_3112_);
v___x_3116_ = lean_apply_4(v_toBind_3106_, lean_box(0), lean_box(0), v___x_3115_, v___f_3109_);
return v___x_3116_;
}
else
{
lean_object* v___f_3117_; uint8_t v___x_3118_; 
lean_inc_ref(v_inst_3102_);
v___f_3117_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_3117_, 0, v_inst_3102_);
lean_closure_set(v___f_3117_, 1, v_f_3103_);
v___x_3118_ = lean_nat_dec_le(v___x_3111_, v___x_3111_);
if (v___x_3118_ == 0)
{
if (v___x_3113_ == 0)
{
lean_object* v_toPure_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
lean_inc_ref(v_toApplicative_3105_);
lean_dec_ref(v___f_3117_);
lean_dec_ref(v_params_3107_);
lean_dec_ref(v_inst_3102_);
v_toPure_3119_ = lean_ctor_get(v_toApplicative_3105_, 1);
lean_inc(v_toPure_3119_);
lean_dec_ref(v_toApplicative_3105_);
v___x_3120_ = lean_apply_2(v_toPure_3119_, lean_box(0), v___x_3112_);
v___x_3121_ = lean_apply_4(v_toBind_3106_, lean_box(0), lean_box(0), v___x_3120_, v___f_3109_);
return v___x_3121_;
}
else
{
size_t v___x_3122_; size_t v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3122_ = ((size_t)0ULL);
v___x_3123_ = lean_usize_of_nat(v___x_3111_);
v___x_3124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3102_, v___f_3117_, v_params_3107_, v___x_3122_, v___x_3123_, v___x_3112_);
v___x_3125_ = lean_apply_4(v_toBind_3106_, lean_box(0), lean_box(0), v___x_3124_, v___f_3109_);
return v___x_3125_;
}
}
else
{
size_t v___x_3126_; size_t v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3126_ = ((size_t)0ULL);
v___x_3127_ = lean_usize_of_nat(v___x_3111_);
v___x_3128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3102_, v___f_3117_, v_params_3107_, v___x_3126_, v___x_3127_, v___x_3112_);
v___x_3129_ = lean_apply_4(v_toBind_3106_, lean_box(0), lean_box(0), v___x_3128_, v___f_3109_);
return v___x_3129_;
}
}
}
case 1:
{
lean_object* v_code_3130_; lean_object* v___x_3131_; 
v_code_3130_ = lean_ctor_get(v_alt_3104_, 1);
lean_inc_ref(v_code_3130_);
lean_dec_ref_known(v_alt_3104_, 2);
v___x_3131_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_3102_, v_f_3103_, v_code_3130_);
return v___x_3131_;
}
default: 
{
lean_object* v_code_3132_; lean_object* v___x_3133_; 
v_code_3132_ = lean_ctor_get(v_alt_3104_, 0);
lean_inc_ref(v_code_3132_);
lean_dec_ref_known(v_alt_3104_, 1);
v___x_3133_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_3102_, v_f_3103_, v_code_3132_);
return v___x_3133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt(uint8_t v_pu_3135_){
_start:
{
lean_object* v___x_3136_; lean_object* v___f_3137_; lean_object* v___f_3138_; lean_object* v___x_3139_; 
v___x_3136_ = lean_box(v_pu_3135_);
v___f_3137_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed), 6, 1);
lean_closure_set(v___f_3137_, 0, v___x_3136_);
v___f_3138_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0));
v___x_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___f_3137_);
lean_ctor_set(v___x_3139_, 1, v___f_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___boxed(lean_object* v_pu_3140_){
_start:
{
uint8_t v_pu_boxed_3141_; lean_object* v_res_3142_; 
v_pu_boxed_3141_ = lean_unbox(v_pu_3140_);
v_res_3142_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt(v_pu_boxed_3141_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(lean_object* v_toPure_3145_, lean_object* v_____do__lift_3146_){
_start:
{
if (lean_obj_tag(v_____do__lift_3146_) == 0)
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3147_ = lean_box(0);
v___x_3148_ = lean_apply_2(v_toPure_3145_, lean_box(0), v___x_3147_);
return v___x_3148_;
}
else
{
lean_object* v_val_3149_; uint8_t v___x_3150_; 
v_val_3149_ = lean_ctor_get(v_____do__lift_3146_, 0);
v___x_3150_ = lean_unbox(v_val_3149_);
if (v___x_3150_ == 0)
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3151_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0));
v___x_3152_ = lean_apply_2(v_toPure_3145_, lean_box(0), v___x_3151_);
return v___x_3152_;
}
else
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = lean_box(0);
v___x_3154_ = lean_apply_2(v_toPure_3145_, lean_box(0), v___x_3153_);
return v___x_3154_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed(lean_object* v_toPure_3155_, lean_object* v_____do__lift_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(v_toPure_3155_, v_____do__lift_3156_);
lean_dec(v_____do__lift_3156_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(lean_object* v_toPure_3158_, uint8_t v_____do__lift_3159_){
_start:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3160_ = lean_box(v_____do__lift_3159_);
v___x_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
v___x_3162_ = lean_apply_2(v_toPure_3158_, lean_box(0), v___x_3161_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed(lean_object* v_toPure_3163_, lean_object* v_____do__lift_3164_){
_start:
{
uint8_t v_____do__lift_405__boxed_3165_; lean_object* v_res_3166_; 
v_____do__lift_405__boxed_3165_ = lean_unbox(v_____do__lift_3164_);
v_res_3166_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(v_toPure_3163_, v_____do__lift_405__boxed_3165_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(lean_object* v_inst_3167_, lean_object* v_f_3168_, lean_object* v_fvar_3169_){
_start:
{
lean_object* v_toApplicative_3170_; lean_object* v_toBind_3171_; lean_object* v_toPure_3172_; lean_object* v___x_3173_; lean_object* v___f_3174_; lean_object* v___f_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v_toApplicative_3170_ = lean_ctor_get(v_inst_3167_, 0);
lean_inc_ref(v_toApplicative_3170_);
v_toBind_3171_ = lean_ctor_get(v_inst_3167_, 1);
lean_inc_n(v_toBind_3171_, 2);
lean_dec_ref(v_inst_3167_);
v_toPure_3172_ = lean_ctor_get(v_toApplicative_3170_, 1);
lean_inc_n(v_toPure_3172_, 2);
lean_dec_ref(v_toApplicative_3170_);
v___x_3173_ = lean_apply_1(v_f_3168_, v_fvar_3169_);
v___f_3174_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3174_, 0, v_toPure_3172_);
v___f_3175_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3175_, 0, v_toPure_3172_);
v___x_3176_ = lean_apply_4(v_toBind_3171_, lean_box(0), lean_box(0), v___x_3173_, v___f_3175_);
v___x_3177_ = lean_apply_4(v_toBind_3171_, lean_box(0), lean_box(0), v___x_3176_, v___f_3174_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go(lean_object* v_m_3178_, lean_object* v_inst_3179_, lean_object* v_f_3180_, lean_object* v_fvar_3181_){
_start:
{
lean_object* v___x_3182_; 
v___x_3182_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(v_inst_3179_, v_f_3180_, v_fvar_3181_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(lean_object* v_toPure_3183_, lean_object* v_____do__lift_3184_){
_start:
{
if (lean_obj_tag(v_____do__lift_3184_) == 0)
{
uint8_t v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3185_ = 1;
v___x_3186_ = lean_box(v___x_3185_);
v___x_3187_ = lean_apply_2(v_toPure_3183_, lean_box(0), v___x_3186_);
return v___x_3187_;
}
else
{
uint8_t v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3188_ = 0;
v___x_3189_ = lean_box(v___x_3188_);
v___x_3190_ = lean_apply_2(v_toPure_3183_, lean_box(0), v___x_3189_);
return v___x_3190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed(lean_object* v_toPure_3191_, lean_object* v_____do__lift_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(v_toPure_3191_, v_____do__lift_3192_);
lean_dec(v_____do__lift_3192_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg(lean_object* v_inst_3194_, lean_object* v_inst_3195_, lean_object* v_f_3196_, lean_object* v_x_3197_){
_start:
{
lean_object* v_toApplicative_3198_; lean_object* v_toBind_3199_; lean_object* v_forFVarM_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3221_; 
v_toApplicative_3198_ = lean_ctor_get(v_inst_3194_, 0);
v_toBind_3199_ = lean_ctor_get(v_inst_3194_, 1);
lean_inc(v_toBind_3199_);
v_forFVarM_3200_ = lean_ctor_get(v_inst_3195_, 1);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_inst_3195_);
if (v_isSharedCheck_3221_ == 0)
{
lean_object* v_unused_3222_; 
v_unused_3222_ = lean_ctor_get(v_inst_3195_, 0);
lean_dec(v_unused_3222_);
v___x_3202_ = v_inst_3195_;
v_isShared_3203_ = v_isSharedCheck_3221_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_forFVarM_3200_);
lean_dec(v_inst_3195_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3221_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___f_3204_; lean_object* v___f_3205_; lean_object* v___f_3206_; lean_object* v___f_3207_; lean_object* v___f_3208_; lean_object* v___x_3210_; 
lean_inc_ref_n(v_inst_3194_, 5);
v___f_3204_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3204_, 0, v_inst_3194_);
v___f_3205_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3205_, 0, v_inst_3194_);
v___f_3206_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3206_, 0, v_inst_3194_);
v___f_3207_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3207_, 0, v_inst_3194_);
v___f_3208_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3208_, 0, v_inst_3194_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 1, v___f_3205_);
lean_ctor_set(v___x_3202_, 0, v___f_3204_);
v___x_3210_ = v___x_3202_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___f_3204_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v___f_3205_);
v___x_3210_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v_toPure_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___f_3218_; lean_object* v___x_3219_; 
lean_inc_ref_n(v_inst_3194_, 2);
v___x_3211_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3211_, 0, lean_box(0));
lean_closure_set(v___x_3211_, 1, v_inst_3194_);
v___x_3212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3210_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
lean_ctor_set(v___x_3212_, 2, v___f_3206_);
lean_ctor_set(v___x_3212_, 3, v___f_3207_);
lean_ctor_set(v___x_3212_, 4, v___f_3208_);
v___x_3213_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3213_, 0, lean_box(0));
lean_closure_set(v___x_3213_, 1, v_inst_3194_);
v___x_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3212_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
v_toPure_3215_ = lean_ctor_get(v_toApplicative_3198_, 1);
lean_inc(v_toPure_3215_);
v___x_3216_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go), 4, 3);
lean_closure_set(v___x_3216_, 0, lean_box(0));
lean_closure_set(v___x_3216_, 1, v_inst_3194_);
lean_closure_set(v___x_3216_, 2, v_f_3196_);
v___x_3217_ = lean_apply_4(v_forFVarM_3200_, lean_box(0), v___x_3214_, v___x_3216_, v_x_3197_);
v___f_3218_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3218_, 0, v_toPure_3215_);
v___x_3219_ = lean_apply_4(v_toBind_3199_, lean_box(0), lean_box(0), v___x_3217_, v___f_3218_);
return v___x_3219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM(lean_object* v_m_3223_, lean_object* v_00_u03b1_3224_, lean_object* v_inst_3225_, lean_object* v_inst_3226_, lean_object* v_f_3227_, lean_object* v_x_3228_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_Compiler_LCNF_anyFVarM___redArg(v_inst_3225_, v_inst_3226_, v_f_3227_, v_x_3228_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(lean_object* v_toPure_3230_, lean_object* v_____do__lift_3231_){
_start:
{
if (lean_obj_tag(v_____do__lift_3231_) == 0)
{
lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3232_ = lean_box(0);
v___x_3233_ = lean_apply_2(v_toPure_3230_, lean_box(0), v___x_3232_);
return v___x_3233_;
}
else
{
lean_object* v_val_3234_; uint8_t v___x_3235_; 
v_val_3234_ = lean_ctor_get(v_____do__lift_3231_, 0);
v___x_3235_ = lean_unbox(v_val_3234_);
if (v___x_3235_ == 0)
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3236_ = lean_box(0);
v___x_3237_ = lean_apply_2(v_toPure_3230_, lean_box(0), v___x_3236_);
return v___x_3237_;
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0));
v___x_3239_ = lean_apply_2(v_toPure_3230_, lean_box(0), v___x_3238_);
return v___x_3239_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed(lean_object* v_toPure_3240_, lean_object* v_____do__lift_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(v_toPure_3240_, v_____do__lift_3241_);
lean_dec(v_____do__lift_3241_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(lean_object* v_inst_3243_, lean_object* v_f_3244_, lean_object* v_fvar_3245_){
_start:
{
lean_object* v_toApplicative_3246_; lean_object* v_toBind_3247_; lean_object* v_toPure_3248_; lean_object* v___x_3249_; lean_object* v___f_3250_; lean_object* v___f_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v_toApplicative_3246_ = lean_ctor_get(v_inst_3243_, 0);
lean_inc_ref(v_toApplicative_3246_);
v_toBind_3247_ = lean_ctor_get(v_inst_3243_, 1);
lean_inc_n(v_toBind_3247_, 2);
lean_dec_ref(v_inst_3243_);
v_toPure_3248_ = lean_ctor_get(v_toApplicative_3246_, 1);
lean_inc_n(v_toPure_3248_, 2);
lean_dec_ref(v_toApplicative_3246_);
v___x_3249_ = lean_apply_1(v_f_3244_, v_fvar_3245_);
v___f_3250_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3250_, 0, v_toPure_3248_);
v___f_3251_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3251_, 0, v_toPure_3248_);
v___x_3252_ = lean_apply_4(v_toBind_3247_, lean_box(0), lean_box(0), v___x_3249_, v___f_3251_);
v___x_3253_ = lean_apply_4(v_toBind_3247_, lean_box(0), lean_box(0), v___x_3252_, v___f_3250_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go(lean_object* v_m_3254_, lean_object* v_inst_3255_, lean_object* v_f_3256_, lean_object* v_fvar_3257_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(v_inst_3255_, v_f_3256_, v_fvar_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(lean_object* v_toPure_3259_, lean_object* v_____do__lift_3260_){
_start:
{
if (lean_obj_tag(v_____do__lift_3260_) == 1)
{
uint8_t v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3261_ = 1;
v___x_3262_ = lean_box(v___x_3261_);
v___x_3263_ = lean_apply_2(v_toPure_3259_, lean_box(0), v___x_3262_);
return v___x_3263_;
}
else
{
uint8_t v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3264_ = 0;
v___x_3265_ = lean_box(v___x_3264_);
v___x_3266_ = lean_apply_2(v_toPure_3259_, lean_box(0), v___x_3265_);
return v___x_3266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed(lean_object* v_toPure_3267_, lean_object* v_____do__lift_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(v_toPure_3267_, v_____do__lift_3268_);
lean_dec(v_____do__lift_3268_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg(lean_object* v_inst_3270_, lean_object* v_inst_3271_, lean_object* v_f_3272_, lean_object* v_x_3273_){
_start:
{
lean_object* v_toApplicative_3274_; lean_object* v_toBind_3275_; lean_object* v_forFVarM_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3297_; 
v_toApplicative_3274_ = lean_ctor_get(v_inst_3270_, 0);
v_toBind_3275_ = lean_ctor_get(v_inst_3270_, 1);
lean_inc(v_toBind_3275_);
v_forFVarM_3276_ = lean_ctor_get(v_inst_3271_, 1);
v_isSharedCheck_3297_ = !lean_is_exclusive(v_inst_3271_);
if (v_isSharedCheck_3297_ == 0)
{
lean_object* v_unused_3298_; 
v_unused_3298_ = lean_ctor_get(v_inst_3271_, 0);
lean_dec(v_unused_3298_);
v___x_3278_ = v_inst_3271_;
v_isShared_3279_ = v_isSharedCheck_3297_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_forFVarM_3276_);
lean_dec(v_inst_3271_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3297_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___f_3280_; lean_object* v___f_3281_; lean_object* v___f_3282_; lean_object* v___f_3283_; lean_object* v___f_3284_; lean_object* v___x_3286_; 
lean_inc_ref_n(v_inst_3270_, 5);
v___f_3280_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3280_, 0, v_inst_3270_);
v___f_3281_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3281_, 0, v_inst_3270_);
v___f_3282_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3282_, 0, v_inst_3270_);
v___f_3283_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3283_, 0, v_inst_3270_);
v___f_3284_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3284_, 0, v_inst_3270_);
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 1, v___f_3281_);
lean_ctor_set(v___x_3278_, 0, v___f_3280_);
v___x_3286_ = v___x_3278_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___f_3280_);
lean_ctor_set(v_reuseFailAlloc_3296_, 1, v___f_3281_);
v___x_3286_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v_toPure_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___f_3294_; lean_object* v___x_3295_; 
lean_inc_ref_n(v_inst_3270_, 2);
v___x_3287_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3287_, 0, lean_box(0));
lean_closure_set(v___x_3287_, 1, v_inst_3270_);
v___x_3288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3286_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
lean_ctor_set(v___x_3288_, 2, v___f_3282_);
lean_ctor_set(v___x_3288_, 3, v___f_3283_);
lean_ctor_set(v___x_3288_, 4, v___f_3284_);
v___x_3289_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3289_, 0, lean_box(0));
lean_closure_set(v___x_3289_, 1, v_inst_3270_);
v___x_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3288_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v_toPure_3291_ = lean_ctor_get(v_toApplicative_3274_, 1);
lean_inc(v_toPure_3291_);
v___x_3292_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go), 4, 3);
lean_closure_set(v___x_3292_, 0, lean_box(0));
lean_closure_set(v___x_3292_, 1, v_inst_3270_);
lean_closure_set(v___x_3292_, 2, v_f_3272_);
v___x_3293_ = lean_apply_4(v_forFVarM_3276_, lean_box(0), v___x_3290_, v___x_3292_, v_x_3273_);
v___f_3294_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3294_, 0, v_toPure_3291_);
v___x_3295_ = lean_apply_4(v_toBind_3275_, lean_box(0), lean_box(0), v___x_3293_, v___f_3294_);
return v___x_3295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM(lean_object* v_m_3299_, lean_object* v_00_u03b1_3300_, lean_object* v_inst_3301_, lean_object* v_inst_3302_, lean_object* v_f_3303_, lean_object* v_x_3304_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Lean_Compiler_LCNF_allFVarM___redArg(v_inst_3301_, v_inst_3302_, v_f_3303_, v_x_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(lean_object* v_f_3306_, lean_object* v_x_3307_){
_start:
{
lean_object* v___x_3308_; uint8_t v___x_3309_; 
v___x_3308_ = lean_apply_1(v_f_3306_, v_x_3307_);
v___x_3309_ = lean_unbox(v___x_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed(lean_object* v_f_3310_, lean_object* v_x_3311_){
_start:
{
uint8_t v_res_3312_; lean_object* v_r_3313_; 
v_res_3312_ = l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(v_f_3310_, v_x_3311_);
v_r_3313_ = lean_box(v_res_3312_);
return v_r_3313_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar___redArg(lean_object* v_inst_3333_, lean_object* v_f_3334_, lean_object* v_x_3335_){
_start:
{
lean_object* v___f_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; uint8_t v___x_3339_; 
v___f_3336_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3336_, 0, v_f_3334_);
v___x_3337_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9));
v___x_3338_ = l_Lean_Compiler_LCNF_anyFVarM___redArg(v___x_3337_, v_inst_3333_, v___f_3336_, v_x_3335_);
v___x_3339_ = lean_unbox(v___x_3338_);
lean_dec(v___x_3338_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___boxed(lean_object* v_inst_3340_, lean_object* v_f_3341_, lean_object* v_x_3342_){
_start:
{
uint8_t v_res_3343_; lean_object* v_r_3344_; 
v_res_3343_ = l_Lean_Compiler_LCNF_anyFVar___redArg(v_inst_3340_, v_f_3341_, v_x_3342_);
v_r_3344_ = lean_box(v_res_3343_);
return v_r_3344_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar(lean_object* v_00_u03b1_3345_, lean_object* v_inst_3346_, lean_object* v_f_3347_, lean_object* v_x_3348_){
_start:
{
uint8_t v___x_3349_; 
v___x_3349_ = l_Lean_Compiler_LCNF_anyFVar___redArg(v_inst_3346_, v_f_3347_, v_x_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___boxed(lean_object* v_00_u03b1_3350_, lean_object* v_inst_3351_, lean_object* v_f_3352_, lean_object* v_x_3353_){
_start:
{
uint8_t v_res_3354_; lean_object* v_r_3355_; 
v_res_3354_ = l_Lean_Compiler_LCNF_anyFVar(v_00_u03b1_3350_, v_inst_3351_, v_f_3352_, v_x_3353_);
v_r_3355_ = lean_box(v_res_3354_);
return v_r_3355_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar___redArg(lean_object* v_inst_3356_, lean_object* v_f_3357_, lean_object* v_x_3358_){
_start:
{
lean_object* v___f_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
v___f_3359_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3359_, 0, v_f_3357_);
v___x_3360_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9));
v___x_3361_ = l_Lean_Compiler_LCNF_allFVarM___redArg(v___x_3360_, v_inst_3356_, v___f_3359_, v_x_3358_);
v___x_3362_ = lean_unbox(v___x_3361_);
lean_dec(v___x_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___redArg___boxed(lean_object* v_inst_3363_, lean_object* v_f_3364_, lean_object* v_x_3365_){
_start:
{
uint8_t v_res_3366_; lean_object* v_r_3367_; 
v_res_3366_ = l_Lean_Compiler_LCNF_allFVar___redArg(v_inst_3363_, v_f_3364_, v_x_3365_);
v_r_3367_ = lean_box(v_res_3366_);
return v_r_3367_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar(lean_object* v_00_u03b1_3368_, lean_object* v_inst_3369_, lean_object* v_f_3370_, lean_object* v_x_3371_){
_start:
{
uint8_t v___x_3372_; 
v___x_3372_ = l_Lean_Compiler_LCNF_allFVar___redArg(v_inst_3369_, v_f_3370_, v_x_3371_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___boxed(lean_object* v_00_u03b1_3373_, lean_object* v_inst_3374_, lean_object* v_f_3375_, lean_object* v_x_3376_){
_start:
{
uint8_t v_res_3377_; lean_object* v_r_3378_; 
v_res_3377_ = l_Lean_Compiler_LCNF_allFVar(v_00_u03b1_3373_, v_inst_3374_, v_f_3375_, v_x_3376_);
v_r_3378_ = lean_box(v_res_3377_);
return v_r_3378_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_FVarUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
