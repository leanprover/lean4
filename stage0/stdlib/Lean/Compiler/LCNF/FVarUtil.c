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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v_fvarId_174_);
v_toApplicative_175_ = lean_ctor_get(v_inst_167_, 0);
lean_inc_ref(v_toApplicative_175_);
v_toBind_176_ = lean_ctor_get(v_inst_167_, 1);
lean_inc(v_toBind_176_);
lean_dec_ref(v_inst_167_);
lean_inc(v_fvarId_174_);
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
lean_dec_ref(v_e_169_);
lean_dec(v_f_168_);
v___x_180_ = l_Lean_instInhabitedExpr;
v___x_181_ = l_instInhabitedOfMonad___redArg(v_inst_167_, v___x_180_);
v___x_182_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3, &l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3);
v___x_183_ = l_panic___redArg(v___x_181_, v___x_182_);
return v___x_183_;
}
case 5:
{
lean_object* v_fn_184_; lean_object* v_arg_185_; lean_object* v_toApplicative_186_; lean_object* v_toBind_187_; lean_object* v___f_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_fn_184_ = lean_ctor_get(v_e_169_, 0);
lean_inc_ref(v_fn_184_);
v_arg_185_ = lean_ctor_get(v_e_169_, 1);
lean_inc_ref(v_arg_185_);
v_toApplicative_186_ = lean_ctor_get(v_inst_167_, 0);
v_toBind_187_ = lean_ctor_get(v_inst_167_, 1);
lean_inc(v_toBind_187_);
lean_inc(v_toBind_187_);
lean_inc(v_f_168_);
lean_inc_ref(v_inst_167_);
lean_inc_ref(v_fn_184_);
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
lean_inc_ref(v_binderType_192_);
v_body_193_ = lean_ctor_get(v_e_169_, 2);
lean_inc_ref(v_body_193_);
v_binderInfo_194_ = lean_ctor_get_uint8(v_e_169_, sizeof(void*)*3 + 8);
v_toApplicative_195_ = lean_ctor_get(v_inst_167_, 0);
v_toBind_196_ = lean_ctor_get(v_inst_167_, 1);
lean_inc(v_toBind_196_);
v___x_197_ = lean_box(v_binderInfo_194_);
lean_inc(v_toBind_196_);
lean_inc(v_f_168_);
lean_inc_ref(v_inst_167_);
lean_inc_ref(v_binderType_192_);
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
lean_inc_ref(v_binderType_202_);
v_body_203_ = lean_ctor_get(v_e_169_, 2);
lean_inc_ref(v_body_203_);
v_binderInfo_204_ = lean_ctor_get_uint8(v_e_169_, sizeof(void*)*3 + 8);
v_toApplicative_205_ = lean_ctor_get(v_inst_167_, 0);
v_toBind_206_ = lean_ctor_get(v_inst_167_, 1);
lean_inc(v_toBind_206_);
v___x_207_ = lean_box(v_binderInfo_204_);
lean_inc(v_toBind_206_);
lean_inc(v_f_168_);
lean_inc_ref(v_inst_167_);
lean_inc_ref(v_binderType_202_);
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
lean_dec_ref(v_e_169_);
lean_dec(v_f_168_);
v___x_211_ = l_Lean_instInhabitedExpr;
v___x_212_ = l_instInhabitedOfMonad___redArg(v_inst_167_, v___x_211_);
v___x_213_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3, &l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3);
v___x_214_ = l_panic___redArg(v___x_212_, v___x_213_);
return v___x_214_;
}
case 11:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec_ref(v_e_169_);
lean_dec(v_f_168_);
v___x_215_ = l_Lean_instInhabitedExpr;
v___x_216_ = l_instInhabitedOfMonad___redArg(v_inst_167_, v___x_215_);
v___x_217_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3, &l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3);
v___x_218_ = l_panic___redArg(v___x_216_, v___x_217_);
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
lean_dec_ref(v_e_259_);
v___x_273_ = lean_apply_1(v_f_258_, v_fvarId_272_);
return v___x_273_;
}
case 2:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec_ref(v_e_259_);
lean_dec(v_f_258_);
v___x_274_ = lean_box(0);
v___x_275_ = l_instInhabitedOfMonad___redArg(v_inst_257_, v___x_274_);
v___x_276_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1, &l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1);
v___x_277_ = l_panic___redArg(v___x_275_, v___x_276_);
return v___x_277_;
}
case 5:
{
lean_object* v_fn_278_; lean_object* v_arg_279_; lean_object* v_toBind_280_; lean_object* v___f_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_fn_278_ = lean_ctor_get(v_e_259_, 0);
lean_inc_ref(v_fn_278_);
v_arg_279_ = lean_ctor_get(v_e_259_, 1);
lean_inc_ref(v_arg_279_);
lean_dec_ref(v_e_259_);
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
lean_dec_ref(v_e_259_);
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
lean_dec_ref(v_e_259_);
v_ty_261_ = v_binderType_286_;
v_body_262_ = v_body_287_;
goto v___jp_260_;
}
case 8:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
lean_dec_ref(v_e_259_);
lean_dec(v_f_258_);
v___x_288_ = lean_box(0);
v___x_289_ = l_instInhabitedOfMonad___redArg(v_inst_257_, v___x_288_);
v___x_290_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1, &l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1);
v___x_291_ = l_panic___redArg(v___x_289_, v___x_290_);
return v___x_291_;
}
case 11:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec_ref(v_e_259_);
lean_dec(v_f_258_);
v___x_292_ = lean_box(0);
v___x_293_ = l_instInhabitedOfMonad___redArg(v_inst_257_, v___x_292_);
v___x_294_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1, &l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1);
v___x_295_ = l_panic___redArg(v___x_293_, v___x_294_);
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
lean_dec_ref(v_arg_396_);
v___x_402_ = lean_apply_1(v_f_395_, v_fvarId_401_);
return v___x_402_;
}
default: 
{
lean_object* v_expr_403_; lean_object* v___x_404_; 
v_expr_403_ = lean_ctor_get(v_arg_396_, 0);
lean_inc_ref(v_expr_403_);
lean_dec_ref(v_arg_396_);
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
lean_inc(v_toPure_627_);
lean_inc(v_e_624_);
v___f_631_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_631_, 0, v___x_630_);
lean_closure_set(v___f_631_, 1, v_e_624_);
lean_closure_set(v___f_631_, 2, v_toPure_627_);
v___x_638_ = lean_box(v_pu_621_);
lean_inc(v_toPure_627_);
lean_inc(v_e_624_);
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
lean_dec_ref(v_e_624_);
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
lean_dec_ref(v_e_624_);
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
lean_dec_ref(v_e_624_);
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
lean_dec_ref(v_e_624_);
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
lean_dec_ref(v_e_624_);
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
lean_dec_ref(v_e_624_);
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
lean_dec_ref(v_e_624_);
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
lean_dec_ref(v_e_624_);
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
lean_dec_ref(v_e_748_);
v___x_769_ = lean_apply_1(v_f_747_, v_struct_768_);
return v___x_769_;
}
case 3:
{
lean_object* v_args_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
lean_dec(v_f_747_);
v_args_770_ = lean_ctor_get(v_e_748_, 2);
lean_inc_ref(v_args_770_);
lean_dec_ref(v_e_748_);
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
lean_dec_ref(v_e_748_);
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
lean_dec_ref(v_e_748_);
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
lean_dec_ref(v_e_748_);
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
lean_dec_ref(v_e_748_);
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
lean_dec_ref(v_e_748_);
v___x_808_ = lean_apply_1(v_f_747_, v_var_807_);
return v___x_808_;
}
case 9:
{
lean_object* v_args_809_; 
lean_dec(v_f_747_);
v_args_809_ = lean_ctor_get(v_e_748_, 1);
lean_inc_ref(v_args_809_);
lean_dec_ref(v_e_748_);
v_args_754_ = v_args_809_;
goto v___jp_753_;
}
case 10:
{
lean_object* v_args_810_; 
lean_dec(v_f_747_);
v_args_810_ = lean_ctor_get(v_e_748_, 1);
lean_inc_ref(v_args_810_);
lean_dec_ref(v_e_748_);
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
lean_dec_ref(v_e_748_);
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
lean_dec_ref(v_e_748_);
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
lean_dec_ref(v_e_748_);
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
lean_dec_ref(v_e_748_);
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
lean_dec_ref(v_e_748_);
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
lean_inc(v_toBind_910_);
v_type_911_ = lean_ctor_get(v_decl_909_, 2);
lean_inc_ref(v_type_911_);
v_value_912_ = lean_ctor_get(v_decl_909_, 3);
lean_inc(v_value_912_);
v___x_913_ = lean_box(v_pu_905_);
lean_inc(v_toBind_910_);
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
uint8_t v_check_1804__boxed_1224_; uint8_t v_persistent_1805__boxed_1225_; lean_object* v_res_1226_; 
v_check_1804__boxed_1224_ = lean_unbox(v_check_1217_);
v_persistent_1805__boxed_1225_ = lean_unbox(v_persistent_1218_);
v_res_1226_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(v_____do__lift_1215_, v_n_1216_, v_check_1804__boxed_1224_, v_persistent_1805__boxed_1225_, v_toPure_1219_, v_k_1220_, v_c_1221_, v_fvarId_1222_, v_____do__lift_1223_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(lean_object* v_____do__lift_1414_, lean_object* v_n_1415_, uint8_t v_check_1416_, uint8_t v_persistent_1417_, lean_object* v_toPure_1418_, lean_object* v_k_1419_, lean_object* v_c_1420_, lean_object* v_fvarId_1421_, lean_object* v_____do__lift_1422_){
_start:
{
uint8_t v___y_1424_; size_t v___x_1433_; size_t v___x_1434_; uint8_t v___x_1435_; 
v___x_1433_ = lean_ptr_addr(v_fvarId_1421_);
v___x_1434_ = lean_ptr_addr(v_____do__lift_1414_);
v___x_1435_ = lean_usize_dec_eq(v___x_1433_, v___x_1434_);
if (v___x_1435_ == 0)
{
v___y_1424_ = v___x_1435_;
goto v___jp_1423_;
}
else
{
uint8_t v___x_1436_; 
v___x_1436_ = lean_nat_dec_eq(v_n_1415_, v_n_1415_);
v___y_1424_ = v___x_1436_;
goto v___jp_1423_;
}
v___jp_1423_:
{
if (v___y_1424_ == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec_ref(v_c_1420_);
v___x_1425_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v___x_1425_, 0, v_____do__lift_1414_);
lean_ctor_set(v___x_1425_, 1, v_n_1415_);
lean_ctor_set(v___x_1425_, 2, v_____do__lift_1422_);
lean_ctor_set_uint8(v___x_1425_, sizeof(void*)*3, v_check_1416_);
lean_ctor_set_uint8(v___x_1425_, sizeof(void*)*3 + 1, v_persistent_1417_);
v___x_1426_ = lean_apply_2(v_toPure_1418_, lean_box(0), v___x_1425_);
return v___x_1426_;
}
else
{
size_t v___x_1427_; size_t v___x_1428_; uint8_t v___x_1429_; 
v___x_1427_ = lean_ptr_addr(v_k_1419_);
v___x_1428_ = lean_ptr_addr(v_____do__lift_1422_);
v___x_1429_ = lean_usize_dec_eq(v___x_1427_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec_ref(v_c_1420_);
v___x_1430_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v___x_1430_, 0, v_____do__lift_1414_);
lean_ctor_set(v___x_1430_, 1, v_n_1415_);
lean_ctor_set(v___x_1430_, 2, v_____do__lift_1422_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3, v_check_1416_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3 + 1, v_persistent_1417_);
v___x_1431_ = lean_apply_2(v_toPure_1418_, lean_box(0), v___x_1430_);
return v___x_1431_;
}
else
{
lean_object* v___x_1432_; 
lean_dec_ref(v_____do__lift_1422_);
lean_dec(v_n_1415_);
lean_dec(v_____do__lift_1414_);
v___x_1432_ = lean_apply_2(v_toPure_1418_, lean_box(0), v_c_1420_);
return v___x_1432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed(lean_object* v_____do__lift_1437_, lean_object* v_n_1438_, lean_object* v_check_1439_, lean_object* v_persistent_1440_, lean_object* v_toPure_1441_, lean_object* v_k_1442_, lean_object* v_c_1443_, lean_object* v_fvarId_1444_, lean_object* v_____do__lift_1445_){
_start:
{
uint8_t v_check_2110__boxed_1446_; uint8_t v_persistent_2111__boxed_1447_; lean_object* v_res_1448_; 
v_check_2110__boxed_1446_ = lean_unbox(v_check_1439_);
v_persistent_2111__boxed_1447_ = lean_unbox(v_persistent_1440_);
v_res_1448_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(v_____do__lift_1437_, v_n_1438_, v_check_2110__boxed_1446_, v_persistent_2111__boxed_1447_, v_toPure_1441_, v_k_1442_, v_c_1443_, v_fvarId_1444_, v_____do__lift_1445_);
lean_dec(v_fvarId_1444_);
lean_dec_ref(v_k_1442_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(lean_object* v_decl_1449_, lean_object* v_toPure_1450_, lean_object* v_c_1451_, lean_object* v_k_1452_, lean_object* v_decl_1453_, lean_object* v_____do__lift_1454_){
_start:
{
uint8_t v___y_1456_; size_t v___x_1460_; size_t v___x_1461_; uint8_t v___x_1462_; 
v___x_1460_ = lean_ptr_addr(v_k_1452_);
v___x_1461_ = lean_ptr_addr(v_____do__lift_1454_);
v___x_1462_ = lean_usize_dec_eq(v___x_1460_, v___x_1461_);
if (v___x_1462_ == 0)
{
v___y_1456_ = v___x_1462_;
goto v___jp_1455_;
}
else
{
size_t v___x_1463_; size_t v___x_1464_; uint8_t v___x_1465_; 
v___x_1463_ = lean_ptr_addr(v_decl_1453_);
v___x_1464_ = lean_ptr_addr(v_decl_1449_);
v___x_1465_ = lean_usize_dec_eq(v___x_1463_, v___x_1464_);
v___y_1456_ = v___x_1465_;
goto v___jp_1455_;
}
v___jp_1455_:
{
if (v___y_1456_ == 0)
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec_ref(v_c_1451_);
v___x_1457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1457_, 0, v_decl_1449_);
lean_ctor_set(v___x_1457_, 1, v_____do__lift_1454_);
v___x_1458_ = lean_apply_2(v_toPure_1450_, lean_box(0), v___x_1457_);
return v___x_1458_;
}
else
{
lean_object* v___x_1459_; 
lean_dec_ref(v_____do__lift_1454_);
lean_dec_ref(v_decl_1449_);
v___x_1459_ = lean_apply_2(v_toPure_1450_, lean_box(0), v_c_1451_);
return v___x_1459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed(lean_object* v_decl_1466_, lean_object* v_toPure_1467_, lean_object* v_c_1468_, lean_object* v_k_1469_, lean_object* v_decl_1470_, lean_object* v_____do__lift_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(v_decl_1466_, v_toPure_1467_, v_c_1468_, v_k_1469_, v_decl_1470_, v_____do__lift_1471_);
lean_dec_ref(v_decl_1470_);
lean_dec_ref(v_k_1469_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(lean_object* v_decl_1473_, lean_object* v_toPure_1474_, lean_object* v_c_1475_, lean_object* v_k_1476_, lean_object* v_decl_1477_, lean_object* v_____do__lift_1478_){
_start:
{
uint8_t v___y_1480_; size_t v___x_1484_; size_t v___x_1485_; uint8_t v___x_1486_; 
v___x_1484_ = lean_ptr_addr(v_k_1476_);
v___x_1485_ = lean_ptr_addr(v_____do__lift_1478_);
v___x_1486_ = lean_usize_dec_eq(v___x_1484_, v___x_1485_);
if (v___x_1486_ == 0)
{
v___y_1480_ = v___x_1486_;
goto v___jp_1479_;
}
else
{
size_t v___x_1487_; size_t v___x_1488_; uint8_t v___x_1489_; 
v___x_1487_ = lean_ptr_addr(v_decl_1477_);
v___x_1488_ = lean_ptr_addr(v_decl_1473_);
v___x_1489_ = lean_usize_dec_eq(v___x_1487_, v___x_1488_);
v___y_1480_ = v___x_1489_;
goto v___jp_1479_;
}
v___jp_1479_:
{
if (v___y_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_dec_ref(v_c_1475_);
v___x_1481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1481_, 0, v_decl_1473_);
lean_ctor_set(v___x_1481_, 1, v_____do__lift_1478_);
v___x_1482_ = lean_apply_2(v_toPure_1474_, lean_box(0), v___x_1481_);
return v___x_1482_;
}
else
{
lean_object* v___x_1483_; 
lean_dec_ref(v_____do__lift_1478_);
lean_dec_ref(v_decl_1473_);
v___x_1483_ = lean_apply_2(v_toPure_1474_, lean_box(0), v_c_1475_);
return v___x_1483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed(lean_object* v_decl_1490_, lean_object* v_toPure_1491_, lean_object* v_c_1492_, lean_object* v_k_1493_, lean_object* v_decl_1494_, lean_object* v_____do__lift_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(v_decl_1490_, v_toPure_1491_, v_c_1492_, v_k_1493_, v_decl_1494_, v_____do__lift_1495_);
lean_dec_ref(v_decl_1494_);
lean_dec_ref(v_k_1493_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(lean_object* v_____do__lift_1497_, lean_object* v_i_1498_, lean_object* v_____do__lift_1499_, lean_object* v_toPure_1500_, lean_object* v_y_1501_, lean_object* v_k_1502_, lean_object* v_c_1503_, lean_object* v_fvarId_1504_, lean_object* v_____do__lift_1505_){
_start:
{
uint8_t v___y_1507_; size_t v___x_1521_; size_t v___x_1522_; uint8_t v___x_1523_; 
v___x_1521_ = lean_ptr_addr(v_fvarId_1504_);
v___x_1522_ = lean_ptr_addr(v_____do__lift_1497_);
v___x_1523_ = lean_usize_dec_eq(v___x_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
v___y_1507_ = v___x_1523_;
goto v___jp_1506_;
}
else
{
uint8_t v___x_1524_; 
v___x_1524_ = lean_nat_dec_eq(v_i_1498_, v_i_1498_);
v___y_1507_ = v___x_1524_;
goto v___jp_1506_;
}
v___jp_1506_:
{
if (v___y_1507_ == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_dec_ref(v_c_1503_);
v___x_1508_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1508_, 0, v_____do__lift_1497_);
lean_ctor_set(v___x_1508_, 1, v_i_1498_);
lean_ctor_set(v___x_1508_, 2, v_____do__lift_1499_);
lean_ctor_set(v___x_1508_, 3, v_____do__lift_1505_);
v___x_1509_ = lean_apply_2(v_toPure_1500_, lean_box(0), v___x_1508_);
return v___x_1509_;
}
else
{
size_t v___x_1510_; size_t v___x_1511_; uint8_t v___x_1512_; 
v___x_1510_ = lean_ptr_addr(v_y_1501_);
v___x_1511_ = lean_ptr_addr(v_____do__lift_1499_);
v___x_1512_ = lean_usize_dec_eq(v___x_1510_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec_ref(v_c_1503_);
v___x_1513_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1513_, 0, v_____do__lift_1497_);
lean_ctor_set(v___x_1513_, 1, v_i_1498_);
lean_ctor_set(v___x_1513_, 2, v_____do__lift_1499_);
lean_ctor_set(v___x_1513_, 3, v_____do__lift_1505_);
v___x_1514_ = lean_apply_2(v_toPure_1500_, lean_box(0), v___x_1513_);
return v___x_1514_;
}
else
{
size_t v___x_1515_; size_t v___x_1516_; uint8_t v___x_1517_; 
v___x_1515_ = lean_ptr_addr(v_k_1502_);
v___x_1516_ = lean_ptr_addr(v_____do__lift_1505_);
v___x_1517_ = lean_usize_dec_eq(v___x_1515_, v___x_1516_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec_ref(v_c_1503_);
v___x_1518_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1518_, 0, v_____do__lift_1497_);
lean_ctor_set(v___x_1518_, 1, v_i_1498_);
lean_ctor_set(v___x_1518_, 2, v_____do__lift_1499_);
lean_ctor_set(v___x_1518_, 3, v_____do__lift_1505_);
v___x_1519_ = lean_apply_2(v_toPure_1500_, lean_box(0), v___x_1518_);
return v___x_1519_;
}
else
{
lean_object* v___x_1520_; 
lean_dec_ref(v_____do__lift_1505_);
lean_dec(v_____do__lift_1499_);
lean_dec(v_i_1498_);
lean_dec(v_____do__lift_1497_);
v___x_1520_ = lean_apply_2(v_toPure_1500_, lean_box(0), v_c_1503_);
return v___x_1520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed(lean_object* v_____do__lift_1525_, lean_object* v_i_1526_, lean_object* v_____do__lift_1527_, lean_object* v_toPure_1528_, lean_object* v_y_1529_, lean_object* v_k_1530_, lean_object* v_c_1531_, lean_object* v_fvarId_1532_, lean_object* v_____do__lift_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(v_____do__lift_1525_, v_i_1526_, v_____do__lift_1527_, v_toPure_1528_, v_y_1529_, v_k_1530_, v_c_1531_, v_fvarId_1532_, v_____do__lift_1533_);
lean_dec(v_fvarId_1532_);
lean_dec_ref(v_k_1530_);
lean_dec(v_y_1529_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(lean_object* v_____do__lift_1535_, lean_object* v_toPure_1536_, lean_object* v_c_1537_, lean_object* v_fvarId_1538_, lean_object* v_k_1539_, lean_object* v_____do__lift_1540_){
_start:
{
uint8_t v___y_1542_; size_t v___x_1546_; size_t v___x_1547_; uint8_t v___x_1548_; 
v___x_1546_ = lean_ptr_addr(v_fvarId_1538_);
v___x_1547_ = lean_ptr_addr(v_____do__lift_1535_);
v___x_1548_ = lean_usize_dec_eq(v___x_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
v___y_1542_ = v___x_1548_;
goto v___jp_1541_;
}
else
{
size_t v___x_1549_; size_t v___x_1550_; uint8_t v___x_1551_; 
v___x_1549_ = lean_ptr_addr(v_k_1539_);
v___x_1550_ = lean_ptr_addr(v_____do__lift_1540_);
v___x_1551_ = lean_usize_dec_eq(v___x_1549_, v___x_1550_);
v___y_1542_ = v___x_1551_;
goto v___jp_1541_;
}
v___jp_1541_:
{
if (v___y_1542_ == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec_ref(v_c_1537_);
v___x_1543_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_1543_, 0, v_____do__lift_1535_);
lean_ctor_set(v___x_1543_, 1, v_____do__lift_1540_);
v___x_1544_ = lean_apply_2(v_toPure_1536_, lean_box(0), v___x_1543_);
return v___x_1544_;
}
else
{
lean_object* v___x_1545_; 
lean_dec_ref(v_____do__lift_1540_);
lean_dec(v_____do__lift_1535_);
v___x_1545_ = lean_apply_2(v_toPure_1536_, lean_box(0), v_c_1537_);
return v___x_1545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed(lean_object* v_____do__lift_1552_, lean_object* v_toPure_1553_, lean_object* v_c_1554_, lean_object* v_fvarId_1555_, lean_object* v_k_1556_, lean_object* v_____do__lift_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(v_____do__lift_1552_, v_toPure_1553_, v_c_1554_, v_fvarId_1555_, v_k_1556_, v_____do__lift_1557_);
lean_dec_ref(v_k_1556_);
lean_dec(v_fvarId_1555_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(lean_object* v_type_1559_, lean_object* v_toPure_1560_, lean_object* v_c_1561_, lean_object* v_____do__lift_1562_){
_start:
{
size_t v___x_1563_; size_t v___x_1564_; uint8_t v___x_1565_; 
v___x_1563_ = lean_ptr_addr(v_type_1559_);
v___x_1564_ = lean_ptr_addr(v_____do__lift_1562_);
v___x_1565_ = lean_usize_dec_eq(v___x_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
lean_dec_ref(v_c_1561_);
v___x_1566_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_____do__lift_1562_);
v___x_1567_ = lean_apply_2(v_toPure_1560_, lean_box(0), v___x_1566_);
return v___x_1567_;
}
else
{
lean_object* v___x_1568_; 
lean_dec_ref(v_____do__lift_1562_);
v___x_1568_ = lean_apply_2(v_toPure_1560_, lean_box(0), v_c_1561_);
return v___x_1568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed(lean_object* v_type_1569_, lean_object* v_toPure_1570_, lean_object* v_c_1571_, lean_object* v_____do__lift_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(v_type_1569_, v_toPure_1570_, v_c_1571_, v_____do__lift_1572_);
lean_dec_ref(v_type_1569_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(lean_object* v_toPure_1574_, lean_object* v_c_1575_, lean_object* v_k_1576_, lean_object* v_decl_1577_, uint8_t v_pu_1578_, lean_object* v_inst_1579_, lean_object* v_inst_1580_, lean_object* v_f_1581_, lean_object* v_toBind_1582_, lean_object* v_decl_1583_){
_start:
{
lean_object* v___f_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_inc_ref(v_k_1576_);
v___f_1584_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1584_, 0, v_decl_1583_);
lean_closure_set(v___f_1584_, 1, v_toPure_1574_);
lean_closure_set(v___f_1584_, 2, v_c_1575_);
lean_closure_set(v___f_1584_, 3, v_k_1576_);
lean_closure_set(v___f_1584_, 4, v_decl_1577_);
v___x_1585_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1578_, v_inst_1579_, v_inst_1580_, v_f_1581_, v_k_1576_);
v___x_1586_ = lean_apply_4(v_toBind_1582_, lean_box(0), lean_box(0), v___x_1585_, v___f_1584_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed(lean_object* v_toPure_1587_, lean_object* v_c_1588_, lean_object* v_k_1589_, lean_object* v_decl_1590_, lean_object* v_pu_1591_, lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_f_1594_, lean_object* v_toBind_1595_, lean_object* v_decl_1596_){
_start:
{
uint8_t v_pu_boxed_1597_; lean_object* v_res_1598_; 
v_pu_boxed_1597_ = lean_unbox(v_pu_1591_);
v_res_1598_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(v_toPure_1587_, v_c_1588_, v_k_1589_, v_decl_1590_, v_pu_boxed_1597_, v_inst_1592_, v_inst_1593_, v_f_1594_, v_toBind_1595_, v_decl_1596_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(lean_object* v_toPure_1599_, lean_object* v_c_1600_, lean_object* v_k_1601_, lean_object* v_decl_1602_, uint8_t v_pu_1603_, lean_object* v_inst_1604_, lean_object* v_inst_1605_, lean_object* v_f_1606_, lean_object* v_toBind_1607_, lean_object* v_decl_1608_){
_start:
{
lean_object* v___f_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_inc_ref(v_k_1601_);
v___f_1609_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_1609_, 0, v_decl_1608_);
lean_closure_set(v___f_1609_, 1, v_toPure_1599_);
lean_closure_set(v___f_1609_, 2, v_c_1600_);
lean_closure_set(v___f_1609_, 3, v_k_1601_);
lean_closure_set(v___f_1609_, 4, v_decl_1602_);
v___x_1610_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1603_, v_inst_1604_, v_inst_1605_, v_f_1606_, v_k_1601_);
v___x_1611_ = lean_apply_4(v_toBind_1607_, lean_box(0), lean_box(0), v___x_1610_, v___f_1609_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed(lean_object* v_toPure_1612_, lean_object* v_c_1613_, lean_object* v_k_1614_, lean_object* v_decl_1615_, lean_object* v_pu_1616_, lean_object* v_inst_1617_, lean_object* v_inst_1618_, lean_object* v_f_1619_, lean_object* v_toBind_1620_, lean_object* v_decl_1621_){
_start:
{
uint8_t v_pu_boxed_1622_; lean_object* v_res_1623_; 
v_pu_boxed_1622_ = lean_unbox(v_pu_1616_);
v_res_1623_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(v_toPure_1612_, v_c_1613_, v_k_1614_, v_decl_1615_, v_pu_boxed_1622_, v_inst_1617_, v_inst_1618_, v_f_1619_, v_toBind_1620_, v_decl_1621_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(uint8_t v_pu_1624_, lean_object* v_decl_1625_, lean_object* v_params_1626_, lean_object* v_inst_1627_, lean_object* v_toBind_1628_, lean_object* v___f_1629_, lean_object* v_inst_1630_, lean_object* v_f_1631_, lean_object* v_value_1632_, lean_object* v_____do__lift_1633_){
_start:
{
lean_object* v___x_1634_; lean_object* v___f_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1634_ = lean_box(v_pu_1624_);
lean_inc(v_toBind_1628_);
lean_inc(v_inst_1627_);
v___f_1635_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_1635_, 0, v___x_1634_);
lean_closure_set(v___f_1635_, 1, v_decl_1625_);
lean_closure_set(v___f_1635_, 2, v_____do__lift_1633_);
lean_closure_set(v___f_1635_, 3, v_params_1626_);
lean_closure_set(v___f_1635_, 4, v_inst_1627_);
lean_closure_set(v___f_1635_, 5, v_toBind_1628_);
lean_closure_set(v___f_1635_, 6, v___f_1629_);
v___x_1636_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1624_, v_inst_1627_, v_inst_1630_, v_f_1631_, v_value_1632_);
v___x_1637_ = lean_apply_4(v_toBind_1628_, lean_box(0), lean_box(0), v___x_1636_, v___f_1635_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed(lean_object* v_pu_1638_, lean_object* v_decl_1639_, lean_object* v_params_1640_, lean_object* v_inst_1641_, lean_object* v_toBind_1642_, lean_object* v___f_1643_, lean_object* v_inst_1644_, lean_object* v_f_1645_, lean_object* v_value_1646_, lean_object* v_____do__lift_1647_){
_start:
{
uint8_t v_pu_boxed_1648_; lean_object* v_res_1649_; 
v_pu_boxed_1648_ = lean_unbox(v_pu_1638_);
v_res_1649_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(v_pu_boxed_1648_, v_decl_1639_, v_params_1640_, v_inst_1641_, v_toBind_1642_, v___f_1643_, v_inst_1644_, v_f_1645_, v_value_1646_, v_____do__lift_1647_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(uint8_t v_pu_1650_, lean_object* v_decl_1651_, lean_object* v_inst_1652_, lean_object* v_toBind_1653_, lean_object* v___f_1654_, lean_object* v_inst_1655_, lean_object* v_f_1656_, lean_object* v_value_1657_, lean_object* v_type_1658_, lean_object* v_params_1659_){
_start:
{
lean_object* v___x_1660_; lean_object* v___f_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1660_ = lean_box(v_pu_1650_);
lean_inc(v_f_1656_);
lean_inc_ref(v_inst_1655_);
lean_inc(v_toBind_1653_);
v___f_1661_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed), 10, 9);
lean_closure_set(v___f_1661_, 0, v___x_1660_);
lean_closure_set(v___f_1661_, 1, v_decl_1651_);
lean_closure_set(v___f_1661_, 2, v_params_1659_);
lean_closure_set(v___f_1661_, 3, v_inst_1652_);
lean_closure_set(v___f_1661_, 4, v_toBind_1653_);
lean_closure_set(v___f_1661_, 5, v___f_1654_);
lean_closure_set(v___f_1661_, 6, v_inst_1655_);
lean_closure_set(v___f_1661_, 7, v_f_1656_);
lean_closure_set(v___f_1661_, 8, v_value_1657_);
v___x_1662_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1655_, v_f_1656_, v_type_1658_);
v___x_1663_ = lean_apply_4(v_toBind_1653_, lean_box(0), lean_box(0), v___x_1662_, v___f_1661_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed(lean_object* v_pu_1664_, lean_object* v_decl_1665_, lean_object* v_inst_1666_, lean_object* v_toBind_1667_, lean_object* v___f_1668_, lean_object* v_inst_1669_, lean_object* v_f_1670_, lean_object* v_value_1671_, lean_object* v_type_1672_, lean_object* v_params_1673_){
_start:
{
uint8_t v_pu_boxed_1674_; lean_object* v_res_1675_; 
v_pu_boxed_1674_ = lean_unbox(v_pu_1664_);
v_res_1675_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(v_pu_boxed_1674_, v_decl_1665_, v_inst_1666_, v_toBind_1667_, v___f_1668_, v_inst_1669_, v_f_1670_, v_value_1671_, v_type_1672_, v_params_1673_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(lean_object* v_toPure_1676_, lean_object* v_c_1677_, lean_object* v_k_1678_, lean_object* v_decl_1679_, uint8_t v_pu_1680_, lean_object* v_inst_1681_, lean_object* v_inst_1682_, lean_object* v_f_1683_, lean_object* v_toBind_1684_, lean_object* v_decl_1685_){
_start:
{
lean_object* v___f_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_inc_ref(v_k_1678_);
v___f_1686_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_1686_, 0, v_decl_1685_);
lean_closure_set(v___f_1686_, 1, v_toPure_1676_);
lean_closure_set(v___f_1686_, 2, v_c_1677_);
lean_closure_set(v___f_1686_, 3, v_k_1678_);
lean_closure_set(v___f_1686_, 4, v_decl_1679_);
v___x_1687_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1680_, v_inst_1681_, v_inst_1682_, v_f_1683_, v_k_1678_);
v___x_1688_ = lean_apply_4(v_toBind_1684_, lean_box(0), lean_box(0), v___x_1687_, v___f_1686_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed(lean_object* v_toPure_1689_, lean_object* v_c_1690_, lean_object* v_k_1691_, lean_object* v_decl_1692_, lean_object* v_pu_1693_, lean_object* v_inst_1694_, lean_object* v_inst_1695_, lean_object* v_f_1696_, lean_object* v_toBind_1697_, lean_object* v_decl_1698_){
_start:
{
uint8_t v_pu_boxed_1699_; lean_object* v_res_1700_; 
v_pu_boxed_1699_ = lean_unbox(v_pu_1693_);
v_res_1700_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(v_toPure_1689_, v_c_1690_, v_k_1691_, v_decl_1692_, v_pu_boxed_1699_, v_inst_1694_, v_inst_1695_, v_f_1696_, v_toBind_1697_, v_decl_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed(lean_object* v_pu_1701_, lean_object* v_inst_1702_, lean_object* v_inst_1703_, lean_object* v_f_1704_, lean_object* v_x_1705_){
_start:
{
uint8_t v_pu_boxed_1706_; lean_object* v_res_1707_; 
v_pu_boxed_1706_ = lean_unbox(v_pu_1701_);
v_res_1707_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(v_pu_boxed_1706_, v_inst_1702_, v_inst_1703_, v_f_1704_, v_x_1705_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(lean_object* v_____do__lift_1708_, lean_object* v_i_1709_, lean_object* v_toPure_1710_, lean_object* v_y_1711_, lean_object* v_k_1712_, lean_object* v_c_1713_, lean_object* v_fvarId_1714_, uint8_t v_pu_1715_, lean_object* v_inst_1716_, lean_object* v_inst_1717_, lean_object* v_f_1718_, lean_object* v_toBind_1719_, lean_object* v_____do__lift_1720_){
_start:
{
lean_object* v___f_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_inc_ref(v_k_1712_);
v___f_1721_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed), 9, 8);
lean_closure_set(v___f_1721_, 0, v_____do__lift_1708_);
lean_closure_set(v___f_1721_, 1, v_i_1709_);
lean_closure_set(v___f_1721_, 2, v_____do__lift_1720_);
lean_closure_set(v___f_1721_, 3, v_toPure_1710_);
lean_closure_set(v___f_1721_, 4, v_y_1711_);
lean_closure_set(v___f_1721_, 5, v_k_1712_);
lean_closure_set(v___f_1721_, 6, v_c_1713_);
lean_closure_set(v___f_1721_, 7, v_fvarId_1714_);
v___x_1722_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1715_, v_inst_1716_, v_inst_1717_, v_f_1718_, v_k_1712_);
v___x_1723_ = lean_apply_4(v_toBind_1719_, lean_box(0), lean_box(0), v___x_1722_, v___f_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed(lean_object* v_____do__lift_1724_, lean_object* v_i_1725_, lean_object* v_toPure_1726_, lean_object* v_y_1727_, lean_object* v_k_1728_, lean_object* v_c_1729_, lean_object* v_fvarId_1730_, lean_object* v_pu_1731_, lean_object* v_inst_1732_, lean_object* v_inst_1733_, lean_object* v_f_1734_, lean_object* v_toBind_1735_, lean_object* v_____do__lift_1736_){
_start:
{
uint8_t v_pu_boxed_1737_; lean_object* v_res_1738_; 
v_pu_boxed_1737_ = lean_unbox(v_pu_1731_);
v_res_1738_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(v_____do__lift_1724_, v_i_1725_, v_toPure_1726_, v_y_1727_, v_k_1728_, v_c_1729_, v_fvarId_1730_, v_pu_boxed_1737_, v_inst_1732_, v_inst_1733_, v_f_1734_, v_toBind_1735_, v_____do__lift_1736_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(lean_object* v_i_1739_, lean_object* v_toPure_1740_, lean_object* v_y_1741_, lean_object* v_k_1742_, lean_object* v_c_1743_, lean_object* v_fvarId_1744_, uint8_t v_pu_1745_, lean_object* v_inst_1746_, lean_object* v_inst_1747_, lean_object* v_f_1748_, lean_object* v_toBind_1749_, lean_object* v_____do__lift_1750_){
_start:
{
lean_object* v___x_1751_; lean_object* v___f_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1751_ = lean_box(v_pu_1745_);
lean_inc(v_toBind_1749_);
lean_inc(v_f_1748_);
lean_inc_ref(v_inst_1747_);
lean_inc(v_y_1741_);
v___f_1752_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed), 13, 12);
lean_closure_set(v___f_1752_, 0, v_____do__lift_1750_);
lean_closure_set(v___f_1752_, 1, v_i_1739_);
lean_closure_set(v___f_1752_, 2, v_toPure_1740_);
lean_closure_set(v___f_1752_, 3, v_y_1741_);
lean_closure_set(v___f_1752_, 4, v_k_1742_);
lean_closure_set(v___f_1752_, 5, v_c_1743_);
lean_closure_set(v___f_1752_, 6, v_fvarId_1744_);
lean_closure_set(v___f_1752_, 7, v___x_1751_);
lean_closure_set(v___f_1752_, 8, v_inst_1746_);
lean_closure_set(v___f_1752_, 9, v_inst_1747_);
lean_closure_set(v___f_1752_, 10, v_f_1748_);
lean_closure_set(v___f_1752_, 11, v_toBind_1749_);
v___x_1753_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_1745_, v_inst_1747_, v_f_1748_, v_y_1741_);
v___x_1754_ = lean_apply_4(v_toBind_1749_, lean_box(0), lean_box(0), v___x_1753_, v___f_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed(lean_object* v_i_1755_, lean_object* v_toPure_1756_, lean_object* v_y_1757_, lean_object* v_k_1758_, lean_object* v_c_1759_, lean_object* v_fvarId_1760_, lean_object* v_pu_1761_, lean_object* v_inst_1762_, lean_object* v_inst_1763_, lean_object* v_f_1764_, lean_object* v_toBind_1765_, lean_object* v_____do__lift_1766_){
_start:
{
uint8_t v_pu_boxed_1767_; lean_object* v_res_1768_; 
v_pu_boxed_1767_ = lean_unbox(v_pu_1761_);
v_res_1768_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(v_i_1755_, v_toPure_1756_, v_y_1757_, v_k_1758_, v_c_1759_, v_fvarId_1760_, v_pu_boxed_1767_, v_inst_1762_, v_inst_1763_, v_f_1764_, v_toBind_1765_, v_____do__lift_1766_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(lean_object* v_____do__lift_1769_, lean_object* v_i_1770_, lean_object* v_toPure_1771_, lean_object* v_y_1772_, lean_object* v_k_1773_, lean_object* v_c_1774_, lean_object* v_fvarId_1775_, uint8_t v_pu_1776_, lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_f_1779_, lean_object* v_toBind_1780_, lean_object* v_____do__lift_1781_){
_start:
{
lean_object* v___f_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_inc_ref(v_k_1773_);
v___f_1782_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed), 9, 8);
lean_closure_set(v___f_1782_, 0, v_____do__lift_1769_);
lean_closure_set(v___f_1782_, 1, v_i_1770_);
lean_closure_set(v___f_1782_, 2, v_____do__lift_1781_);
lean_closure_set(v___f_1782_, 3, v_toPure_1771_);
lean_closure_set(v___f_1782_, 4, v_y_1772_);
lean_closure_set(v___f_1782_, 5, v_k_1773_);
lean_closure_set(v___f_1782_, 6, v_c_1774_);
lean_closure_set(v___f_1782_, 7, v_fvarId_1775_);
v___x_1783_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1776_, v_inst_1777_, v_inst_1778_, v_f_1779_, v_k_1773_);
v___x_1784_ = lean_apply_4(v_toBind_1780_, lean_box(0), lean_box(0), v___x_1783_, v___f_1782_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed(lean_object* v_____do__lift_1785_, lean_object* v_i_1786_, lean_object* v_toPure_1787_, lean_object* v_y_1788_, lean_object* v_k_1789_, lean_object* v_c_1790_, lean_object* v_fvarId_1791_, lean_object* v_pu_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_f_1795_, lean_object* v_toBind_1796_, lean_object* v_____do__lift_1797_){
_start:
{
uint8_t v_pu_boxed_1798_; lean_object* v_res_1799_; 
v_pu_boxed_1798_ = lean_unbox(v_pu_1792_);
v_res_1799_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(v_____do__lift_1785_, v_i_1786_, v_toPure_1787_, v_y_1788_, v_k_1789_, v_c_1790_, v_fvarId_1791_, v_pu_boxed_1798_, v_inst_1793_, v_inst_1794_, v_f_1795_, v_toBind_1796_, v_____do__lift_1797_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(lean_object* v_i_1800_, lean_object* v_toPure_1801_, lean_object* v_y_1802_, lean_object* v_k_1803_, lean_object* v_c_1804_, lean_object* v_fvarId_1805_, uint8_t v_pu_1806_, lean_object* v_inst_1807_, lean_object* v_inst_1808_, lean_object* v_f_1809_, lean_object* v_toBind_1810_, lean_object* v_____do__lift_1811_){
_start:
{
lean_object* v___x_1812_; lean_object* v___f_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1812_ = lean_box(v_pu_1806_);
lean_inc(v_toBind_1810_);
lean_inc(v_f_1809_);
lean_inc(v_y_1802_);
v___f_1813_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed), 13, 12);
lean_closure_set(v___f_1813_, 0, v_____do__lift_1811_);
lean_closure_set(v___f_1813_, 1, v_i_1800_);
lean_closure_set(v___f_1813_, 2, v_toPure_1801_);
lean_closure_set(v___f_1813_, 3, v_y_1802_);
lean_closure_set(v___f_1813_, 4, v_k_1803_);
lean_closure_set(v___f_1813_, 5, v_c_1804_);
lean_closure_set(v___f_1813_, 6, v_fvarId_1805_);
lean_closure_set(v___f_1813_, 7, v___x_1812_);
lean_closure_set(v___f_1813_, 8, v_inst_1807_);
lean_closure_set(v___f_1813_, 9, v_inst_1808_);
lean_closure_set(v___f_1813_, 10, v_f_1809_);
lean_closure_set(v___f_1813_, 11, v_toBind_1810_);
v___x_1814_ = lean_apply_1(v_f_1809_, v_y_1802_);
v___x_1815_ = lean_apply_4(v_toBind_1810_, lean_box(0), lean_box(0), v___x_1814_, v___f_1813_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed(lean_object* v_i_1816_, lean_object* v_toPure_1817_, lean_object* v_y_1818_, lean_object* v_k_1819_, lean_object* v_c_1820_, lean_object* v_fvarId_1821_, lean_object* v_pu_1822_, lean_object* v_inst_1823_, lean_object* v_inst_1824_, lean_object* v_f_1825_, lean_object* v_toBind_1826_, lean_object* v_____do__lift_1827_){
_start:
{
uint8_t v_pu_boxed_1828_; lean_object* v_res_1829_; 
v_pu_boxed_1828_ = lean_unbox(v_pu_1822_);
v_res_1829_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(v_i_1816_, v_toPure_1817_, v_y_1818_, v_k_1819_, v_c_1820_, v_fvarId_1821_, v_pu_boxed_1828_, v_inst_1823_, v_inst_1824_, v_f_1825_, v_toBind_1826_, v_____do__lift_1827_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(lean_object* v_____do__lift_1830_, lean_object* v_i_1831_, lean_object* v_offset_1832_, lean_object* v_____do__lift_1833_, lean_object* v_toPure_1834_, lean_object* v_y_1835_, lean_object* v_ty_1836_, lean_object* v_k_1837_, lean_object* v_c_1838_, lean_object* v_fvarId_1839_, uint8_t v_pu_1840_, lean_object* v_inst_1841_, lean_object* v_inst_1842_, lean_object* v_f_1843_, lean_object* v_toBind_1844_, lean_object* v_____do__lift_1845_){
_start:
{
lean_object* v___f_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_inc_ref(v_k_1837_);
v___f_1846_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed), 12, 11);
lean_closure_set(v___f_1846_, 0, v_____do__lift_1830_);
lean_closure_set(v___f_1846_, 1, v_i_1831_);
lean_closure_set(v___f_1846_, 2, v_offset_1832_);
lean_closure_set(v___f_1846_, 3, v_____do__lift_1833_);
lean_closure_set(v___f_1846_, 4, v_____do__lift_1845_);
lean_closure_set(v___f_1846_, 5, v_toPure_1834_);
lean_closure_set(v___f_1846_, 6, v_y_1835_);
lean_closure_set(v___f_1846_, 7, v_ty_1836_);
lean_closure_set(v___f_1846_, 8, v_k_1837_);
lean_closure_set(v___f_1846_, 9, v_c_1838_);
lean_closure_set(v___f_1846_, 10, v_fvarId_1839_);
v___x_1847_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1840_, v_inst_1841_, v_inst_1842_, v_f_1843_, v_k_1837_);
v___x_1848_ = lean_apply_4(v_toBind_1844_, lean_box(0), lean_box(0), v___x_1847_, v___f_1846_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed(lean_object* v_____do__lift_1849_, lean_object* v_i_1850_, lean_object* v_offset_1851_, lean_object* v_____do__lift_1852_, lean_object* v_toPure_1853_, lean_object* v_y_1854_, lean_object* v_ty_1855_, lean_object* v_k_1856_, lean_object* v_c_1857_, lean_object* v_fvarId_1858_, lean_object* v_pu_1859_, lean_object* v_inst_1860_, lean_object* v_inst_1861_, lean_object* v_f_1862_, lean_object* v_toBind_1863_, lean_object* v_____do__lift_1864_){
_start:
{
uint8_t v_pu_boxed_1865_; lean_object* v_res_1866_; 
v_pu_boxed_1865_ = lean_unbox(v_pu_1859_);
v_res_1866_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(v_____do__lift_1849_, v_i_1850_, v_offset_1851_, v_____do__lift_1852_, v_toPure_1853_, v_y_1854_, v_ty_1855_, v_k_1856_, v_c_1857_, v_fvarId_1858_, v_pu_boxed_1865_, v_inst_1860_, v_inst_1861_, v_f_1862_, v_toBind_1863_, v_____do__lift_1864_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(lean_object* v_____do__lift_1867_, lean_object* v_i_1868_, lean_object* v_offset_1869_, lean_object* v_toPure_1870_, lean_object* v_y_1871_, lean_object* v_ty_1872_, lean_object* v_k_1873_, lean_object* v_c_1874_, lean_object* v_fvarId_1875_, uint8_t v_pu_1876_, lean_object* v_inst_1877_, lean_object* v_inst_1878_, lean_object* v_f_1879_, lean_object* v_toBind_1880_, lean_object* v_____do__lift_1881_){
_start:
{
lean_object* v___x_1882_; lean_object* v___f_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1882_ = lean_box(v_pu_1876_);
lean_inc(v_toBind_1880_);
lean_inc(v_f_1879_);
lean_inc_ref(v_inst_1878_);
lean_inc_ref(v_ty_1872_);
v___f_1883_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed), 16, 15);
lean_closure_set(v___f_1883_, 0, v_____do__lift_1867_);
lean_closure_set(v___f_1883_, 1, v_i_1868_);
lean_closure_set(v___f_1883_, 2, v_offset_1869_);
lean_closure_set(v___f_1883_, 3, v_____do__lift_1881_);
lean_closure_set(v___f_1883_, 4, v_toPure_1870_);
lean_closure_set(v___f_1883_, 5, v_y_1871_);
lean_closure_set(v___f_1883_, 6, v_ty_1872_);
lean_closure_set(v___f_1883_, 7, v_k_1873_);
lean_closure_set(v___f_1883_, 8, v_c_1874_);
lean_closure_set(v___f_1883_, 9, v_fvarId_1875_);
lean_closure_set(v___f_1883_, 10, v___x_1882_);
lean_closure_set(v___f_1883_, 11, v_inst_1877_);
lean_closure_set(v___f_1883_, 12, v_inst_1878_);
lean_closure_set(v___f_1883_, 13, v_f_1879_);
lean_closure_set(v___f_1883_, 14, v_toBind_1880_);
v___x_1884_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1878_, v_f_1879_, v_ty_1872_);
v___x_1885_ = lean_apply_4(v_toBind_1880_, lean_box(0), lean_box(0), v___x_1884_, v___f_1883_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed(lean_object* v_____do__lift_1886_, lean_object* v_i_1887_, lean_object* v_offset_1888_, lean_object* v_toPure_1889_, lean_object* v_y_1890_, lean_object* v_ty_1891_, lean_object* v_k_1892_, lean_object* v_c_1893_, lean_object* v_fvarId_1894_, lean_object* v_pu_1895_, lean_object* v_inst_1896_, lean_object* v_inst_1897_, lean_object* v_f_1898_, lean_object* v_toBind_1899_, lean_object* v_____do__lift_1900_){
_start:
{
uint8_t v_pu_boxed_1901_; lean_object* v_res_1902_; 
v_pu_boxed_1901_ = lean_unbox(v_pu_1895_);
v_res_1902_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(v_____do__lift_1886_, v_i_1887_, v_offset_1888_, v_toPure_1889_, v_y_1890_, v_ty_1891_, v_k_1892_, v_c_1893_, v_fvarId_1894_, v_pu_boxed_1901_, v_inst_1896_, v_inst_1897_, v_f_1898_, v_toBind_1899_, v_____do__lift_1900_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(lean_object* v_i_1903_, lean_object* v_offset_1904_, lean_object* v_toPure_1905_, lean_object* v_y_1906_, lean_object* v_ty_1907_, lean_object* v_k_1908_, lean_object* v_c_1909_, lean_object* v_fvarId_1910_, uint8_t v_pu_1911_, lean_object* v_inst_1912_, lean_object* v_inst_1913_, lean_object* v_f_1914_, lean_object* v_toBind_1915_, lean_object* v_____do__lift_1916_){
_start:
{
lean_object* v___x_1917_; lean_object* v___f_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1917_ = lean_box(v_pu_1911_);
lean_inc(v_toBind_1915_);
lean_inc(v_f_1914_);
lean_inc(v_y_1906_);
v___f_1918_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed), 15, 14);
lean_closure_set(v___f_1918_, 0, v_____do__lift_1916_);
lean_closure_set(v___f_1918_, 1, v_i_1903_);
lean_closure_set(v___f_1918_, 2, v_offset_1904_);
lean_closure_set(v___f_1918_, 3, v_toPure_1905_);
lean_closure_set(v___f_1918_, 4, v_y_1906_);
lean_closure_set(v___f_1918_, 5, v_ty_1907_);
lean_closure_set(v___f_1918_, 6, v_k_1908_);
lean_closure_set(v___f_1918_, 7, v_c_1909_);
lean_closure_set(v___f_1918_, 8, v_fvarId_1910_);
lean_closure_set(v___f_1918_, 9, v___x_1917_);
lean_closure_set(v___f_1918_, 10, v_inst_1912_);
lean_closure_set(v___f_1918_, 11, v_inst_1913_);
lean_closure_set(v___f_1918_, 12, v_f_1914_);
lean_closure_set(v___f_1918_, 13, v_toBind_1915_);
v___x_1919_ = lean_apply_1(v_f_1914_, v_y_1906_);
v___x_1920_ = lean_apply_4(v_toBind_1915_, lean_box(0), lean_box(0), v___x_1919_, v___f_1918_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed(lean_object* v_i_1921_, lean_object* v_offset_1922_, lean_object* v_toPure_1923_, lean_object* v_y_1924_, lean_object* v_ty_1925_, lean_object* v_k_1926_, lean_object* v_c_1927_, lean_object* v_fvarId_1928_, lean_object* v_pu_1929_, lean_object* v_inst_1930_, lean_object* v_inst_1931_, lean_object* v_f_1932_, lean_object* v_toBind_1933_, lean_object* v_____do__lift_1934_){
_start:
{
uint8_t v_pu_boxed_1935_; lean_object* v_res_1936_; 
v_pu_boxed_1935_ = lean_unbox(v_pu_1929_);
v_res_1936_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(v_i_1921_, v_offset_1922_, v_toPure_1923_, v_y_1924_, v_ty_1925_, v_k_1926_, v_c_1927_, v_fvarId_1928_, v_pu_boxed_1935_, v_inst_1930_, v_inst_1931_, v_f_1932_, v_toBind_1933_, v_____do__lift_1934_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(lean_object* v_cidx_1937_, lean_object* v_toPure_1938_, lean_object* v_k_1939_, lean_object* v_c_1940_, lean_object* v_fvarId_1941_, uint8_t v_pu_1942_, lean_object* v_inst_1943_, lean_object* v_inst_1944_, lean_object* v_f_1945_, lean_object* v_toBind_1946_, lean_object* v_____do__lift_1947_){
_start:
{
lean_object* v___f_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
lean_inc_ref(v_k_1939_);
v___f_1948_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27___boxed), 7, 6);
lean_closure_set(v___f_1948_, 0, v_____do__lift_1947_);
lean_closure_set(v___f_1948_, 1, v_cidx_1937_);
lean_closure_set(v___f_1948_, 2, v_toPure_1938_);
lean_closure_set(v___f_1948_, 3, v_k_1939_);
lean_closure_set(v___f_1948_, 4, v_c_1940_);
lean_closure_set(v___f_1948_, 5, v_fvarId_1941_);
v___x_1949_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1942_, v_inst_1943_, v_inst_1944_, v_f_1945_, v_k_1939_);
v___x_1950_ = lean_apply_4(v_toBind_1946_, lean_box(0), lean_box(0), v___x_1949_, v___f_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed(lean_object* v_cidx_1951_, lean_object* v_toPure_1952_, lean_object* v_k_1953_, lean_object* v_c_1954_, lean_object* v_fvarId_1955_, lean_object* v_pu_1956_, lean_object* v_inst_1957_, lean_object* v_inst_1958_, lean_object* v_f_1959_, lean_object* v_toBind_1960_, lean_object* v_____do__lift_1961_){
_start:
{
uint8_t v_pu_boxed_1962_; lean_object* v_res_1963_; 
v_pu_boxed_1962_ = lean_unbox(v_pu_1956_);
v_res_1963_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(v_cidx_1951_, v_toPure_1952_, v_k_1953_, v_c_1954_, v_fvarId_1955_, v_pu_boxed_1962_, v_inst_1957_, v_inst_1958_, v_f_1959_, v_toBind_1960_, v_____do__lift_1961_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(lean_object* v_n_1964_, uint8_t v_check_1965_, uint8_t v_persistent_1966_, lean_object* v_toPure_1967_, lean_object* v_k_1968_, lean_object* v_c_1969_, lean_object* v_fvarId_1970_, uint8_t v_pu_1971_, lean_object* v_inst_1972_, lean_object* v_inst_1973_, lean_object* v_f_1974_, lean_object* v_toBind_1975_, lean_object* v_____do__lift_1976_){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___f_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1977_ = lean_box(v_check_1965_);
v___x_1978_ = lean_box(v_persistent_1966_);
lean_inc_ref(v_k_1968_);
v___f_1979_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29___boxed), 9, 8);
lean_closure_set(v___f_1979_, 0, v_____do__lift_1976_);
lean_closure_set(v___f_1979_, 1, v_n_1964_);
lean_closure_set(v___f_1979_, 2, v___x_1977_);
lean_closure_set(v___f_1979_, 3, v___x_1978_);
lean_closure_set(v___f_1979_, 4, v_toPure_1967_);
lean_closure_set(v___f_1979_, 5, v_k_1968_);
lean_closure_set(v___f_1979_, 6, v_c_1969_);
lean_closure_set(v___f_1979_, 7, v_fvarId_1970_);
v___x_1980_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1971_, v_inst_1972_, v_inst_1973_, v_f_1974_, v_k_1968_);
v___x_1981_ = lean_apply_4(v_toBind_1975_, lean_box(0), lean_box(0), v___x_1980_, v___f_1979_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed(lean_object* v_n_1982_, lean_object* v_check_1983_, lean_object* v_persistent_1984_, lean_object* v_toPure_1985_, lean_object* v_k_1986_, lean_object* v_c_1987_, lean_object* v_fvarId_1988_, lean_object* v_pu_1989_, lean_object* v_inst_1990_, lean_object* v_inst_1991_, lean_object* v_f_1992_, lean_object* v_toBind_1993_, lean_object* v_____do__lift_1994_){
_start:
{
uint8_t v_check_2440__boxed_1995_; uint8_t v_persistent_2441__boxed_1996_; uint8_t v_pu_boxed_1997_; lean_object* v_res_1998_; 
v_check_2440__boxed_1995_ = lean_unbox(v_check_1983_);
v_persistent_2441__boxed_1996_ = lean_unbox(v_persistent_1984_);
v_pu_boxed_1997_ = lean_unbox(v_pu_1989_);
v_res_1998_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(v_n_1982_, v_check_2440__boxed_1995_, v_persistent_2441__boxed_1996_, v_toPure_1985_, v_k_1986_, v_c_1987_, v_fvarId_1988_, v_pu_boxed_1997_, v_inst_1990_, v_inst_1991_, v_f_1992_, v_toBind_1993_, v_____do__lift_1994_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(lean_object* v_n_1999_, uint8_t v_check_2000_, uint8_t v_persistent_2001_, lean_object* v_toPure_2002_, lean_object* v_k_2003_, lean_object* v_c_2004_, lean_object* v_fvarId_2005_, uint8_t v_pu_2006_, lean_object* v_inst_2007_, lean_object* v_inst_2008_, lean_object* v_f_2009_, lean_object* v_toBind_2010_, lean_object* v_____do__lift_2011_){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___f_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2012_ = lean_box(v_check_2000_);
v___x_2013_ = lean_box(v_persistent_2001_);
lean_inc_ref(v_k_2003_);
v___f_2014_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed), 9, 8);
lean_closure_set(v___f_2014_, 0, v_____do__lift_2011_);
lean_closure_set(v___f_2014_, 1, v_n_1999_);
lean_closure_set(v___f_2014_, 2, v___x_2012_);
lean_closure_set(v___f_2014_, 3, v___x_2013_);
lean_closure_set(v___f_2014_, 4, v_toPure_2002_);
lean_closure_set(v___f_2014_, 5, v_k_2003_);
lean_closure_set(v___f_2014_, 6, v_c_2004_);
lean_closure_set(v___f_2014_, 7, v_fvarId_2005_);
v___x_2015_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2006_, v_inst_2007_, v_inst_2008_, v_f_2009_, v_k_2003_);
v___x_2016_ = lean_apply_4(v_toBind_2010_, lean_box(0), lean_box(0), v___x_2015_, v___f_2014_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed(lean_object* v_n_2017_, lean_object* v_check_2018_, lean_object* v_persistent_2019_, lean_object* v_toPure_2020_, lean_object* v_k_2021_, lean_object* v_c_2022_, lean_object* v_fvarId_2023_, lean_object* v_pu_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_f_2027_, lean_object* v_toBind_2028_, lean_object* v_____do__lift_2029_){
_start:
{
uint8_t v_check_2451__boxed_2030_; uint8_t v_persistent_2452__boxed_2031_; uint8_t v_pu_boxed_2032_; lean_object* v_res_2033_; 
v_check_2451__boxed_2030_ = lean_unbox(v_check_2018_);
v_persistent_2452__boxed_2031_ = lean_unbox(v_persistent_2019_);
v_pu_boxed_2032_ = lean_unbox(v_pu_2024_);
v_res_2033_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(v_n_2017_, v_check_2451__boxed_2030_, v_persistent_2452__boxed_2031_, v_toPure_2020_, v_k_2021_, v_c_2022_, v_fvarId_2023_, v_pu_boxed_2032_, v_inst_2025_, v_inst_2026_, v_f_2027_, v_toBind_2028_, v_____do__lift_2029_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(lean_object* v_toPure_2034_, lean_object* v_c_2035_, lean_object* v_fvarId_2036_, lean_object* v_k_2037_, uint8_t v_pu_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_f_2041_, lean_object* v_toBind_2042_, lean_object* v_____do__lift_2043_){
_start:
{
lean_object* v___f_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
lean_inc_ref(v_k_2037_);
v___f_2044_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed), 6, 5);
lean_closure_set(v___f_2044_, 0, v_____do__lift_2043_);
lean_closure_set(v___f_2044_, 1, v_toPure_2034_);
lean_closure_set(v___f_2044_, 2, v_c_2035_);
lean_closure_set(v___f_2044_, 3, v_fvarId_2036_);
lean_closure_set(v___f_2044_, 4, v_k_2037_);
v___x_2045_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2038_, v_inst_2039_, v_inst_2040_, v_f_2041_, v_k_2037_);
v___x_2046_ = lean_apply_4(v_toBind_2042_, lean_box(0), lean_box(0), v___x_2045_, v___f_2044_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed(lean_object* v_toPure_2047_, lean_object* v_c_2048_, lean_object* v_fvarId_2049_, lean_object* v_k_2050_, lean_object* v_pu_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_f_2054_, lean_object* v_toBind_2055_, lean_object* v_____do__lift_2056_){
_start:
{
uint8_t v_pu_boxed_2057_; lean_object* v_res_2058_; 
v_pu_boxed_2057_ = lean_unbox(v_pu_2051_);
v_res_2058_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(v_toPure_2047_, v_c_2048_, v_fvarId_2049_, v_k_2050_, v_pu_boxed_2057_, v_inst_2052_, v_inst_2053_, v_f_2054_, v_toBind_2055_, v_____do__lift_2056_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(uint8_t v_pu_2059_, lean_object* v_inst_2060_, lean_object* v_inst_2061_, lean_object* v_f_2062_, lean_object* v_c_2063_){
_start:
{
switch(lean_obj_tag(v_c_2063_))
{
case 0:
{
lean_object* v_toApplicative_2064_; lean_object* v_toBind_2065_; lean_object* v_toPure_2066_; lean_object* v_decl_2067_; lean_object* v_k_2068_; lean_object* v___x_2069_; lean_object* v___f_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v_toApplicative_2064_ = lean_ctor_get(v_inst_2061_, 0);
v_toBind_2065_ = lean_ctor_get(v_inst_2061_, 1);
lean_inc(v_toBind_2065_);
v_toPure_2066_ = lean_ctor_get(v_toApplicative_2064_, 1);
v_decl_2067_ = lean_ctor_get(v_c_2063_, 0);
lean_inc_ref(v_decl_2067_);
v_k_2068_ = lean_ctor_get(v_c_2063_, 1);
lean_inc_ref(v_k_2068_);
v___x_2069_ = lean_box(v_pu_2059_);
lean_inc(v_toBind_2065_);
lean_inc(v_f_2062_);
lean_inc_ref(v_inst_2061_);
lean_inc(v_inst_2060_);
lean_inc_ref(v_decl_2067_);
lean_inc(v_toPure_2066_);
v___f_2070_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_2070_, 0, v_toPure_2066_);
lean_closure_set(v___f_2070_, 1, v_c_2063_);
lean_closure_set(v___f_2070_, 2, v_k_2068_);
lean_closure_set(v___f_2070_, 3, v_decl_2067_);
lean_closure_set(v___f_2070_, 4, v___x_2069_);
lean_closure_set(v___f_2070_, 5, v_inst_2060_);
lean_closure_set(v___f_2070_, 6, v_inst_2061_);
lean_closure_set(v___f_2070_, 7, v_f_2062_);
lean_closure_set(v___f_2070_, 8, v_toBind_2065_);
v___x_2071_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_2059_, v_inst_2060_, v_inst_2061_, v_f_2062_, v_decl_2067_);
v___x_2072_ = lean_apply_4(v_toBind_2065_, lean_box(0), lean_box(0), v___x_2071_, v___f_2070_);
return v___x_2072_;
}
case 1:
{
lean_object* v_toApplicative_2073_; lean_object* v_decl_2074_; lean_object* v_toBind_2075_; lean_object* v_toPure_2076_; lean_object* v_k_2077_; lean_object* v_params_2078_; lean_object* v_type_2079_; lean_object* v_value_2080_; lean_object* v___x_2081_; lean_object* v___f_2082_; lean_object* v___x_2083_; lean_object* v___f_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; size_t v_sz_2087_; size_t v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v_toApplicative_2073_ = lean_ctor_get(v_inst_2061_, 0);
v_decl_2074_ = lean_ctor_get(v_c_2063_, 0);
lean_inc_ref(v_decl_2074_);
v_toBind_2075_ = lean_ctor_get(v_inst_2061_, 1);
lean_inc(v_toBind_2075_);
v_toPure_2076_ = lean_ctor_get(v_toApplicative_2073_, 1);
v_k_2077_ = lean_ctor_get(v_c_2063_, 1);
lean_inc_ref(v_k_2077_);
v_params_2078_ = lean_ctor_get(v_decl_2074_, 2);
lean_inc_ref(v_params_2078_);
v_type_2079_ = lean_ctor_get(v_decl_2074_, 3);
lean_inc_ref(v_type_2079_);
v_value_2080_ = lean_ctor_get(v_decl_2074_, 4);
lean_inc_ref(v_value_2080_);
v___x_2081_ = lean_box(v_pu_2059_);
lean_inc(v_toBind_2075_);
lean_inc(v_f_2062_);
lean_inc_ref(v_inst_2061_);
lean_inc(v_inst_2060_);
lean_inc_ref(v_decl_2074_);
lean_inc(v_toPure_2076_);
v___f_2082_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_2082_, 0, v_toPure_2076_);
lean_closure_set(v___f_2082_, 1, v_c_2063_);
lean_closure_set(v___f_2082_, 2, v_k_2077_);
lean_closure_set(v___f_2082_, 3, v_decl_2074_);
lean_closure_set(v___f_2082_, 4, v___x_2081_);
lean_closure_set(v___f_2082_, 5, v_inst_2060_);
lean_closure_set(v___f_2082_, 6, v_inst_2061_);
lean_closure_set(v___f_2082_, 7, v_f_2062_);
lean_closure_set(v___f_2082_, 8, v_toBind_2075_);
v___x_2083_ = lean_box(v_pu_2059_);
lean_inc(v_f_2062_);
lean_inc_ref(v_inst_2061_);
lean_inc(v_toBind_2075_);
lean_inc(v_inst_2060_);
v___f_2084_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_2084_, 0, v___x_2083_);
lean_closure_set(v___f_2084_, 1, v_decl_2074_);
lean_closure_set(v___f_2084_, 2, v_inst_2060_);
lean_closure_set(v___f_2084_, 3, v_toBind_2075_);
lean_closure_set(v___f_2084_, 4, v___f_2082_);
lean_closure_set(v___f_2084_, 5, v_inst_2061_);
lean_closure_set(v___f_2084_, 6, v_f_2062_);
lean_closure_set(v___f_2084_, 7, v_value_2080_);
lean_closure_set(v___f_2084_, 8, v_type_2079_);
v___x_2085_ = lean_box(v_pu_2059_);
lean_inc_ref(v_inst_2061_);
v___x_2086_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2086_, 0, lean_box(0));
lean_closure_set(v___x_2086_, 1, v___x_2085_);
lean_closure_set(v___x_2086_, 2, v_inst_2060_);
lean_closure_set(v___x_2086_, 3, v_inst_2061_);
lean_closure_set(v___x_2086_, 4, v_f_2062_);
v_sz_2087_ = lean_array_size(v_params_2078_);
v___x_2088_ = ((size_t)0ULL);
v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2061_, v___x_2086_, v_sz_2087_, v___x_2088_, v_params_2078_);
v___x_2090_ = lean_apply_4(v_toBind_2075_, lean_box(0), lean_box(0), v___x_2089_, v___f_2084_);
return v___x_2090_;
}
case 2:
{
lean_object* v_toApplicative_2091_; lean_object* v_decl_2092_; lean_object* v_toBind_2093_; lean_object* v_toPure_2094_; lean_object* v_k_2095_; lean_object* v_params_2096_; lean_object* v_type_2097_; lean_object* v_value_2098_; lean_object* v___x_2099_; lean_object* v___f_2100_; lean_object* v___x_2101_; lean_object* v___f_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; size_t v_sz_2105_; size_t v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v_toApplicative_2091_ = lean_ctor_get(v_inst_2061_, 0);
v_decl_2092_ = lean_ctor_get(v_c_2063_, 0);
lean_inc_ref(v_decl_2092_);
v_toBind_2093_ = lean_ctor_get(v_inst_2061_, 1);
lean_inc(v_toBind_2093_);
v_toPure_2094_ = lean_ctor_get(v_toApplicative_2091_, 1);
v_k_2095_ = lean_ctor_get(v_c_2063_, 1);
lean_inc_ref(v_k_2095_);
v_params_2096_ = lean_ctor_get(v_decl_2092_, 2);
lean_inc_ref(v_params_2096_);
v_type_2097_ = lean_ctor_get(v_decl_2092_, 3);
lean_inc_ref(v_type_2097_);
v_value_2098_ = lean_ctor_get(v_decl_2092_, 4);
lean_inc_ref(v_value_2098_);
v___x_2099_ = lean_box(v_pu_2059_);
lean_inc(v_toBind_2093_);
lean_inc(v_f_2062_);
lean_inc_ref(v_inst_2061_);
lean_inc(v_inst_2060_);
lean_inc_ref(v_decl_2092_);
lean_inc(v_toPure_2094_);
v___f_2100_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed), 10, 9);
lean_closure_set(v___f_2100_, 0, v_toPure_2094_);
lean_closure_set(v___f_2100_, 1, v_c_2063_);
lean_closure_set(v___f_2100_, 2, v_k_2095_);
lean_closure_set(v___f_2100_, 3, v_decl_2092_);
lean_closure_set(v___f_2100_, 4, v___x_2099_);
lean_closure_set(v___f_2100_, 5, v_inst_2060_);
lean_closure_set(v___f_2100_, 6, v_inst_2061_);
lean_closure_set(v___f_2100_, 7, v_f_2062_);
lean_closure_set(v___f_2100_, 8, v_toBind_2093_);
v___x_2101_ = lean_box(v_pu_2059_);
lean_inc(v_f_2062_);
lean_inc_ref(v_inst_2061_);
lean_inc(v_toBind_2093_);
lean_inc(v_inst_2060_);
v___f_2102_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_2102_, 0, v___x_2101_);
lean_closure_set(v___f_2102_, 1, v_decl_2092_);
lean_closure_set(v___f_2102_, 2, v_inst_2060_);
lean_closure_set(v___f_2102_, 3, v_toBind_2093_);
lean_closure_set(v___f_2102_, 4, v___f_2100_);
lean_closure_set(v___f_2102_, 5, v_inst_2061_);
lean_closure_set(v___f_2102_, 6, v_f_2062_);
lean_closure_set(v___f_2102_, 7, v_value_2098_);
lean_closure_set(v___f_2102_, 8, v_type_2097_);
v___x_2103_ = lean_box(v_pu_2059_);
lean_inc_ref(v_inst_2061_);
v___x_2104_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2104_, 0, lean_box(0));
lean_closure_set(v___x_2104_, 1, v___x_2103_);
lean_closure_set(v___x_2104_, 2, v_inst_2060_);
lean_closure_set(v___x_2104_, 3, v_inst_2061_);
lean_closure_set(v___x_2104_, 4, v_f_2062_);
v_sz_2105_ = lean_array_size(v_params_2096_);
v___x_2106_ = ((size_t)0ULL);
v___x_2107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2061_, v___x_2104_, v_sz_2105_, v___x_2106_, v_params_2096_);
v___x_2108_ = lean_apply_4(v_toBind_2093_, lean_box(0), lean_box(0), v___x_2107_, v___f_2102_);
return v___x_2108_;
}
case 3:
{
lean_object* v_toApplicative_2109_; lean_object* v_toBind_2110_; lean_object* v_toPure_2111_; lean_object* v_fvarId_2112_; lean_object* v_args_2113_; lean_object* v___x_2114_; lean_object* v___f_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v_toApplicative_2109_ = lean_ctor_get(v_inst_2061_, 0);
v_toBind_2110_ = lean_ctor_get(v_inst_2061_, 1);
lean_inc(v_toBind_2110_);
v_toPure_2111_ = lean_ctor_get(v_toApplicative_2109_, 1);
lean_inc(v_toPure_2111_);
v_fvarId_2112_ = lean_ctor_get(v_c_2063_, 0);
lean_inc(v_fvarId_2112_);
v_args_2113_ = lean_ctor_get(v_c_2063_, 1);
lean_inc_ref(v_args_2113_);
v___x_2114_ = lean_box(v_pu_2059_);
lean_inc(v_toBind_2110_);
lean_inc(v_f_2062_);
lean_inc(v_fvarId_2112_);
v___f_2115_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_2115_, 0, v_toPure_2111_);
lean_closure_set(v___f_2115_, 1, v_c_2063_);
lean_closure_set(v___f_2115_, 2, v_fvarId_2112_);
lean_closure_set(v___f_2115_, 3, v_args_2113_);
lean_closure_set(v___f_2115_, 4, v___x_2114_);
lean_closure_set(v___f_2115_, 5, v_inst_2060_);
lean_closure_set(v___f_2115_, 6, v_inst_2061_);
lean_closure_set(v___f_2115_, 7, v_f_2062_);
lean_closure_set(v___f_2115_, 8, v_toBind_2110_);
v___x_2116_ = lean_apply_1(v_f_2062_, v_fvarId_2112_);
v___x_2117_ = lean_apply_4(v_toBind_2110_, lean_box(0), lean_box(0), v___x_2116_, v___f_2115_);
return v___x_2117_;
}
case 4:
{
lean_object* v_toApplicative_2118_; lean_object* v_cases_2119_; lean_object* v_toBind_2120_; lean_object* v_toPure_2121_; lean_object* v_typeName_2122_; lean_object* v_resultType_2123_; lean_object* v_discr_2124_; lean_object* v_alts_2125_; lean_object* v___x_2126_; lean_object* v___f_2127_; lean_object* v___f_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v_toApplicative_2118_ = lean_ctor_get(v_inst_2061_, 0);
v_cases_2119_ = lean_ctor_get(v_c_2063_, 0);
v_toBind_2120_ = lean_ctor_get(v_inst_2061_, 1);
lean_inc(v_toBind_2120_);
v_toPure_2121_ = lean_ctor_get(v_toApplicative_2118_, 1);
v_typeName_2122_ = lean_ctor_get(v_cases_2119_, 0);
lean_inc(v_typeName_2122_);
v_resultType_2123_ = lean_ctor_get(v_cases_2119_, 1);
lean_inc_ref(v_resultType_2123_);
v_discr_2124_ = lean_ctor_get(v_cases_2119_, 2);
lean_inc(v_discr_2124_);
v_alts_2125_ = lean_ctor_get(v_cases_2119_, 3);
lean_inc_ref(v_alts_2125_);
v___x_2126_ = lean_box(v_pu_2059_);
lean_inc(v_f_2062_);
lean_inc_ref(v_inst_2061_);
v___f_2127_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed), 5, 4);
lean_closure_set(v___f_2127_, 0, v___x_2126_);
lean_closure_set(v___f_2127_, 1, v_inst_2060_);
lean_closure_set(v___f_2127_, 2, v_inst_2061_);
lean_closure_set(v___f_2127_, 3, v_f_2062_);
lean_inc(v_f_2062_);
lean_inc(v_toBind_2120_);
lean_inc_ref(v_inst_2061_);
lean_inc_ref(v_resultType_2123_);
lean_inc(v_toPure_2121_);
v___f_2128_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14), 11, 10);
lean_closure_set(v___f_2128_, 0, v_typeName_2122_);
lean_closure_set(v___f_2128_, 1, v_toPure_2121_);
lean_closure_set(v___f_2128_, 2, v_discr_2124_);
lean_closure_set(v___f_2128_, 3, v_c_2063_);
lean_closure_set(v___f_2128_, 4, v_alts_2125_);
lean_closure_set(v___f_2128_, 5, v_resultType_2123_);
lean_closure_set(v___f_2128_, 6, v_inst_2061_);
lean_closure_set(v___f_2128_, 7, v___f_2127_);
lean_closure_set(v___f_2128_, 8, v_toBind_2120_);
lean_closure_set(v___f_2128_, 9, v_f_2062_);
v___x_2129_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2061_, v_f_2062_, v_resultType_2123_);
v___x_2130_ = lean_apply_4(v_toBind_2120_, lean_box(0), lean_box(0), v___x_2129_, v___f_2128_);
return v___x_2130_;
}
case 5:
{
lean_object* v_toApplicative_2131_; lean_object* v_toBind_2132_; lean_object* v_toPure_2133_; lean_object* v_fvarId_2134_; lean_object* v___f_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_toApplicative_2131_ = lean_ctor_get(v_inst_2061_, 0);
lean_inc_ref(v_toApplicative_2131_);
lean_dec(v_inst_2060_);
v_toBind_2132_ = lean_ctor_get(v_inst_2061_, 1);
lean_inc(v_toBind_2132_);
lean_dec_ref(v_inst_2061_);
v_toPure_2133_ = lean_ctor_get(v_toApplicative_2131_, 1);
lean_inc(v_toPure_2133_);
lean_dec_ref(v_toApplicative_2131_);
v_fvarId_2134_ = lean_ctor_get(v_c_2063_, 0);
lean_inc(v_fvarId_2134_);
lean_inc(v_fvarId_2134_);
v___f_2135_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed), 4, 3);
lean_closure_set(v___f_2135_, 0, v_fvarId_2134_);
lean_closure_set(v___f_2135_, 1, v_toPure_2133_);
lean_closure_set(v___f_2135_, 2, v_c_2063_);
v___x_2136_ = lean_apply_1(v_f_2062_, v_fvarId_2134_);
v___x_2137_ = lean_apply_4(v_toBind_2132_, lean_box(0), lean_box(0), v___x_2136_, v___f_2135_);
return v___x_2137_;
}
case 6:
{
lean_object* v_toApplicative_2138_; lean_object* v_toBind_2139_; lean_object* v_toPure_2140_; lean_object* v_type_2141_; lean_object* v___f_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v_toApplicative_2138_ = lean_ctor_get(v_inst_2061_, 0);
lean_dec(v_inst_2060_);
v_toBind_2139_ = lean_ctor_get(v_inst_2061_, 1);
lean_inc(v_toBind_2139_);
v_toPure_2140_ = lean_ctor_get(v_toApplicative_2138_, 1);
v_type_2141_ = lean_ctor_get(v_c_2063_, 0);
lean_inc_ref(v_type_2141_);
lean_inc(v_toPure_2140_);
lean_inc_ref(v_type_2141_);
v___f_2142_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed), 4, 3);
lean_closure_set(v___f_2142_, 0, v_type_2141_);
lean_closure_set(v___f_2142_, 1, v_toPure_2140_);
lean_closure_set(v___f_2142_, 2, v_c_2063_);
v___x_2143_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2061_, v_f_2062_, v_type_2141_);
v___x_2144_ = lean_apply_4(v_toBind_2139_, lean_box(0), lean_box(0), v___x_2143_, v___f_2142_);
return v___x_2144_;
}
case 7:
{
lean_object* v_toApplicative_2145_; lean_object* v_toBind_2146_; lean_object* v_toPure_2147_; lean_object* v_fvarId_2148_; lean_object* v_i_2149_; lean_object* v_y_2150_; lean_object* v_k_2151_; lean_object* v___x_2152_; lean_object* v___f_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v_toApplicative_2145_ = lean_ctor_get(v_inst_2061_, 0);
v_toBind_2146_ = lean_ctor_get(v_inst_2061_, 1);
lean_inc(v_toBind_2146_);
v_toPure_2147_ = lean_ctor_get(v_toApplicative_2145_, 1);
lean_inc(v_toPure_2147_);
v_fvarId_2148_ = lean_ctor_get(v_c_2063_, 0);
lean_inc(v_fvarId_2148_);
v_i_2149_ = lean_ctor_get(v_c_2063_, 1);
lean_inc(v_i_2149_);
v_y_2150_ = lean_ctor_get(v_c_2063_, 2);
lean_inc(v_y_2150_);
v_k_2151_ = lean_ctor_get(v_c_2063_, 3);
lean_inc_ref(v_k_2151_);
v___x_2152_ = lean_box(v_pu_2059_);
lean_inc(v_toBind_2146_);
lean_inc(v_f_2062_);
lean_inc(v_fvarId_2148_);
v___f_2153_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed), 12, 11);
lean_closure_set(v___f_2153_, 0, v_i_2149_);
lean_closure_set(v___f_2153_, 1, v_toPure_2147_);
lean_closure_set(v___f_2153_, 2, v_y_2150_);
lean_closure_set(v___f_2153_, 3, v_k_2151_);
lean_closure_set(v___f_2153_, 4, v_c_2063_);
lean_closure_set(v___f_2153_, 5, v_fvarId_2148_);
lean_closure_set(v___f_2153_, 6, v___x_2152_);
lean_closure_set(v___f_2153_, 7, v_inst_2060_);
lean_closure_set(v___f_2153_, 8, v_inst_2061_);
lean_closure_set(v___f_2153_, 9, v_f_2062_);
lean_closure_set(v___f_2153_, 10, v_toBind_2146_);
v___x_2154_ = lean_apply_1(v_f_2062_, v_fvarId_2148_);
v___x_2155_ = lean_apply_4(v_toBind_2146_, lean_box(0), lean_box(0), v___x_2154_, v___f_2153_);
return v___x_2155_;
}
case 8:
{
lean_object* v_toApplicative_2156_; lean_object* v_toBind_2157_; lean_object* v_toPure_2158_; lean_object* v_fvarId_2159_; lean_object* v_i_2160_; lean_object* v_y_2161_; lean_object* v_k_2162_; lean_object* v___x_2163_; lean_object* v___f_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v_toApplicative_2156_ = lean_ctor_get(v_inst_2061_, 0);
v_toBind_2157_ = lean_ctor_get(v_inst_2061_, 1);
lean_inc(v_toBind_2157_);
v_toPure_2158_ = lean_ctor_get(v_toApplicative_2156_, 1);
lean_inc(v_toPure_2158_);
v_fvarId_2159_ = lean_ctor_get(v_c_2063_, 0);
lean_inc(v_fvarId_2159_);
v_i_2160_ = lean_ctor_get(v_c_2063_, 1);
lean_inc(v_i_2160_);
v_y_2161_ = lean_ctor_get(v_c_2063_, 2);
lean_inc(v_y_2161_);
v_k_2162_ = lean_ctor_get(v_c_2063_, 3);
lean_inc_ref(v_k_2162_);
v___x_2163_ = lean_box(v_pu_2059_);
lean_inc(v_toBind_2157_);
lean_inc(v_f_2062_);
lean_inc(v_fvarId_2159_);
v___f_2164_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed), 12, 11);
lean_closure_set(v___f_2164_, 0, v_i_2160_);
lean_closure_set(v___f_2164_, 1, v_toPure_2158_);
lean_closure_set(v___f_2164_, 2, v_y_2161_);
lean_closure_set(v___f_2164_, 3, v_k_2162_);
lean_closure_set(v___f_2164_, 4, v_c_2063_);
lean_closure_set(v___f_2164_, 5, v_fvarId_2159_);
lean_closure_set(v___f_2164_, 6, v___x_2163_);
lean_closure_set(v___f_2164_, 7, v_inst_2060_);
lean_closure_set(v___f_2164_, 8, v_inst_2061_);
lean_closure_set(v___f_2164_, 9, v_f_2062_);
lean_closure_set(v___f_2164_, 10, v_toBind_2157_);
v___x_2165_ = lean_apply_1(v_f_2062_, v_fvarId_2159_);
v___x_2166_ = lean_apply_4(v_toBind_2157_, lean_box(0), lean_box(0), v___x_2165_, v___f_2164_);
return v___x_2166_;
}
case 9:
{
lean_object* v_toApplicative_2167_; lean_object* v_toBind_2168_; lean_object* v_toPure_2169_; lean_object* v_fvarId_2170_; lean_object* v_i_2171_; lean_object* v_offset_2172_; lean_object* v_y_2173_; lean_object* v_ty_2174_; lean_object* v_k_2175_; lean_object* v___x_2176_; lean_object* v___f_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v_toApplicative_2167_ = lean_ctor_get(v_inst_2061_, 0);
v_toBind_2168_ = lean_ctor_get(v_inst_2061_, 1);
lean_inc(v_toBind_2168_);
v_toPure_2169_ = lean_ctor_get(v_toApplicative_2167_, 1);
lean_inc(v_toPure_2169_);
v_fvarId_2170_ = lean_ctor_get(v_c_2063_, 0);
lean_inc(v_fvarId_2170_);
v_i_2171_ = lean_ctor_get(v_c_2063_, 1);
lean_inc(v_i_2171_);
v_offset_2172_ = lean_ctor_get(v_c_2063_, 2);
lean_inc(v_offset_2172_);
v_y_2173_ = lean_ctor_get(v_c_2063_, 3);
lean_inc(v_y_2173_);
v_ty_2174_ = lean_ctor_get(v_c_2063_, 4);
lean_inc_ref(v_ty_2174_);
v_k_2175_ = lean_ctor_get(v_c_2063_, 5);
lean_inc_ref(v_k_2175_);
v___x_2176_ = lean_box(v_pu_2059_);
lean_inc(v_toBind_2168_);
lean_inc(v_f_2062_);
lean_inc(v_fvarId_2170_);
v___f_2177_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed), 14, 13);
lean_closure_set(v___f_2177_, 0, v_i_2171_);
lean_closure_set(v___f_2177_, 1, v_offset_2172_);
lean_closure_set(v___f_2177_, 2, v_toPure_2169_);
lean_closure_set(v___f_2177_, 3, v_y_2173_);
lean_closure_set(v___f_2177_, 4, v_ty_2174_);
lean_closure_set(v___f_2177_, 5, v_k_2175_);
lean_closure_set(v___f_2177_, 6, v_c_2063_);
lean_closure_set(v___f_2177_, 7, v_fvarId_2170_);
lean_closure_set(v___f_2177_, 8, v___x_2176_);
lean_closure_set(v___f_2177_, 9, v_inst_2060_);
lean_closure_set(v___f_2177_, 10, v_inst_2061_);
lean_closure_set(v___f_2177_, 11, v_f_2062_);
lean_closure_set(v___f_2177_, 12, v_toBind_2168_);
v___x_2178_ = lean_apply_1(v_f_2062_, v_fvarId_2170_);
v___x_2179_ = lean_apply_4(v_toBind_2168_, lean_box(0), lean_box(0), v___x_2178_, v___f_2177_);
return v___x_2179_;
}
case 10:
{
lean_object* v_toApplicative_2180_; lean_object* v_toBind_2181_; lean_object* v_toPure_2182_; lean_object* v_fvarId_2183_; lean_object* v_cidx_2184_; lean_object* v_k_2185_; lean_object* v___x_2186_; lean_object* v___f_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v_toApplicative_2180_ = lean_ctor_get(v_inst_2061_, 0);
v_toBind_2181_ = lean_ctor_get(v_inst_2061_, 1);
lean_inc(v_toBind_2181_);
v_toPure_2182_ = lean_ctor_get(v_toApplicative_2180_, 1);
lean_inc(v_toPure_2182_);
v_fvarId_2183_ = lean_ctor_get(v_c_2063_, 0);
lean_inc(v_fvarId_2183_);
v_cidx_2184_ = lean_ctor_get(v_c_2063_, 1);
lean_inc(v_cidx_2184_);
v_k_2185_ = lean_ctor_get(v_c_2063_, 2);
lean_inc_ref(v_k_2185_);
v___x_2186_ = lean_box(v_pu_2059_);
lean_inc(v_toBind_2181_);
lean_inc(v_f_2062_);
lean_inc(v_fvarId_2183_);
v___f_2187_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed), 11, 10);
lean_closure_set(v___f_2187_, 0, v_cidx_2184_);
lean_closure_set(v___f_2187_, 1, v_toPure_2182_);
lean_closure_set(v___f_2187_, 2, v_k_2185_);
lean_closure_set(v___f_2187_, 3, v_c_2063_);
lean_closure_set(v___f_2187_, 4, v_fvarId_2183_);
lean_closure_set(v___f_2187_, 5, v___x_2186_);
lean_closure_set(v___f_2187_, 6, v_inst_2060_);
lean_closure_set(v___f_2187_, 7, v_inst_2061_);
lean_closure_set(v___f_2187_, 8, v_f_2062_);
lean_closure_set(v___f_2187_, 9, v_toBind_2181_);
v___x_2188_ = lean_apply_1(v_f_2062_, v_fvarId_2183_);
v___x_2189_ = lean_apply_4(v_toBind_2181_, lean_box(0), lean_box(0), v___x_2188_, v___f_2187_);
return v___x_2189_;
}
case 11:
{
lean_object* v_toApplicative_2190_; lean_object* v_toBind_2191_; lean_object* v_toPure_2192_; lean_object* v_fvarId_2193_; lean_object* v_n_2194_; uint8_t v_check_2195_; uint8_t v_persistent_2196_; lean_object* v_k_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___f_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v_toApplicative_2190_ = lean_ctor_get(v_inst_2061_, 0);
v_toBind_2191_ = lean_ctor_get(v_inst_2061_, 1);
lean_inc(v_toBind_2191_);
v_toPure_2192_ = lean_ctor_get(v_toApplicative_2190_, 1);
lean_inc(v_toPure_2192_);
v_fvarId_2193_ = lean_ctor_get(v_c_2063_, 0);
lean_inc(v_fvarId_2193_);
v_n_2194_ = lean_ctor_get(v_c_2063_, 1);
lean_inc(v_n_2194_);
v_check_2195_ = lean_ctor_get_uint8(v_c_2063_, sizeof(void*)*3);
v_persistent_2196_ = lean_ctor_get_uint8(v_c_2063_, sizeof(void*)*3 + 1);
v_k_2197_ = lean_ctor_get(v_c_2063_, 2);
lean_inc_ref(v_k_2197_);
v___x_2198_ = lean_box(v_check_2195_);
v___x_2199_ = lean_box(v_persistent_2196_);
v___x_2200_ = lean_box(v_pu_2059_);
lean_inc(v_toBind_2191_);
lean_inc(v_f_2062_);
lean_inc(v_fvarId_2193_);
v___f_2201_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed), 13, 12);
lean_closure_set(v___f_2201_, 0, v_n_2194_);
lean_closure_set(v___f_2201_, 1, v___x_2198_);
lean_closure_set(v___f_2201_, 2, v___x_2199_);
lean_closure_set(v___f_2201_, 3, v_toPure_2192_);
lean_closure_set(v___f_2201_, 4, v_k_2197_);
lean_closure_set(v___f_2201_, 5, v_c_2063_);
lean_closure_set(v___f_2201_, 6, v_fvarId_2193_);
lean_closure_set(v___f_2201_, 7, v___x_2200_);
lean_closure_set(v___f_2201_, 8, v_inst_2060_);
lean_closure_set(v___f_2201_, 9, v_inst_2061_);
lean_closure_set(v___f_2201_, 10, v_f_2062_);
lean_closure_set(v___f_2201_, 11, v_toBind_2191_);
v___x_2202_ = lean_apply_1(v_f_2062_, v_fvarId_2193_);
v___x_2203_ = lean_apply_4(v_toBind_2191_, lean_box(0), lean_box(0), v___x_2202_, v___f_2201_);
return v___x_2203_;
}
case 12:
{
lean_object* v_toApplicative_2204_; lean_object* v_toBind_2205_; lean_object* v_toPure_2206_; lean_object* v_fvarId_2207_; lean_object* v_n_2208_; uint8_t v_check_2209_; uint8_t v_persistent_2210_; lean_object* v_k_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___f_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v_toApplicative_2204_ = lean_ctor_get(v_inst_2061_, 0);
v_toBind_2205_ = lean_ctor_get(v_inst_2061_, 1);
lean_inc(v_toBind_2205_);
v_toPure_2206_ = lean_ctor_get(v_toApplicative_2204_, 1);
lean_inc(v_toPure_2206_);
v_fvarId_2207_ = lean_ctor_get(v_c_2063_, 0);
lean_inc(v_fvarId_2207_);
v_n_2208_ = lean_ctor_get(v_c_2063_, 1);
lean_inc(v_n_2208_);
v_check_2209_ = lean_ctor_get_uint8(v_c_2063_, sizeof(void*)*3);
v_persistent_2210_ = lean_ctor_get_uint8(v_c_2063_, sizeof(void*)*3 + 1);
v_k_2211_ = lean_ctor_get(v_c_2063_, 2);
lean_inc_ref(v_k_2211_);
v___x_2212_ = lean_box(v_check_2209_);
v___x_2213_ = lean_box(v_persistent_2210_);
v___x_2214_ = lean_box(v_pu_2059_);
lean_inc(v_toBind_2205_);
lean_inc(v_f_2062_);
lean_inc(v_fvarId_2207_);
v___f_2215_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed), 13, 12);
lean_closure_set(v___f_2215_, 0, v_n_2208_);
lean_closure_set(v___f_2215_, 1, v___x_2212_);
lean_closure_set(v___f_2215_, 2, v___x_2213_);
lean_closure_set(v___f_2215_, 3, v_toPure_2206_);
lean_closure_set(v___f_2215_, 4, v_k_2211_);
lean_closure_set(v___f_2215_, 5, v_c_2063_);
lean_closure_set(v___f_2215_, 6, v_fvarId_2207_);
lean_closure_set(v___f_2215_, 7, v___x_2214_);
lean_closure_set(v___f_2215_, 8, v_inst_2060_);
lean_closure_set(v___f_2215_, 9, v_inst_2061_);
lean_closure_set(v___f_2215_, 10, v_f_2062_);
lean_closure_set(v___f_2215_, 11, v_toBind_2205_);
v___x_2216_ = lean_apply_1(v_f_2062_, v_fvarId_2207_);
v___x_2217_ = lean_apply_4(v_toBind_2205_, lean_box(0), lean_box(0), v___x_2216_, v___f_2215_);
return v___x_2217_;
}
default: 
{
lean_object* v_toApplicative_2218_; lean_object* v_toBind_2219_; lean_object* v_toPure_2220_; lean_object* v_fvarId_2221_; lean_object* v_k_2222_; lean_object* v___x_2223_; lean_object* v___f_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v_toApplicative_2218_ = lean_ctor_get(v_inst_2061_, 0);
v_toBind_2219_ = lean_ctor_get(v_inst_2061_, 1);
lean_inc(v_toBind_2219_);
v_toPure_2220_ = lean_ctor_get(v_toApplicative_2218_, 1);
lean_inc(v_toPure_2220_);
v_fvarId_2221_ = lean_ctor_get(v_c_2063_, 0);
lean_inc(v_fvarId_2221_);
v_k_2222_ = lean_ctor_get(v_c_2063_, 1);
lean_inc_ref(v_k_2222_);
v___x_2223_ = lean_box(v_pu_2059_);
lean_inc(v_toBind_2219_);
lean_inc(v_f_2062_);
lean_inc(v_fvarId_2221_);
v___f_2224_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed), 10, 9);
lean_closure_set(v___f_2224_, 0, v_toPure_2220_);
lean_closure_set(v___f_2224_, 1, v_c_2063_);
lean_closure_set(v___f_2224_, 2, v_fvarId_2221_);
lean_closure_set(v___f_2224_, 3, v_k_2222_);
lean_closure_set(v___f_2224_, 4, v___x_2223_);
lean_closure_set(v___f_2224_, 5, v_inst_2060_);
lean_closure_set(v___f_2224_, 6, v_inst_2061_);
lean_closure_set(v___f_2224_, 7, v_f_2062_);
lean_closure_set(v___f_2224_, 8, v_toBind_2219_);
v___x_2225_ = lean_apply_1(v_f_2062_, v_fvarId_2221_);
v___x_2226_ = lean_apply_4(v_toBind_2219_, lean_box(0), lean_box(0), v___x_2225_, v___f_2224_);
return v___x_2226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed(lean_object* v_pu_2227_, lean_object* v_inst_2228_, lean_object* v_inst_2229_, lean_object* v_f_2230_, lean_object* v_c_2231_){
_start:
{
uint8_t v_pu_boxed_2232_; lean_object* v_res_2233_; 
v_pu_boxed_2232_ = lean_unbox(v_pu_2227_);
v_res_2233_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_boxed_2232_, v_inst_2228_, v_inst_2229_, v_f_2230_, v_c_2231_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(uint8_t v_pu_2234_, lean_object* v_inst_2235_, lean_object* v_inst_2236_, lean_object* v_f_2237_, lean_object* v_x_2238_){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2239_ = lean_box(v_pu_2234_);
lean_inc_ref(v_inst_2236_);
v___x_2240_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed), 5, 4);
lean_closure_set(v___x_2240_, 0, v___x_2239_);
lean_closure_set(v___x_2240_, 1, v_inst_2235_);
lean_closure_set(v___x_2240_, 2, v_inst_2236_);
lean_closure_set(v___x_2240_, 3, v_f_2237_);
v___x_2241_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg(v_inst_2236_, v_x_2238_, v___x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM(lean_object* v_m_2242_, uint8_t v_pu_2243_, lean_object* v_inst_2244_, lean_object* v_inst_2245_, lean_object* v_f_2246_, lean_object* v_c_2247_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2243_, v_inst_2244_, v_inst_2245_, v_f_2246_, v_c_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___boxed(lean_object* v_m_2249_, lean_object* v_pu_2250_, lean_object* v_inst_2251_, lean_object* v_inst_2252_, lean_object* v_f_2253_, lean_object* v_c_2254_){
_start:
{
uint8_t v_pu_boxed_2255_; lean_object* v_res_2256_; 
v_pu_boxed_2255_ = lean_unbox(v_pu_2250_);
v_res_2256_ = l_Lean_Compiler_LCNF_Code_mapFVarM(v_m_2249_, v_pu_boxed_2255_, v_inst_2251_, v_inst_2252_, v_f_2253_, v_c_2254_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1(lean_object* v_inst_2257_, lean_object* v_f_2258_, lean_object* v_type_2259_, lean_object* v_toBind_2260_, lean_object* v___f_2261_, lean_object* v_____r_2262_){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2257_, v_f_2258_, v_type_2259_);
v___x_2264_ = lean_apply_4(v_toBind_2260_, lean_box(0), lean_box(0), v___x_2263_, v___f_2261_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12(lean_object* v_inst_2265_, lean_object* v_f_2266_, lean_object* v_ty_2267_, lean_object* v_toBind_2268_, lean_object* v___f_2269_, lean_object* v_____r_2270_){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2265_, v_f_2266_, v_ty_2267_);
v___x_2272_ = lean_apply_4(v_toBind_2268_, lean_box(0), lean_box(0), v___x_2271_, v___f_2269_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4(lean_object* v_args_2273_, lean_object* v_toApplicative_2274_, lean_object* v_inst_2275_, lean_object* v___f_2276_, lean_object* v_____r_2277_){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; 
v___x_2278_ = lean_unsigned_to_nat(0u);
v___x_2279_ = lean_array_get_size(v_args_2273_);
v___x_2280_ = lean_box(0);
v___x_2281_ = lean_nat_dec_lt(v___x_2278_, v___x_2279_);
if (v___x_2281_ == 0)
{
lean_object* v_toPure_2282_; lean_object* v___x_2283_; 
lean_dec(v___f_2276_);
lean_dec_ref(v_inst_2275_);
lean_dec_ref(v_args_2273_);
v_toPure_2282_ = lean_ctor_get(v_toApplicative_2274_, 1);
lean_inc(v_toPure_2282_);
lean_dec_ref(v_toApplicative_2274_);
v___x_2283_ = lean_apply_2(v_toPure_2282_, lean_box(0), v___x_2280_);
return v___x_2283_;
}
else
{
uint8_t v___x_2284_; 
v___x_2284_ = lean_nat_dec_le(v___x_2279_, v___x_2279_);
if (v___x_2284_ == 0)
{
if (v___x_2281_ == 0)
{
lean_object* v_toPure_2285_; lean_object* v___x_2286_; 
lean_dec(v___f_2276_);
lean_dec_ref(v_inst_2275_);
lean_dec_ref(v_args_2273_);
v_toPure_2285_ = lean_ctor_get(v_toApplicative_2274_, 1);
lean_inc(v_toPure_2285_);
lean_dec_ref(v_toApplicative_2274_);
v___x_2286_ = lean_apply_2(v_toPure_2285_, lean_box(0), v___x_2280_);
return v___x_2286_;
}
else
{
size_t v___x_2287_; size_t v___x_2288_; lean_object* v___x_2289_; 
lean_dec_ref(v_toApplicative_2274_);
v___x_2287_ = ((size_t)0ULL);
v___x_2288_ = lean_usize_of_nat(v___x_2279_);
v___x_2289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2275_, v___f_2276_, v_args_2273_, v___x_2287_, v___x_2288_, v___x_2280_);
return v___x_2289_;
}
}
else
{
size_t v___x_2290_; size_t v___x_2291_; lean_object* v___x_2292_; 
lean_dec_ref(v_toApplicative_2274_);
v___x_2290_ = ((size_t)0ULL);
v___x_2291_ = lean_usize_of_nat(v___x_2279_);
v___x_2292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2275_, v___f_2276_, v_args_2273_, v___x_2290_, v___x_2291_, v___x_2280_);
return v___x_2292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3(lean_object* v_inst_2293_, lean_object* v_f_2294_, lean_object* v_x_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_2293_, v_f_2294_, v___y_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10(lean_object* v_inst_2298_, lean_object* v_f_2299_, lean_object* v_y_2300_, lean_object* v_toBind_2301_, lean_object* v___f_2302_, lean_object* v_____r_2303_){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2298_, v_f_2299_, v_y_2300_);
v___x_2305_ = lean_apply_4(v_toBind_2301_, lean_box(0), lean_box(0), v___x_2304_, v___f_2302_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11(lean_object* v_f_2306_, lean_object* v_y_2307_, lean_object* v_toBind_2308_, lean_object* v___f_2309_, lean_object* v_____r_2310_){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = lean_apply_1(v_f_2306_, v_y_2307_);
v___x_2312_ = lean_apply_4(v_toBind_2308_, lean_box(0), lean_box(0), v___x_2311_, v___f_2309_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7(lean_object* v_f_2313_, lean_object* v_discr_2314_, lean_object* v_toBind_2315_, lean_object* v___f_2316_, lean_object* v_____r_2317_){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = lean_apply_1(v_f_2313_, v_discr_2314_);
v___x_2319_ = lean_apply_4(v_toBind_2315_, lean_box(0), lean_box(0), v___x_2318_, v___f_2316_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6(lean_object* v_alts_2320_, lean_object* v_toApplicative_2321_, lean_object* v_inst_2322_, lean_object* v___f_2323_, lean_object* v_____r_2324_){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2325_ = lean_unsigned_to_nat(0u);
v___x_2326_ = lean_array_get_size(v_alts_2320_);
v___x_2327_ = lean_box(0);
v___x_2328_ = lean_nat_dec_lt(v___x_2325_, v___x_2326_);
if (v___x_2328_ == 0)
{
lean_object* v_toPure_2329_; lean_object* v___x_2330_; 
lean_dec(v___f_2323_);
lean_dec_ref(v_inst_2322_);
lean_dec_ref(v_alts_2320_);
v_toPure_2329_ = lean_ctor_get(v_toApplicative_2321_, 1);
lean_inc(v_toPure_2329_);
lean_dec_ref(v_toApplicative_2321_);
v___x_2330_ = lean_apply_2(v_toPure_2329_, lean_box(0), v___x_2327_);
return v___x_2330_;
}
else
{
uint8_t v___x_2331_; 
v___x_2331_ = lean_nat_dec_le(v___x_2326_, v___x_2326_);
if (v___x_2331_ == 0)
{
if (v___x_2328_ == 0)
{
lean_object* v_toPure_2332_; lean_object* v___x_2333_; 
lean_dec(v___f_2323_);
lean_dec_ref(v_inst_2322_);
lean_dec_ref(v_alts_2320_);
v_toPure_2332_ = lean_ctor_get(v_toApplicative_2321_, 1);
lean_inc(v_toPure_2332_);
lean_dec_ref(v_toApplicative_2321_);
v___x_2333_ = lean_apply_2(v_toPure_2332_, lean_box(0), v___x_2327_);
return v___x_2333_;
}
else
{
size_t v___x_2334_; size_t v___x_2335_; lean_object* v___x_2336_; 
lean_dec_ref(v_toApplicative_2321_);
v___x_2334_ = ((size_t)0ULL);
v___x_2335_ = lean_usize_of_nat(v___x_2326_);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2322_, v___f_2323_, v_alts_2320_, v___x_2334_, v___x_2335_, v___x_2327_);
return v___x_2336_;
}
}
else
{
size_t v___x_2337_; size_t v___x_2338_; lean_object* v___x_2339_; 
lean_dec_ref(v_toApplicative_2321_);
v___x_2337_ = ((size_t)0ULL);
v___x_2338_ = lean_usize_of_nat(v___x_2326_);
v___x_2339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2322_, v___f_2323_, v_alts_2320_, v___x_2337_, v___x_2338_, v___x_2327_);
return v___x_2339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8(lean_object* v_inst_2340_, lean_object* v_f_2341_, lean_object* v_x_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2340_, v_f_2341_, v___y_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2(lean_object* v_inst_2345_, lean_object* v_f_2346_, lean_object* v_value_2347_, lean_object* v_toBind_2348_, lean_object* v___f_2349_, lean_object* v_____r_2350_){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2345_, v_f_2346_, v_value_2347_);
v___x_2352_ = lean_apply_4(v_toBind_2348_, lean_box(0), lean_box(0), v___x_2351_, v___f_2349_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5(lean_object* v_inst_2353_, lean_object* v_f_2354_, lean_object* v_x_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg), 3, 2);
lean_closure_set(v___x_2357_, 0, v_inst_2353_);
lean_closure_set(v___x_2357_, 1, v_f_2354_);
v___x_2358_ = l_Lean_Compiler_LCNF_Alt_forCodeM___redArg(v___y_2356_, v___x_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg(lean_object* v_inst_2359_, lean_object* v_f_2360_, lean_object* v_c_2361_){
_start:
{
switch(lean_obj_tag(v_c_2361_))
{
case 0:
{
lean_object* v_toBind_2362_; lean_object* v_decl_2363_; lean_object* v_k_2364_; lean_object* v___f_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v_toBind_2362_ = lean_ctor_get(v_inst_2359_, 1);
lean_inc(v_toBind_2362_);
v_decl_2363_ = lean_ctor_get(v_c_2361_, 0);
lean_inc_ref(v_decl_2363_);
v_k_2364_ = lean_ctor_get(v_c_2361_, 1);
lean_inc_ref(v_k_2364_);
lean_dec_ref(v_c_2361_);
lean_inc(v_f_2360_);
lean_inc_ref(v_inst_2359_);
v___f_2365_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2365_, 0, v_inst_2359_);
lean_closure_set(v___f_2365_, 1, v_f_2360_);
lean_closure_set(v___f_2365_, 2, v_k_2364_);
v___x_2366_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_2359_, v_f_2360_, v_decl_2363_);
v___x_2367_ = lean_apply_4(v_toBind_2362_, lean_box(0), lean_box(0), v___x_2366_, v___f_2365_);
return v___x_2367_;
}
case 1:
{
lean_object* v_decl_2368_; lean_object* v_toApplicative_2369_; lean_object* v_toBind_2370_; lean_object* v_k_2371_; lean_object* v_params_2372_; lean_object* v_type_2373_; lean_object* v_value_2374_; lean_object* v___f_2375_; lean_object* v___f_2376_; lean_object* v___f_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; 
v_decl_2368_ = lean_ctor_get(v_c_2361_, 0);
lean_inc_ref(v_decl_2368_);
v_toApplicative_2369_ = lean_ctor_get(v_inst_2359_, 0);
v_toBind_2370_ = lean_ctor_get(v_inst_2359_, 1);
lean_inc(v_toBind_2370_);
v_k_2371_ = lean_ctor_get(v_c_2361_, 1);
lean_inc_ref(v_k_2371_);
lean_dec_ref(v_c_2361_);
v_params_2372_ = lean_ctor_get(v_decl_2368_, 2);
lean_inc_ref(v_params_2372_);
v_type_2373_ = lean_ctor_get(v_decl_2368_, 3);
lean_inc_ref(v_type_2373_);
v_value_2374_ = lean_ctor_get(v_decl_2368_, 4);
lean_inc_ref(v_value_2374_);
lean_dec_ref(v_decl_2368_);
lean_inc(v_f_2360_);
lean_inc_ref(v_inst_2359_);
v___f_2375_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2375_, 0, v_inst_2359_);
lean_closure_set(v___f_2375_, 1, v_f_2360_);
lean_closure_set(v___f_2375_, 2, v_k_2371_);
lean_inc(v_toBind_2370_);
lean_inc(v_f_2360_);
lean_inc_ref(v_inst_2359_);
v___f_2376_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2376_, 0, v_inst_2359_);
lean_closure_set(v___f_2376_, 1, v_f_2360_);
lean_closure_set(v___f_2376_, 2, v_value_2374_);
lean_closure_set(v___f_2376_, 3, v_toBind_2370_);
lean_closure_set(v___f_2376_, 4, v___f_2375_);
lean_inc(v_toBind_2370_);
lean_inc(v_f_2360_);
lean_inc_ref(v_inst_2359_);
v___f_2377_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2377_, 0, v_inst_2359_);
lean_closure_set(v___f_2377_, 1, v_f_2360_);
lean_closure_set(v___f_2377_, 2, v_type_2373_);
lean_closure_set(v___f_2377_, 3, v_toBind_2370_);
lean_closure_set(v___f_2377_, 4, v___f_2376_);
v___x_2378_ = lean_unsigned_to_nat(0u);
v___x_2379_ = lean_array_get_size(v_params_2372_);
v___x_2380_ = lean_box(0);
v___x_2381_ = lean_nat_dec_lt(v___x_2378_, v___x_2379_);
if (v___x_2381_ == 0)
{
lean_object* v_toPure_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
lean_inc_ref(v_toApplicative_2369_);
lean_dec_ref(v_params_2372_);
lean_dec(v_f_2360_);
lean_dec_ref(v_inst_2359_);
v_toPure_2382_ = lean_ctor_get(v_toApplicative_2369_, 1);
lean_inc(v_toPure_2382_);
lean_dec_ref(v_toApplicative_2369_);
v___x_2383_ = lean_apply_2(v_toPure_2382_, lean_box(0), v___x_2380_);
v___x_2384_ = lean_apply_4(v_toBind_2370_, lean_box(0), lean_box(0), v___x_2383_, v___f_2377_);
return v___x_2384_;
}
else
{
lean_object* v___f_2385_; uint8_t v___x_2386_; 
lean_inc_ref(v_inst_2359_);
v___f_2385_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2385_, 0, v_inst_2359_);
lean_closure_set(v___f_2385_, 1, v_f_2360_);
v___x_2386_ = lean_nat_dec_le(v___x_2379_, v___x_2379_);
if (v___x_2386_ == 0)
{
if (v___x_2381_ == 0)
{
lean_object* v_toPure_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_inc_ref(v_toApplicative_2369_);
lean_dec_ref(v___f_2385_);
lean_dec_ref(v_params_2372_);
lean_dec_ref(v_inst_2359_);
v_toPure_2387_ = lean_ctor_get(v_toApplicative_2369_, 1);
lean_inc(v_toPure_2387_);
lean_dec_ref(v_toApplicative_2369_);
v___x_2388_ = lean_apply_2(v_toPure_2387_, lean_box(0), v___x_2380_);
v___x_2389_ = lean_apply_4(v_toBind_2370_, lean_box(0), lean_box(0), v___x_2388_, v___f_2377_);
return v___x_2389_;
}
else
{
size_t v___x_2390_; size_t v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2390_ = ((size_t)0ULL);
v___x_2391_ = lean_usize_of_nat(v___x_2379_);
v___x_2392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2359_, v___f_2385_, v_params_2372_, v___x_2390_, v___x_2391_, v___x_2380_);
v___x_2393_ = lean_apply_4(v_toBind_2370_, lean_box(0), lean_box(0), v___x_2392_, v___f_2377_);
return v___x_2393_;
}
}
else
{
size_t v___x_2394_; size_t v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2394_ = ((size_t)0ULL);
v___x_2395_ = lean_usize_of_nat(v___x_2379_);
v___x_2396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2359_, v___f_2385_, v_params_2372_, v___x_2394_, v___x_2395_, v___x_2380_);
v___x_2397_ = lean_apply_4(v_toBind_2370_, lean_box(0), lean_box(0), v___x_2396_, v___f_2377_);
return v___x_2397_;
}
}
}
case 2:
{
lean_object* v_decl_2398_; lean_object* v_toApplicative_2399_; lean_object* v_toBind_2400_; lean_object* v_k_2401_; lean_object* v_params_2402_; lean_object* v_type_2403_; lean_object* v_value_2404_; lean_object* v___f_2405_; lean_object* v___f_2406_; lean_object* v___f_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
v_decl_2398_ = lean_ctor_get(v_c_2361_, 0);
lean_inc_ref(v_decl_2398_);
v_toApplicative_2399_ = lean_ctor_get(v_inst_2359_, 0);
v_toBind_2400_ = lean_ctor_get(v_inst_2359_, 1);
lean_inc(v_toBind_2400_);
v_k_2401_ = lean_ctor_get(v_c_2361_, 1);
lean_inc_ref(v_k_2401_);
lean_dec_ref(v_c_2361_);
v_params_2402_ = lean_ctor_get(v_decl_2398_, 2);
lean_inc_ref(v_params_2402_);
v_type_2403_ = lean_ctor_get(v_decl_2398_, 3);
lean_inc_ref(v_type_2403_);
v_value_2404_ = lean_ctor_get(v_decl_2398_, 4);
lean_inc_ref(v_value_2404_);
lean_dec_ref(v_decl_2398_);
lean_inc(v_f_2360_);
lean_inc_ref(v_inst_2359_);
v___f_2405_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2405_, 0, v_inst_2359_);
lean_closure_set(v___f_2405_, 1, v_f_2360_);
lean_closure_set(v___f_2405_, 2, v_k_2401_);
lean_inc(v_toBind_2400_);
lean_inc(v_f_2360_);
lean_inc_ref(v_inst_2359_);
v___f_2406_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2406_, 0, v_inst_2359_);
lean_closure_set(v___f_2406_, 1, v_f_2360_);
lean_closure_set(v___f_2406_, 2, v_value_2404_);
lean_closure_set(v___f_2406_, 3, v_toBind_2400_);
lean_closure_set(v___f_2406_, 4, v___f_2405_);
lean_inc(v_toBind_2400_);
lean_inc(v_f_2360_);
lean_inc_ref(v_inst_2359_);
v___f_2407_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2407_, 0, v_inst_2359_);
lean_closure_set(v___f_2407_, 1, v_f_2360_);
lean_closure_set(v___f_2407_, 2, v_type_2403_);
lean_closure_set(v___f_2407_, 3, v_toBind_2400_);
lean_closure_set(v___f_2407_, 4, v___f_2406_);
v___x_2408_ = lean_unsigned_to_nat(0u);
v___x_2409_ = lean_array_get_size(v_params_2402_);
v___x_2410_ = lean_box(0);
v___x_2411_ = lean_nat_dec_lt(v___x_2408_, v___x_2409_);
if (v___x_2411_ == 0)
{
lean_object* v_toPure_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
lean_inc_ref(v_toApplicative_2399_);
lean_dec_ref(v_params_2402_);
lean_dec(v_f_2360_);
lean_dec_ref(v_inst_2359_);
v_toPure_2412_ = lean_ctor_get(v_toApplicative_2399_, 1);
lean_inc(v_toPure_2412_);
lean_dec_ref(v_toApplicative_2399_);
v___x_2413_ = lean_apply_2(v_toPure_2412_, lean_box(0), v___x_2410_);
v___x_2414_ = lean_apply_4(v_toBind_2400_, lean_box(0), lean_box(0), v___x_2413_, v___f_2407_);
return v___x_2414_;
}
else
{
lean_object* v___f_2415_; uint8_t v___x_2416_; 
lean_inc_ref(v_inst_2359_);
v___f_2415_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2415_, 0, v_inst_2359_);
lean_closure_set(v___f_2415_, 1, v_f_2360_);
v___x_2416_ = lean_nat_dec_le(v___x_2409_, v___x_2409_);
if (v___x_2416_ == 0)
{
if (v___x_2411_ == 0)
{
lean_object* v_toPure_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_inc_ref(v_toApplicative_2399_);
lean_dec_ref(v___f_2415_);
lean_dec_ref(v_params_2402_);
lean_dec_ref(v_inst_2359_);
v_toPure_2417_ = lean_ctor_get(v_toApplicative_2399_, 1);
lean_inc(v_toPure_2417_);
lean_dec_ref(v_toApplicative_2399_);
v___x_2418_ = lean_apply_2(v_toPure_2417_, lean_box(0), v___x_2410_);
v___x_2419_ = lean_apply_4(v_toBind_2400_, lean_box(0), lean_box(0), v___x_2418_, v___f_2407_);
return v___x_2419_;
}
else
{
size_t v___x_2420_; size_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2420_ = ((size_t)0ULL);
v___x_2421_ = lean_usize_of_nat(v___x_2409_);
v___x_2422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2359_, v___f_2415_, v_params_2402_, v___x_2420_, v___x_2421_, v___x_2410_);
v___x_2423_ = lean_apply_4(v_toBind_2400_, lean_box(0), lean_box(0), v___x_2422_, v___f_2407_);
return v___x_2423_;
}
}
else
{
size_t v___x_2424_; size_t v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2424_ = ((size_t)0ULL);
v___x_2425_ = lean_usize_of_nat(v___x_2409_);
v___x_2426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2359_, v___f_2415_, v_params_2402_, v___x_2424_, v___x_2425_, v___x_2410_);
v___x_2427_ = lean_apply_4(v_toBind_2400_, lean_box(0), lean_box(0), v___x_2426_, v___f_2407_);
return v___x_2427_;
}
}
}
case 3:
{
lean_object* v_toApplicative_2428_; lean_object* v_toBind_2429_; lean_object* v_fvarId_2430_; lean_object* v_args_2431_; lean_object* v___f_2432_; lean_object* v___f_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v_toApplicative_2428_ = lean_ctor_get(v_inst_2359_, 0);
lean_inc_ref(v_toApplicative_2428_);
v_toBind_2429_ = lean_ctor_get(v_inst_2359_, 1);
lean_inc(v_toBind_2429_);
v_fvarId_2430_ = lean_ctor_get(v_c_2361_, 0);
lean_inc(v_fvarId_2430_);
v_args_2431_ = lean_ctor_get(v_c_2361_, 1);
lean_inc_ref(v_args_2431_);
lean_dec_ref(v_c_2361_);
lean_inc(v_f_2360_);
lean_inc_ref(v_inst_2359_);
v___f_2432_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8), 4, 2);
lean_closure_set(v___f_2432_, 0, v_inst_2359_);
lean_closure_set(v___f_2432_, 1, v_f_2360_);
v___f_2433_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2433_, 0, v_args_2431_);
lean_closure_set(v___f_2433_, 1, v_toApplicative_2428_);
lean_closure_set(v___f_2433_, 2, v_inst_2359_);
lean_closure_set(v___f_2433_, 3, v___f_2432_);
v___x_2434_ = lean_apply_1(v_f_2360_, v_fvarId_2430_);
v___x_2435_ = lean_apply_4(v_toBind_2429_, lean_box(0), lean_box(0), v___x_2434_, v___f_2433_);
return v___x_2435_;
}
case 4:
{
lean_object* v_cases_2436_; lean_object* v_toApplicative_2437_; lean_object* v_toBind_2438_; lean_object* v_resultType_2439_; lean_object* v_discr_2440_; lean_object* v_alts_2441_; lean_object* v___f_2442_; lean_object* v___f_2443_; lean_object* v___f_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v_cases_2436_ = lean_ctor_get(v_c_2361_, 0);
lean_inc_ref(v_cases_2436_);
lean_dec_ref(v_c_2361_);
v_toApplicative_2437_ = lean_ctor_get(v_inst_2359_, 0);
v_toBind_2438_ = lean_ctor_get(v_inst_2359_, 1);
lean_inc(v_toBind_2438_);
v_resultType_2439_ = lean_ctor_get(v_cases_2436_, 1);
lean_inc_ref(v_resultType_2439_);
v_discr_2440_ = lean_ctor_get(v_cases_2436_, 2);
lean_inc(v_discr_2440_);
v_alts_2441_ = lean_ctor_get(v_cases_2436_, 3);
lean_inc_ref(v_alts_2441_);
lean_dec_ref(v_cases_2436_);
lean_inc(v_f_2360_);
lean_inc_ref(v_inst_2359_);
v___f_2442_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5), 4, 2);
lean_closure_set(v___f_2442_, 0, v_inst_2359_);
lean_closure_set(v___f_2442_, 1, v_f_2360_);
lean_inc_ref(v_inst_2359_);
lean_inc_ref(v_toApplicative_2437_);
v___f_2443_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6), 5, 4);
lean_closure_set(v___f_2443_, 0, v_alts_2441_);
lean_closure_set(v___f_2443_, 1, v_toApplicative_2437_);
lean_closure_set(v___f_2443_, 2, v_inst_2359_);
lean_closure_set(v___f_2443_, 3, v___f_2442_);
lean_inc(v_toBind_2438_);
lean_inc(v_f_2360_);
v___f_2444_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7), 5, 4);
lean_closure_set(v___f_2444_, 0, v_f_2360_);
lean_closure_set(v___f_2444_, 1, v_discr_2440_);
lean_closure_set(v___f_2444_, 2, v_toBind_2438_);
lean_closure_set(v___f_2444_, 3, v___f_2443_);
v___x_2445_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2359_, v_f_2360_, v_resultType_2439_);
v___x_2446_ = lean_apply_4(v_toBind_2438_, lean_box(0), lean_box(0), v___x_2445_, v___f_2444_);
return v___x_2446_;
}
case 5:
{
lean_object* v_fvarId_2447_; lean_object* v___x_2448_; 
lean_dec_ref(v_inst_2359_);
v_fvarId_2447_ = lean_ctor_get(v_c_2361_, 0);
lean_inc(v_fvarId_2447_);
lean_dec_ref(v_c_2361_);
v___x_2448_ = lean_apply_1(v_f_2360_, v_fvarId_2447_);
return v___x_2448_;
}
case 6:
{
lean_object* v_type_2449_; lean_object* v___x_2450_; 
v_type_2449_ = lean_ctor_get(v_c_2361_, 0);
lean_inc_ref(v_type_2449_);
lean_dec_ref(v_c_2361_);
v___x_2450_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2359_, v_f_2360_, v_type_2449_);
return v___x_2450_;
}
case 7:
{
lean_object* v_toBind_2451_; lean_object* v_fvarId_2452_; lean_object* v_y_2453_; lean_object* v_k_2454_; lean_object* v___f_2455_; lean_object* v___f_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v_toBind_2451_ = lean_ctor_get(v_inst_2359_, 1);
lean_inc(v_toBind_2451_);
v_fvarId_2452_ = lean_ctor_get(v_c_2361_, 0);
lean_inc(v_fvarId_2452_);
v_y_2453_ = lean_ctor_get(v_c_2361_, 2);
lean_inc(v_y_2453_);
v_k_2454_ = lean_ctor_get(v_c_2361_, 3);
lean_inc_ref(v_k_2454_);
lean_dec_ref(v_c_2361_);
lean_inc(v_f_2360_);
lean_inc_ref(v_inst_2359_);
v___f_2455_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2455_, 0, v_inst_2359_);
lean_closure_set(v___f_2455_, 1, v_f_2360_);
lean_closure_set(v___f_2455_, 2, v_k_2454_);
lean_inc(v_toBind_2451_);
lean_inc(v_f_2360_);
v___f_2456_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10), 6, 5);
lean_closure_set(v___f_2456_, 0, v_inst_2359_);
lean_closure_set(v___f_2456_, 1, v_f_2360_);
lean_closure_set(v___f_2456_, 2, v_y_2453_);
lean_closure_set(v___f_2456_, 3, v_toBind_2451_);
lean_closure_set(v___f_2456_, 4, v___f_2455_);
v___x_2457_ = lean_apply_1(v_f_2360_, v_fvarId_2452_);
v___x_2458_ = lean_apply_4(v_toBind_2451_, lean_box(0), lean_box(0), v___x_2457_, v___f_2456_);
return v___x_2458_;
}
case 8:
{
lean_object* v_toBind_2459_; lean_object* v_fvarId_2460_; lean_object* v_y_2461_; lean_object* v_k_2462_; lean_object* v___f_2463_; lean_object* v___f_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v_toBind_2459_ = lean_ctor_get(v_inst_2359_, 1);
lean_inc(v_toBind_2459_);
v_fvarId_2460_ = lean_ctor_get(v_c_2361_, 0);
lean_inc(v_fvarId_2460_);
v_y_2461_ = lean_ctor_get(v_c_2361_, 2);
lean_inc(v_y_2461_);
v_k_2462_ = lean_ctor_get(v_c_2361_, 3);
lean_inc_ref(v_k_2462_);
lean_dec_ref(v_c_2361_);
lean_inc(v_f_2360_);
v___f_2463_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2463_, 0, v_inst_2359_);
lean_closure_set(v___f_2463_, 1, v_f_2360_);
lean_closure_set(v___f_2463_, 2, v_k_2462_);
lean_inc(v_toBind_2459_);
lean_inc(v_f_2360_);
v___f_2464_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11), 5, 4);
lean_closure_set(v___f_2464_, 0, v_f_2360_);
lean_closure_set(v___f_2464_, 1, v_y_2461_);
lean_closure_set(v___f_2464_, 2, v_toBind_2459_);
lean_closure_set(v___f_2464_, 3, v___f_2463_);
v___x_2465_ = lean_apply_1(v_f_2360_, v_fvarId_2460_);
v___x_2466_ = lean_apply_4(v_toBind_2459_, lean_box(0), lean_box(0), v___x_2465_, v___f_2464_);
return v___x_2466_;
}
case 9:
{
lean_object* v_toBind_2467_; lean_object* v_fvarId_2468_; lean_object* v_y_2469_; lean_object* v_ty_2470_; lean_object* v_k_2471_; lean_object* v___f_2472_; lean_object* v___f_2473_; lean_object* v___f_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_toBind_2467_ = lean_ctor_get(v_inst_2359_, 1);
lean_inc(v_toBind_2467_);
v_fvarId_2468_ = lean_ctor_get(v_c_2361_, 0);
lean_inc(v_fvarId_2468_);
v_y_2469_ = lean_ctor_get(v_c_2361_, 3);
lean_inc(v_y_2469_);
v_ty_2470_ = lean_ctor_get(v_c_2361_, 4);
lean_inc_ref(v_ty_2470_);
v_k_2471_ = lean_ctor_get(v_c_2361_, 5);
lean_inc_ref(v_k_2471_);
lean_dec_ref(v_c_2361_);
lean_inc(v_f_2360_);
lean_inc_ref(v_inst_2359_);
v___f_2472_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2472_, 0, v_inst_2359_);
lean_closure_set(v___f_2472_, 1, v_f_2360_);
lean_closure_set(v___f_2472_, 2, v_k_2471_);
lean_inc(v_toBind_2467_);
lean_inc(v_f_2360_);
v___f_2473_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12), 6, 5);
lean_closure_set(v___f_2473_, 0, v_inst_2359_);
lean_closure_set(v___f_2473_, 1, v_f_2360_);
lean_closure_set(v___f_2473_, 2, v_ty_2470_);
lean_closure_set(v___f_2473_, 3, v_toBind_2467_);
lean_closure_set(v___f_2473_, 4, v___f_2472_);
lean_inc(v_toBind_2467_);
lean_inc(v_f_2360_);
v___f_2474_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11), 5, 4);
lean_closure_set(v___f_2474_, 0, v_f_2360_);
lean_closure_set(v___f_2474_, 1, v_y_2469_);
lean_closure_set(v___f_2474_, 2, v_toBind_2467_);
lean_closure_set(v___f_2474_, 3, v___f_2473_);
v___x_2475_ = lean_apply_1(v_f_2360_, v_fvarId_2468_);
v___x_2476_ = lean_apply_4(v_toBind_2467_, lean_box(0), lean_box(0), v___x_2475_, v___f_2474_);
return v___x_2476_;
}
case 13:
{
lean_object* v_toBind_2477_; lean_object* v_fvarId_2478_; lean_object* v_k_2479_; lean_object* v___f_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v_toBind_2477_ = lean_ctor_get(v_inst_2359_, 1);
lean_inc(v_toBind_2477_);
v_fvarId_2478_ = lean_ctor_get(v_c_2361_, 0);
lean_inc(v_fvarId_2478_);
v_k_2479_ = lean_ctor_get(v_c_2361_, 1);
lean_inc_ref(v_k_2479_);
lean_dec_ref(v_c_2361_);
lean_inc(v_f_2360_);
v___f_2480_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2480_, 0, v_inst_2359_);
lean_closure_set(v___f_2480_, 1, v_f_2360_);
lean_closure_set(v___f_2480_, 2, v_k_2479_);
v___x_2481_ = lean_apply_1(v_f_2360_, v_fvarId_2478_);
v___x_2482_ = lean_apply_4(v_toBind_2477_, lean_box(0), lean_box(0), v___x_2481_, v___f_2480_);
return v___x_2482_;
}
default: 
{
lean_object* v_toBind_2483_; lean_object* v_fvarId_2484_; lean_object* v_k_2485_; lean_object* v___f_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v_toBind_2483_ = lean_ctor_get(v_inst_2359_, 1);
lean_inc(v_toBind_2483_);
v_fvarId_2484_ = lean_ctor_get(v_c_2361_, 0);
lean_inc(v_fvarId_2484_);
v_k_2485_ = lean_ctor_get(v_c_2361_, 2);
lean_inc_ref(v_k_2485_);
lean_dec_ref(v_c_2361_);
lean_inc(v_f_2360_);
v___f_2486_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2486_, 0, v_inst_2359_);
lean_closure_set(v___f_2486_, 1, v_f_2360_);
lean_closure_set(v___f_2486_, 2, v_k_2485_);
v___x_2487_ = lean_apply_1(v_f_2360_, v_fvarId_2484_);
v___x_2488_ = lean_apply_4(v_toBind_2483_, lean_box(0), lean_box(0), v___x_2487_, v___f_2486_);
return v___x_2488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0(lean_object* v_inst_2489_, lean_object* v_f_2490_, lean_object* v_k_2491_, lean_object* v_____r_2492_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2489_, v_f_2490_, v_k_2491_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM(lean_object* v_m_2494_, uint8_t v_pu_2495_, lean_object* v_inst_2496_, lean_object* v_f_2497_, lean_object* v_c_2498_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2496_, v_f_2497_, v_c_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___boxed(lean_object* v_m_2500_, lean_object* v_pu_2501_, lean_object* v_inst_2502_, lean_object* v_f_2503_, lean_object* v_c_2504_){
_start:
{
uint8_t v_pu_boxed_2505_; lean_object* v_res_2506_; 
v_pu_boxed_2505_ = lean_unbox(v_pu_2501_);
v_res_2506_ = l_Lean_Compiler_LCNF_Code_forFVarM(v_m_2500_, v_pu_boxed_2505_, v_inst_2502_, v_f_2503_, v_c_2504_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(uint8_t v_pu_2507_, lean_object* v_m_2508_, lean_object* v_inst_2509_, lean_object* v_inst_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2507_, v_inst_2509_, v_inst_2510_, v___y_2511_, v___y_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed(lean_object* v_pu_2514_, lean_object* v_m_2515_, lean_object* v_inst_2516_, lean_object* v_inst_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
uint8_t v_pu_boxed_2520_; lean_object* v_res_2521_; 
v_pu_boxed_2520_ = lean_unbox(v_pu_2514_);
v_res_2521_ = l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(v_pu_boxed_2520_, v_m_2515_, v_inst_2516_, v_inst_2517_, v___y_2518_, v___y_2519_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__1(lean_object* v_m_2522_, lean_object* v_inst_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2523_, v___y_2524_, v___y_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode(uint8_t v_pu_2528_){
_start:
{
lean_object* v___x_2529_; lean_object* v___f_2530_; lean_object* v___f_2531_; lean_object* v___x_2532_; 
v___x_2529_ = lean_box(v_pu_2528_);
v___f_2530_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2530_, 0, v___x_2529_);
v___f_2531_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0));
v___x_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___f_2530_);
lean_ctor_set(v___x_2532_, 1, v___f_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___boxed(lean_object* v_pu_2533_){
_start:
{
uint8_t v_pu_boxed_2534_; lean_object* v_res_2535_; 
v_pu_boxed_2534_ = lean_unbox(v_pu_2533_);
v_res_2535_ = l_Lean_Compiler_LCNF_instTraverseFVarCode(v_pu_boxed_2534_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(uint8_t v_pu_2536_, lean_object* v_decl_2537_, lean_object* v_____do__lift_2538_, lean_object* v_params_2539_, lean_object* v_inst_2540_, lean_object* v_____do__lift_2541_){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = lean_box(v_pu_2536_);
v___x_2543_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed), 10, 5);
lean_closure_set(v___x_2543_, 0, v___x_2542_);
lean_closure_set(v___x_2543_, 1, v_decl_2537_);
lean_closure_set(v___x_2543_, 2, v_____do__lift_2538_);
lean_closure_set(v___x_2543_, 3, v_params_2539_);
lean_closure_set(v___x_2543_, 4, v_____do__lift_2541_);
v___x_2544_ = lean_apply_2(v_inst_2540_, lean_box(0), v___x_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_2545_, lean_object* v_decl_2546_, lean_object* v_____do__lift_2547_, lean_object* v_params_2548_, lean_object* v_inst_2549_, lean_object* v_____do__lift_2550_){
_start:
{
uint8_t v_pu_boxed_2551_; lean_object* v_res_2552_; 
v_pu_boxed_2551_ = lean_unbox(v_pu_2545_);
v_res_2552_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(v_pu_boxed_2551_, v_decl_2546_, v_____do__lift_2547_, v_params_2548_, v_inst_2549_, v_____do__lift_2550_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(uint8_t v_pu_2553_, lean_object* v_decl_2554_, lean_object* v_params_2555_, lean_object* v_inst_2556_, lean_object* v_inst_2557_, lean_object* v_f_2558_, lean_object* v_value_2559_, lean_object* v_toBind_2560_, lean_object* v_____do__lift_2561_){
_start:
{
lean_object* v___x_2562_; lean_object* v___f_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2562_ = lean_box(v_pu_2553_);
lean_inc(v_inst_2556_);
v___f_2563_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2563_, 0, v___x_2562_);
lean_closure_set(v___f_2563_, 1, v_decl_2554_);
lean_closure_set(v___f_2563_, 2, v_____do__lift_2561_);
lean_closure_set(v___f_2563_, 3, v_params_2555_);
lean_closure_set(v___f_2563_, 4, v_inst_2556_);
v___x_2564_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2553_, v_inst_2556_, v_inst_2557_, v_f_2558_, v_value_2559_);
v___x_2565_ = lean_apply_4(v_toBind_2560_, lean_box(0), lean_box(0), v___x_2564_, v___f_2563_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed(lean_object* v_pu_2566_, lean_object* v_decl_2567_, lean_object* v_params_2568_, lean_object* v_inst_2569_, lean_object* v_inst_2570_, lean_object* v_f_2571_, lean_object* v_value_2572_, lean_object* v_toBind_2573_, lean_object* v_____do__lift_2574_){
_start:
{
uint8_t v_pu_boxed_2575_; lean_object* v_res_2576_; 
v_pu_boxed_2575_ = lean_unbox(v_pu_2566_);
v_res_2576_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(v_pu_boxed_2575_, v_decl_2567_, v_params_2568_, v_inst_2569_, v_inst_2570_, v_f_2571_, v_value_2572_, v_toBind_2573_, v_____do__lift_2574_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(uint8_t v_pu_2577_, lean_object* v_decl_2578_, lean_object* v_inst_2579_, lean_object* v_inst_2580_, lean_object* v_f_2581_, lean_object* v_value_2582_, lean_object* v_toBind_2583_, lean_object* v_type_2584_, lean_object* v_params_2585_){
_start:
{
lean_object* v___x_2586_; lean_object* v___f_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2586_ = lean_box(v_pu_2577_);
lean_inc(v_toBind_2583_);
lean_inc(v_f_2581_);
lean_inc_ref(v_inst_2580_);
v___f_2587_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2587_, 0, v___x_2586_);
lean_closure_set(v___f_2587_, 1, v_decl_2578_);
lean_closure_set(v___f_2587_, 2, v_params_2585_);
lean_closure_set(v___f_2587_, 3, v_inst_2579_);
lean_closure_set(v___f_2587_, 4, v_inst_2580_);
lean_closure_set(v___f_2587_, 5, v_f_2581_);
lean_closure_set(v___f_2587_, 6, v_value_2582_);
lean_closure_set(v___f_2587_, 7, v_toBind_2583_);
v___x_2588_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2580_, v_f_2581_, v_type_2584_);
v___x_2589_ = lean_apply_4(v_toBind_2583_, lean_box(0), lean_box(0), v___x_2588_, v___f_2587_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed(lean_object* v_pu_2590_, lean_object* v_decl_2591_, lean_object* v_inst_2592_, lean_object* v_inst_2593_, lean_object* v_f_2594_, lean_object* v_value_2595_, lean_object* v_toBind_2596_, lean_object* v_type_2597_, lean_object* v_params_2598_){
_start:
{
uint8_t v_pu_boxed_2599_; lean_object* v_res_2600_; 
v_pu_boxed_2599_ = lean_unbox(v_pu_2590_);
v_res_2600_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(v_pu_boxed_2599_, v_decl_2591_, v_inst_2592_, v_inst_2593_, v_f_2594_, v_value_2595_, v_toBind_2596_, v_type_2597_, v_params_2598_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(uint8_t v_pu_2601_, lean_object* v_inst_2602_, lean_object* v_inst_2603_, lean_object* v_f_2604_, lean_object* v_decl_2605_){
_start:
{
lean_object* v_toBind_2606_; lean_object* v_params_2607_; lean_object* v_type_2608_; lean_object* v_value_2609_; lean_object* v___x_2610_; lean_object* v___f_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; size_t v_sz_2614_; size_t v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v_toBind_2606_ = lean_ctor_get(v_inst_2603_, 1);
lean_inc(v_toBind_2606_);
v_params_2607_ = lean_ctor_get(v_decl_2605_, 2);
lean_inc_ref(v_params_2607_);
v_type_2608_ = lean_ctor_get(v_decl_2605_, 3);
lean_inc_ref(v_type_2608_);
v_value_2609_ = lean_ctor_get(v_decl_2605_, 4);
lean_inc_ref(v_value_2609_);
v___x_2610_ = lean_box(v_pu_2601_);
lean_inc(v_toBind_2606_);
lean_inc(v_f_2604_);
lean_inc_ref(v_inst_2603_);
lean_inc(v_inst_2602_);
v___f_2611_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2611_, 0, v___x_2610_);
lean_closure_set(v___f_2611_, 1, v_decl_2605_);
lean_closure_set(v___f_2611_, 2, v_inst_2602_);
lean_closure_set(v___f_2611_, 3, v_inst_2603_);
lean_closure_set(v___f_2611_, 4, v_f_2604_);
lean_closure_set(v___f_2611_, 5, v_value_2609_);
lean_closure_set(v___f_2611_, 6, v_toBind_2606_);
lean_closure_set(v___f_2611_, 7, v_type_2608_);
v___x_2612_ = lean_box(v_pu_2601_);
lean_inc_ref(v_inst_2603_);
v___x_2613_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2613_, 0, lean_box(0));
lean_closure_set(v___x_2613_, 1, v___x_2612_);
lean_closure_set(v___x_2613_, 2, v_inst_2602_);
lean_closure_set(v___x_2613_, 3, v_inst_2603_);
lean_closure_set(v___x_2613_, 4, v_f_2604_);
v_sz_2614_ = lean_array_size(v_params_2607_);
v___x_2615_ = ((size_t)0ULL);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2603_, v___x_2613_, v_sz_2614_, v___x_2615_, v_params_2607_);
v___x_2617_ = lean_apply_4(v_toBind_2606_, lean_box(0), lean_box(0), v___x_2616_, v___f_2611_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___boxed(lean_object* v_pu_2618_, lean_object* v_inst_2619_, lean_object* v_inst_2620_, lean_object* v_f_2621_, lean_object* v_decl_2622_){
_start:
{
uint8_t v_pu_boxed_2623_; lean_object* v_res_2624_; 
v_pu_boxed_2623_ = lean_unbox(v_pu_2618_);
v_res_2624_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_boxed_2623_, v_inst_2619_, v_inst_2620_, v_f_2621_, v_decl_2622_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM(lean_object* v_m_2625_, uint8_t v_pu_2626_, lean_object* v_inst_2627_, lean_object* v_inst_2628_, lean_object* v_f_2629_, lean_object* v_decl_2630_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2626_, v_inst_2627_, v_inst_2628_, v_f_2629_, v_decl_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___boxed(lean_object* v_m_2632_, lean_object* v_pu_2633_, lean_object* v_inst_2634_, lean_object* v_inst_2635_, lean_object* v_f_2636_, lean_object* v_decl_2637_){
_start:
{
uint8_t v_pu_boxed_2638_; lean_object* v_res_2639_; 
v_pu_boxed_2638_ = lean_unbox(v_pu_2633_);
v_res_2639_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM(v_m_2632_, v_pu_boxed_2638_, v_inst_2634_, v_inst_2635_, v_f_2636_, v_decl_2637_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0(lean_object* v_inst_2640_, lean_object* v_f_2641_, lean_object* v_value_2642_, lean_object* v_____r_2643_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2640_, v_f_2641_, v_value_2642_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1(lean_object* v_inst_2645_, lean_object* v_f_2646_, lean_object* v_type_2647_, lean_object* v_toBind_2648_, lean_object* v___f_2649_, lean_object* v_____r_2650_){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2645_, v_f_2646_, v_type_2647_);
v___x_2652_ = lean_apply_4(v_toBind_2648_, lean_box(0), lean_box(0), v___x_2651_, v___f_2649_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2(lean_object* v_inst_2653_, lean_object* v_f_2654_, lean_object* v_x_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_2653_, v_f_2654_, v___y_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(lean_object* v_inst_2658_, lean_object* v_f_2659_, lean_object* v_decl_2660_){
_start:
{
lean_object* v_toApplicative_2661_; lean_object* v_toBind_2662_; lean_object* v_params_2663_; lean_object* v_type_2664_; lean_object* v_value_2665_; lean_object* v___f_2666_; lean_object* v___f_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; 
v_toApplicative_2661_ = lean_ctor_get(v_inst_2658_, 0);
v_toBind_2662_ = lean_ctor_get(v_inst_2658_, 1);
lean_inc(v_toBind_2662_);
v_params_2663_ = lean_ctor_get(v_decl_2660_, 2);
lean_inc_ref(v_params_2663_);
v_type_2664_ = lean_ctor_get(v_decl_2660_, 3);
lean_inc_ref(v_type_2664_);
v_value_2665_ = lean_ctor_get(v_decl_2660_, 4);
lean_inc_ref(v_value_2665_);
lean_dec_ref(v_decl_2660_);
lean_inc(v_f_2659_);
lean_inc_ref(v_inst_2658_);
v___f_2666_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2666_, 0, v_inst_2658_);
lean_closure_set(v___f_2666_, 1, v_f_2659_);
lean_closure_set(v___f_2666_, 2, v_value_2665_);
lean_inc(v_toBind_2662_);
lean_inc(v_f_2659_);
lean_inc_ref(v_inst_2658_);
v___f_2667_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2667_, 0, v_inst_2658_);
lean_closure_set(v___f_2667_, 1, v_f_2659_);
lean_closure_set(v___f_2667_, 2, v_type_2664_);
lean_closure_set(v___f_2667_, 3, v_toBind_2662_);
lean_closure_set(v___f_2667_, 4, v___f_2666_);
v___x_2668_ = lean_unsigned_to_nat(0u);
v___x_2669_ = lean_array_get_size(v_params_2663_);
v___x_2670_ = lean_box(0);
v___x_2671_ = lean_nat_dec_lt(v___x_2668_, v___x_2669_);
if (v___x_2671_ == 0)
{
lean_object* v_toPure_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_inc_ref(v_toApplicative_2661_);
lean_dec_ref(v_params_2663_);
lean_dec(v_f_2659_);
lean_dec_ref(v_inst_2658_);
v_toPure_2672_ = lean_ctor_get(v_toApplicative_2661_, 1);
lean_inc(v_toPure_2672_);
lean_dec_ref(v_toApplicative_2661_);
v___x_2673_ = lean_apply_2(v_toPure_2672_, lean_box(0), v___x_2670_);
v___x_2674_ = lean_apply_4(v_toBind_2662_, lean_box(0), lean_box(0), v___x_2673_, v___f_2667_);
return v___x_2674_;
}
else
{
lean_object* v___f_2675_; uint8_t v___x_2676_; 
lean_inc_ref(v_inst_2658_);
v___f_2675_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_2675_, 0, v_inst_2658_);
lean_closure_set(v___f_2675_, 1, v_f_2659_);
v___x_2676_ = lean_nat_dec_le(v___x_2669_, v___x_2669_);
if (v___x_2676_ == 0)
{
if (v___x_2671_ == 0)
{
lean_object* v_toPure_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_inc_ref(v_toApplicative_2661_);
lean_dec_ref(v___f_2675_);
lean_dec_ref(v_params_2663_);
lean_dec_ref(v_inst_2658_);
v_toPure_2677_ = lean_ctor_get(v_toApplicative_2661_, 1);
lean_inc(v_toPure_2677_);
lean_dec_ref(v_toApplicative_2661_);
v___x_2678_ = lean_apply_2(v_toPure_2677_, lean_box(0), v___x_2670_);
v___x_2679_ = lean_apply_4(v_toBind_2662_, lean_box(0), lean_box(0), v___x_2678_, v___f_2667_);
return v___x_2679_;
}
else
{
size_t v___x_2680_; size_t v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2680_ = ((size_t)0ULL);
v___x_2681_ = lean_usize_of_nat(v___x_2669_);
v___x_2682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2658_, v___f_2675_, v_params_2663_, v___x_2680_, v___x_2681_, v___x_2670_);
v___x_2683_ = lean_apply_4(v_toBind_2662_, lean_box(0), lean_box(0), v___x_2682_, v___f_2667_);
return v___x_2683_;
}
}
else
{
size_t v___x_2684_; size_t v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2684_ = ((size_t)0ULL);
v___x_2685_ = lean_usize_of_nat(v___x_2669_);
v___x_2686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2658_, v___f_2675_, v_params_2663_, v___x_2684_, v___x_2685_, v___x_2670_);
v___x_2687_ = lean_apply_4(v_toBind_2662_, lean_box(0), lean_box(0), v___x_2686_, v___f_2667_);
return v___x_2687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM(lean_object* v_m_2688_, uint8_t v_pu_2689_, lean_object* v_inst_2690_, lean_object* v_f_2691_, lean_object* v_decl_2692_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2690_, v_f_2691_, v_decl_2692_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___boxed(lean_object* v_m_2694_, lean_object* v_pu_2695_, lean_object* v_inst_2696_, lean_object* v_f_2697_, lean_object* v_decl_2698_){
_start:
{
uint8_t v_pu_boxed_2699_; lean_object* v_res_2700_; 
v_pu_boxed_2699_ = lean_unbox(v_pu_2695_);
v_res_2700_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM(v_m_2694_, v_pu_boxed_2699_, v_inst_2696_, v_f_2697_, v_decl_2698_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(uint8_t v_pu_2701_, lean_object* v_m_2702_, lean_object* v_inst_2703_, lean_object* v_inst_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2701_, v_inst_2703_, v_inst_2704_, v___y_2705_, v___y_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed(lean_object* v_pu_2708_, lean_object* v_m_2709_, lean_object* v_inst_2710_, lean_object* v_inst_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
uint8_t v_pu_boxed_2714_; lean_object* v_res_2715_; 
v_pu_boxed_2714_ = lean_unbox(v_pu_2708_);
v_res_2715_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(v_pu_boxed_2714_, v_m_2709_, v_inst_2710_, v_inst_2711_, v___y_2712_, v___y_2713_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__1(lean_object* v_m_2716_, lean_object* v_inst_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2717_, v___y_2718_, v___y_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(uint8_t v_pu_2722_){
_start:
{
lean_object* v___x_2723_; lean_object* v___f_2724_; lean_object* v___f_2725_; lean_object* v___x_2726_; 
v___x_2723_ = lean_box(v_pu_2722_);
v___f_2724_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2724_, 0, v___x_2723_);
v___f_2725_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0));
v___x_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___f_2724_);
lean_ctor_set(v___x_2726_, 1, v___f_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___boxed(lean_object* v_pu_2727_){
_start:
{
uint8_t v_pu_boxed_2728_; lean_object* v_res_2729_; 
v_pu_boxed_2728_ = lean_unbox(v_pu_2727_);
v_res_2729_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(v_pu_boxed_2728_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0(lean_object* v_toPure_2730_, lean_object* v_____do__lift_2731_){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v_____do__lift_2731_);
v___x_2733_ = lean_apply_2(v_toPure_2730_, lean_box(0), v___x_2732_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1(lean_object* v_toPure_2734_, lean_object* v_____do__lift_2735_){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2736_, 0, v_____do__lift_2735_);
v___x_2737_ = lean_apply_2(v_toPure_2734_, lean_box(0), v___x_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2(lean_object* v_toPure_2738_, lean_object* v_____do__lift_2739_){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2740_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2740_, 0, v_____do__lift_2739_);
v___x_2741_ = lean_apply_2(v_toPure_2738_, lean_box(0), v___x_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3(lean_object* v_____do__lift_2742_, lean_object* v_i_2743_, lean_object* v_toPure_2744_, lean_object* v_____do__lift_2745_){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2746_, 0, v_____do__lift_2742_);
lean_ctor_set(v___x_2746_, 1, v_i_2743_);
lean_ctor_set(v___x_2746_, 2, v_____do__lift_2745_);
v___x_2747_ = lean_apply_2(v_toPure_2744_, lean_box(0), v___x_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(lean_object* v_i_2748_, lean_object* v_toPure_2749_, uint8_t v_pu_2750_, lean_object* v_inst_2751_, lean_object* v_f_2752_, lean_object* v_y_2753_, lean_object* v_toBind_2754_, lean_object* v_____do__lift_2755_){
_start:
{
lean_object* v___f_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___f_2756_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3), 4, 3);
lean_closure_set(v___f_2756_, 0, v_____do__lift_2755_);
lean_closure_set(v___f_2756_, 1, v_i_2748_);
lean_closure_set(v___f_2756_, 2, v_toPure_2749_);
v___x_2757_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_2750_, v_inst_2751_, v_f_2752_, v_y_2753_);
v___x_2758_ = lean_apply_4(v_toBind_2754_, lean_box(0), lean_box(0), v___x_2757_, v___f_2756_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed(lean_object* v_i_2759_, lean_object* v_toPure_2760_, lean_object* v_pu_2761_, lean_object* v_inst_2762_, lean_object* v_f_2763_, lean_object* v_y_2764_, lean_object* v_toBind_2765_, lean_object* v_____do__lift_2766_){
_start:
{
uint8_t v_pu_boxed_2767_; lean_object* v_res_2768_; 
v_pu_boxed_2767_ = lean_unbox(v_pu_2761_);
v_res_2768_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(v_i_2759_, v_toPure_2760_, v_pu_boxed_2767_, v_inst_2762_, v_f_2763_, v_y_2764_, v_toBind_2765_, v_____do__lift_2766_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5(lean_object* v_____do__lift_2769_, lean_object* v_i_2770_, lean_object* v_toPure_2771_, lean_object* v_____do__lift_2772_){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2773_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_2773_, 0, v_____do__lift_2769_);
lean_ctor_set(v___x_2773_, 1, v_i_2770_);
lean_ctor_set(v___x_2773_, 2, v_____do__lift_2772_);
v___x_2774_ = lean_apply_2(v_toPure_2771_, lean_box(0), v___x_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6(lean_object* v_i_2775_, lean_object* v_toPure_2776_, lean_object* v_f_2777_, lean_object* v_y_2778_, lean_object* v_toBind_2779_, lean_object* v_____do__lift_2780_){
_start:
{
lean_object* v___f_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___f_2781_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5), 4, 3);
lean_closure_set(v___f_2781_, 0, v_____do__lift_2780_);
lean_closure_set(v___f_2781_, 1, v_i_2775_);
lean_closure_set(v___f_2781_, 2, v_toPure_2776_);
v___x_2782_ = lean_apply_1(v_f_2777_, v_y_2778_);
v___x_2783_ = lean_apply_4(v_toBind_2779_, lean_box(0), lean_box(0), v___x_2782_, v___f_2781_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7(lean_object* v_____do__lift_2784_, lean_object* v_i_2785_, lean_object* v_offset_2786_, lean_object* v_____do__lift_2787_, lean_object* v_toPure_2788_, lean_object* v_____do__lift_2789_){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v___x_2790_, 0, v_____do__lift_2784_);
lean_ctor_set(v___x_2790_, 1, v_i_2785_);
lean_ctor_set(v___x_2790_, 2, v_offset_2786_);
lean_ctor_set(v___x_2790_, 3, v_____do__lift_2787_);
lean_ctor_set(v___x_2790_, 4, v_____do__lift_2789_);
v___x_2791_ = lean_apply_2(v_toPure_2788_, lean_box(0), v___x_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8(lean_object* v_____do__lift_2792_, lean_object* v_i_2793_, lean_object* v_offset_2794_, lean_object* v_toPure_2795_, lean_object* v_inst_2796_, lean_object* v_f_2797_, lean_object* v_ty_2798_, lean_object* v_toBind_2799_, lean_object* v_____do__lift_2800_){
_start:
{
lean_object* v___f_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___f_2801_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7), 6, 5);
lean_closure_set(v___f_2801_, 0, v_____do__lift_2792_);
lean_closure_set(v___f_2801_, 1, v_i_2793_);
lean_closure_set(v___f_2801_, 2, v_offset_2794_);
lean_closure_set(v___f_2801_, 3, v_____do__lift_2800_);
lean_closure_set(v___f_2801_, 4, v_toPure_2795_);
v___x_2802_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2796_, v_f_2797_, v_ty_2798_);
v___x_2803_ = lean_apply_4(v_toBind_2799_, lean_box(0), lean_box(0), v___x_2802_, v___f_2801_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9(lean_object* v_i_2804_, lean_object* v_offset_2805_, lean_object* v_toPure_2806_, lean_object* v_inst_2807_, lean_object* v_f_2808_, lean_object* v_ty_2809_, lean_object* v_toBind_2810_, lean_object* v_y_2811_, lean_object* v_____do__lift_2812_){
_start:
{
lean_object* v___f_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
lean_inc(v_toBind_2810_);
lean_inc(v_f_2808_);
v___f_2813_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8), 9, 8);
lean_closure_set(v___f_2813_, 0, v_____do__lift_2812_);
lean_closure_set(v___f_2813_, 1, v_i_2804_);
lean_closure_set(v___f_2813_, 2, v_offset_2805_);
lean_closure_set(v___f_2813_, 3, v_toPure_2806_);
lean_closure_set(v___f_2813_, 4, v_inst_2807_);
lean_closure_set(v___f_2813_, 5, v_f_2808_);
lean_closure_set(v___f_2813_, 6, v_ty_2809_);
lean_closure_set(v___f_2813_, 7, v_toBind_2810_);
v___x_2814_ = lean_apply_1(v_f_2808_, v_y_2811_);
v___x_2815_ = lean_apply_4(v_toBind_2810_, lean_box(0), lean_box(0), v___x_2814_, v___f_2813_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10(lean_object* v_cidx_2816_, lean_object* v_toPure_2817_, lean_object* v_____do__lift_2818_){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2819_, 0, v_____do__lift_2818_);
lean_ctor_set(v___x_2819_, 1, v_cidx_2816_);
v___x_2820_ = lean_apply_2(v_toPure_2817_, lean_box(0), v___x_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(lean_object* v_n_2821_, uint8_t v_check_2822_, uint8_t v_persistent_2823_, lean_object* v_toPure_2824_, lean_object* v_____do__lift_2825_){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v___x_2826_, 0, v_____do__lift_2825_);
lean_ctor_set(v___x_2826_, 1, v_n_2821_);
lean_ctor_set_uint8(v___x_2826_, sizeof(void*)*2, v_check_2822_);
lean_ctor_set_uint8(v___x_2826_, sizeof(void*)*2 + 1, v_persistent_2823_);
v___x_2827_ = lean_apply_2(v_toPure_2824_, lean_box(0), v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed(lean_object* v_n_2828_, lean_object* v_check_2829_, lean_object* v_persistent_2830_, lean_object* v_toPure_2831_, lean_object* v_____do__lift_2832_){
_start:
{
uint8_t v_check_917__boxed_2833_; uint8_t v_persistent_918__boxed_2834_; lean_object* v_res_2835_; 
v_check_917__boxed_2833_ = lean_unbox(v_check_2829_);
v_persistent_918__boxed_2834_ = lean_unbox(v_persistent_2830_);
v_res_2835_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(v_n_2828_, v_check_917__boxed_2833_, v_persistent_918__boxed_2834_, v_toPure_2831_, v_____do__lift_2832_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(lean_object* v_n_2836_, uint8_t v_check_2837_, uint8_t v_persistent_2838_, lean_object* v_toPure_2839_, lean_object* v_____do__lift_2840_){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = lean_alloc_ctor(8, 2, 2);
lean_ctor_set(v___x_2841_, 0, v_____do__lift_2840_);
lean_ctor_set(v___x_2841_, 1, v_n_2836_);
lean_ctor_set_uint8(v___x_2841_, sizeof(void*)*2, v_check_2837_);
lean_ctor_set_uint8(v___x_2841_, sizeof(void*)*2 + 1, v_persistent_2838_);
v___x_2842_ = lean_apply_2(v_toPure_2839_, lean_box(0), v___x_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed(lean_object* v_n_2843_, lean_object* v_check_2844_, lean_object* v_persistent_2845_, lean_object* v_toPure_2846_, lean_object* v_____do__lift_2847_){
_start:
{
uint8_t v_check_933__boxed_2848_; uint8_t v_persistent_934__boxed_2849_; lean_object* v_res_2850_; 
v_check_933__boxed_2848_ = lean_unbox(v_check_2844_);
v_persistent_934__boxed_2849_ = lean_unbox(v_persistent_2845_);
v_res_2850_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(v_n_2843_, v_check_933__boxed_2848_, v_persistent_934__boxed_2849_, v_toPure_2846_, v_____do__lift_2847_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13(lean_object* v_toPure_2851_, lean_object* v_____do__lift_2852_){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2853_, 0, v_____do__lift_2852_);
v___x_2854_ = lean_apply_2(v_toPure_2851_, lean_box(0), v___x_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(uint8_t v_pu_2855_, lean_object* v_m_2856_, lean_object* v_inst_2857_, lean_object* v_inst_2858_, lean_object* v_f_2859_, lean_object* v_decl_2860_){
_start:
{
switch(lean_obj_tag(v_decl_2860_))
{
case 0:
{
lean_object* v_toApplicative_2861_; lean_object* v_toBind_2862_; lean_object* v_toPure_2863_; lean_object* v_decl_2864_; lean_object* v___f_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v_toApplicative_2861_ = lean_ctor_get(v_inst_2858_, 0);
v_toBind_2862_ = lean_ctor_get(v_inst_2858_, 1);
lean_inc(v_toBind_2862_);
v_toPure_2863_ = lean_ctor_get(v_toApplicative_2861_, 1);
v_decl_2864_ = lean_ctor_get(v_decl_2860_, 0);
lean_inc_ref(v_decl_2864_);
lean_dec_ref(v_decl_2860_);
lean_inc(v_toPure_2863_);
v___f_2865_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0), 2, 1);
lean_closure_set(v___f_2865_, 0, v_toPure_2863_);
v___x_2866_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_2855_, v_inst_2857_, v_inst_2858_, v_f_2859_, v_decl_2864_);
v___x_2867_ = lean_apply_4(v_toBind_2862_, lean_box(0), lean_box(0), v___x_2866_, v___f_2865_);
return v___x_2867_;
}
case 1:
{
lean_object* v_toApplicative_2868_; lean_object* v_toBind_2869_; lean_object* v_toPure_2870_; lean_object* v_decl_2871_; lean_object* v___f_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v_toApplicative_2868_ = lean_ctor_get(v_inst_2858_, 0);
v_toBind_2869_ = lean_ctor_get(v_inst_2858_, 1);
lean_inc(v_toBind_2869_);
v_toPure_2870_ = lean_ctor_get(v_toApplicative_2868_, 1);
v_decl_2871_ = lean_ctor_get(v_decl_2860_, 0);
lean_inc_ref(v_decl_2871_);
lean_dec_ref(v_decl_2860_);
lean_inc(v_toPure_2870_);
v___f_2872_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1), 2, 1);
lean_closure_set(v___f_2872_, 0, v_toPure_2870_);
v___x_2873_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2855_, v_inst_2857_, v_inst_2858_, v_f_2859_, v_decl_2871_);
v___x_2874_ = lean_apply_4(v_toBind_2869_, lean_box(0), lean_box(0), v___x_2873_, v___f_2872_);
return v___x_2874_;
}
case 2:
{
lean_object* v_toApplicative_2875_; lean_object* v_toBind_2876_; lean_object* v_toPure_2877_; lean_object* v_decl_2878_; lean_object* v___f_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v_toApplicative_2875_ = lean_ctor_get(v_inst_2858_, 0);
v_toBind_2876_ = lean_ctor_get(v_inst_2858_, 1);
lean_inc(v_toBind_2876_);
v_toPure_2877_ = lean_ctor_get(v_toApplicative_2875_, 1);
v_decl_2878_ = lean_ctor_get(v_decl_2860_, 0);
lean_inc_ref(v_decl_2878_);
lean_dec_ref(v_decl_2860_);
lean_inc(v_toPure_2877_);
v___f_2879_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2), 2, 1);
lean_closure_set(v___f_2879_, 0, v_toPure_2877_);
v___x_2880_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2855_, v_inst_2857_, v_inst_2858_, v_f_2859_, v_decl_2878_);
v___x_2881_ = lean_apply_4(v_toBind_2876_, lean_box(0), lean_box(0), v___x_2880_, v___f_2879_);
return v___x_2881_;
}
case 3:
{
lean_object* v_toApplicative_2882_; lean_object* v_toBind_2883_; lean_object* v_toPure_2884_; lean_object* v_fvarId_2885_; lean_object* v_i_2886_; lean_object* v_y_2887_; lean_object* v___x_2888_; lean_object* v___f_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_toApplicative_2882_ = lean_ctor_get(v_inst_2858_, 0);
lean_dec(v_inst_2857_);
v_toBind_2883_ = lean_ctor_get(v_inst_2858_, 1);
lean_inc(v_toBind_2883_);
v_toPure_2884_ = lean_ctor_get(v_toApplicative_2882_, 1);
lean_inc(v_toPure_2884_);
v_fvarId_2885_ = lean_ctor_get(v_decl_2860_, 0);
lean_inc(v_fvarId_2885_);
v_i_2886_ = lean_ctor_get(v_decl_2860_, 1);
lean_inc(v_i_2886_);
v_y_2887_ = lean_ctor_get(v_decl_2860_, 2);
lean_inc(v_y_2887_);
lean_dec_ref(v_decl_2860_);
v___x_2888_ = lean_box(v_pu_2855_);
lean_inc(v_toBind_2883_);
lean_inc(v_f_2859_);
v___f_2889_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed), 8, 7);
lean_closure_set(v___f_2889_, 0, v_i_2886_);
lean_closure_set(v___f_2889_, 1, v_toPure_2884_);
lean_closure_set(v___f_2889_, 2, v___x_2888_);
lean_closure_set(v___f_2889_, 3, v_inst_2858_);
lean_closure_set(v___f_2889_, 4, v_f_2859_);
lean_closure_set(v___f_2889_, 5, v_y_2887_);
lean_closure_set(v___f_2889_, 6, v_toBind_2883_);
v___x_2890_ = lean_apply_1(v_f_2859_, v_fvarId_2885_);
v___x_2891_ = lean_apply_4(v_toBind_2883_, lean_box(0), lean_box(0), v___x_2890_, v___f_2889_);
return v___x_2891_;
}
case 4:
{
lean_object* v_toApplicative_2892_; lean_object* v_toBind_2893_; lean_object* v_toPure_2894_; lean_object* v_fvarId_2895_; lean_object* v_i_2896_; lean_object* v_y_2897_; lean_object* v___f_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v_toApplicative_2892_ = lean_ctor_get(v_inst_2858_, 0);
lean_inc_ref(v_toApplicative_2892_);
lean_dec(v_inst_2857_);
v_toBind_2893_ = lean_ctor_get(v_inst_2858_, 1);
lean_inc(v_toBind_2893_);
lean_dec_ref(v_inst_2858_);
v_toPure_2894_ = lean_ctor_get(v_toApplicative_2892_, 1);
lean_inc(v_toPure_2894_);
lean_dec_ref(v_toApplicative_2892_);
v_fvarId_2895_ = lean_ctor_get(v_decl_2860_, 0);
lean_inc(v_fvarId_2895_);
v_i_2896_ = lean_ctor_get(v_decl_2860_, 1);
lean_inc(v_i_2896_);
v_y_2897_ = lean_ctor_get(v_decl_2860_, 2);
lean_inc(v_y_2897_);
lean_dec_ref(v_decl_2860_);
lean_inc(v_toBind_2893_);
lean_inc(v_f_2859_);
v___f_2898_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6), 6, 5);
lean_closure_set(v___f_2898_, 0, v_i_2896_);
lean_closure_set(v___f_2898_, 1, v_toPure_2894_);
lean_closure_set(v___f_2898_, 2, v_f_2859_);
lean_closure_set(v___f_2898_, 3, v_y_2897_);
lean_closure_set(v___f_2898_, 4, v_toBind_2893_);
v___x_2899_ = lean_apply_1(v_f_2859_, v_fvarId_2895_);
v___x_2900_ = lean_apply_4(v_toBind_2893_, lean_box(0), lean_box(0), v___x_2899_, v___f_2898_);
return v___x_2900_;
}
case 5:
{
lean_object* v_toApplicative_2901_; lean_object* v_toBind_2902_; lean_object* v_toPure_2903_; lean_object* v_fvarId_2904_; lean_object* v_i_2905_; lean_object* v_offset_2906_; lean_object* v_y_2907_; lean_object* v_ty_2908_; lean_object* v___f_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v_toApplicative_2901_ = lean_ctor_get(v_inst_2858_, 0);
lean_dec(v_inst_2857_);
v_toBind_2902_ = lean_ctor_get(v_inst_2858_, 1);
lean_inc(v_toBind_2902_);
v_toPure_2903_ = lean_ctor_get(v_toApplicative_2901_, 1);
lean_inc(v_toPure_2903_);
v_fvarId_2904_ = lean_ctor_get(v_decl_2860_, 0);
lean_inc(v_fvarId_2904_);
v_i_2905_ = lean_ctor_get(v_decl_2860_, 1);
lean_inc(v_i_2905_);
v_offset_2906_ = lean_ctor_get(v_decl_2860_, 2);
lean_inc(v_offset_2906_);
v_y_2907_ = lean_ctor_get(v_decl_2860_, 3);
lean_inc(v_y_2907_);
v_ty_2908_ = lean_ctor_get(v_decl_2860_, 4);
lean_inc_ref(v_ty_2908_);
lean_dec_ref(v_decl_2860_);
lean_inc(v_toBind_2902_);
lean_inc(v_f_2859_);
v___f_2909_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9), 9, 8);
lean_closure_set(v___f_2909_, 0, v_i_2905_);
lean_closure_set(v___f_2909_, 1, v_offset_2906_);
lean_closure_set(v___f_2909_, 2, v_toPure_2903_);
lean_closure_set(v___f_2909_, 3, v_inst_2858_);
lean_closure_set(v___f_2909_, 4, v_f_2859_);
lean_closure_set(v___f_2909_, 5, v_ty_2908_);
lean_closure_set(v___f_2909_, 6, v_toBind_2902_);
lean_closure_set(v___f_2909_, 7, v_y_2907_);
v___x_2910_ = lean_apply_1(v_f_2859_, v_fvarId_2904_);
v___x_2911_ = lean_apply_4(v_toBind_2902_, lean_box(0), lean_box(0), v___x_2910_, v___f_2909_);
return v___x_2911_;
}
case 6:
{
lean_object* v_toApplicative_2912_; lean_object* v_toBind_2913_; lean_object* v_toPure_2914_; lean_object* v_fvarId_2915_; lean_object* v_cidx_2916_; lean_object* v___f_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_toApplicative_2912_ = lean_ctor_get(v_inst_2858_, 0);
lean_inc_ref(v_toApplicative_2912_);
lean_dec(v_inst_2857_);
v_toBind_2913_ = lean_ctor_get(v_inst_2858_, 1);
lean_inc(v_toBind_2913_);
lean_dec_ref(v_inst_2858_);
v_toPure_2914_ = lean_ctor_get(v_toApplicative_2912_, 1);
lean_inc(v_toPure_2914_);
lean_dec_ref(v_toApplicative_2912_);
v_fvarId_2915_ = lean_ctor_get(v_decl_2860_, 0);
lean_inc(v_fvarId_2915_);
v_cidx_2916_ = lean_ctor_get(v_decl_2860_, 1);
lean_inc(v_cidx_2916_);
lean_dec_ref(v_decl_2860_);
v___f_2917_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10), 3, 2);
lean_closure_set(v___f_2917_, 0, v_cidx_2916_);
lean_closure_set(v___f_2917_, 1, v_toPure_2914_);
v___x_2918_ = lean_apply_1(v_f_2859_, v_fvarId_2915_);
v___x_2919_ = lean_apply_4(v_toBind_2913_, lean_box(0), lean_box(0), v___x_2918_, v___f_2917_);
return v___x_2919_;
}
case 7:
{
lean_object* v_toApplicative_2920_; lean_object* v_toBind_2921_; lean_object* v_toPure_2922_; lean_object* v_fvarId_2923_; lean_object* v_n_2924_; uint8_t v_check_2925_; uint8_t v_persistent_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___f_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v_toApplicative_2920_ = lean_ctor_get(v_inst_2858_, 0);
lean_inc_ref(v_toApplicative_2920_);
lean_dec(v_inst_2857_);
v_toBind_2921_ = lean_ctor_get(v_inst_2858_, 1);
lean_inc(v_toBind_2921_);
lean_dec_ref(v_inst_2858_);
v_toPure_2922_ = lean_ctor_get(v_toApplicative_2920_, 1);
lean_inc(v_toPure_2922_);
lean_dec_ref(v_toApplicative_2920_);
v_fvarId_2923_ = lean_ctor_get(v_decl_2860_, 0);
lean_inc(v_fvarId_2923_);
v_n_2924_ = lean_ctor_get(v_decl_2860_, 1);
lean_inc(v_n_2924_);
v_check_2925_ = lean_ctor_get_uint8(v_decl_2860_, sizeof(void*)*2);
v_persistent_2926_ = lean_ctor_get_uint8(v_decl_2860_, sizeof(void*)*2 + 1);
lean_dec_ref(v_decl_2860_);
v___x_2927_ = lean_box(v_check_2925_);
v___x_2928_ = lean_box(v_persistent_2926_);
v___f_2929_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed), 5, 4);
lean_closure_set(v___f_2929_, 0, v_n_2924_);
lean_closure_set(v___f_2929_, 1, v___x_2927_);
lean_closure_set(v___f_2929_, 2, v___x_2928_);
lean_closure_set(v___f_2929_, 3, v_toPure_2922_);
v___x_2930_ = lean_apply_1(v_f_2859_, v_fvarId_2923_);
v___x_2931_ = lean_apply_4(v_toBind_2921_, lean_box(0), lean_box(0), v___x_2930_, v___f_2929_);
return v___x_2931_;
}
case 8:
{
lean_object* v_toApplicative_2932_; lean_object* v_toBind_2933_; lean_object* v_toPure_2934_; lean_object* v_fvarId_2935_; lean_object* v_n_2936_; uint8_t v_check_2937_; uint8_t v_persistent_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___f_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_toApplicative_2932_ = lean_ctor_get(v_inst_2858_, 0);
lean_inc_ref(v_toApplicative_2932_);
lean_dec(v_inst_2857_);
v_toBind_2933_ = lean_ctor_get(v_inst_2858_, 1);
lean_inc(v_toBind_2933_);
lean_dec_ref(v_inst_2858_);
v_toPure_2934_ = lean_ctor_get(v_toApplicative_2932_, 1);
lean_inc(v_toPure_2934_);
lean_dec_ref(v_toApplicative_2932_);
v_fvarId_2935_ = lean_ctor_get(v_decl_2860_, 0);
lean_inc(v_fvarId_2935_);
v_n_2936_ = lean_ctor_get(v_decl_2860_, 1);
lean_inc(v_n_2936_);
v_check_2937_ = lean_ctor_get_uint8(v_decl_2860_, sizeof(void*)*2);
v_persistent_2938_ = lean_ctor_get_uint8(v_decl_2860_, sizeof(void*)*2 + 1);
lean_dec_ref(v_decl_2860_);
v___x_2939_ = lean_box(v_check_2937_);
v___x_2940_ = lean_box(v_persistent_2938_);
v___f_2941_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed), 5, 4);
lean_closure_set(v___f_2941_, 0, v_n_2936_);
lean_closure_set(v___f_2941_, 1, v___x_2939_);
lean_closure_set(v___f_2941_, 2, v___x_2940_);
lean_closure_set(v___f_2941_, 3, v_toPure_2934_);
v___x_2942_ = lean_apply_1(v_f_2859_, v_fvarId_2935_);
v___x_2943_ = lean_apply_4(v_toBind_2933_, lean_box(0), lean_box(0), v___x_2942_, v___f_2941_);
return v___x_2943_;
}
default: 
{
lean_object* v_toApplicative_2944_; lean_object* v_toBind_2945_; lean_object* v_toPure_2946_; lean_object* v_fvarId_2947_; lean_object* v___f_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v_toApplicative_2944_ = lean_ctor_get(v_inst_2858_, 0);
lean_inc_ref(v_toApplicative_2944_);
lean_dec(v_inst_2857_);
v_toBind_2945_ = lean_ctor_get(v_inst_2858_, 1);
lean_inc(v_toBind_2945_);
lean_dec_ref(v_inst_2858_);
v_toPure_2946_ = lean_ctor_get(v_toApplicative_2944_, 1);
lean_inc(v_toPure_2946_);
lean_dec_ref(v_toApplicative_2944_);
v_fvarId_2947_ = lean_ctor_get(v_decl_2860_, 0);
lean_inc(v_fvarId_2947_);
lean_dec_ref(v_decl_2860_);
v___f_2948_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13), 2, 1);
lean_closure_set(v___f_2948_, 0, v_toPure_2946_);
v___x_2949_ = lean_apply_1(v_f_2859_, v_fvarId_2947_);
v___x_2950_ = lean_apply_4(v_toBind_2945_, lean_box(0), lean_box(0), v___x_2949_, v___f_2948_);
return v___x_2950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed(lean_object* v_pu_2951_, lean_object* v_m_2952_, lean_object* v_inst_2953_, lean_object* v_inst_2954_, lean_object* v_f_2955_, lean_object* v_decl_2956_){
_start:
{
uint8_t v_pu_boxed_2957_; lean_object* v_res_2958_; 
v_pu_boxed_2957_ = lean_unbox(v_pu_2951_);
v_res_2958_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(v_pu_boxed_2957_, v_m_2952_, v_inst_2953_, v_inst_2954_, v_f_2955_, v_decl_2956_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15(lean_object* v_inst_2959_, lean_object* v_f_2960_, lean_object* v_y_2961_, lean_object* v_____r_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2959_, v_f_2960_, v_y_2961_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16(lean_object* v_f_2964_, lean_object* v_y_2965_, lean_object* v_____r_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_apply_1(v_f_2964_, v_y_2965_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17(lean_object* v_inst_2968_, lean_object* v_f_2969_, lean_object* v_ty_2970_, lean_object* v_____r_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2968_, v_f_2969_, v_ty_2970_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18(lean_object* v_f_2973_, lean_object* v_y_2974_, lean_object* v_toBind_2975_, lean_object* v___f_2976_, lean_object* v_____r_2977_){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = lean_apply_1(v_f_2973_, v_y_2974_);
v___x_2979_ = lean_apply_4(v_toBind_2975_, lean_box(0), lean_box(0), v___x_2978_, v___f_2976_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__19(lean_object* v_m_2980_, lean_object* v_inst_2981_, lean_object* v_f_2982_, lean_object* v_decl_2983_){
_start:
{
switch(lean_obj_tag(v_decl_2983_))
{
case 0:
{
lean_object* v_decl_2984_; lean_object* v___x_2985_; 
v_decl_2984_ = lean_ctor_get(v_decl_2983_, 0);
lean_inc_ref(v_decl_2984_);
lean_dec_ref(v_decl_2983_);
v___x_2985_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_2981_, v_f_2982_, v_decl_2984_);
return v___x_2985_;
}
case 1:
{
lean_object* v_decl_2986_; lean_object* v___x_2987_; 
v_decl_2986_ = lean_ctor_get(v_decl_2983_, 0);
lean_inc_ref(v_decl_2986_);
lean_dec_ref(v_decl_2983_);
v___x_2987_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2981_, v_f_2982_, v_decl_2986_);
return v___x_2987_;
}
case 2:
{
lean_object* v_decl_2988_; lean_object* v___x_2989_; 
v_decl_2988_ = lean_ctor_get(v_decl_2983_, 0);
lean_inc_ref(v_decl_2988_);
lean_dec_ref(v_decl_2983_);
v___x_2989_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2981_, v_f_2982_, v_decl_2988_);
return v___x_2989_;
}
case 3:
{
lean_object* v_toBind_2990_; lean_object* v_fvarId_2991_; lean_object* v_y_2992_; lean_object* v___f_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v_toBind_2990_ = lean_ctor_get(v_inst_2981_, 1);
lean_inc(v_toBind_2990_);
v_fvarId_2991_ = lean_ctor_get(v_decl_2983_, 0);
lean_inc(v_fvarId_2991_);
v_y_2992_ = lean_ctor_get(v_decl_2983_, 2);
lean_inc(v_y_2992_);
lean_dec_ref(v_decl_2983_);
lean_inc(v_f_2982_);
v___f_2993_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15), 4, 3);
lean_closure_set(v___f_2993_, 0, v_inst_2981_);
lean_closure_set(v___f_2993_, 1, v_f_2982_);
lean_closure_set(v___f_2993_, 2, v_y_2992_);
v___x_2994_ = lean_apply_1(v_f_2982_, v_fvarId_2991_);
v___x_2995_ = lean_apply_4(v_toBind_2990_, lean_box(0), lean_box(0), v___x_2994_, v___f_2993_);
return v___x_2995_;
}
case 4:
{
lean_object* v_toBind_2996_; lean_object* v_fvarId_2997_; lean_object* v_y_2998_; lean_object* v___f_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v_toBind_2996_ = lean_ctor_get(v_inst_2981_, 1);
lean_inc(v_toBind_2996_);
lean_dec_ref(v_inst_2981_);
v_fvarId_2997_ = lean_ctor_get(v_decl_2983_, 0);
lean_inc(v_fvarId_2997_);
v_y_2998_ = lean_ctor_get(v_decl_2983_, 2);
lean_inc(v_y_2998_);
lean_dec_ref(v_decl_2983_);
lean_inc(v_f_2982_);
v___f_2999_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16), 3, 2);
lean_closure_set(v___f_2999_, 0, v_f_2982_);
lean_closure_set(v___f_2999_, 1, v_y_2998_);
v___x_3000_ = lean_apply_1(v_f_2982_, v_fvarId_2997_);
v___x_3001_ = lean_apply_4(v_toBind_2996_, lean_box(0), lean_box(0), v___x_3000_, v___f_2999_);
return v___x_3001_;
}
case 5:
{
lean_object* v_toBind_3002_; lean_object* v_fvarId_3003_; lean_object* v_y_3004_; lean_object* v_ty_3005_; lean_object* v___f_3006_; lean_object* v___f_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_toBind_3002_ = lean_ctor_get(v_inst_2981_, 1);
lean_inc(v_toBind_3002_);
v_fvarId_3003_ = lean_ctor_get(v_decl_2983_, 0);
lean_inc(v_fvarId_3003_);
v_y_3004_ = lean_ctor_get(v_decl_2983_, 3);
lean_inc(v_y_3004_);
v_ty_3005_ = lean_ctor_get(v_decl_2983_, 4);
lean_inc_ref(v_ty_3005_);
lean_dec_ref(v_decl_2983_);
lean_inc(v_f_2982_);
v___f_3006_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17), 4, 3);
lean_closure_set(v___f_3006_, 0, v_inst_2981_);
lean_closure_set(v___f_3006_, 1, v_f_2982_);
lean_closure_set(v___f_3006_, 2, v_ty_3005_);
lean_inc(v_toBind_3002_);
lean_inc(v_f_2982_);
v___f_3007_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18), 5, 4);
lean_closure_set(v___f_3007_, 0, v_f_2982_);
lean_closure_set(v___f_3007_, 1, v_y_3004_);
lean_closure_set(v___f_3007_, 2, v_toBind_3002_);
lean_closure_set(v___f_3007_, 3, v___f_3006_);
v___x_3008_ = lean_apply_1(v_f_2982_, v_fvarId_3003_);
v___x_3009_ = lean_apply_4(v_toBind_3002_, lean_box(0), lean_box(0), v___x_3008_, v___f_3007_);
return v___x_3009_;
}
default: 
{
lean_object* v_fvarId_3010_; lean_object* v___x_3011_; 
lean_dec_ref(v_inst_2981_);
v_fvarId_3010_ = lean_ctor_get(v_decl_2983_, 0);
lean_inc(v_fvarId_3010_);
lean_dec_ref(v_decl_2983_);
v___x_3011_ = lean_apply_1(v_f_2982_, v_fvarId_3010_);
return v___x_3011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(uint8_t v_pu_3013_){
_start:
{
lean_object* v___x_3014_; lean_object* v___f_3015_; lean_object* v___f_3016_; lean_object* v___x_3017_; 
v___x_3014_ = lean_box(v_pu_3013_);
v___f_3015_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed), 6, 1);
lean_closure_set(v___f_3015_, 0, v___x_3014_);
v___f_3016_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0));
v___x_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___f_3015_);
lean_ctor_set(v___x_3017_, 1, v___f_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___boxed(lean_object* v_pu_3018_){
_start:
{
uint8_t v_pu_boxed_3019_; lean_object* v_res_3020_; 
v_pu_boxed_3019_ = lean_unbox(v_pu_3018_);
v_res_3020_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(v_pu_boxed_3019_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0(lean_object* v_ctorName_3021_, lean_object* v_params_3022_, lean_object* v_toPure_3023_, lean_object* v_____do__lift_3024_){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3025_, 0, v_ctorName_3021_);
lean_ctor_set(v___x_3025_, 1, v_params_3022_);
lean_ctor_set(v___x_3025_, 2, v_____do__lift_3024_);
v___x_3026_ = lean_apply_2(v_toPure_3023_, lean_box(0), v___x_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(lean_object* v_ctorName_3027_, lean_object* v_toPure_3028_, uint8_t v_pu_3029_, lean_object* v_inst_3030_, lean_object* v_inst_3031_, lean_object* v_f_3032_, lean_object* v_code_3033_, lean_object* v_toBind_3034_, lean_object* v_params_3035_){
_start:
{
lean_object* v___f_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___f_3036_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0), 4, 3);
lean_closure_set(v___f_3036_, 0, v_ctorName_3027_);
lean_closure_set(v___f_3036_, 1, v_params_3035_);
lean_closure_set(v___f_3036_, 2, v_toPure_3028_);
v___x_3037_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_3029_, v_inst_3030_, v_inst_3031_, v_f_3032_, v_code_3033_);
v___x_3038_ = lean_apply_4(v_toBind_3034_, lean_box(0), lean_box(0), v___x_3037_, v___f_3036_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed(lean_object* v_ctorName_3039_, lean_object* v_toPure_3040_, lean_object* v_pu_3041_, lean_object* v_inst_3042_, lean_object* v_inst_3043_, lean_object* v_f_3044_, lean_object* v_code_3045_, lean_object* v_toBind_3046_, lean_object* v_params_3047_){
_start:
{
uint8_t v_pu_boxed_3048_; lean_object* v_res_3049_; 
v_pu_boxed_3048_ = lean_unbox(v_pu_3041_);
v_res_3049_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(v_ctorName_3039_, v_toPure_3040_, v_pu_boxed_3048_, v_inst_3042_, v_inst_3043_, v_f_3044_, v_code_3045_, v_toBind_3046_, v_params_3047_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2(lean_object* v_info_3050_, lean_object* v_toPure_3051_, lean_object* v_____do__lift_3052_){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3053_, 0, v_info_3050_);
lean_ctor_set(v___x_3053_, 1, v_____do__lift_3052_);
v___x_3054_ = lean_apply_2(v_toPure_3051_, lean_box(0), v___x_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3(lean_object* v_toPure_3055_, lean_object* v_____do__lift_3056_){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3057_, 0, v_____do__lift_3056_);
v___x_3058_ = lean_apply_2(v_toPure_3055_, lean_box(0), v___x_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(uint8_t v_pu_3059_, lean_object* v_m_3060_, lean_object* v_inst_3061_, lean_object* v_inst_3062_, lean_object* v_f_3063_, lean_object* v_alt_3064_){
_start:
{
switch(lean_obj_tag(v_alt_3064_))
{
case 0:
{
lean_object* v_toApplicative_3065_; lean_object* v_toBind_3066_; lean_object* v_toPure_3067_; lean_object* v_ctorName_3068_; lean_object* v_params_3069_; lean_object* v_code_3070_; lean_object* v___x_3071_; lean_object* v___f_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; size_t v_sz_3075_; size_t v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v_toApplicative_3065_ = lean_ctor_get(v_inst_3062_, 0);
v_toBind_3066_ = lean_ctor_get(v_inst_3062_, 1);
lean_inc(v_toBind_3066_);
v_toPure_3067_ = lean_ctor_get(v_toApplicative_3065_, 1);
v_ctorName_3068_ = lean_ctor_get(v_alt_3064_, 0);
lean_inc(v_ctorName_3068_);
v_params_3069_ = lean_ctor_get(v_alt_3064_, 1);
lean_inc_ref(v_params_3069_);
v_code_3070_ = lean_ctor_get(v_alt_3064_, 2);
lean_inc_ref(v_code_3070_);
lean_dec_ref(v_alt_3064_);
v___x_3071_ = lean_box(v_pu_3059_);
lean_inc(v_toBind_3066_);
lean_inc(v_f_3063_);
lean_inc_ref(v_inst_3062_);
lean_inc(v_inst_3061_);
lean_inc(v_toPure_3067_);
v___f_3072_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed), 9, 8);
lean_closure_set(v___f_3072_, 0, v_ctorName_3068_);
lean_closure_set(v___f_3072_, 1, v_toPure_3067_);
lean_closure_set(v___f_3072_, 2, v___x_3071_);
lean_closure_set(v___f_3072_, 3, v_inst_3061_);
lean_closure_set(v___f_3072_, 4, v_inst_3062_);
lean_closure_set(v___f_3072_, 5, v_f_3063_);
lean_closure_set(v___f_3072_, 6, v_code_3070_);
lean_closure_set(v___f_3072_, 7, v_toBind_3066_);
v___x_3073_ = lean_box(v_pu_3059_);
lean_inc_ref(v_inst_3062_);
v___x_3074_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_3074_, 0, lean_box(0));
lean_closure_set(v___x_3074_, 1, v___x_3073_);
lean_closure_set(v___x_3074_, 2, v_inst_3061_);
lean_closure_set(v___x_3074_, 3, v_inst_3062_);
lean_closure_set(v___x_3074_, 4, v_f_3063_);
v_sz_3075_ = lean_array_size(v_params_3069_);
v___x_3076_ = ((size_t)0ULL);
v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3062_, v___x_3074_, v_sz_3075_, v___x_3076_, v_params_3069_);
v___x_3078_ = lean_apply_4(v_toBind_3066_, lean_box(0), lean_box(0), v___x_3077_, v___f_3072_);
return v___x_3078_;
}
case 1:
{
lean_object* v_toApplicative_3079_; lean_object* v_toBind_3080_; lean_object* v_toPure_3081_; lean_object* v_info_3082_; lean_object* v_code_3083_; lean_object* v___f_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v_toApplicative_3079_ = lean_ctor_get(v_inst_3062_, 0);
v_toBind_3080_ = lean_ctor_get(v_inst_3062_, 1);
lean_inc(v_toBind_3080_);
v_toPure_3081_ = lean_ctor_get(v_toApplicative_3079_, 1);
v_info_3082_ = lean_ctor_get(v_alt_3064_, 0);
lean_inc_ref(v_info_3082_);
v_code_3083_ = lean_ctor_get(v_alt_3064_, 1);
lean_inc_ref(v_code_3083_);
lean_dec_ref(v_alt_3064_);
lean_inc(v_toPure_3081_);
v___f_3084_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2), 3, 2);
lean_closure_set(v___f_3084_, 0, v_info_3082_);
lean_closure_set(v___f_3084_, 1, v_toPure_3081_);
v___x_3085_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_3059_, v_inst_3061_, v_inst_3062_, v_f_3063_, v_code_3083_);
v___x_3086_ = lean_apply_4(v_toBind_3080_, lean_box(0), lean_box(0), v___x_3085_, v___f_3084_);
return v___x_3086_;
}
default: 
{
lean_object* v_toApplicative_3087_; lean_object* v_toBind_3088_; lean_object* v_toPure_3089_; lean_object* v_code_3090_; lean_object* v___f_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v_toApplicative_3087_ = lean_ctor_get(v_inst_3062_, 0);
v_toBind_3088_ = lean_ctor_get(v_inst_3062_, 1);
lean_inc(v_toBind_3088_);
v_toPure_3089_ = lean_ctor_get(v_toApplicative_3087_, 1);
v_code_3090_ = lean_ctor_get(v_alt_3064_, 0);
lean_inc_ref(v_code_3090_);
lean_dec_ref(v_alt_3064_);
lean_inc(v_toPure_3089_);
v___f_3091_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3), 2, 1);
lean_closure_set(v___f_3091_, 0, v_toPure_3089_);
v___x_3092_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_3059_, v_inst_3061_, v_inst_3062_, v_f_3063_, v_code_3090_);
v___x_3093_ = lean_apply_4(v_toBind_3088_, lean_box(0), lean_box(0), v___x_3092_, v___f_3091_);
return v___x_3093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed(lean_object* v_pu_3094_, lean_object* v_m_3095_, lean_object* v_inst_3096_, lean_object* v_inst_3097_, lean_object* v_f_3098_, lean_object* v_alt_3099_){
_start:
{
uint8_t v_pu_boxed_3100_; lean_object* v_res_3101_; 
v_pu_boxed_3100_ = lean_unbox(v_pu_3094_);
v_res_3101_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(v_pu_boxed_3100_, v_m_3095_, v_inst_3096_, v_inst_3097_, v_f_3098_, v_alt_3099_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5(lean_object* v_inst_3102_, lean_object* v_f_3103_, lean_object* v_code_3104_, lean_object* v_____r_3105_){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_3102_, v_f_3103_, v_code_3104_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__7(lean_object* v_m_3107_, lean_object* v_inst_3108_, lean_object* v_f_3109_, lean_object* v_alt_3110_){
_start:
{
switch(lean_obj_tag(v_alt_3110_))
{
case 0:
{
lean_object* v_toApplicative_3111_; lean_object* v_toBind_3112_; lean_object* v_params_3113_; lean_object* v_code_3114_; lean_object* v___f_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; uint8_t v___x_3119_; 
v_toApplicative_3111_ = lean_ctor_get(v_inst_3108_, 0);
v_toBind_3112_ = lean_ctor_get(v_inst_3108_, 1);
lean_inc(v_toBind_3112_);
v_params_3113_ = lean_ctor_get(v_alt_3110_, 1);
lean_inc_ref(v_params_3113_);
v_code_3114_ = lean_ctor_get(v_alt_3110_, 2);
lean_inc_ref(v_code_3114_);
lean_dec_ref(v_alt_3110_);
lean_inc(v_f_3109_);
lean_inc_ref(v_inst_3108_);
v___f_3115_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5), 4, 3);
lean_closure_set(v___f_3115_, 0, v_inst_3108_);
lean_closure_set(v___f_3115_, 1, v_f_3109_);
lean_closure_set(v___f_3115_, 2, v_code_3114_);
v___x_3116_ = lean_unsigned_to_nat(0u);
v___x_3117_ = lean_array_get_size(v_params_3113_);
v___x_3118_ = lean_box(0);
v___x_3119_ = lean_nat_dec_lt(v___x_3116_, v___x_3117_);
if (v___x_3119_ == 0)
{
lean_object* v_toPure_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
lean_inc_ref(v_toApplicative_3111_);
lean_dec_ref(v_params_3113_);
lean_dec(v_f_3109_);
lean_dec_ref(v_inst_3108_);
v_toPure_3120_ = lean_ctor_get(v_toApplicative_3111_, 1);
lean_inc(v_toPure_3120_);
lean_dec_ref(v_toApplicative_3111_);
v___x_3121_ = lean_apply_2(v_toPure_3120_, lean_box(0), v___x_3118_);
v___x_3122_ = lean_apply_4(v_toBind_3112_, lean_box(0), lean_box(0), v___x_3121_, v___f_3115_);
return v___x_3122_;
}
else
{
lean_object* v___f_3123_; uint8_t v___x_3124_; 
lean_inc_ref(v_inst_3108_);
v___f_3123_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_3123_, 0, v_inst_3108_);
lean_closure_set(v___f_3123_, 1, v_f_3109_);
v___x_3124_ = lean_nat_dec_le(v___x_3117_, v___x_3117_);
if (v___x_3124_ == 0)
{
if (v___x_3119_ == 0)
{
lean_object* v_toPure_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_inc_ref(v_toApplicative_3111_);
lean_dec_ref(v___f_3123_);
lean_dec_ref(v_params_3113_);
lean_dec_ref(v_inst_3108_);
v_toPure_3125_ = lean_ctor_get(v_toApplicative_3111_, 1);
lean_inc(v_toPure_3125_);
lean_dec_ref(v_toApplicative_3111_);
v___x_3126_ = lean_apply_2(v_toPure_3125_, lean_box(0), v___x_3118_);
v___x_3127_ = lean_apply_4(v_toBind_3112_, lean_box(0), lean_box(0), v___x_3126_, v___f_3115_);
return v___x_3127_;
}
else
{
size_t v___x_3128_; size_t v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3128_ = ((size_t)0ULL);
v___x_3129_ = lean_usize_of_nat(v___x_3117_);
v___x_3130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3108_, v___f_3123_, v_params_3113_, v___x_3128_, v___x_3129_, v___x_3118_);
v___x_3131_ = lean_apply_4(v_toBind_3112_, lean_box(0), lean_box(0), v___x_3130_, v___f_3115_);
return v___x_3131_;
}
}
else
{
size_t v___x_3132_; size_t v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3132_ = ((size_t)0ULL);
v___x_3133_ = lean_usize_of_nat(v___x_3117_);
v___x_3134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3108_, v___f_3123_, v_params_3113_, v___x_3132_, v___x_3133_, v___x_3118_);
v___x_3135_ = lean_apply_4(v_toBind_3112_, lean_box(0), lean_box(0), v___x_3134_, v___f_3115_);
return v___x_3135_;
}
}
}
case 1:
{
lean_object* v_code_3136_; lean_object* v___x_3137_; 
v_code_3136_ = lean_ctor_get(v_alt_3110_, 1);
lean_inc_ref(v_code_3136_);
lean_dec_ref(v_alt_3110_);
v___x_3137_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_3108_, v_f_3109_, v_code_3136_);
return v___x_3137_;
}
default: 
{
lean_object* v_code_3138_; lean_object* v___x_3139_; 
v_code_3138_ = lean_ctor_get(v_alt_3110_, 0);
lean_inc_ref(v_code_3138_);
lean_dec_ref(v_alt_3110_);
v___x_3139_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_3108_, v_f_3109_, v_code_3138_);
return v___x_3139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt(uint8_t v_pu_3141_){
_start:
{
lean_object* v___x_3142_; lean_object* v___f_3143_; lean_object* v___f_3144_; lean_object* v___x_3145_; 
v___x_3142_ = lean_box(v_pu_3141_);
v___f_3143_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed), 6, 1);
lean_closure_set(v___f_3143_, 0, v___x_3142_);
v___f_3144_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0));
v___x_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___f_3143_);
lean_ctor_set(v___x_3145_, 1, v___f_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___boxed(lean_object* v_pu_3146_){
_start:
{
uint8_t v_pu_boxed_3147_; lean_object* v_res_3148_; 
v_pu_boxed_3147_ = lean_unbox(v_pu_3146_);
v_res_3148_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt(v_pu_boxed_3147_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(lean_object* v_toPure_3151_, lean_object* v_____do__lift_3152_){
_start:
{
if (lean_obj_tag(v_____do__lift_3152_) == 0)
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = lean_box(0);
v___x_3154_ = lean_apply_2(v_toPure_3151_, lean_box(0), v___x_3153_);
return v___x_3154_;
}
else
{
lean_object* v_val_3155_; uint8_t v___x_3156_; 
v_val_3155_ = lean_ctor_get(v_____do__lift_3152_, 0);
v___x_3156_ = lean_unbox(v_val_3155_);
if (v___x_3156_ == 0)
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0));
v___x_3158_ = lean_apply_2(v_toPure_3151_, lean_box(0), v___x_3157_);
return v___x_3158_;
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = lean_box(0);
v___x_3160_ = lean_apply_2(v_toPure_3151_, lean_box(0), v___x_3159_);
return v___x_3160_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed(lean_object* v_toPure_3161_, lean_object* v_____do__lift_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(v_toPure_3161_, v_____do__lift_3162_);
lean_dec(v_____do__lift_3162_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(lean_object* v_toPure_3164_, uint8_t v_____do__lift_3165_){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3166_ = lean_box(v_____do__lift_3165_);
v___x_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
v___x_3168_ = lean_apply_2(v_toPure_3164_, lean_box(0), v___x_3167_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed(lean_object* v_toPure_3169_, lean_object* v_____do__lift_3170_){
_start:
{
uint8_t v_____do__lift_404__boxed_3171_; lean_object* v_res_3172_; 
v_____do__lift_404__boxed_3171_ = lean_unbox(v_____do__lift_3170_);
v_res_3172_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(v_toPure_3169_, v_____do__lift_404__boxed_3171_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(lean_object* v_inst_3173_, lean_object* v_f_3174_, lean_object* v_fvar_3175_){
_start:
{
lean_object* v_toApplicative_3176_; lean_object* v_toBind_3177_; lean_object* v_toPure_3178_; lean_object* v___x_3179_; lean_object* v___f_3180_; lean_object* v___f_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v_toApplicative_3176_ = lean_ctor_get(v_inst_3173_, 0);
lean_inc_ref(v_toApplicative_3176_);
v_toBind_3177_ = lean_ctor_get(v_inst_3173_, 1);
lean_inc(v_toBind_3177_);
lean_dec_ref(v_inst_3173_);
v_toPure_3178_ = lean_ctor_get(v_toApplicative_3176_, 1);
lean_inc(v_toPure_3178_);
lean_dec_ref(v_toApplicative_3176_);
v___x_3179_ = lean_apply_1(v_f_3174_, v_fvar_3175_);
lean_inc(v_toPure_3178_);
v___f_3180_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3180_, 0, v_toPure_3178_);
v___f_3181_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3181_, 0, v_toPure_3178_);
lean_inc(v_toBind_3177_);
v___x_3182_ = lean_apply_4(v_toBind_3177_, lean_box(0), lean_box(0), v___x_3179_, v___f_3181_);
v___x_3183_ = lean_apply_4(v_toBind_3177_, lean_box(0), lean_box(0), v___x_3182_, v___f_3180_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go(lean_object* v_m_3184_, lean_object* v_inst_3185_, lean_object* v_f_3186_, lean_object* v_fvar_3187_){
_start:
{
lean_object* v___x_3188_; 
v___x_3188_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(v_inst_3185_, v_f_3186_, v_fvar_3187_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(lean_object* v_toPure_3189_, lean_object* v_____do__lift_3190_){
_start:
{
if (lean_obj_tag(v_____do__lift_3190_) == 0)
{
uint8_t v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3191_ = 1;
v___x_3192_ = lean_box(v___x_3191_);
v___x_3193_ = lean_apply_2(v_toPure_3189_, lean_box(0), v___x_3192_);
return v___x_3193_;
}
else
{
uint8_t v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3194_ = 0;
v___x_3195_ = lean_box(v___x_3194_);
v___x_3196_ = lean_apply_2(v_toPure_3189_, lean_box(0), v___x_3195_);
return v___x_3196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed(lean_object* v_toPure_3197_, lean_object* v_____do__lift_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(v_toPure_3197_, v_____do__lift_3198_);
lean_dec(v_____do__lift_3198_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg(lean_object* v_inst_3200_, lean_object* v_inst_3201_, lean_object* v_f_3202_, lean_object* v_x_3203_){
_start:
{
lean_object* v_toApplicative_3204_; lean_object* v_toBind_3205_; lean_object* v_forFVarM_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3227_; 
v_toApplicative_3204_ = lean_ctor_get(v_inst_3200_, 0);
v_toBind_3205_ = lean_ctor_get(v_inst_3200_, 1);
lean_inc(v_toBind_3205_);
v_forFVarM_3206_ = lean_ctor_get(v_inst_3201_, 1);
v_isSharedCheck_3227_ = !lean_is_exclusive(v_inst_3201_);
if (v_isSharedCheck_3227_ == 0)
{
lean_object* v_unused_3228_; 
v_unused_3228_ = lean_ctor_get(v_inst_3201_, 0);
lean_dec(v_unused_3228_);
v___x_3208_ = v_inst_3201_;
v_isShared_3209_ = v_isSharedCheck_3227_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_forFVarM_3206_);
lean_dec(v_inst_3201_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3227_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___f_3210_; lean_object* v___f_3211_; lean_object* v___f_3212_; lean_object* v___f_3213_; lean_object* v___f_3214_; lean_object* v___x_3216_; 
lean_inc_ref(v_inst_3200_);
v___f_3210_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3210_, 0, v_inst_3200_);
lean_inc_ref(v_inst_3200_);
v___f_3211_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3211_, 0, v_inst_3200_);
lean_inc_ref(v_inst_3200_);
v___f_3212_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3212_, 0, v_inst_3200_);
lean_inc_ref(v_inst_3200_);
v___f_3213_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3213_, 0, v_inst_3200_);
lean_inc_ref(v_inst_3200_);
v___f_3214_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3214_, 0, v_inst_3200_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 1, v___f_3211_);
lean_ctor_set(v___x_3208_, 0, v___f_3210_);
v___x_3216_ = v___x_3208_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___f_3210_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v___f_3211_);
v___x_3216_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v_toPure_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___f_3224_; lean_object* v___x_3225_; 
lean_inc_ref(v_inst_3200_);
v___x_3217_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3217_, 0, lean_box(0));
lean_closure_set(v___x_3217_, 1, v_inst_3200_);
v___x_3218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3216_);
lean_ctor_set(v___x_3218_, 1, v___x_3217_);
lean_ctor_set(v___x_3218_, 2, v___f_3212_);
lean_ctor_set(v___x_3218_, 3, v___f_3213_);
lean_ctor_set(v___x_3218_, 4, v___f_3214_);
lean_inc_ref(v_inst_3200_);
v___x_3219_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3219_, 0, lean_box(0));
lean_closure_set(v___x_3219_, 1, v_inst_3200_);
v___x_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3218_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v_toPure_3221_ = lean_ctor_get(v_toApplicative_3204_, 1);
lean_inc(v_toPure_3221_);
v___x_3222_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go), 4, 3);
lean_closure_set(v___x_3222_, 0, lean_box(0));
lean_closure_set(v___x_3222_, 1, v_inst_3200_);
lean_closure_set(v___x_3222_, 2, v_f_3202_);
v___x_3223_ = lean_apply_4(v_forFVarM_3206_, lean_box(0), v___x_3220_, v___x_3222_, v_x_3203_);
v___f_3224_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3224_, 0, v_toPure_3221_);
v___x_3225_ = lean_apply_4(v_toBind_3205_, lean_box(0), lean_box(0), v___x_3223_, v___f_3224_);
return v___x_3225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM(lean_object* v_m_3229_, lean_object* v_00_u03b1_3230_, lean_object* v_inst_3231_, lean_object* v_inst_3232_, lean_object* v_f_3233_, lean_object* v_x_3234_){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = l_Lean_Compiler_LCNF_anyFVarM___redArg(v_inst_3231_, v_inst_3232_, v_f_3233_, v_x_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(lean_object* v_toPure_3236_, lean_object* v_____do__lift_3237_){
_start:
{
if (lean_obj_tag(v_____do__lift_3237_) == 0)
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = lean_box(0);
v___x_3239_ = lean_apply_2(v_toPure_3236_, lean_box(0), v___x_3238_);
return v___x_3239_;
}
else
{
lean_object* v_val_3240_; uint8_t v___x_3241_; 
v_val_3240_ = lean_ctor_get(v_____do__lift_3237_, 0);
v___x_3241_ = lean_unbox(v_val_3240_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = lean_box(0);
v___x_3243_ = lean_apply_2(v_toPure_3236_, lean_box(0), v___x_3242_);
return v___x_3243_;
}
else
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3244_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0));
v___x_3245_ = lean_apply_2(v_toPure_3236_, lean_box(0), v___x_3244_);
return v___x_3245_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed(lean_object* v_toPure_3246_, lean_object* v_____do__lift_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(v_toPure_3246_, v_____do__lift_3247_);
lean_dec(v_____do__lift_3247_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(lean_object* v_inst_3249_, lean_object* v_f_3250_, lean_object* v_fvar_3251_){
_start:
{
lean_object* v_toApplicative_3252_; lean_object* v_toBind_3253_; lean_object* v_toPure_3254_; lean_object* v___x_3255_; lean_object* v___f_3256_; lean_object* v___f_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v_toApplicative_3252_ = lean_ctor_get(v_inst_3249_, 0);
lean_inc_ref(v_toApplicative_3252_);
v_toBind_3253_ = lean_ctor_get(v_inst_3249_, 1);
lean_inc(v_toBind_3253_);
lean_dec_ref(v_inst_3249_);
v_toPure_3254_ = lean_ctor_get(v_toApplicative_3252_, 1);
lean_inc(v_toPure_3254_);
lean_dec_ref(v_toApplicative_3252_);
v___x_3255_ = lean_apply_1(v_f_3250_, v_fvar_3251_);
lean_inc(v_toPure_3254_);
v___f_3256_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3256_, 0, v_toPure_3254_);
v___f_3257_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3257_, 0, v_toPure_3254_);
lean_inc(v_toBind_3253_);
v___x_3258_ = lean_apply_4(v_toBind_3253_, lean_box(0), lean_box(0), v___x_3255_, v___f_3257_);
v___x_3259_ = lean_apply_4(v_toBind_3253_, lean_box(0), lean_box(0), v___x_3258_, v___f_3256_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go(lean_object* v_m_3260_, lean_object* v_inst_3261_, lean_object* v_f_3262_, lean_object* v_fvar_3263_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(v_inst_3261_, v_f_3262_, v_fvar_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(lean_object* v_toPure_3265_, lean_object* v_____do__lift_3266_){
_start:
{
if (lean_obj_tag(v_____do__lift_3266_) == 1)
{
uint8_t v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3267_ = 1;
v___x_3268_ = lean_box(v___x_3267_);
v___x_3269_ = lean_apply_2(v_toPure_3265_, lean_box(0), v___x_3268_);
return v___x_3269_;
}
else
{
uint8_t v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3270_ = 0;
v___x_3271_ = lean_box(v___x_3270_);
v___x_3272_ = lean_apply_2(v_toPure_3265_, lean_box(0), v___x_3271_);
return v___x_3272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed(lean_object* v_toPure_3273_, lean_object* v_____do__lift_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(v_toPure_3273_, v_____do__lift_3274_);
lean_dec(v_____do__lift_3274_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg(lean_object* v_inst_3276_, lean_object* v_inst_3277_, lean_object* v_f_3278_, lean_object* v_x_3279_){
_start:
{
lean_object* v_toApplicative_3280_; lean_object* v_toBind_3281_; lean_object* v_forFVarM_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3303_; 
v_toApplicative_3280_ = lean_ctor_get(v_inst_3276_, 0);
v_toBind_3281_ = lean_ctor_get(v_inst_3276_, 1);
lean_inc(v_toBind_3281_);
v_forFVarM_3282_ = lean_ctor_get(v_inst_3277_, 1);
v_isSharedCheck_3303_ = !lean_is_exclusive(v_inst_3277_);
if (v_isSharedCheck_3303_ == 0)
{
lean_object* v_unused_3304_; 
v_unused_3304_ = lean_ctor_get(v_inst_3277_, 0);
lean_dec(v_unused_3304_);
v___x_3284_ = v_inst_3277_;
v_isShared_3285_ = v_isSharedCheck_3303_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_forFVarM_3282_);
lean_dec(v_inst_3277_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3303_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___f_3286_; lean_object* v___f_3287_; lean_object* v___f_3288_; lean_object* v___f_3289_; lean_object* v___f_3290_; lean_object* v___x_3292_; 
lean_inc_ref(v_inst_3276_);
v___f_3286_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3286_, 0, v_inst_3276_);
lean_inc_ref(v_inst_3276_);
v___f_3287_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3287_, 0, v_inst_3276_);
lean_inc_ref(v_inst_3276_);
v___f_3288_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3288_, 0, v_inst_3276_);
lean_inc_ref(v_inst_3276_);
v___f_3289_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3289_, 0, v_inst_3276_);
lean_inc_ref(v_inst_3276_);
v___f_3290_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3290_, 0, v_inst_3276_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 1, v___f_3287_);
lean_ctor_set(v___x_3284_, 0, v___f_3286_);
v___x_3292_ = v___x_3284_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___f_3286_);
lean_ctor_set(v_reuseFailAlloc_3302_, 1, v___f_3287_);
v___x_3292_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v_toPure_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___f_3300_; lean_object* v___x_3301_; 
lean_inc_ref(v_inst_3276_);
v___x_3293_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3293_, 0, lean_box(0));
lean_closure_set(v___x_3293_, 1, v_inst_3276_);
v___x_3294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3292_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
lean_ctor_set(v___x_3294_, 2, v___f_3288_);
lean_ctor_set(v___x_3294_, 3, v___f_3289_);
lean_ctor_set(v___x_3294_, 4, v___f_3290_);
lean_inc_ref(v_inst_3276_);
v___x_3295_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3295_, 0, lean_box(0));
lean_closure_set(v___x_3295_, 1, v_inst_3276_);
v___x_3296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3294_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
v_toPure_3297_ = lean_ctor_get(v_toApplicative_3280_, 1);
lean_inc(v_toPure_3297_);
v___x_3298_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go), 4, 3);
lean_closure_set(v___x_3298_, 0, lean_box(0));
lean_closure_set(v___x_3298_, 1, v_inst_3276_);
lean_closure_set(v___x_3298_, 2, v_f_3278_);
v___x_3299_ = lean_apply_4(v_forFVarM_3282_, lean_box(0), v___x_3296_, v___x_3298_, v_x_3279_);
v___f_3300_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3300_, 0, v_toPure_3297_);
v___x_3301_ = lean_apply_4(v_toBind_3281_, lean_box(0), lean_box(0), v___x_3299_, v___f_3300_);
return v___x_3301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM(lean_object* v_m_3305_, lean_object* v_00_u03b1_3306_, lean_object* v_inst_3307_, lean_object* v_inst_3308_, lean_object* v_f_3309_, lean_object* v_x_3310_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = l_Lean_Compiler_LCNF_allFVarM___redArg(v_inst_3307_, v_inst_3308_, v_f_3309_, v_x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(lean_object* v_f_3312_, lean_object* v_x_3313_){
_start:
{
lean_object* v___x_3314_; uint8_t v___x_3315_; 
v___x_3314_ = lean_apply_1(v_f_3312_, v_x_3313_);
v___x_3315_ = lean_unbox(v___x_3314_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed(lean_object* v_f_3316_, lean_object* v_x_3317_){
_start:
{
uint8_t v_res_3318_; lean_object* v_r_3319_; 
v_res_3318_ = l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(v_f_3316_, v_x_3317_);
v_r_3319_ = lean_box(v_res_3318_);
return v_r_3319_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar___redArg(lean_object* v_inst_3339_, lean_object* v_f_3340_, lean_object* v_x_3341_){
_start:
{
lean_object* v___f_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; 
v___f_3342_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3342_, 0, v_f_3340_);
v___x_3343_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9));
v___x_3344_ = l_Lean_Compiler_LCNF_anyFVarM___redArg(v___x_3343_, v_inst_3339_, v___f_3342_, v_x_3341_);
v___x_3345_ = lean_unbox(v___x_3344_);
lean_dec(v___x_3344_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___boxed(lean_object* v_inst_3346_, lean_object* v_f_3347_, lean_object* v_x_3348_){
_start:
{
uint8_t v_res_3349_; lean_object* v_r_3350_; 
v_res_3349_ = l_Lean_Compiler_LCNF_anyFVar___redArg(v_inst_3346_, v_f_3347_, v_x_3348_);
v_r_3350_ = lean_box(v_res_3349_);
return v_r_3350_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar(lean_object* v_00_u03b1_3351_, lean_object* v_inst_3352_, lean_object* v_f_3353_, lean_object* v_x_3354_){
_start:
{
uint8_t v___x_3355_; 
v___x_3355_ = l_Lean_Compiler_LCNF_anyFVar___redArg(v_inst_3352_, v_f_3353_, v_x_3354_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___boxed(lean_object* v_00_u03b1_3356_, lean_object* v_inst_3357_, lean_object* v_f_3358_, lean_object* v_x_3359_){
_start:
{
uint8_t v_res_3360_; lean_object* v_r_3361_; 
v_res_3360_ = l_Lean_Compiler_LCNF_anyFVar(v_00_u03b1_3356_, v_inst_3357_, v_f_3358_, v_x_3359_);
v_r_3361_ = lean_box(v_res_3360_);
return v_r_3361_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar___redArg(lean_object* v_inst_3362_, lean_object* v_f_3363_, lean_object* v_x_3364_){
_start:
{
lean_object* v___f_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; uint8_t v___x_3368_; 
v___f_3365_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3365_, 0, v_f_3363_);
v___x_3366_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9));
v___x_3367_ = l_Lean_Compiler_LCNF_allFVarM___redArg(v___x_3366_, v_inst_3362_, v___f_3365_, v_x_3364_);
v___x_3368_ = lean_unbox(v___x_3367_);
lean_dec(v___x_3367_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___redArg___boxed(lean_object* v_inst_3369_, lean_object* v_f_3370_, lean_object* v_x_3371_){
_start:
{
uint8_t v_res_3372_; lean_object* v_r_3373_; 
v_res_3372_ = l_Lean_Compiler_LCNF_allFVar___redArg(v_inst_3369_, v_f_3370_, v_x_3371_);
v_r_3373_ = lean_box(v_res_3372_);
return v_r_3373_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar(lean_object* v_00_u03b1_3374_, lean_object* v_inst_3375_, lean_object* v_f_3376_, lean_object* v_x_3377_){
_start:
{
uint8_t v___x_3378_; 
v___x_3378_ = l_Lean_Compiler_LCNF_allFVar___redArg(v_inst_3375_, v_f_3376_, v_x_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___boxed(lean_object* v_00_u03b1_3379_, lean_object* v_inst_3380_, lean_object* v_f_3381_, lean_object* v_x_3382_){
_start:
{
uint8_t v_res_3383_; lean_object* v_r_3384_; 
v_res_3383_ = l_Lean_Compiler_LCNF_allFVar(v_00_u03b1_3379_, v_inst_3380_, v_f_3381_, v_x_3382_);
v_r_3384_ = lean_box(v_res_3383_);
return v_r_3384_;
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
