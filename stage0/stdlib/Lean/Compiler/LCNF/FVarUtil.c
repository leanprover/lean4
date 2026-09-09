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
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
uint8_t v_binderInfo_644__boxed_68_; lean_object* v_res_69_; 
v_binderInfo_644__boxed_68_ = lean_unbox(v_binderInfo_63_);
v_res_69_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3(v_binderType_60_, v_____do__lift_61_, v_binderName_62_, v_binderInfo_644__boxed_68_, v_toPure_64_, v_body_65_, v_e_66_, v_____do__lift_67_);
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
uint8_t v_binderInfo_690__boxed_100_; lean_object* v_res_101_; 
v_binderInfo_690__boxed_100_ = lean_unbox(v_binderInfo_95_);
v_res_101_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5(v_binderType_92_, v_____do__lift_93_, v_binderName_94_, v_binderInfo_690__boxed_100_, v_toPure_96_, v_body_97_, v_e_98_, v_____do__lift_99_);
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
uint8_t v_binderInfo_769__boxed_135_; lean_object* v_res_136_; 
v_binderInfo_769__boxed_135_ = lean_unbox(v_binderInfo_127_);
v_res_136_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4(v_binderType_125_, v_binderName_126_, v_binderInfo_769__boxed_135_, v_toPure_128_, v_body_129_, v_e_130_, v_inst_131_, v_f_132_, v_toBind_133_, v_____do__lift_134_);
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
uint8_t v_binderInfo_778__boxed_161_; lean_object* v_res_162_; 
v_binderInfo_778__boxed_161_ = lean_unbox(v_binderInfo_153_);
v_res_162_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6(v_binderType_151_, v_binderName_152_, v_binderInfo_778__boxed_161_, v_toPure_154_, v_body_155_, v_e_156_, v_inst_157_, v_f_158_, v_toBind_159_, v_____do__lift_160_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1(uint8_t v_pu_433_, lean_object* v_e_434_, lean_object* v_toPure_435_, lean_object* v_____do__lift_436_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_433_, v_e_434_, v_____do__lift_436_);
v___x_438_ = lean_apply_2(v_toPure_435_, lean_box(0), v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1___boxed(lean_object* v_pu_439_, lean_object* v_e_440_, lean_object* v_toPure_441_, lean_object* v_____do__lift_442_){
_start:
{
uint8_t v_pu_boxed_443_; lean_object* v_res_444_; 
v_pu_boxed_443_ = lean_unbox(v_pu_439_);
v_res_444_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1(v_pu_boxed_443_, v_e_440_, v_toPure_441_, v_____do__lift_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(uint8_t v_pu_445_, lean_object* v_e_446_, lean_object* v_toPure_447_, lean_object* v_____do__lift_448_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_445_, v_e_446_, v_____do__lift_448_);
v___x_450_ = lean_apply_2(v_toPure_447_, lean_box(0), v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed(lean_object* v_pu_451_, lean_object* v_e_452_, lean_object* v_toPure_453_, lean_object* v_____do__lift_454_){
_start:
{
uint8_t v_pu_boxed_455_; lean_object* v_res_456_; 
v_pu_boxed_455_ = lean_unbox(v_pu_451_);
v_res_456_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(v_pu_boxed_455_, v_e_452_, v_toPure_453_, v_____do__lift_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7(uint8_t v_pu_457_, lean_object* v_e_458_, lean_object* v_____do__lift_459_, lean_object* v_toPure_460_, lean_object* v_____do__lift_461_){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_457_, v_e_458_, v_____do__lift_459_, v_____do__lift_461_);
v___x_463_ = lean_apply_2(v_toPure_460_, lean_box(0), v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7___boxed(lean_object* v_pu_464_, lean_object* v_e_465_, lean_object* v_____do__lift_466_, lean_object* v_toPure_467_, lean_object* v_____do__lift_468_){
_start:
{
uint8_t v_pu_boxed_469_; lean_object* v_res_470_; 
v_pu_boxed_469_ = lean_unbox(v_pu_464_);
v_res_470_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7(v_pu_boxed_469_, v_e_465_, v_____do__lift_466_, v_toPure_467_, v_____do__lift_468_);
lean_dec(v_e_465_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3(uint8_t v_pu_471_, lean_object* v_e_472_, lean_object* v_toPure_473_, lean_object* v_args_474_, lean_object* v_inst_475_, lean_object* v___f_476_, lean_object* v_toBind_477_, lean_object* v_____do__lift_478_){
_start:
{
lean_object* v___x_479_; lean_object* v___f_480_; size_t v_sz_481_; size_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_479_ = lean_box(v_pu_471_);
v___f_480_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7___boxed), 5, 4);
lean_closure_set(v___f_480_, 0, v___x_479_);
lean_closure_set(v___f_480_, 1, v_e_472_);
lean_closure_set(v___f_480_, 2, v_____do__lift_478_);
lean_closure_set(v___f_480_, 3, v_toPure_473_);
v_sz_481_ = lean_array_size(v_args_474_);
v___x_482_ = ((size_t)0ULL);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_475_, v___f_476_, v_sz_481_, v___x_482_, v_args_474_);
v___x_484_ = lean_apply_4(v_toBind_477_, lean_box(0), lean_box(0), v___x_483_, v___f_480_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3___boxed(lean_object* v_pu_485_, lean_object* v_e_486_, lean_object* v_toPure_487_, lean_object* v_args_488_, lean_object* v_inst_489_, lean_object* v___f_490_, lean_object* v_toBind_491_, lean_object* v_____do__lift_492_){
_start:
{
uint8_t v_pu_boxed_493_; lean_object* v_res_494_; 
v_pu_boxed_493_ = lean_unbox(v_pu_485_);
v_res_494_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3(v_pu_boxed_493_, v_e_486_, v_toPure_487_, v_args_488_, v_inst_489_, v___f_490_, v_toBind_491_, v_____do__lift_492_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8(uint8_t v_pu_495_, lean_object* v_e_496_, lean_object* v_n_497_, lean_object* v_toPure_498_, lean_object* v_____do__lift_499_){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_495_, v_e_496_, v_n_497_, v_____do__lift_499_);
v___x_501_ = lean_apply_2(v_toPure_498_, lean_box(0), v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8___boxed(lean_object* v_pu_502_, lean_object* v_e_503_, lean_object* v_n_504_, lean_object* v_toPure_505_, lean_object* v_____do__lift_506_){
_start:
{
uint8_t v_pu_boxed_507_; lean_object* v_res_508_; 
v_pu_boxed_507_ = lean_unbox(v_pu_502_);
v_res_508_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8(v_pu_boxed_507_, v_e_503_, v_n_504_, v_toPure_505_, v_____do__lift_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(uint8_t v_pu_509_, lean_object* v_e_510_, lean_object* v_____do__lift_511_, lean_object* v_i_512_, uint8_t v_updateHeader_513_, lean_object* v_toPure_514_, lean_object* v_____do__lift_515_){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_509_, v_e_510_, v_____do__lift_511_, v_i_512_, v_updateHeader_513_, v_____do__lift_515_);
v___x_517_ = lean_apply_2(v_toPure_514_, lean_box(0), v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed(lean_object* v_pu_518_, lean_object* v_e_519_, lean_object* v_____do__lift_520_, lean_object* v_i_521_, lean_object* v_updateHeader_522_, lean_object* v_toPure_523_, lean_object* v_____do__lift_524_){
_start:
{
uint8_t v_pu_boxed_525_; uint8_t v_updateHeader_627__boxed_526_; lean_object* v_res_527_; 
v_pu_boxed_525_ = lean_unbox(v_pu_518_);
v_updateHeader_627__boxed_526_ = lean_unbox(v_updateHeader_522_);
v_res_527_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(v_pu_boxed_525_, v_e_519_, v_____do__lift_520_, v_i_521_, v_updateHeader_627__boxed_526_, v_toPure_523_, v_____do__lift_524_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(uint8_t v_pu_528_, lean_object* v_e_529_, lean_object* v_i_530_, uint8_t v_updateHeader_531_, lean_object* v_toPure_532_, lean_object* v_args_533_, lean_object* v_inst_534_, lean_object* v___f_535_, lean_object* v_toBind_536_, lean_object* v_____do__lift_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___f_540_; size_t v_sz_541_; size_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_538_ = lean_box(v_pu_528_);
v___x_539_ = lean_box(v_updateHeader_531_);
v___f_540_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_540_, 0, v___x_538_);
lean_closure_set(v___f_540_, 1, v_e_529_);
lean_closure_set(v___f_540_, 2, v_____do__lift_537_);
lean_closure_set(v___f_540_, 3, v_i_530_);
lean_closure_set(v___f_540_, 4, v___x_539_);
lean_closure_set(v___f_540_, 5, v_toPure_532_);
v_sz_541_ = lean_array_size(v_args_533_);
v___x_542_ = ((size_t)0ULL);
v___x_543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_534_, v___f_535_, v_sz_541_, v___x_542_, v_args_533_);
v___x_544_ = lean_apply_4(v_toBind_536_, lean_box(0), lean_box(0), v___x_543_, v___f_540_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed(lean_object* v_pu_545_, lean_object* v_e_546_, lean_object* v_i_547_, lean_object* v_updateHeader_548_, lean_object* v_toPure_549_, lean_object* v_args_550_, lean_object* v_inst_551_, lean_object* v___f_552_, lean_object* v_toBind_553_, lean_object* v_____do__lift_554_){
_start:
{
uint8_t v_pu_boxed_555_; uint8_t v_updateHeader_642__boxed_556_; lean_object* v_res_557_; 
v_pu_boxed_555_ = lean_unbox(v_pu_545_);
v_updateHeader_642__boxed_556_ = lean_unbox(v_updateHeader_548_);
v_res_557_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(v_pu_boxed_555_, v_e_546_, v_i_547_, v_updateHeader_642__boxed_556_, v_toPure_549_, v_args_550_, v_inst_551_, v___f_552_, v_toBind_553_, v_____do__lift_554_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6(uint8_t v_pu_558_, lean_object* v_e_559_, lean_object* v_ty_560_, lean_object* v_toPure_561_, lean_object* v_____do__lift_562_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_558_, v_e_559_, v_ty_560_, v_____do__lift_562_);
v___x_564_ = lean_apply_2(v_toPure_561_, lean_box(0), v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6___boxed(lean_object* v_pu_565_, lean_object* v_e_566_, lean_object* v_ty_567_, lean_object* v_toPure_568_, lean_object* v_____do__lift_569_){
_start:
{
uint8_t v_pu_boxed_570_; lean_object* v_res_571_; 
v_pu_boxed_570_ = lean_unbox(v_pu_565_);
v_res_571_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6(v_pu_boxed_570_, v_e_566_, v_ty_567_, v_toPure_568_, v_____do__lift_569_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9(uint8_t v_pu_572_, lean_object* v_e_573_, lean_object* v_toPure_574_, lean_object* v_____do__lift_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_572_, v_e_573_, v_____do__lift_575_);
v___x_577_ = lean_apply_2(v_toPure_574_, lean_box(0), v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9___boxed(lean_object* v_pu_578_, lean_object* v_e_579_, lean_object* v_toPure_580_, lean_object* v_____do__lift_581_){
_start:
{
uint8_t v_pu_boxed_582_; lean_object* v_res_583_; 
v_pu_boxed_582_ = lean_unbox(v_pu_578_);
v_res_583_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9(v_pu_boxed_582_, v_e_579_, v_toPure_580_, v_____do__lift_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10(uint8_t v_pu_584_, lean_object* v_e_585_, lean_object* v_toPure_586_, lean_object* v_____do__lift_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_584_, v_e_585_, v_____do__lift_587_);
v___x_589_ = lean_apply_2(v_toPure_586_, lean_box(0), v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10___boxed(lean_object* v_pu_590_, lean_object* v_e_591_, lean_object* v_toPure_592_, lean_object* v_____do__lift_593_){
_start:
{
uint8_t v_pu_boxed_594_; lean_object* v_res_595_; 
v_pu_boxed_594_ = lean_unbox(v_pu_590_);
v_res_595_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10(v_pu_boxed_594_, v_e_591_, v_toPure_592_, v_____do__lift_593_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(uint8_t v_pu_596_, lean_object* v_inst_597_, lean_object* v_f_598_, lean_object* v_e_599_){
_start:
{
lean_object* v_toApplicative_600_; lean_object* v_toBind_601_; lean_object* v_toPure_602_; lean_object* v___x_603_; lean_object* v___f_604_; lean_object* v___x_605_; lean_object* v___f_606_; lean_object* v_args_608_; lean_object* v___x_613_; lean_object* v___f_614_; lean_object* v_fvarId_616_; 
v_toApplicative_600_ = lean_ctor_get(v_inst_597_, 0);
v_toBind_601_ = lean_ctor_get(v_inst_597_, 1);
lean_inc(v_toBind_601_);
v_toPure_602_ = lean_ctor_get(v_toApplicative_600_, 1);
v___x_603_ = lean_box(v_pu_596_);
lean_inc(v_f_598_);
lean_inc_ref(v_inst_597_);
v___f_604_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_604_, 0, v___x_603_);
lean_closure_set(v___f_604_, 1, v_inst_597_);
lean_closure_set(v___f_604_, 2, v_f_598_);
v___x_605_ = lean_box(v_pu_596_);
lean_inc_n(v_toPure_602_, 2);
lean_inc_n(v_e_599_, 2);
v___f_606_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_606_, 0, v___x_605_);
lean_closure_set(v___f_606_, 1, v_e_599_);
lean_closure_set(v___f_606_, 2, v_toPure_602_);
v___x_613_ = lean_box(v_pu_596_);
v___f_614_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_614_, 0, v___x_613_);
lean_closure_set(v___f_614_, 1, v_e_599_);
lean_closure_set(v___f_614_, 2, v_toPure_602_);
switch(lean_obj_tag(v_e_599_))
{
case 2:
{
lean_object* v_struct_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec_ref(v___f_606_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v_inst_597_);
v_struct_619_ = lean_ctor_get(v_e_599_, 2);
lean_inc(v_struct_619_);
lean_dec_ref_known(v_e_599_, 3);
v___x_620_ = lean_apply_1(v_f_598_, v_struct_619_);
v___x_621_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_620_, v___f_614_);
return v___x_621_;
}
case 3:
{
lean_object* v_args_622_; size_t v_sz_623_; size_t v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec_ref(v___f_614_);
lean_dec(v_f_598_);
v_args_622_ = lean_ctor_get(v_e_599_, 2);
lean_inc_ref(v_args_622_);
lean_dec_ref_known(v_e_599_, 3);
v_sz_623_ = lean_array_size(v_args_622_);
v___x_624_ = ((size_t)0ULL);
v___x_625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_597_, v___f_604_, v_sz_623_, v___x_624_, v_args_622_);
v___x_626_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_625_, v___f_606_);
return v___x_626_;
}
case 4:
{
lean_object* v_fvarId_627_; lean_object* v_args_628_; lean_object* v___x_629_; lean_object* v___f_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
lean_inc(v_toPure_602_);
lean_dec_ref(v___f_614_);
lean_dec_ref(v___f_606_);
v_fvarId_627_ = lean_ctor_get(v_e_599_, 0);
lean_inc(v_fvarId_627_);
v_args_628_ = lean_ctor_get(v_e_599_, 1);
lean_inc_ref(v_args_628_);
v___x_629_ = lean_box(v_pu_596_);
lean_inc(v_toBind_601_);
v___f_630_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_630_, 0, v___x_629_);
lean_closure_set(v___f_630_, 1, v_e_599_);
lean_closure_set(v___f_630_, 2, v_toPure_602_);
lean_closure_set(v___f_630_, 3, v_args_628_);
lean_closure_set(v___f_630_, 4, v_inst_597_);
lean_closure_set(v___f_630_, 5, v___f_604_);
lean_closure_set(v___f_630_, 6, v_toBind_601_);
v___x_631_ = lean_apply_1(v_f_598_, v_fvarId_627_);
v___x_632_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_631_, v___f_630_);
return v___x_632_;
}
case 5:
{
lean_object* v_args_633_; size_t v_sz_634_; size_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
lean_dec_ref(v___f_614_);
lean_dec(v_f_598_);
v_args_633_ = lean_ctor_get(v_e_599_, 1);
lean_inc_ref(v_args_633_);
lean_dec_ref_known(v_e_599_, 2);
v_sz_634_ = lean_array_size(v_args_633_);
v___x_635_ = ((size_t)0ULL);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_597_, v___f_604_, v_sz_634_, v___x_635_, v_args_633_);
v___x_637_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_636_, v___f_606_);
return v___x_637_;
}
case 6:
{
lean_object* v_var_638_; 
lean_dec_ref(v___f_606_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v_inst_597_);
v_var_638_ = lean_ctor_get(v_e_599_, 1);
lean_inc(v_var_638_);
lean_dec_ref_known(v_e_599_, 2);
v_fvarId_616_ = v_var_638_;
goto v___jp_615_;
}
case 7:
{
lean_object* v_var_639_; 
lean_dec_ref(v___f_606_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v_inst_597_);
v_var_639_ = lean_ctor_get(v_e_599_, 1);
lean_inc(v_var_639_);
lean_dec_ref_known(v_e_599_, 2);
v_fvarId_616_ = v_var_639_;
goto v___jp_615_;
}
case 8:
{
lean_object* v_var_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
lean_dec_ref(v___f_606_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v_inst_597_);
v_var_640_ = lean_ctor_get(v_e_599_, 2);
lean_inc(v_var_640_);
lean_dec_ref_known(v_e_599_, 3);
v___x_641_ = lean_apply_1(v_f_598_, v_var_640_);
v___x_642_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_641_, v___f_614_);
return v___x_642_;
}
case 9:
{
lean_object* v_args_643_; 
lean_dec_ref(v___f_614_);
lean_dec(v_f_598_);
v_args_643_ = lean_ctor_get(v_e_599_, 1);
lean_inc_ref(v_args_643_);
lean_dec_ref_known(v_e_599_, 2);
v_args_608_ = v_args_643_;
goto v___jp_607_;
}
case 10:
{
lean_object* v_args_644_; 
lean_dec_ref(v___f_614_);
lean_dec(v_f_598_);
v_args_644_ = lean_ctor_get(v_e_599_, 1);
lean_inc_ref(v_args_644_);
lean_dec_ref_known(v_e_599_, 2);
v_args_608_ = v_args_644_;
goto v___jp_607_;
}
case 11:
{
lean_object* v_n_645_; lean_object* v_var_646_; lean_object* v___x_647_; lean_object* v___f_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
lean_inc(v_toPure_602_);
lean_dec_ref(v___f_614_);
lean_dec_ref(v___f_606_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v_inst_597_);
v_n_645_ = lean_ctor_get(v_e_599_, 0);
lean_inc(v_n_645_);
v_var_646_ = lean_ctor_get(v_e_599_, 1);
lean_inc(v_var_646_);
v___x_647_ = lean_box(v_pu_596_);
v___f_648_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_648_, 0, v___x_647_);
lean_closure_set(v___f_648_, 1, v_e_599_);
lean_closure_set(v___f_648_, 2, v_n_645_);
lean_closure_set(v___f_648_, 3, v_toPure_602_);
v___x_649_ = lean_apply_1(v_f_598_, v_var_646_);
v___x_650_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_649_, v___f_648_);
return v___x_650_;
}
case 12:
{
lean_object* v_var_651_; lean_object* v_i_652_; uint8_t v_updateHeader_653_; lean_object* v_args_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___f_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
lean_inc(v_toPure_602_);
lean_dec_ref(v___f_614_);
lean_dec_ref(v___f_606_);
v_var_651_ = lean_ctor_get(v_e_599_, 0);
lean_inc(v_var_651_);
v_i_652_ = lean_ctor_get(v_e_599_, 1);
lean_inc_ref(v_i_652_);
v_updateHeader_653_ = lean_ctor_get_uint8(v_e_599_, sizeof(void*)*3);
v_args_654_ = lean_ctor_get(v_e_599_, 2);
lean_inc_ref(v_args_654_);
v___x_655_ = lean_box(v_pu_596_);
v___x_656_ = lean_box(v_updateHeader_653_);
lean_inc(v_toBind_601_);
v___f_657_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_657_, 0, v___x_655_);
lean_closure_set(v___f_657_, 1, v_e_599_);
lean_closure_set(v___f_657_, 2, v_i_652_);
lean_closure_set(v___f_657_, 3, v___x_656_);
lean_closure_set(v___f_657_, 4, v_toPure_602_);
lean_closure_set(v___f_657_, 5, v_args_654_);
lean_closure_set(v___f_657_, 6, v_inst_597_);
lean_closure_set(v___f_657_, 7, v___f_604_);
lean_closure_set(v___f_657_, 8, v_toBind_601_);
v___x_658_ = lean_apply_1(v_f_598_, v_var_651_);
v___x_659_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_658_, v___f_657_);
return v___x_659_;
}
case 13:
{
lean_object* v_ty_660_; lean_object* v_fvarId_661_; lean_object* v___x_662_; lean_object* v___f_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
lean_inc(v_toPure_602_);
lean_dec_ref(v___f_614_);
lean_dec_ref(v___f_606_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v_inst_597_);
v_ty_660_ = lean_ctor_get(v_e_599_, 0);
lean_inc_ref(v_ty_660_);
v_fvarId_661_ = lean_ctor_get(v_e_599_, 1);
lean_inc(v_fvarId_661_);
v___x_662_ = lean_box(v_pu_596_);
v___f_663_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6___boxed), 5, 4);
lean_closure_set(v___f_663_, 0, v___x_662_);
lean_closure_set(v___f_663_, 1, v_e_599_);
lean_closure_set(v___f_663_, 2, v_ty_660_);
lean_closure_set(v___f_663_, 3, v_toPure_602_);
v___x_664_ = lean_apply_1(v_f_598_, v_fvarId_661_);
v___x_665_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_664_, v___f_663_);
return v___x_665_;
}
case 14:
{
lean_object* v_fvarId_666_; lean_object* v___x_667_; lean_object* v___f_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
lean_inc(v_toPure_602_);
lean_dec_ref(v___f_614_);
lean_dec_ref(v___f_606_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v_inst_597_);
v_fvarId_666_ = lean_ctor_get(v_e_599_, 0);
lean_inc(v_fvarId_666_);
v___x_667_ = lean_box(v_pu_596_);
v___f_668_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9___boxed), 4, 3);
lean_closure_set(v___f_668_, 0, v___x_667_);
lean_closure_set(v___f_668_, 1, v_e_599_);
lean_closure_set(v___f_668_, 2, v_toPure_602_);
v___x_669_ = lean_apply_1(v_f_598_, v_fvarId_666_);
v___x_670_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_669_, v___f_668_);
return v___x_670_;
}
case 15:
{
lean_object* v_fvarId_671_; lean_object* v___x_672_; lean_object* v___f_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
lean_inc(v_toPure_602_);
lean_dec_ref(v___f_614_);
lean_dec_ref(v___f_606_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v_inst_597_);
v_fvarId_671_ = lean_ctor_get(v_e_599_, 0);
lean_inc(v_fvarId_671_);
v___x_672_ = lean_box(v_pu_596_);
v___f_673_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10___boxed), 4, 3);
lean_closure_set(v___f_673_, 0, v___x_672_);
lean_closure_set(v___f_673_, 1, v_e_599_);
lean_closure_set(v___f_673_, 2, v_toPure_602_);
v___x_674_ = lean_apply_1(v_f_598_, v_fvarId_671_);
v___x_675_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_674_, v___f_673_);
return v___x_675_;
}
default: 
{
lean_object* v___x_676_; 
lean_inc(v_toPure_602_);
lean_dec_ref(v___f_614_);
lean_dec_ref(v___f_606_);
lean_dec_ref(v___f_604_);
lean_dec(v_toBind_601_);
lean_dec(v_f_598_);
lean_dec_ref(v_inst_597_);
v___x_676_ = lean_apply_2(v_toPure_602_, lean_box(0), v_e_599_);
return v___x_676_;
}
}
v___jp_607_:
{
size_t v_sz_609_; size_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_sz_609_ = lean_array_size(v_args_608_);
v___x_610_ = ((size_t)0ULL);
v___x_611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_597_, v___f_604_, v_sz_609_, v___x_610_, v_args_608_);
v___x_612_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_611_, v___f_606_);
return v___x_612_;
}
v___jp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_apply_1(v_f_598_, v_fvarId_616_);
v___x_618_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_617_, v___f_614_);
return v___x_618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___boxed(lean_object* v_pu_677_, lean_object* v_inst_678_, lean_object* v_f_679_, lean_object* v_e_680_){
_start:
{
uint8_t v_pu_boxed_681_; lean_object* v_res_682_; 
v_pu_boxed_681_ = lean_unbox(v_pu_677_);
v_res_682_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_boxed_681_, v_inst_678_, v_f_679_, v_e_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM(lean_object* v_m_683_, uint8_t v_pu_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_f_687_, lean_object* v_e_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_684_, v_inst_686_, v_f_687_, v_e_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___boxed(lean_object* v_m_690_, lean_object* v_pu_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_f_694_, lean_object* v_e_695_){
_start:
{
uint8_t v_pu_boxed_696_; lean_object* v_res_697_; 
v_pu_boxed_696_ = lean_unbox(v_pu_691_);
v_res_697_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM(v_m_690_, v_pu_boxed_696_, v_inst_692_, v_inst_693_, v_f_694_, v_e_695_);
lean_dec(v_inst_692_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0(lean_object* v_inst_698_, lean_object* v_f_699_, lean_object* v_x_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_698_, v_f_699_, v___y_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3(lean_object* v_args_703_, lean_object* v_toPure_704_, lean_object* v_inst_705_, lean_object* v___f_706_, lean_object* v_____r_707_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_array_get_size(v_args_703_);
v___x_710_ = lean_box(0);
v___x_711_ = lean_nat_dec_lt(v___x_708_, v___x_709_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; 
lean_dec(v___f_706_);
lean_dec_ref(v_inst_705_);
lean_dec_ref(v_args_703_);
v___x_712_ = lean_apply_2(v_toPure_704_, lean_box(0), v___x_710_);
return v___x_712_;
}
else
{
uint8_t v___x_713_; 
v___x_713_ = lean_nat_dec_le(v___x_709_, v___x_709_);
if (v___x_713_ == 0)
{
if (v___x_711_ == 0)
{
lean_object* v___x_714_; 
lean_dec(v___f_706_);
lean_dec_ref(v_inst_705_);
lean_dec_ref(v_args_703_);
v___x_714_ = lean_apply_2(v_toPure_704_, lean_box(0), v___x_710_);
return v___x_714_;
}
else
{
size_t v___x_715_; size_t v___x_716_; lean_object* v___x_717_; 
lean_dec(v_toPure_704_);
v___x_715_ = ((size_t)0ULL);
v___x_716_ = lean_usize_of_nat(v___x_709_);
v___x_717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_705_, v___f_706_, v_args_703_, v___x_715_, v___x_716_, v___x_710_);
return v___x_717_;
}
}
else
{
size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; 
lean_dec(v_toPure_704_);
v___x_718_ = ((size_t)0ULL);
v___x_719_ = lean_usize_of_nat(v___x_709_);
v___x_720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_705_, v___f_706_, v_args_703_, v___x_718_, v___x_719_, v___x_710_);
return v___x_720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(lean_object* v_inst_721_, lean_object* v_f_722_, lean_object* v_e_723_){
_start:
{
lean_object* v_toApplicative_724_; lean_object* v_toBind_725_; lean_object* v_toPure_726_; lean_object* v___f_727_; lean_object* v_args_729_; 
v_toApplicative_724_ = lean_ctor_get(v_inst_721_, 0);
v_toBind_725_ = lean_ctor_get(v_inst_721_, 1);
v_toPure_726_ = lean_ctor_get(v_toApplicative_724_, 1);
lean_inc(v_f_722_);
lean_inc_ref(v_inst_721_);
v___f_727_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_727_, 0, v_inst_721_);
lean_closure_set(v___f_727_, 1, v_f_722_);
switch(lean_obj_tag(v_e_723_))
{
case 2:
{
lean_object* v_struct_743_; lean_object* v___x_744_; 
lean_dec_ref(v___f_727_);
lean_dec_ref(v_inst_721_);
v_struct_743_ = lean_ctor_get(v_e_723_, 2);
lean_inc(v_struct_743_);
lean_dec_ref_known(v_e_723_, 3);
v___x_744_ = lean_apply_1(v_f_722_, v_struct_743_);
return v___x_744_;
}
case 3:
{
lean_object* v_args_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
lean_dec(v_f_722_);
v_args_745_ = lean_ctor_get(v_e_723_, 2);
lean_inc_ref(v_args_745_);
lean_dec_ref_known(v_e_723_, 3);
v___x_746_ = lean_unsigned_to_nat(0u);
v___x_747_ = lean_array_get_size(v_args_745_);
v___x_748_ = lean_box(0);
v___x_749_ = lean_nat_dec_lt(v___x_746_, v___x_747_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
lean_inc(v_toPure_726_);
lean_dec_ref(v_args_745_);
lean_dec_ref(v___f_727_);
lean_dec_ref(v_inst_721_);
v___x_750_ = lean_apply_2(v_toPure_726_, lean_box(0), v___x_748_);
return v___x_750_;
}
else
{
uint8_t v___x_751_; 
v___x_751_ = lean_nat_dec_le(v___x_747_, v___x_747_);
if (v___x_751_ == 0)
{
if (v___x_749_ == 0)
{
lean_object* v___x_752_; 
lean_inc(v_toPure_726_);
lean_dec_ref(v_args_745_);
lean_dec_ref(v___f_727_);
lean_dec_ref(v_inst_721_);
v___x_752_ = lean_apply_2(v_toPure_726_, lean_box(0), v___x_748_);
return v___x_752_;
}
else
{
size_t v___x_753_; size_t v___x_754_; lean_object* v___x_755_; 
v___x_753_ = ((size_t)0ULL);
v___x_754_ = lean_usize_of_nat(v___x_747_);
v___x_755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_721_, v___f_727_, v_args_745_, v___x_753_, v___x_754_, v___x_748_);
return v___x_755_;
}
}
else
{
size_t v___x_756_; size_t v___x_757_; lean_object* v___x_758_; 
v___x_756_ = ((size_t)0ULL);
v___x_757_ = lean_usize_of_nat(v___x_747_);
v___x_758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_721_, v___f_727_, v_args_745_, v___x_756_, v___x_757_, v___x_748_);
return v___x_758_;
}
}
}
case 4:
{
lean_object* v_fvarId_759_; lean_object* v_args_760_; lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
lean_inc(v_toPure_726_);
lean_inc(v_toBind_725_);
v_fvarId_759_ = lean_ctor_get(v_e_723_, 0);
lean_inc(v_fvarId_759_);
v_args_760_ = lean_ctor_get(v_e_723_, 1);
lean_inc_ref(v_args_760_);
lean_dec_ref_known(v_e_723_, 2);
v___f_761_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3), 5, 4);
lean_closure_set(v___f_761_, 0, v_args_760_);
lean_closure_set(v___f_761_, 1, v_toPure_726_);
lean_closure_set(v___f_761_, 2, v_inst_721_);
lean_closure_set(v___f_761_, 3, v___f_727_);
v___x_762_ = lean_apply_1(v_f_722_, v_fvarId_759_);
v___x_763_ = lean_apply_4(v_toBind_725_, lean_box(0), lean_box(0), v___x_762_, v___f_761_);
return v___x_763_;
}
case 5:
{
lean_object* v_args_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
lean_dec(v_f_722_);
v_args_764_ = lean_ctor_get(v_e_723_, 1);
lean_inc_ref(v_args_764_);
lean_dec_ref_known(v_e_723_, 2);
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = lean_array_get_size(v_args_764_);
v___x_767_ = lean_box(0);
v___x_768_ = lean_nat_dec_lt(v___x_765_, v___x_766_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
lean_inc(v_toPure_726_);
lean_dec_ref(v_args_764_);
lean_dec_ref(v___f_727_);
lean_dec_ref(v_inst_721_);
v___x_769_ = lean_apply_2(v_toPure_726_, lean_box(0), v___x_767_);
return v___x_769_;
}
else
{
uint8_t v___x_770_; 
v___x_770_ = lean_nat_dec_le(v___x_766_, v___x_766_);
if (v___x_770_ == 0)
{
if (v___x_768_ == 0)
{
lean_object* v___x_771_; 
lean_inc(v_toPure_726_);
lean_dec_ref(v_args_764_);
lean_dec_ref(v___f_727_);
lean_dec_ref(v_inst_721_);
v___x_771_ = lean_apply_2(v_toPure_726_, lean_box(0), v___x_767_);
return v___x_771_;
}
else
{
size_t v___x_772_; size_t v___x_773_; lean_object* v___x_774_; 
v___x_772_ = ((size_t)0ULL);
v___x_773_ = lean_usize_of_nat(v___x_766_);
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_721_, v___f_727_, v_args_764_, v___x_772_, v___x_773_, v___x_767_);
return v___x_774_;
}
}
else
{
size_t v___x_775_; size_t v___x_776_; lean_object* v___x_777_; 
v___x_775_ = ((size_t)0ULL);
v___x_776_ = lean_usize_of_nat(v___x_766_);
v___x_777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_721_, v___f_727_, v_args_764_, v___x_775_, v___x_776_, v___x_767_);
return v___x_777_;
}
}
}
case 6:
{
lean_object* v_var_778_; lean_object* v___x_779_; 
lean_dec_ref(v___f_727_);
lean_dec_ref(v_inst_721_);
v_var_778_ = lean_ctor_get(v_e_723_, 1);
lean_inc(v_var_778_);
lean_dec_ref_known(v_e_723_, 2);
v___x_779_ = lean_apply_1(v_f_722_, v_var_778_);
return v___x_779_;
}
case 7:
{
lean_object* v_var_780_; lean_object* v___x_781_; 
lean_dec_ref(v___f_727_);
lean_dec_ref(v_inst_721_);
v_var_780_ = lean_ctor_get(v_e_723_, 1);
lean_inc(v_var_780_);
lean_dec_ref_known(v_e_723_, 2);
v___x_781_ = lean_apply_1(v_f_722_, v_var_780_);
return v___x_781_;
}
case 8:
{
lean_object* v_var_782_; lean_object* v___x_783_; 
lean_dec_ref(v___f_727_);
lean_dec_ref(v_inst_721_);
v_var_782_ = lean_ctor_get(v_e_723_, 2);
lean_inc(v_var_782_);
lean_dec_ref_known(v_e_723_, 3);
v___x_783_ = lean_apply_1(v_f_722_, v_var_782_);
return v___x_783_;
}
case 9:
{
lean_object* v_args_784_; 
lean_dec(v_f_722_);
v_args_784_ = lean_ctor_get(v_e_723_, 1);
lean_inc_ref(v_args_784_);
lean_dec_ref_known(v_e_723_, 2);
v_args_729_ = v_args_784_;
goto v___jp_728_;
}
case 10:
{
lean_object* v_args_785_; 
lean_dec(v_f_722_);
v_args_785_ = lean_ctor_get(v_e_723_, 1);
lean_inc_ref(v_args_785_);
lean_dec_ref_known(v_e_723_, 2);
v_args_729_ = v_args_785_;
goto v___jp_728_;
}
case 11:
{
lean_object* v_var_786_; lean_object* v___x_787_; 
lean_dec_ref(v___f_727_);
lean_dec_ref(v_inst_721_);
v_var_786_ = lean_ctor_get(v_e_723_, 1);
lean_inc(v_var_786_);
lean_dec_ref_known(v_e_723_, 2);
v___x_787_ = lean_apply_1(v_f_722_, v_var_786_);
return v___x_787_;
}
case 12:
{
lean_object* v_var_788_; lean_object* v_args_789_; lean_object* v___f_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
lean_inc(v_toPure_726_);
lean_inc(v_toBind_725_);
v_var_788_ = lean_ctor_get(v_e_723_, 0);
lean_inc(v_var_788_);
v_args_789_ = lean_ctor_get(v_e_723_, 2);
lean_inc_ref(v_args_789_);
lean_dec_ref_known(v_e_723_, 3);
v___f_790_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3), 5, 4);
lean_closure_set(v___f_790_, 0, v_args_789_);
lean_closure_set(v___f_790_, 1, v_toPure_726_);
lean_closure_set(v___f_790_, 2, v_inst_721_);
lean_closure_set(v___f_790_, 3, v___f_727_);
v___x_791_ = lean_apply_1(v_f_722_, v_var_788_);
v___x_792_ = lean_apply_4(v_toBind_725_, lean_box(0), lean_box(0), v___x_791_, v___f_790_);
return v___x_792_;
}
case 13:
{
lean_object* v_fvarId_793_; lean_object* v___x_794_; 
lean_dec_ref(v___f_727_);
lean_dec_ref(v_inst_721_);
v_fvarId_793_ = lean_ctor_get(v_e_723_, 1);
lean_inc(v_fvarId_793_);
lean_dec_ref_known(v_e_723_, 2);
v___x_794_ = lean_apply_1(v_f_722_, v_fvarId_793_);
return v___x_794_;
}
case 14:
{
lean_object* v_fvarId_795_; lean_object* v___x_796_; 
lean_dec_ref(v___f_727_);
lean_dec_ref(v_inst_721_);
v_fvarId_795_ = lean_ctor_get(v_e_723_, 0);
lean_inc(v_fvarId_795_);
lean_dec_ref_known(v_e_723_, 1);
v___x_796_ = lean_apply_1(v_f_722_, v_fvarId_795_);
return v___x_796_;
}
case 15:
{
lean_object* v_fvarId_797_; lean_object* v___x_798_; 
lean_dec_ref(v___f_727_);
lean_dec_ref(v_inst_721_);
v_fvarId_797_ = lean_ctor_get(v_e_723_, 0);
lean_inc(v_fvarId_797_);
lean_dec_ref_known(v_e_723_, 1);
v___x_798_ = lean_apply_1(v_f_722_, v_fvarId_797_);
return v___x_798_;
}
default: 
{
lean_object* v___x_799_; lean_object* v___x_800_; 
lean_inc(v_toPure_726_);
lean_dec_ref(v___f_727_);
lean_dec(v_e_723_);
lean_dec(v_f_722_);
lean_dec_ref(v_inst_721_);
v___x_799_ = lean_box(0);
v___x_800_ = lean_apply_2(v_toPure_726_, lean_box(0), v___x_799_);
return v___x_800_;
}
}
v___jp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_730_ = lean_unsigned_to_nat(0u);
v___x_731_ = lean_array_get_size(v_args_729_);
v___x_732_ = lean_box(0);
v___x_733_ = lean_nat_dec_lt(v___x_730_, v___x_731_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; 
lean_inc(v_toPure_726_);
lean_dec_ref(v_args_729_);
lean_dec_ref(v___f_727_);
lean_dec_ref(v_inst_721_);
v___x_734_ = lean_apply_2(v_toPure_726_, lean_box(0), v___x_732_);
return v___x_734_;
}
else
{
uint8_t v___x_735_; 
v___x_735_ = lean_nat_dec_le(v___x_731_, v___x_731_);
if (v___x_735_ == 0)
{
if (v___x_733_ == 0)
{
lean_object* v___x_736_; 
lean_inc(v_toPure_726_);
lean_dec_ref(v_args_729_);
lean_dec_ref(v___f_727_);
lean_dec_ref(v_inst_721_);
v___x_736_ = lean_apply_2(v_toPure_726_, lean_box(0), v___x_732_);
return v___x_736_;
}
else
{
size_t v___x_737_; size_t v___x_738_; lean_object* v___x_739_; 
v___x_737_ = ((size_t)0ULL);
v___x_738_ = lean_usize_of_nat(v___x_731_);
v___x_739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_721_, v___f_727_, v_args_729_, v___x_737_, v___x_738_, v___x_732_);
return v___x_739_;
}
}
else
{
size_t v___x_740_; size_t v___x_741_; lean_object* v___x_742_; 
v___x_740_ = ((size_t)0ULL);
v___x_741_ = lean_usize_of_nat(v___x_731_);
v___x_742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_721_, v___f_727_, v_args_729_, v___x_740_, v___x_741_, v___x_732_);
return v___x_742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM(lean_object* v_m_801_, uint8_t v_pu_802_, lean_object* v_inst_803_, lean_object* v_f_804_, lean_object* v_e_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_803_, v_f_804_, v_e_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___boxed(lean_object* v_m_807_, lean_object* v_pu_808_, lean_object* v_inst_809_, lean_object* v_f_810_, lean_object* v_e_811_){
_start:
{
uint8_t v_pu_boxed_812_; lean_object* v_res_813_; 
v_pu_boxed_812_ = lean_unbox(v_pu_808_);
v_res_813_ = l_Lean_Compiler_LCNF_LetValue_forFVarM(v_m_807_, v_pu_boxed_812_, v_inst_809_, v_f_810_, v_e_811_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(uint8_t v_pu_814_, lean_object* v_m_815_, lean_object* v_inst_816_, lean_object* v_inst_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_814_, v_inst_817_, v___y_818_, v___y_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0___boxed(lean_object* v_pu_821_, lean_object* v_m_822_, lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
uint8_t v_pu_boxed_827_; lean_object* v_res_828_; 
v_pu_boxed_827_ = lean_unbox(v_pu_821_);
v_res_828_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(v_pu_boxed_827_, v_m_822_, v_inst_823_, v_inst_824_, v___y_825_, v___y_826_);
lean_dec(v_inst_823_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__1(lean_object* v_m_829_, lean_object* v_inst_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_830_, v___y_831_, v___y_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue(uint8_t v_pu_835_){
_start:
{
lean_object* v___x_836_; lean_object* v___f_837_; lean_object* v___f_838_; lean_object* v___x_839_; 
v___x_836_ = lean_box(v_pu_835_);
v___f_837_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0___boxed), 6, 1);
lean_closure_set(v___f_837_, 0, v___x_836_);
v___f_838_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarLetValue___closed__0));
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v___f_837_);
lean_ctor_set(v___x_839_, 1, v___f_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___boxed(lean_object* v_pu_840_){
_start:
{
uint8_t v_pu_boxed_841_; lean_object* v_res_842_; 
v_pu_boxed_841_ = lean_unbox(v_pu_840_);
v_res_842_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue(v_pu_boxed_841_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(uint8_t v_pu_843_, lean_object* v_decl_844_, lean_object* v_____do__lift_845_, lean_object* v_inst_846_, lean_object* v_____do__lift_847_){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_848_ = lean_box(v_pu_843_);
v___x_849_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_849_, 0, v___x_848_);
lean_closure_set(v___x_849_, 1, v_decl_844_);
lean_closure_set(v___x_849_, 2, v_____do__lift_845_);
lean_closure_set(v___x_849_, 3, v_____do__lift_847_);
v___x_850_ = lean_apply_2(v_inst_846_, lean_box(0), v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_851_, lean_object* v_decl_852_, lean_object* v_____do__lift_853_, lean_object* v_inst_854_, lean_object* v_____do__lift_855_){
_start:
{
uint8_t v_pu_boxed_856_; lean_object* v_res_857_; 
v_pu_boxed_856_ = lean_unbox(v_pu_851_);
v_res_857_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(v_pu_boxed_856_, v_decl_852_, v_____do__lift_853_, v_inst_854_, v_____do__lift_855_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(uint8_t v_pu_858_, lean_object* v_decl_859_, lean_object* v_inst_860_, lean_object* v_inst_861_, lean_object* v_f_862_, lean_object* v_value_863_, lean_object* v_toBind_864_, lean_object* v_____do__lift_865_){
_start:
{
lean_object* v___x_866_; lean_object* v___f_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_866_ = lean_box(v_pu_858_);
v___f_867_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_867_, 0, v___x_866_);
lean_closure_set(v___f_867_, 1, v_decl_859_);
lean_closure_set(v___f_867_, 2, v_____do__lift_865_);
lean_closure_set(v___f_867_, 3, v_inst_860_);
v___x_868_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(v_pu_858_, v_inst_861_, v_f_862_, v_value_863_);
v___x_869_ = lean_apply_4(v_toBind_864_, lean_box(0), lean_box(0), v___x_868_, v___f_867_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1___boxed(lean_object* v_pu_870_, lean_object* v_decl_871_, lean_object* v_inst_872_, lean_object* v_inst_873_, lean_object* v_f_874_, lean_object* v_value_875_, lean_object* v_toBind_876_, lean_object* v_____do__lift_877_){
_start:
{
uint8_t v_pu_boxed_878_; lean_object* v_res_879_; 
v_pu_boxed_878_ = lean_unbox(v_pu_870_);
v_res_879_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(v_pu_boxed_878_, v_decl_871_, v_inst_872_, v_inst_873_, v_f_874_, v_value_875_, v_toBind_876_, v_____do__lift_877_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(uint8_t v_pu_880_, lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_f_883_, lean_object* v_decl_884_){
_start:
{
lean_object* v_toBind_885_; lean_object* v_type_886_; lean_object* v_value_887_; lean_object* v___x_888_; lean_object* v___f_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_toBind_885_ = lean_ctor_get(v_inst_882_, 1);
lean_inc_n(v_toBind_885_, 2);
v_type_886_ = lean_ctor_get(v_decl_884_, 2);
lean_inc_ref(v_type_886_);
v_value_887_ = lean_ctor_get(v_decl_884_, 3);
lean_inc(v_value_887_);
v___x_888_ = lean_box(v_pu_880_);
lean_inc(v_f_883_);
lean_inc_ref(v_inst_882_);
v___f_889_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_889_, 0, v___x_888_);
lean_closure_set(v___f_889_, 1, v_decl_884_);
lean_closure_set(v___f_889_, 2, v_inst_881_);
lean_closure_set(v___f_889_, 3, v_inst_882_);
lean_closure_set(v___f_889_, 4, v_f_883_);
lean_closure_set(v___f_889_, 5, v_value_887_);
lean_closure_set(v___f_889_, 6, v_toBind_885_);
v___x_890_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_882_, v_f_883_, v_type_886_);
v___x_891_ = lean_apply_4(v_toBind_885_, lean_box(0), lean_box(0), v___x_890_, v___f_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___boxed(lean_object* v_pu_892_, lean_object* v_inst_893_, lean_object* v_inst_894_, lean_object* v_f_895_, lean_object* v_decl_896_){
_start:
{
uint8_t v_pu_boxed_897_; lean_object* v_res_898_; 
v_pu_boxed_897_ = lean_unbox(v_pu_892_);
v_res_898_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_boxed_897_, v_inst_893_, v_inst_894_, v_f_895_, v_decl_896_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM(lean_object* v_m_899_, uint8_t v_pu_900_, lean_object* v_inst_901_, lean_object* v_inst_902_, lean_object* v_f_903_, lean_object* v_decl_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_900_, v_inst_901_, v_inst_902_, v_f_903_, v_decl_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___boxed(lean_object* v_m_906_, lean_object* v_pu_907_, lean_object* v_inst_908_, lean_object* v_inst_909_, lean_object* v_f_910_, lean_object* v_decl_911_){
_start:
{
uint8_t v_pu_boxed_912_; lean_object* v_res_913_; 
v_pu_boxed_912_ = lean_unbox(v_pu_907_);
v_res_913_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM(v_m_906_, v_pu_boxed_912_, v_inst_908_, v_inst_909_, v_f_910_, v_decl_911_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg___lam__0(lean_object* v_inst_914_, lean_object* v_f_915_, lean_object* v_value_916_, lean_object* v_____r_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_914_, v_f_915_, v_value_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(lean_object* v_inst_919_, lean_object* v_f_920_, lean_object* v_decl_921_){
_start:
{
lean_object* v_toBind_922_; lean_object* v_type_923_; lean_object* v_value_924_; lean_object* v___f_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_toBind_922_ = lean_ctor_get(v_inst_919_, 1);
lean_inc(v_toBind_922_);
v_type_923_ = lean_ctor_get(v_decl_921_, 2);
lean_inc_ref(v_type_923_);
v_value_924_ = lean_ctor_get(v_decl_921_, 3);
lean_inc(v_value_924_);
lean_dec_ref(v_decl_921_);
lean_inc(v_f_920_);
lean_inc_ref(v_inst_919_);
v___f_925_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_925_, 0, v_inst_919_);
lean_closure_set(v___f_925_, 1, v_f_920_);
lean_closure_set(v___f_925_, 2, v_value_924_);
v___x_926_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_919_, v_f_920_, v_type_923_);
v___x_927_ = lean_apply_4(v_toBind_922_, lean_box(0), lean_box(0), v___x_926_, v___f_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM(lean_object* v_m_928_, uint8_t v_pu_929_, lean_object* v_inst_930_, lean_object* v_f_931_, lean_object* v_decl_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_930_, v_f_931_, v_decl_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___boxed(lean_object* v_m_934_, lean_object* v_pu_935_, lean_object* v_inst_936_, lean_object* v_f_937_, lean_object* v_decl_938_){
_start:
{
uint8_t v_pu_boxed_939_; lean_object* v_res_940_; 
v_pu_boxed_939_ = lean_unbox(v_pu_935_);
v_res_940_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM(v_m_934_, v_pu_boxed_939_, v_inst_936_, v_f_937_, v_decl_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(uint8_t v_pu_941_, lean_object* v_m_942_, lean_object* v_inst_943_, lean_object* v_inst_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_941_, v_inst_943_, v_inst_944_, v___y_945_, v___y_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0___boxed(lean_object* v_pu_948_, lean_object* v_m_949_, lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
uint8_t v_pu_boxed_954_; lean_object* v_res_955_; 
v_pu_boxed_954_ = lean_unbox(v_pu_948_);
v_res_955_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(v_pu_boxed_954_, v_m_949_, v_inst_950_, v_inst_951_, v___y_952_, v___y_953_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__1(lean_object* v_m_956_, lean_object* v_inst_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_957_, v___y_958_, v___y_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(uint8_t v_pu_962_){
_start:
{
lean_object* v___x_963_; lean_object* v___f_964_; lean_object* v___f_965_; lean_object* v___x_966_; 
v___x_963_ = lean_box(v_pu_962_);
v___f_964_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0___boxed), 6, 1);
lean_closure_set(v___f_964_, 0, v___x_963_);
v___f_965_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___closed__0));
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v___f_964_);
lean_ctor_set(v___x_966_, 1, v___f_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___boxed(lean_object* v_pu_967_){
_start:
{
uint8_t v_pu_boxed_968_; lean_object* v_res_969_; 
v_pu_boxed_968_ = lean_unbox(v_pu_967_);
v_res_969_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(v_pu_boxed_968_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(uint8_t v_pu_970_, lean_object* v_param_971_, lean_object* v_inst_972_, lean_object* v_____do__lift_973_){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = lean_box(v_pu_970_);
v___x_975_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_975_, 0, v___x_974_);
lean_closure_set(v___x_975_, 1, v_param_971_);
lean_closure_set(v___x_975_, 2, v_____do__lift_973_);
v___x_976_ = lean_apply_2(v_inst_972_, lean_box(0), v___x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_977_, lean_object* v_param_978_, lean_object* v_inst_979_, lean_object* v_____do__lift_980_){
_start:
{
uint8_t v_pu_boxed_981_; lean_object* v_res_982_; 
v_pu_boxed_981_ = lean_unbox(v_pu_977_);
v_res_982_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(v_pu_boxed_981_, v_param_978_, v_inst_979_, v_____do__lift_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(uint8_t v_pu_983_, lean_object* v_inst_984_, lean_object* v_inst_985_, lean_object* v_f_986_, lean_object* v_param_987_){
_start:
{
lean_object* v_toBind_988_; lean_object* v_type_989_; lean_object* v___x_990_; lean_object* v___f_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_toBind_988_ = lean_ctor_get(v_inst_985_, 1);
lean_inc(v_toBind_988_);
v_type_989_ = lean_ctor_get(v_param_987_, 2);
lean_inc_ref(v_type_989_);
v___x_990_ = lean_box(v_pu_983_);
v___f_991_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_991_, 0, v___x_990_);
lean_closure_set(v___f_991_, 1, v_param_987_);
lean_closure_set(v___f_991_, 2, v_inst_984_);
v___x_992_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_985_, v_f_986_, v_type_989_);
v___x_993_ = lean_apply_4(v_toBind_988_, lean_box(0), lean_box(0), v___x_992_, v___f_991_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___boxed(lean_object* v_pu_994_, lean_object* v_inst_995_, lean_object* v_inst_996_, lean_object* v_f_997_, lean_object* v_param_998_){
_start:
{
uint8_t v_pu_boxed_999_; lean_object* v_res_1000_; 
v_pu_boxed_999_ = lean_unbox(v_pu_994_);
v_res_1000_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(v_pu_boxed_999_, v_inst_995_, v_inst_996_, v_f_997_, v_param_998_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM(lean_object* v_m_1001_, uint8_t v_pu_1002_, lean_object* v_inst_1003_, lean_object* v_inst_1004_, lean_object* v_f_1005_, lean_object* v_param_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(v_pu_1002_, v_inst_1003_, v_inst_1004_, v_f_1005_, v_param_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___boxed(lean_object* v_m_1008_, lean_object* v_pu_1009_, lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_f_1012_, lean_object* v_param_1013_){
_start:
{
uint8_t v_pu_boxed_1014_; lean_object* v_res_1015_; 
v_pu_boxed_1014_ = lean_unbox(v_pu_1009_);
v_res_1015_ = l_Lean_Compiler_LCNF_Param_mapFVarM(v_m_1008_, v_pu_boxed_1014_, v_inst_1010_, v_inst_1011_, v_f_1012_, v_param_1013_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___redArg(lean_object* v_inst_1016_, lean_object* v_f_1017_, lean_object* v_param_1018_){
_start:
{
lean_object* v_type_1019_; lean_object* v___x_1020_; 
v_type_1019_ = lean_ctor_get(v_param_1018_, 2);
lean_inc_ref(v_type_1019_);
lean_dec_ref(v_param_1018_);
v___x_1020_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_1016_, v_f_1017_, v_type_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM(lean_object* v_m_1021_, uint8_t v_pu_1022_, lean_object* v_inst_1023_, lean_object* v_f_1024_, lean_object* v_param_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_1023_, v_f_1024_, v_param_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___boxed(lean_object* v_m_1027_, lean_object* v_pu_1028_, lean_object* v_inst_1029_, lean_object* v_f_1030_, lean_object* v_param_1031_){
_start:
{
uint8_t v_pu_boxed_1032_; lean_object* v_res_1033_; 
v_pu_boxed_1032_ = lean_unbox(v_pu_1028_);
v_res_1033_ = l_Lean_Compiler_LCNF_Param_forFVarM(v_m_1027_, v_pu_boxed_1032_, v_inst_1029_, v_f_1030_, v_param_1031_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(uint8_t v_pu_1034_, lean_object* v_m_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(v_pu_1034_, v_inst_1036_, v_inst_1037_, v___y_1038_, v___y_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0___boxed(lean_object* v_pu_1041_, lean_object* v_m_1042_, lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
uint8_t v_pu_boxed_1047_; lean_object* v_res_1048_; 
v_pu_boxed_1047_ = lean_unbox(v_pu_1041_);
v_res_1048_ = l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(v_pu_boxed_1047_, v_m_1042_, v_inst_1043_, v_inst_1044_, v___y_1045_, v___y_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__1(lean_object* v_m_1049_, lean_object* v_inst_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_1050_, v___y_1051_, v___y_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam(uint8_t v_pu_1055_){
_start:
{
lean_object* v___x_1056_; lean_object* v___f_1057_; lean_object* v___f_1058_; lean_object* v___x_1059_; 
v___x_1056_ = lean_box(v_pu_1055_);
v___f_1057_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1057_, 0, v___x_1056_);
v___f_1058_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarParam___closed__0));
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___f_1057_);
lean_ctor_set(v___x_1059_, 1, v___f_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___boxed(lean_object* v_pu_1060_){
_start:
{
uint8_t v_pu_boxed_1061_; lean_object* v_res_1062_; 
v_pu_boxed_1061_ = lean_unbox(v_pu_1060_);
v_res_1062_ = l_Lean_Compiler_LCNF_instTraverseFVarParam(v_pu_boxed_1061_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0(lean_object* v_k_1063_, lean_object* v_decl_1064_, lean_object* v_toPure_1065_, lean_object* v_decl_1066_, lean_object* v_c_1067_, lean_object* v_____do__lift_1068_){
_start:
{
size_t v___x_1069_; size_t v___x_1070_; uint8_t v___x_1071_; 
v___x_1069_ = lean_ptr_addr(v_k_1063_);
v___x_1070_ = lean_ptr_addr(v_____do__lift_1068_);
v___x_1071_ = lean_usize_dec_eq(v___x_1069_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_dec_ref(v_c_1067_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_decl_1064_);
lean_ctor_set(v___x_1072_, 1, v_____do__lift_1068_);
v___x_1073_ = lean_apply_2(v_toPure_1065_, lean_box(0), v___x_1072_);
return v___x_1073_;
}
else
{
size_t v___x_1074_; size_t v___x_1075_; uint8_t v___x_1076_; 
v___x_1074_ = lean_ptr_addr(v_decl_1066_);
v___x_1075_ = lean_ptr_addr(v_decl_1064_);
v___x_1076_ = lean_usize_dec_eq(v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_dec_ref(v_c_1067_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_decl_1064_);
lean_ctor_set(v___x_1077_, 1, v_____do__lift_1068_);
v___x_1078_ = lean_apply_2(v_toPure_1065_, lean_box(0), v___x_1077_);
return v___x_1078_;
}
else
{
lean_object* v___x_1079_; 
lean_dec_ref(v_____do__lift_1068_);
lean_dec_ref(v_decl_1064_);
v___x_1079_ = lean_apply_2(v_toPure_1065_, lean_box(0), v_c_1067_);
return v___x_1079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed(lean_object* v_k_1080_, lean_object* v_decl_1081_, lean_object* v_toPure_1082_, lean_object* v_decl_1083_, lean_object* v_c_1084_, lean_object* v_____do__lift_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0(v_k_1080_, v_decl_1081_, v_toPure_1082_, v_decl_1083_, v_c_1084_, v_____do__lift_1085_);
lean_dec_ref(v_decl_1083_);
lean_dec_ref(v_k_1080_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(lean_object* v_fvarId_1087_, lean_object* v_____do__lift_1088_, lean_object* v_i_1089_, lean_object* v_____do__lift_1090_, lean_object* v_toPure_1091_, lean_object* v_y_1092_, lean_object* v_k_1093_, lean_object* v_c_1094_, lean_object* v_____do__lift_1095_){
_start:
{
size_t v___x_1096_; size_t v___x_1097_; uint8_t v___x_1098_; 
v___x_1096_ = lean_ptr_addr(v_fvarId_1087_);
v___x_1097_ = lean_ptr_addr(v_____do__lift_1088_);
v___x_1098_ = lean_usize_dec_eq(v___x_1096_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_dec_ref(v_c_1094_);
v___x_1099_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1099_, 0, v_____do__lift_1088_);
lean_ctor_set(v___x_1099_, 1, v_i_1089_);
lean_ctor_set(v___x_1099_, 2, v_____do__lift_1090_);
lean_ctor_set(v___x_1099_, 3, v_____do__lift_1095_);
v___x_1100_ = lean_apply_2(v_toPure_1091_, lean_box(0), v___x_1099_);
return v___x_1100_;
}
else
{
uint8_t v___x_1101_; 
v___x_1101_ = lean_nat_dec_eq(v_i_1089_, v_i_1089_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_dec_ref(v_c_1094_);
v___x_1102_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1102_, 0, v_____do__lift_1088_);
lean_ctor_set(v___x_1102_, 1, v_i_1089_);
lean_ctor_set(v___x_1102_, 2, v_____do__lift_1090_);
lean_ctor_set(v___x_1102_, 3, v_____do__lift_1095_);
v___x_1103_ = lean_apply_2(v_toPure_1091_, lean_box(0), v___x_1102_);
return v___x_1103_;
}
else
{
size_t v___x_1104_; size_t v___x_1105_; uint8_t v___x_1106_; 
v___x_1104_ = lean_ptr_addr(v_y_1092_);
v___x_1105_ = lean_ptr_addr(v_____do__lift_1090_);
v___x_1106_ = lean_usize_dec_eq(v___x_1104_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec_ref(v_c_1094_);
v___x_1107_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1107_, 0, v_____do__lift_1088_);
lean_ctor_set(v___x_1107_, 1, v_i_1089_);
lean_ctor_set(v___x_1107_, 2, v_____do__lift_1090_);
lean_ctor_set(v___x_1107_, 3, v_____do__lift_1095_);
v___x_1108_ = lean_apply_2(v_toPure_1091_, lean_box(0), v___x_1107_);
return v___x_1108_;
}
else
{
size_t v___x_1109_; size_t v___x_1110_; uint8_t v___x_1111_; 
v___x_1109_ = lean_ptr_addr(v_k_1093_);
v___x_1110_ = lean_ptr_addr(v_____do__lift_1095_);
v___x_1111_ = lean_usize_dec_eq(v___x_1109_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_dec_ref(v_c_1094_);
v___x_1112_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1112_, 0, v_____do__lift_1088_);
lean_ctor_set(v___x_1112_, 1, v_i_1089_);
lean_ctor_set(v___x_1112_, 2, v_____do__lift_1090_);
lean_ctor_set(v___x_1112_, 3, v_____do__lift_1095_);
v___x_1113_ = lean_apply_2(v_toPure_1091_, lean_box(0), v___x_1112_);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; 
lean_dec_ref(v_____do__lift_1095_);
lean_dec(v_____do__lift_1090_);
lean_dec(v_i_1089_);
lean_dec(v_____do__lift_1088_);
v___x_1114_ = lean_apply_2(v_toPure_1091_, lean_box(0), v_c_1094_);
return v___x_1114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed(lean_object* v_fvarId_1115_, lean_object* v_____do__lift_1116_, lean_object* v_i_1117_, lean_object* v_____do__lift_1118_, lean_object* v_toPure_1119_, lean_object* v_y_1120_, lean_object* v_k_1121_, lean_object* v_c_1122_, lean_object* v_____do__lift_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(v_fvarId_1115_, v_____do__lift_1116_, v_i_1117_, v_____do__lift_1118_, v_toPure_1119_, v_y_1120_, v_k_1121_, v_c_1122_, v_____do__lift_1123_);
lean_dec_ref(v_k_1121_);
lean_dec(v_y_1120_);
lean_dec(v_fvarId_1115_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(lean_object* v_fvarId_1125_, lean_object* v_toPure_1126_, lean_object* v_c_1127_, lean_object* v_____do__lift_1128_){
_start:
{
uint8_t v___x_1129_; 
v___x_1129_ = l_Lean_instBEqFVarId_beq(v_fvarId_1125_, v_____do__lift_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec_ref(v_c_1127_);
v___x_1130_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_____do__lift_1128_);
v___x_1131_ = lean_apply_2(v_toPure_1126_, lean_box(0), v___x_1130_);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; 
lean_dec(v_____do__lift_1128_);
v___x_1132_ = lean_apply_2(v_toPure_1126_, lean_box(0), v_c_1127_);
return v___x_1132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed(lean_object* v_fvarId_1133_, lean_object* v_toPure_1134_, lean_object* v_c_1135_, lean_object* v_____do__lift_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(v_fvarId_1133_, v_toPure_1134_, v_c_1135_, v_____do__lift_1136_);
lean_dec(v_fvarId_1133_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27(lean_object* v_fvarId_1138_, lean_object* v_____do__lift_1139_, lean_object* v_cidx_1140_, lean_object* v_toPure_1141_, lean_object* v_k_1142_, lean_object* v_c_1143_, lean_object* v_____do__lift_1144_){
_start:
{
size_t v___x_1145_; size_t v___x_1146_; uint8_t v___x_1147_; 
v___x_1145_ = lean_ptr_addr(v_fvarId_1138_);
v___x_1146_ = lean_ptr_addr(v_____do__lift_1139_);
v___x_1147_ = lean_usize_dec_eq(v___x_1145_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_dec_ref(v_c_1143_);
v___x_1148_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1148_, 0, v_____do__lift_1139_);
lean_ctor_set(v___x_1148_, 1, v_cidx_1140_);
lean_ctor_set(v___x_1148_, 2, v_____do__lift_1144_);
v___x_1149_ = lean_apply_2(v_toPure_1141_, lean_box(0), v___x_1148_);
return v___x_1149_;
}
else
{
uint8_t v___x_1150_; 
v___x_1150_ = lean_nat_dec_eq(v_cidx_1140_, v_cidx_1140_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_dec_ref(v_c_1143_);
v___x_1151_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1151_, 0, v_____do__lift_1139_);
lean_ctor_set(v___x_1151_, 1, v_cidx_1140_);
lean_ctor_set(v___x_1151_, 2, v_____do__lift_1144_);
v___x_1152_ = lean_apply_2(v_toPure_1141_, lean_box(0), v___x_1151_);
return v___x_1152_;
}
else
{
size_t v___x_1153_; size_t v___x_1154_; uint8_t v___x_1155_; 
v___x_1153_ = lean_ptr_addr(v_k_1142_);
v___x_1154_ = lean_ptr_addr(v_____do__lift_1144_);
v___x_1155_ = lean_usize_dec_eq(v___x_1153_, v___x_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec_ref(v_c_1143_);
v___x_1156_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1156_, 0, v_____do__lift_1139_);
lean_ctor_set(v___x_1156_, 1, v_cidx_1140_);
lean_ctor_set(v___x_1156_, 2, v_____do__lift_1144_);
v___x_1157_ = lean_apply_2(v_toPure_1141_, lean_box(0), v___x_1156_);
return v___x_1157_;
}
else
{
lean_object* v___x_1158_; 
lean_dec_ref(v_____do__lift_1144_);
lean_dec(v_cidx_1140_);
lean_dec(v_____do__lift_1139_);
v___x_1158_ = lean_apply_2(v_toPure_1141_, lean_box(0), v_c_1143_);
return v___x_1158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27___boxed(lean_object* v_fvarId_1159_, lean_object* v_____do__lift_1160_, lean_object* v_cidx_1161_, lean_object* v_toPure_1162_, lean_object* v_k_1163_, lean_object* v_c_1164_, lean_object* v_____do__lift_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27(v_fvarId_1159_, v_____do__lift_1160_, v_cidx_1161_, v_toPure_1162_, v_k_1163_, v_c_1164_, v_____do__lift_1165_);
lean_dec_ref(v_k_1163_);
lean_dec(v_fvarId_1159_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(lean_object* v_fvarId_1167_, lean_object* v_____do__lift_1168_, lean_object* v_n_1169_, uint8_t v_check_1170_, uint8_t v_persistent_1171_, lean_object* v_toPure_1172_, lean_object* v_k_1173_, lean_object* v_c_1174_, lean_object* v_____do__lift_1175_){
_start:
{
size_t v___x_1176_; size_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1176_ = lean_ptr_addr(v_fvarId_1167_);
v___x_1177_ = lean_ptr_addr(v_____do__lift_1168_);
v___x_1178_ = lean_usize_dec_eq(v___x_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec_ref(v_c_1174_);
v___x_1179_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1179_, 0, v_____do__lift_1168_);
lean_ctor_set(v___x_1179_, 1, v_n_1169_);
lean_ctor_set(v___x_1179_, 2, v_____do__lift_1175_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*3, v_check_1170_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*3 + 1, v_persistent_1171_);
v___x_1180_ = lean_apply_2(v_toPure_1172_, lean_box(0), v___x_1179_);
return v___x_1180_;
}
else
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_nat_dec_eq(v_n_1169_, v_n_1169_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec_ref(v_c_1174_);
v___x_1182_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1182_, 0, v_____do__lift_1168_);
lean_ctor_set(v___x_1182_, 1, v_n_1169_);
lean_ctor_set(v___x_1182_, 2, v_____do__lift_1175_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*3, v_check_1170_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*3 + 1, v_persistent_1171_);
v___x_1183_ = lean_apply_2(v_toPure_1172_, lean_box(0), v___x_1182_);
return v___x_1183_;
}
else
{
size_t v___x_1184_; size_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1184_ = lean_ptr_addr(v_k_1173_);
v___x_1185_ = lean_ptr_addr(v_____do__lift_1175_);
v___x_1186_ = lean_usize_dec_eq(v___x_1184_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec_ref(v_c_1174_);
v___x_1187_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1187_, 0, v_____do__lift_1168_);
lean_ctor_set(v___x_1187_, 1, v_n_1169_);
lean_ctor_set(v___x_1187_, 2, v_____do__lift_1175_);
lean_ctor_set_uint8(v___x_1187_, sizeof(void*)*3, v_check_1170_);
lean_ctor_set_uint8(v___x_1187_, sizeof(void*)*3 + 1, v_persistent_1171_);
v___x_1188_ = lean_apply_2(v_toPure_1172_, lean_box(0), v___x_1187_);
return v___x_1188_;
}
else
{
lean_object* v___x_1189_; 
lean_dec_ref(v_____do__lift_1175_);
lean_dec(v_n_1169_);
lean_dec(v_____do__lift_1168_);
v___x_1189_ = lean_apply_2(v_toPure_1172_, lean_box(0), v_c_1174_);
return v___x_1189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29___boxed(lean_object* v_fvarId_1190_, lean_object* v_____do__lift_1191_, lean_object* v_n_1192_, lean_object* v_check_1193_, lean_object* v_persistent_1194_, lean_object* v_toPure_1195_, lean_object* v_k_1196_, lean_object* v_c_1197_, lean_object* v_____do__lift_1198_){
_start:
{
uint8_t v_check_1963__boxed_1199_; uint8_t v_persistent_1964__boxed_1200_; lean_object* v_res_1201_; 
v_check_1963__boxed_1199_ = lean_unbox(v_check_1193_);
v_persistent_1964__boxed_1200_ = lean_unbox(v_persistent_1194_);
v_res_1201_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(v_fvarId_1190_, v_____do__lift_1191_, v_n_1192_, v_check_1963__boxed_1199_, v_persistent_1964__boxed_1200_, v_toPure_1195_, v_k_1196_, v_c_1197_, v_____do__lift_1198_);
lean_dec_ref(v_k_1196_);
lean_dec(v_fvarId_1190_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(lean_object* v_fvarId_1202_, lean_object* v_____do__lift_1203_, lean_object* v_i_1204_, lean_object* v_offset_1205_, lean_object* v_____do__lift_1206_, lean_object* v_____do__lift_1207_, lean_object* v_toPure_1208_, lean_object* v_y_1209_, lean_object* v_ty_1210_, lean_object* v_k_1211_, lean_object* v_c_1212_, lean_object* v_____do__lift_1213_){
_start:
{
size_t v___x_1214_; size_t v___x_1215_; uint8_t v___x_1216_; 
v___x_1214_ = lean_ptr_addr(v_fvarId_1202_);
v___x_1215_ = lean_ptr_addr(v_____do__lift_1203_);
v___x_1216_ = lean_usize_dec_eq(v___x_1214_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
lean_dec_ref(v_c_1212_);
v___x_1217_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1217_, 0, v_____do__lift_1203_);
lean_ctor_set(v___x_1217_, 1, v_i_1204_);
lean_ctor_set(v___x_1217_, 2, v_offset_1205_);
lean_ctor_set(v___x_1217_, 3, v_____do__lift_1206_);
lean_ctor_set(v___x_1217_, 4, v_____do__lift_1207_);
lean_ctor_set(v___x_1217_, 5, v_____do__lift_1213_);
v___x_1218_ = lean_apply_2(v_toPure_1208_, lean_box(0), v___x_1217_);
return v___x_1218_;
}
else
{
uint8_t v___x_1219_; 
v___x_1219_ = lean_nat_dec_eq(v_i_1204_, v_i_1204_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec_ref(v_c_1212_);
v___x_1220_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1220_, 0, v_____do__lift_1203_);
lean_ctor_set(v___x_1220_, 1, v_i_1204_);
lean_ctor_set(v___x_1220_, 2, v_offset_1205_);
lean_ctor_set(v___x_1220_, 3, v_____do__lift_1206_);
lean_ctor_set(v___x_1220_, 4, v_____do__lift_1207_);
lean_ctor_set(v___x_1220_, 5, v_____do__lift_1213_);
v___x_1221_ = lean_apply_2(v_toPure_1208_, lean_box(0), v___x_1220_);
return v___x_1221_;
}
else
{
uint8_t v___x_1222_; 
v___x_1222_ = lean_nat_dec_eq(v_offset_1205_, v_offset_1205_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec_ref(v_c_1212_);
v___x_1223_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1223_, 0, v_____do__lift_1203_);
lean_ctor_set(v___x_1223_, 1, v_i_1204_);
lean_ctor_set(v___x_1223_, 2, v_offset_1205_);
lean_ctor_set(v___x_1223_, 3, v_____do__lift_1206_);
lean_ctor_set(v___x_1223_, 4, v_____do__lift_1207_);
lean_ctor_set(v___x_1223_, 5, v_____do__lift_1213_);
v___x_1224_ = lean_apply_2(v_toPure_1208_, lean_box(0), v___x_1223_);
return v___x_1224_;
}
else
{
size_t v___x_1225_; size_t v___x_1226_; uint8_t v___x_1227_; 
v___x_1225_ = lean_ptr_addr(v_y_1209_);
v___x_1226_ = lean_ptr_addr(v_____do__lift_1206_);
v___x_1227_ = lean_usize_dec_eq(v___x_1225_, v___x_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref(v_c_1212_);
v___x_1228_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1228_, 0, v_____do__lift_1203_);
lean_ctor_set(v___x_1228_, 1, v_i_1204_);
lean_ctor_set(v___x_1228_, 2, v_offset_1205_);
lean_ctor_set(v___x_1228_, 3, v_____do__lift_1206_);
lean_ctor_set(v___x_1228_, 4, v_____do__lift_1207_);
lean_ctor_set(v___x_1228_, 5, v_____do__lift_1213_);
v___x_1229_ = lean_apply_2(v_toPure_1208_, lean_box(0), v___x_1228_);
return v___x_1229_;
}
else
{
size_t v___x_1230_; size_t v___x_1231_; uint8_t v___x_1232_; 
v___x_1230_ = lean_ptr_addr(v_ty_1210_);
v___x_1231_ = lean_ptr_addr(v_____do__lift_1207_);
v___x_1232_ = lean_usize_dec_eq(v___x_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec_ref(v_c_1212_);
v___x_1233_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1233_, 0, v_____do__lift_1203_);
lean_ctor_set(v___x_1233_, 1, v_i_1204_);
lean_ctor_set(v___x_1233_, 2, v_offset_1205_);
lean_ctor_set(v___x_1233_, 3, v_____do__lift_1206_);
lean_ctor_set(v___x_1233_, 4, v_____do__lift_1207_);
lean_ctor_set(v___x_1233_, 5, v_____do__lift_1213_);
v___x_1234_ = lean_apply_2(v_toPure_1208_, lean_box(0), v___x_1233_);
return v___x_1234_;
}
else
{
size_t v___x_1235_; size_t v___x_1236_; uint8_t v___x_1237_; 
v___x_1235_ = lean_ptr_addr(v_k_1211_);
v___x_1236_ = lean_ptr_addr(v_____do__lift_1213_);
v___x_1237_ = lean_usize_dec_eq(v___x_1235_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_dec_ref(v_c_1212_);
v___x_1238_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1238_, 0, v_____do__lift_1203_);
lean_ctor_set(v___x_1238_, 1, v_i_1204_);
lean_ctor_set(v___x_1238_, 2, v_offset_1205_);
lean_ctor_set(v___x_1238_, 3, v_____do__lift_1206_);
lean_ctor_set(v___x_1238_, 4, v_____do__lift_1207_);
lean_ctor_set(v___x_1238_, 5, v_____do__lift_1213_);
v___x_1239_ = lean_apply_2(v_toPure_1208_, lean_box(0), v___x_1238_);
return v___x_1239_;
}
else
{
lean_object* v___x_1240_; 
lean_dec_ref(v_____do__lift_1213_);
lean_dec_ref(v_____do__lift_1207_);
lean_dec(v_____do__lift_1206_);
lean_dec(v_offset_1205_);
lean_dec(v_i_1204_);
lean_dec(v_____do__lift_1203_);
v___x_1240_ = lean_apply_2(v_toPure_1208_, lean_box(0), v_c_1212_);
return v___x_1240_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed(lean_object* v_fvarId_1241_, lean_object* v_____do__lift_1242_, lean_object* v_i_1243_, lean_object* v_offset_1244_, lean_object* v_____do__lift_1245_, lean_object* v_____do__lift_1246_, lean_object* v_toPure_1247_, lean_object* v_y_1248_, lean_object* v_ty_1249_, lean_object* v_k_1250_, lean_object* v_c_1251_, lean_object* v_____do__lift_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(v_fvarId_1241_, v_____do__lift_1242_, v_i_1243_, v_offset_1244_, v_____do__lift_1245_, v_____do__lift_1246_, v_toPure_1247_, v_y_1248_, v_ty_1249_, v_k_1250_, v_c_1251_, v_____do__lift_1252_);
lean_dec_ref(v_k_1250_);
lean_dec_ref(v_ty_1249_);
lean_dec(v_y_1248_);
lean_dec(v_fvarId_1241_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(uint8_t v_pu_1254_, lean_object* v_decl_1255_, lean_object* v_____do__lift_1256_, lean_object* v_params_1257_, lean_object* v_inst_1258_, lean_object* v_toBind_1259_, lean_object* v___f_1260_, lean_object* v_____do__lift_1261_){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1262_ = lean_box(v_pu_1254_);
v___x_1263_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed), 10, 5);
lean_closure_set(v___x_1263_, 0, v___x_1262_);
lean_closure_set(v___x_1263_, 1, v_decl_1255_);
lean_closure_set(v___x_1263_, 2, v_____do__lift_1256_);
lean_closure_set(v___x_1263_, 3, v_params_1257_);
lean_closure_set(v___x_1263_, 4, v_____do__lift_1261_);
v___x_1264_ = lean_apply_2(v_inst_1258_, lean_box(0), v___x_1263_);
v___x_1265_ = lean_apply_4(v_toBind_1259_, lean_box(0), lean_box(0), v___x_1264_, v___f_1260_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed(lean_object* v_pu_1266_, lean_object* v_decl_1267_, lean_object* v_____do__lift_1268_, lean_object* v_params_1269_, lean_object* v_inst_1270_, lean_object* v_toBind_1271_, lean_object* v___f_1272_, lean_object* v_____do__lift_1273_){
_start:
{
uint8_t v_pu_boxed_1274_; lean_object* v_res_1275_; 
v_pu_boxed_1274_ = lean_unbox(v_pu_1266_);
v_res_1275_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(v_pu_boxed_1274_, v_decl_1267_, v_____do__lift_1268_, v_params_1269_, v_inst_1270_, v_toBind_1271_, v___f_1272_, v_____do__lift_1273_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(lean_object* v_____do__lift_1276_, lean_object* v_toPure_1277_, lean_object* v_c_1278_, lean_object* v_fvarId_1279_, lean_object* v_args_1280_, lean_object* v_____do__lift_1281_){
_start:
{
uint8_t v___y_1283_; uint8_t v___x_1287_; 
v___x_1287_ = l_Lean_instBEqFVarId_beq(v_fvarId_1279_, v_____do__lift_1276_);
if (v___x_1287_ == 0)
{
v___y_1283_ = v___x_1287_;
goto v___jp_1282_;
}
else
{
size_t v___x_1288_; size_t v___x_1289_; uint8_t v___x_1290_; 
v___x_1288_ = lean_ptr_addr(v_args_1280_);
v___x_1289_ = lean_ptr_addr(v_____do__lift_1281_);
v___x_1290_ = lean_usize_dec_eq(v___x_1288_, v___x_1289_);
v___y_1283_ = v___x_1290_;
goto v___jp_1282_;
}
v___jp_1282_:
{
if (v___y_1283_ == 0)
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec_ref(v_c_1278_);
v___x_1284_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1284_, 0, v_____do__lift_1276_);
lean_ctor_set(v___x_1284_, 1, v_____do__lift_1281_);
v___x_1285_ = lean_apply_2(v_toPure_1277_, lean_box(0), v___x_1284_);
return v___x_1285_;
}
else
{
lean_object* v___x_1286_; 
lean_dec_ref(v_____do__lift_1281_);
lean_dec(v_____do__lift_1276_);
v___x_1286_ = lean_apply_2(v_toPure_1277_, lean_box(0), v_c_1278_);
return v___x_1286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed(lean_object* v_____do__lift_1291_, lean_object* v_toPure_1292_, lean_object* v_c_1293_, lean_object* v_fvarId_1294_, lean_object* v_args_1295_, lean_object* v_____do__lift_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(v_____do__lift_1291_, v_toPure_1292_, v_c_1293_, v_fvarId_1294_, v_args_1295_, v_____do__lift_1296_);
lean_dec_ref(v_args_1295_);
lean_dec(v_fvarId_1294_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(lean_object* v_toPure_1298_, lean_object* v_c_1299_, lean_object* v_fvarId_1300_, lean_object* v_args_1301_, uint8_t v_pu_1302_, lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_f_1305_, lean_object* v_toBind_1306_, lean_object* v_____do__lift_1307_){
_start:
{
lean_object* v___f_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; size_t v_sz_1311_; size_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
lean_inc_ref(v_args_1301_);
v___f_1308_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed), 6, 5);
lean_closure_set(v___f_1308_, 0, v_____do__lift_1307_);
lean_closure_set(v___f_1308_, 1, v_toPure_1298_);
lean_closure_set(v___f_1308_, 2, v_c_1299_);
lean_closure_set(v___f_1308_, 3, v_fvarId_1300_);
lean_closure_set(v___f_1308_, 4, v_args_1301_);
v___x_1309_ = lean_box(v_pu_1302_);
lean_inc_ref(v_inst_1304_);
v___x_1310_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Arg_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_1310_, 0, lean_box(0));
lean_closure_set(v___x_1310_, 1, v___x_1309_);
lean_closure_set(v___x_1310_, 2, v_inst_1303_);
lean_closure_set(v___x_1310_, 3, v_inst_1304_);
lean_closure_set(v___x_1310_, 4, v_f_1305_);
v_sz_1311_ = lean_array_size(v_args_1301_);
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1304_, v___x_1310_, v_sz_1311_, v___x_1312_, v_args_1301_);
v___x_1314_ = lean_apply_4(v_toBind_1306_, lean_box(0), lean_box(0), v___x_1313_, v___f_1308_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed(lean_object* v_toPure_1315_, lean_object* v_c_1316_, lean_object* v_fvarId_1317_, lean_object* v_args_1318_, lean_object* v_pu_1319_, lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_f_1322_, lean_object* v_toBind_1323_, lean_object* v_____do__lift_1324_){
_start:
{
uint8_t v_pu_boxed_1325_; lean_object* v_res_1326_; 
v_pu_boxed_1325_ = lean_unbox(v_pu_1319_);
v_res_1326_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(v_toPure_1315_, v_c_1316_, v_fvarId_1317_, v_args_1318_, v_pu_boxed_1325_, v_inst_1320_, v_inst_1321_, v_f_1322_, v_toBind_1323_, v_____do__lift_1324_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(lean_object* v_typeName_1327_, lean_object* v_____do__lift_1328_, lean_object* v_____do__lift_1329_, lean_object* v_toPure_1330_, lean_object* v_alts_1331_, lean_object* v_resultType_1332_, lean_object* v_discr_1333_, lean_object* v_c_1334_, lean_object* v_____do__lift_1335_){
_start:
{
size_t v___x_1340_; size_t v___x_1341_; uint8_t v___x_1342_; 
v___x_1340_ = lean_ptr_addr(v_alts_1331_);
v___x_1341_ = lean_ptr_addr(v_____do__lift_1335_);
v___x_1342_ = lean_usize_dec_eq(v___x_1340_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_dec_ref(v_c_1334_);
goto v___jp_1336_;
}
else
{
size_t v___x_1343_; size_t v___x_1344_; uint8_t v___x_1345_; 
v___x_1343_ = lean_ptr_addr(v_resultType_1332_);
v___x_1344_ = lean_ptr_addr(v_____do__lift_1328_);
v___x_1345_ = lean_usize_dec_eq(v___x_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_dec_ref(v_c_1334_);
goto v___jp_1336_;
}
else
{
uint8_t v___x_1346_; 
v___x_1346_ = l_Lean_instBEqFVarId_beq(v_discr_1333_, v_____do__lift_1329_);
if (v___x_1346_ == 0)
{
lean_dec_ref(v_c_1334_);
goto v___jp_1336_;
}
else
{
lean_object* v___x_1347_; 
lean_dec_ref(v_____do__lift_1335_);
lean_dec(v_____do__lift_1329_);
lean_dec_ref(v_____do__lift_1328_);
lean_dec(v_typeName_1327_);
v___x_1347_ = lean_apply_2(v_toPure_1330_, lean_box(0), v_c_1334_);
return v___x_1347_;
}
}
}
v___jp_1336_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1337_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1337_, 0, v_typeName_1327_);
lean_ctor_set(v___x_1337_, 1, v_____do__lift_1328_);
lean_ctor_set(v___x_1337_, 2, v_____do__lift_1329_);
lean_ctor_set(v___x_1337_, 3, v_____do__lift_1335_);
v___x_1338_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
v___x_1339_ = lean_apply_2(v_toPure_1330_, lean_box(0), v___x_1338_);
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed(lean_object* v_typeName_1348_, lean_object* v_____do__lift_1349_, lean_object* v_____do__lift_1350_, lean_object* v_toPure_1351_, lean_object* v_alts_1352_, lean_object* v_resultType_1353_, lean_object* v_discr_1354_, lean_object* v_c_1355_, lean_object* v_____do__lift_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(v_typeName_1348_, v_____do__lift_1349_, v_____do__lift_1350_, v_toPure_1351_, v_alts_1352_, v_resultType_1353_, v_discr_1354_, v_c_1355_, v_____do__lift_1356_);
lean_dec(v_discr_1354_);
lean_dec_ref(v_resultType_1353_);
lean_dec_ref(v_alts_1352_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13(lean_object* v_typeName_1358_, lean_object* v_____do__lift_1359_, lean_object* v_toPure_1360_, lean_object* v_alts_1361_, lean_object* v_resultType_1362_, lean_object* v_discr_1363_, lean_object* v_c_1364_, lean_object* v_inst_1365_, lean_object* v___f_1366_, lean_object* v_toBind_1367_, lean_object* v_____do__lift_1368_){
_start:
{
lean_object* v___f_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_inc_ref(v_alts_1361_);
v___f_1369_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed), 9, 8);
lean_closure_set(v___f_1369_, 0, v_typeName_1358_);
lean_closure_set(v___f_1369_, 1, v_____do__lift_1359_);
lean_closure_set(v___f_1369_, 2, v_____do__lift_1368_);
lean_closure_set(v___f_1369_, 3, v_toPure_1360_);
lean_closure_set(v___f_1369_, 4, v_alts_1361_);
lean_closure_set(v___f_1369_, 5, v_resultType_1362_);
lean_closure_set(v___f_1369_, 6, v_discr_1363_);
lean_closure_set(v___f_1369_, 7, v_c_1364_);
v___x_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_1365_, v___f_1366_, v___x_1370_, v_alts_1361_);
v___x_1372_ = lean_apply_4(v_toBind_1367_, lean_box(0), lean_box(0), v___x_1371_, v___f_1369_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14(lean_object* v_typeName_1373_, lean_object* v_toPure_1374_, lean_object* v_alts_1375_, lean_object* v_resultType_1376_, lean_object* v_discr_1377_, lean_object* v_c_1378_, lean_object* v_inst_1379_, lean_object* v___f_1380_, lean_object* v_toBind_1381_, lean_object* v_f_1382_, lean_object* v_____do__lift_1383_){
_start:
{
lean_object* v___f_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_inc(v_toBind_1381_);
lean_inc(v_discr_1377_);
v___f_1384_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13), 11, 10);
lean_closure_set(v___f_1384_, 0, v_typeName_1373_);
lean_closure_set(v___f_1384_, 1, v_____do__lift_1383_);
lean_closure_set(v___f_1384_, 2, v_toPure_1374_);
lean_closure_set(v___f_1384_, 3, v_alts_1375_);
lean_closure_set(v___f_1384_, 4, v_resultType_1376_);
lean_closure_set(v___f_1384_, 5, v_discr_1377_);
lean_closure_set(v___f_1384_, 6, v_c_1378_);
lean_closure_set(v___f_1384_, 7, v_inst_1379_);
lean_closure_set(v___f_1384_, 8, v___f_1380_);
lean_closure_set(v___f_1384_, 9, v_toBind_1381_);
v___x_1385_ = lean_apply_1(v_f_1382_, v_discr_1377_);
v___x_1386_ = lean_apply_4(v_toBind_1381_, lean_box(0), lean_box(0), v___x_1385_, v___f_1384_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(lean_object* v_fvarId_1387_, lean_object* v_____do__lift_1388_, lean_object* v_n_1389_, uint8_t v_check_1390_, uint8_t v_persistent_1391_, lean_object* v_objs_x3f_1392_, lean_object* v_toPure_1393_, lean_object* v_k_1394_, lean_object* v_c_1395_, lean_object* v_____do__lift_1396_){
_start:
{
size_t v___x_1397_; size_t v___x_1398_; uint8_t v___x_1399_; 
v___x_1397_ = lean_ptr_addr(v_fvarId_1387_);
v___x_1398_ = lean_ptr_addr(v_____do__lift_1388_);
v___x_1399_ = lean_usize_dec_eq(v___x_1397_, v___x_1398_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_dec_ref(v_c_1395_);
v___x_1400_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1400_, 0, v_____do__lift_1388_);
lean_ctor_set(v___x_1400_, 1, v_n_1389_);
lean_ctor_set(v___x_1400_, 2, v_objs_x3f_1392_);
lean_ctor_set(v___x_1400_, 3, v_____do__lift_1396_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*4, v_check_1390_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*4 + 1, v_persistent_1391_);
v___x_1401_ = lean_apply_2(v_toPure_1393_, lean_box(0), v___x_1400_);
return v___x_1401_;
}
else
{
uint8_t v___x_1402_; 
v___x_1402_ = lean_nat_dec_eq(v_n_1389_, v_n_1389_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec_ref(v_c_1395_);
v___x_1403_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1403_, 0, v_____do__lift_1388_);
lean_ctor_set(v___x_1403_, 1, v_n_1389_);
lean_ctor_set(v___x_1403_, 2, v_objs_x3f_1392_);
lean_ctor_set(v___x_1403_, 3, v_____do__lift_1396_);
lean_ctor_set_uint8(v___x_1403_, sizeof(void*)*4, v_check_1390_);
lean_ctor_set_uint8(v___x_1403_, sizeof(void*)*4 + 1, v_persistent_1391_);
v___x_1404_ = lean_apply_2(v_toPure_1393_, lean_box(0), v___x_1403_);
return v___x_1404_;
}
else
{
size_t v___x_1405_; uint8_t v___x_1406_; 
v___x_1405_ = lean_ptr_addr(v_objs_x3f_1392_);
v___x_1406_ = lean_usize_dec_eq(v___x_1405_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_dec_ref(v_c_1395_);
v___x_1407_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1407_, 0, v_____do__lift_1388_);
lean_ctor_set(v___x_1407_, 1, v_n_1389_);
lean_ctor_set(v___x_1407_, 2, v_objs_x3f_1392_);
lean_ctor_set(v___x_1407_, 3, v_____do__lift_1396_);
lean_ctor_set_uint8(v___x_1407_, sizeof(void*)*4, v_check_1390_);
lean_ctor_set_uint8(v___x_1407_, sizeof(void*)*4 + 1, v_persistent_1391_);
v___x_1408_ = lean_apply_2(v_toPure_1393_, lean_box(0), v___x_1407_);
return v___x_1408_;
}
else
{
size_t v___x_1409_; size_t v___x_1410_; uint8_t v___x_1411_; 
v___x_1409_ = lean_ptr_addr(v_k_1394_);
v___x_1410_ = lean_ptr_addr(v_____do__lift_1396_);
v___x_1411_ = lean_usize_dec_eq(v___x_1409_, v___x_1410_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
lean_dec_ref(v_c_1395_);
v___x_1412_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1412_, 0, v_____do__lift_1388_);
lean_ctor_set(v___x_1412_, 1, v_n_1389_);
lean_ctor_set(v___x_1412_, 2, v_objs_x3f_1392_);
lean_ctor_set(v___x_1412_, 3, v_____do__lift_1396_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*4, v_check_1390_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*4 + 1, v_persistent_1391_);
v___x_1413_ = lean_apply_2(v_toPure_1393_, lean_box(0), v___x_1412_);
return v___x_1413_;
}
else
{
lean_object* v___x_1414_; 
lean_dec_ref(v_____do__lift_1396_);
lean_dec(v_objs_x3f_1392_);
lean_dec(v_n_1389_);
lean_dec(v_____do__lift_1388_);
v___x_1414_ = lean_apply_2(v_toPure_1393_, lean_box(0), v_c_1395_);
return v___x_1414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed(lean_object* v_fvarId_1415_, lean_object* v_____do__lift_1416_, lean_object* v_n_1417_, lean_object* v_check_1418_, lean_object* v_persistent_1419_, lean_object* v_objs_x3f_1420_, lean_object* v_toPure_1421_, lean_object* v_k_1422_, lean_object* v_c_1423_, lean_object* v_____do__lift_1424_){
_start:
{
uint8_t v_check_2265__boxed_1425_; uint8_t v_persistent_2266__boxed_1426_; lean_object* v_res_1427_; 
v_check_2265__boxed_1425_ = lean_unbox(v_check_1418_);
v_persistent_2266__boxed_1426_ = lean_unbox(v_persistent_1419_);
v_res_1427_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(v_fvarId_1415_, v_____do__lift_1416_, v_n_1417_, v_check_2265__boxed_1425_, v_persistent_2266__boxed_1426_, v_objs_x3f_1420_, v_toPure_1421_, v_k_1422_, v_c_1423_, v_____do__lift_1424_);
lean_dec_ref(v_k_1422_);
lean_dec(v_fvarId_1415_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(lean_object* v_k_1428_, lean_object* v_decl_1429_, lean_object* v_toPure_1430_, lean_object* v_decl_1431_, lean_object* v_c_1432_, lean_object* v_____do__lift_1433_){
_start:
{
size_t v___x_1434_; size_t v___x_1435_; uint8_t v___x_1436_; 
v___x_1434_ = lean_ptr_addr(v_k_1428_);
v___x_1435_ = lean_ptr_addr(v_____do__lift_1433_);
v___x_1436_ = lean_usize_dec_eq(v___x_1434_, v___x_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_dec_ref(v_c_1432_);
v___x_1437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1437_, 0, v_decl_1429_);
lean_ctor_set(v___x_1437_, 1, v_____do__lift_1433_);
v___x_1438_ = lean_apply_2(v_toPure_1430_, lean_box(0), v___x_1437_);
return v___x_1438_;
}
else
{
size_t v___x_1439_; size_t v___x_1440_; uint8_t v___x_1441_; 
v___x_1439_ = lean_ptr_addr(v_decl_1431_);
v___x_1440_ = lean_ptr_addr(v_decl_1429_);
v___x_1441_ = lean_usize_dec_eq(v___x_1439_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
lean_dec_ref(v_c_1432_);
v___x_1442_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1442_, 0, v_decl_1429_);
lean_ctor_set(v___x_1442_, 1, v_____do__lift_1433_);
v___x_1443_ = lean_apply_2(v_toPure_1430_, lean_box(0), v___x_1442_);
return v___x_1443_;
}
else
{
lean_object* v___x_1444_; 
lean_dec_ref(v_____do__lift_1433_);
lean_dec_ref(v_decl_1429_);
v___x_1444_ = lean_apply_2(v_toPure_1430_, lean_box(0), v_c_1432_);
return v___x_1444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed(lean_object* v_k_1445_, lean_object* v_decl_1446_, lean_object* v_toPure_1447_, lean_object* v_decl_1448_, lean_object* v_c_1449_, lean_object* v_____do__lift_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(v_k_1445_, v_decl_1446_, v_toPure_1447_, v_decl_1448_, v_c_1449_, v_____do__lift_1450_);
lean_dec_ref(v_decl_1448_);
lean_dec_ref(v_k_1445_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(lean_object* v_k_1452_, lean_object* v_decl_1453_, lean_object* v_toPure_1454_, lean_object* v_decl_1455_, lean_object* v_c_1456_, lean_object* v_____do__lift_1457_){
_start:
{
size_t v___x_1458_; size_t v___x_1459_; uint8_t v___x_1460_; 
v___x_1458_ = lean_ptr_addr(v_k_1452_);
v___x_1459_ = lean_ptr_addr(v_____do__lift_1457_);
v___x_1460_ = lean_usize_dec_eq(v___x_1458_, v___x_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec_ref(v_c_1456_);
v___x_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1461_, 0, v_decl_1453_);
lean_ctor_set(v___x_1461_, 1, v_____do__lift_1457_);
v___x_1462_ = lean_apply_2(v_toPure_1454_, lean_box(0), v___x_1461_);
return v___x_1462_;
}
else
{
size_t v___x_1463_; size_t v___x_1464_; uint8_t v___x_1465_; 
v___x_1463_ = lean_ptr_addr(v_decl_1455_);
v___x_1464_ = lean_ptr_addr(v_decl_1453_);
v___x_1465_ = lean_usize_dec_eq(v___x_1463_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec_ref(v_c_1456_);
v___x_1466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1466_, 0, v_decl_1453_);
lean_ctor_set(v___x_1466_, 1, v_____do__lift_1457_);
v___x_1467_ = lean_apply_2(v_toPure_1454_, lean_box(0), v___x_1466_);
return v___x_1467_;
}
else
{
lean_object* v___x_1468_; 
lean_dec_ref(v_____do__lift_1457_);
lean_dec_ref(v_decl_1453_);
v___x_1468_ = lean_apply_2(v_toPure_1454_, lean_box(0), v_c_1456_);
return v___x_1468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed(lean_object* v_k_1469_, lean_object* v_decl_1470_, lean_object* v_toPure_1471_, lean_object* v_decl_1472_, lean_object* v_c_1473_, lean_object* v_____do__lift_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(v_k_1469_, v_decl_1470_, v_toPure_1471_, v_decl_1472_, v_c_1473_, v_____do__lift_1474_);
lean_dec_ref(v_decl_1472_);
lean_dec_ref(v_k_1469_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(lean_object* v_fvarId_1476_, lean_object* v_____do__lift_1477_, lean_object* v_i_1478_, lean_object* v_____do__lift_1479_, lean_object* v_toPure_1480_, lean_object* v_y_1481_, lean_object* v_k_1482_, lean_object* v_c_1483_, lean_object* v_____do__lift_1484_){
_start:
{
size_t v___x_1485_; size_t v___x_1486_; uint8_t v___x_1487_; 
v___x_1485_ = lean_ptr_addr(v_fvarId_1476_);
v___x_1486_ = lean_ptr_addr(v_____do__lift_1477_);
v___x_1487_ = lean_usize_dec_eq(v___x_1485_, v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec_ref(v_c_1483_);
v___x_1488_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1488_, 0, v_____do__lift_1477_);
lean_ctor_set(v___x_1488_, 1, v_i_1478_);
lean_ctor_set(v___x_1488_, 2, v_____do__lift_1479_);
lean_ctor_set(v___x_1488_, 3, v_____do__lift_1484_);
v___x_1489_ = lean_apply_2(v_toPure_1480_, lean_box(0), v___x_1488_);
return v___x_1489_;
}
else
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_nat_dec_eq(v_i_1478_, v_i_1478_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_dec_ref(v_c_1483_);
v___x_1491_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1491_, 0, v_____do__lift_1477_);
lean_ctor_set(v___x_1491_, 1, v_i_1478_);
lean_ctor_set(v___x_1491_, 2, v_____do__lift_1479_);
lean_ctor_set(v___x_1491_, 3, v_____do__lift_1484_);
v___x_1492_ = lean_apply_2(v_toPure_1480_, lean_box(0), v___x_1491_);
return v___x_1492_;
}
else
{
size_t v___x_1493_; size_t v___x_1494_; uint8_t v___x_1495_; 
v___x_1493_ = lean_ptr_addr(v_y_1481_);
v___x_1494_ = lean_ptr_addr(v_____do__lift_1479_);
v___x_1495_ = lean_usize_dec_eq(v___x_1493_, v___x_1494_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_dec_ref(v_c_1483_);
v___x_1496_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1496_, 0, v_____do__lift_1477_);
lean_ctor_set(v___x_1496_, 1, v_i_1478_);
lean_ctor_set(v___x_1496_, 2, v_____do__lift_1479_);
lean_ctor_set(v___x_1496_, 3, v_____do__lift_1484_);
v___x_1497_ = lean_apply_2(v_toPure_1480_, lean_box(0), v___x_1496_);
return v___x_1497_;
}
else
{
size_t v___x_1498_; size_t v___x_1499_; uint8_t v___x_1500_; 
v___x_1498_ = lean_ptr_addr(v_k_1482_);
v___x_1499_ = lean_ptr_addr(v_____do__lift_1484_);
v___x_1500_ = lean_usize_dec_eq(v___x_1498_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_dec_ref(v_c_1483_);
v___x_1501_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1501_, 0, v_____do__lift_1477_);
lean_ctor_set(v___x_1501_, 1, v_i_1478_);
lean_ctor_set(v___x_1501_, 2, v_____do__lift_1479_);
lean_ctor_set(v___x_1501_, 3, v_____do__lift_1484_);
v___x_1502_ = lean_apply_2(v_toPure_1480_, lean_box(0), v___x_1501_);
return v___x_1502_;
}
else
{
lean_object* v___x_1503_; 
lean_dec_ref(v_____do__lift_1484_);
lean_dec(v_____do__lift_1479_);
lean_dec(v_i_1478_);
lean_dec(v_____do__lift_1477_);
v___x_1503_ = lean_apply_2(v_toPure_1480_, lean_box(0), v_c_1483_);
return v___x_1503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed(lean_object* v_fvarId_1504_, lean_object* v_____do__lift_1505_, lean_object* v_i_1506_, lean_object* v_____do__lift_1507_, lean_object* v_toPure_1508_, lean_object* v_y_1509_, lean_object* v_k_1510_, lean_object* v_c_1511_, lean_object* v_____do__lift_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(v_fvarId_1504_, v_____do__lift_1505_, v_i_1506_, v_____do__lift_1507_, v_toPure_1508_, v_y_1509_, v_k_1510_, v_c_1511_, v_____do__lift_1512_);
lean_dec_ref(v_k_1510_);
lean_dec(v_y_1509_);
lean_dec(v_fvarId_1504_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(lean_object* v_fvarId_1514_, lean_object* v_____do__lift_1515_, lean_object* v_toPure_1516_, lean_object* v_k_1517_, lean_object* v_c_1518_, lean_object* v_____do__lift_1519_){
_start:
{
size_t v___x_1520_; size_t v___x_1521_; uint8_t v___x_1522_; 
v___x_1520_ = lean_ptr_addr(v_fvarId_1514_);
v___x_1521_ = lean_ptr_addr(v_____do__lift_1515_);
v___x_1522_ = lean_usize_dec_eq(v___x_1520_, v___x_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_dec_ref(v_c_1518_);
v___x_1523_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_1523_, 0, v_____do__lift_1515_);
lean_ctor_set(v___x_1523_, 1, v_____do__lift_1519_);
v___x_1524_ = lean_apply_2(v_toPure_1516_, lean_box(0), v___x_1523_);
return v___x_1524_;
}
else
{
size_t v___x_1525_; size_t v___x_1526_; uint8_t v___x_1527_; 
v___x_1525_ = lean_ptr_addr(v_k_1517_);
v___x_1526_ = lean_ptr_addr(v_____do__lift_1519_);
v___x_1527_ = lean_usize_dec_eq(v___x_1525_, v___x_1526_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec_ref(v_c_1518_);
v___x_1528_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_1528_, 0, v_____do__lift_1515_);
lean_ctor_set(v___x_1528_, 1, v_____do__lift_1519_);
v___x_1529_ = lean_apply_2(v_toPure_1516_, lean_box(0), v___x_1528_);
return v___x_1529_;
}
else
{
lean_object* v___x_1530_; 
lean_dec_ref(v_____do__lift_1519_);
lean_dec(v_____do__lift_1515_);
v___x_1530_ = lean_apply_2(v_toPure_1516_, lean_box(0), v_c_1518_);
return v___x_1530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed(lean_object* v_fvarId_1531_, lean_object* v_____do__lift_1532_, lean_object* v_toPure_1533_, lean_object* v_k_1534_, lean_object* v_c_1535_, lean_object* v_____do__lift_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(v_fvarId_1531_, v_____do__lift_1532_, v_toPure_1533_, v_k_1534_, v_c_1535_, v_____do__lift_1536_);
lean_dec_ref(v_k_1534_);
lean_dec(v_fvarId_1531_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(lean_object* v_type_1538_, lean_object* v_toPure_1539_, lean_object* v_c_1540_, lean_object* v_____do__lift_1541_){
_start:
{
size_t v___x_1542_; size_t v___x_1543_; uint8_t v___x_1544_; 
v___x_1542_ = lean_ptr_addr(v_type_1538_);
v___x_1543_ = lean_ptr_addr(v_____do__lift_1541_);
v___x_1544_ = lean_usize_dec_eq(v___x_1542_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_dec_ref(v_c_1540_);
v___x_1545_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1545_, 0, v_____do__lift_1541_);
v___x_1546_ = lean_apply_2(v_toPure_1539_, lean_box(0), v___x_1545_);
return v___x_1546_;
}
else
{
lean_object* v___x_1547_; 
lean_dec_ref(v_____do__lift_1541_);
v___x_1547_ = lean_apply_2(v_toPure_1539_, lean_box(0), v_c_1540_);
return v___x_1547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed(lean_object* v_type_1548_, lean_object* v_toPure_1549_, lean_object* v_c_1550_, lean_object* v_____do__lift_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(v_type_1548_, v_toPure_1549_, v_c_1550_, v_____do__lift_1551_);
lean_dec_ref(v_type_1548_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(lean_object* v_k_1553_, lean_object* v_toPure_1554_, lean_object* v_decl_1555_, lean_object* v_c_1556_, uint8_t v_pu_1557_, lean_object* v_inst_1558_, lean_object* v_inst_1559_, lean_object* v_f_1560_, lean_object* v_toBind_1561_, lean_object* v_decl_1562_){
_start:
{
lean_object* v___f_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_inc_ref(v_k_1553_);
v___f_1563_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1563_, 0, v_k_1553_);
lean_closure_set(v___f_1563_, 1, v_decl_1562_);
lean_closure_set(v___f_1563_, 2, v_toPure_1554_);
lean_closure_set(v___f_1563_, 3, v_decl_1555_);
lean_closure_set(v___f_1563_, 4, v_c_1556_);
v___x_1564_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1557_, v_inst_1558_, v_inst_1559_, v_f_1560_, v_k_1553_);
v___x_1565_ = lean_apply_4(v_toBind_1561_, lean_box(0), lean_box(0), v___x_1564_, v___f_1563_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed(lean_object* v_k_1566_, lean_object* v_toPure_1567_, lean_object* v_decl_1568_, lean_object* v_c_1569_, lean_object* v_pu_1570_, lean_object* v_inst_1571_, lean_object* v_inst_1572_, lean_object* v_f_1573_, lean_object* v_toBind_1574_, lean_object* v_decl_1575_){
_start:
{
uint8_t v_pu_boxed_1576_; lean_object* v_res_1577_; 
v_pu_boxed_1576_ = lean_unbox(v_pu_1570_);
v_res_1577_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(v_k_1566_, v_toPure_1567_, v_decl_1568_, v_c_1569_, v_pu_boxed_1576_, v_inst_1571_, v_inst_1572_, v_f_1573_, v_toBind_1574_, v_decl_1575_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(lean_object* v_k_1578_, lean_object* v_toPure_1579_, lean_object* v_decl_1580_, lean_object* v_c_1581_, uint8_t v_pu_1582_, lean_object* v_inst_1583_, lean_object* v_inst_1584_, lean_object* v_f_1585_, lean_object* v_toBind_1586_, lean_object* v_decl_1587_){
_start:
{
lean_object* v___f_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_inc_ref(v_k_1578_);
v___f_1588_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_1588_, 0, v_k_1578_);
lean_closure_set(v___f_1588_, 1, v_decl_1587_);
lean_closure_set(v___f_1588_, 2, v_toPure_1579_);
lean_closure_set(v___f_1588_, 3, v_decl_1580_);
lean_closure_set(v___f_1588_, 4, v_c_1581_);
v___x_1589_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1582_, v_inst_1583_, v_inst_1584_, v_f_1585_, v_k_1578_);
v___x_1590_ = lean_apply_4(v_toBind_1586_, lean_box(0), lean_box(0), v___x_1589_, v___f_1588_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed(lean_object* v_k_1591_, lean_object* v_toPure_1592_, lean_object* v_decl_1593_, lean_object* v_c_1594_, lean_object* v_pu_1595_, lean_object* v_inst_1596_, lean_object* v_inst_1597_, lean_object* v_f_1598_, lean_object* v_toBind_1599_, lean_object* v_decl_1600_){
_start:
{
uint8_t v_pu_boxed_1601_; lean_object* v_res_1602_; 
v_pu_boxed_1601_ = lean_unbox(v_pu_1595_);
v_res_1602_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(v_k_1591_, v_toPure_1592_, v_decl_1593_, v_c_1594_, v_pu_boxed_1601_, v_inst_1596_, v_inst_1597_, v_f_1598_, v_toBind_1599_, v_decl_1600_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(uint8_t v_pu_1603_, lean_object* v_decl_1604_, lean_object* v_params_1605_, lean_object* v_inst_1606_, lean_object* v_toBind_1607_, lean_object* v___f_1608_, lean_object* v_inst_1609_, lean_object* v_f_1610_, lean_object* v_value_1611_, lean_object* v_____do__lift_1612_){
_start:
{
lean_object* v___x_1613_; lean_object* v___f_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1613_ = lean_box(v_pu_1603_);
lean_inc(v_toBind_1607_);
lean_inc(v_inst_1606_);
v___f_1614_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_1614_, 0, v___x_1613_);
lean_closure_set(v___f_1614_, 1, v_decl_1604_);
lean_closure_set(v___f_1614_, 2, v_____do__lift_1612_);
lean_closure_set(v___f_1614_, 3, v_params_1605_);
lean_closure_set(v___f_1614_, 4, v_inst_1606_);
lean_closure_set(v___f_1614_, 5, v_toBind_1607_);
lean_closure_set(v___f_1614_, 6, v___f_1608_);
v___x_1615_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1603_, v_inst_1606_, v_inst_1609_, v_f_1610_, v_value_1611_);
v___x_1616_ = lean_apply_4(v_toBind_1607_, lean_box(0), lean_box(0), v___x_1615_, v___f_1614_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed(lean_object* v_pu_1617_, lean_object* v_decl_1618_, lean_object* v_params_1619_, lean_object* v_inst_1620_, lean_object* v_toBind_1621_, lean_object* v___f_1622_, lean_object* v_inst_1623_, lean_object* v_f_1624_, lean_object* v_value_1625_, lean_object* v_____do__lift_1626_){
_start:
{
uint8_t v_pu_boxed_1627_; lean_object* v_res_1628_; 
v_pu_boxed_1627_ = lean_unbox(v_pu_1617_);
v_res_1628_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(v_pu_boxed_1627_, v_decl_1618_, v_params_1619_, v_inst_1620_, v_toBind_1621_, v___f_1622_, v_inst_1623_, v_f_1624_, v_value_1625_, v_____do__lift_1626_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(uint8_t v_pu_1629_, lean_object* v_decl_1630_, lean_object* v_inst_1631_, lean_object* v_toBind_1632_, lean_object* v___f_1633_, lean_object* v_inst_1634_, lean_object* v_f_1635_, lean_object* v_value_1636_, lean_object* v_type_1637_, lean_object* v_params_1638_){
_start:
{
lean_object* v___x_1639_; lean_object* v___f_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1639_ = lean_box(v_pu_1629_);
lean_inc(v_f_1635_);
lean_inc_ref(v_inst_1634_);
lean_inc(v_toBind_1632_);
v___f_1640_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed), 10, 9);
lean_closure_set(v___f_1640_, 0, v___x_1639_);
lean_closure_set(v___f_1640_, 1, v_decl_1630_);
lean_closure_set(v___f_1640_, 2, v_params_1638_);
lean_closure_set(v___f_1640_, 3, v_inst_1631_);
lean_closure_set(v___f_1640_, 4, v_toBind_1632_);
lean_closure_set(v___f_1640_, 5, v___f_1633_);
lean_closure_set(v___f_1640_, 6, v_inst_1634_);
lean_closure_set(v___f_1640_, 7, v_f_1635_);
lean_closure_set(v___f_1640_, 8, v_value_1636_);
v___x_1641_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1634_, v_f_1635_, v_type_1637_);
v___x_1642_ = lean_apply_4(v_toBind_1632_, lean_box(0), lean_box(0), v___x_1641_, v___f_1640_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed(lean_object* v_pu_1643_, lean_object* v_decl_1644_, lean_object* v_inst_1645_, lean_object* v_toBind_1646_, lean_object* v___f_1647_, lean_object* v_inst_1648_, lean_object* v_f_1649_, lean_object* v_value_1650_, lean_object* v_type_1651_, lean_object* v_params_1652_){
_start:
{
uint8_t v_pu_boxed_1653_; lean_object* v_res_1654_; 
v_pu_boxed_1653_ = lean_unbox(v_pu_1643_);
v_res_1654_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(v_pu_boxed_1653_, v_decl_1644_, v_inst_1645_, v_toBind_1646_, v___f_1647_, v_inst_1648_, v_f_1649_, v_value_1650_, v_type_1651_, v_params_1652_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(lean_object* v_k_1655_, lean_object* v_toPure_1656_, lean_object* v_decl_1657_, lean_object* v_c_1658_, uint8_t v_pu_1659_, lean_object* v_inst_1660_, lean_object* v_inst_1661_, lean_object* v_f_1662_, lean_object* v_toBind_1663_, lean_object* v_decl_1664_){
_start:
{
lean_object* v___f_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_inc_ref(v_k_1655_);
v___f_1665_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_1665_, 0, v_k_1655_);
lean_closure_set(v___f_1665_, 1, v_decl_1664_);
lean_closure_set(v___f_1665_, 2, v_toPure_1656_);
lean_closure_set(v___f_1665_, 3, v_decl_1657_);
lean_closure_set(v___f_1665_, 4, v_c_1658_);
v___x_1666_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1659_, v_inst_1660_, v_inst_1661_, v_f_1662_, v_k_1655_);
v___x_1667_ = lean_apply_4(v_toBind_1663_, lean_box(0), lean_box(0), v___x_1666_, v___f_1665_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed(lean_object* v_k_1668_, lean_object* v_toPure_1669_, lean_object* v_decl_1670_, lean_object* v_c_1671_, lean_object* v_pu_1672_, lean_object* v_inst_1673_, lean_object* v_inst_1674_, lean_object* v_f_1675_, lean_object* v_toBind_1676_, lean_object* v_decl_1677_){
_start:
{
uint8_t v_pu_boxed_1678_; lean_object* v_res_1679_; 
v_pu_boxed_1678_ = lean_unbox(v_pu_1672_);
v_res_1679_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(v_k_1668_, v_toPure_1669_, v_decl_1670_, v_c_1671_, v_pu_boxed_1678_, v_inst_1673_, v_inst_1674_, v_f_1675_, v_toBind_1676_, v_decl_1677_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed(lean_object* v_pu_1680_, lean_object* v_inst_1681_, lean_object* v_inst_1682_, lean_object* v_f_1683_, lean_object* v_x_1684_){
_start:
{
uint8_t v_pu_boxed_1685_; lean_object* v_res_1686_; 
v_pu_boxed_1685_ = lean_unbox(v_pu_1680_);
v_res_1686_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(v_pu_boxed_1685_, v_inst_1681_, v_inst_1682_, v_f_1683_, v_x_1684_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(lean_object* v_fvarId_1687_, lean_object* v_____do__lift_1688_, lean_object* v_i_1689_, lean_object* v_toPure_1690_, lean_object* v_y_1691_, lean_object* v_k_1692_, lean_object* v_c_1693_, uint8_t v_pu_1694_, lean_object* v_inst_1695_, lean_object* v_inst_1696_, lean_object* v_f_1697_, lean_object* v_toBind_1698_, lean_object* v_____do__lift_1699_){
_start:
{
lean_object* v___f_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_inc_ref(v_k_1692_);
v___f_1700_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed), 9, 8);
lean_closure_set(v___f_1700_, 0, v_fvarId_1687_);
lean_closure_set(v___f_1700_, 1, v_____do__lift_1688_);
lean_closure_set(v___f_1700_, 2, v_i_1689_);
lean_closure_set(v___f_1700_, 3, v_____do__lift_1699_);
lean_closure_set(v___f_1700_, 4, v_toPure_1690_);
lean_closure_set(v___f_1700_, 5, v_y_1691_);
lean_closure_set(v___f_1700_, 6, v_k_1692_);
lean_closure_set(v___f_1700_, 7, v_c_1693_);
v___x_1701_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1694_, v_inst_1695_, v_inst_1696_, v_f_1697_, v_k_1692_);
v___x_1702_ = lean_apply_4(v_toBind_1698_, lean_box(0), lean_box(0), v___x_1701_, v___f_1700_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed(lean_object* v_fvarId_1703_, lean_object* v_____do__lift_1704_, lean_object* v_i_1705_, lean_object* v_toPure_1706_, lean_object* v_y_1707_, lean_object* v_k_1708_, lean_object* v_c_1709_, lean_object* v_pu_1710_, lean_object* v_inst_1711_, lean_object* v_inst_1712_, lean_object* v_f_1713_, lean_object* v_toBind_1714_, lean_object* v_____do__lift_1715_){
_start:
{
uint8_t v_pu_boxed_1716_; lean_object* v_res_1717_; 
v_pu_boxed_1716_ = lean_unbox(v_pu_1710_);
v_res_1717_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(v_fvarId_1703_, v_____do__lift_1704_, v_i_1705_, v_toPure_1706_, v_y_1707_, v_k_1708_, v_c_1709_, v_pu_boxed_1716_, v_inst_1711_, v_inst_1712_, v_f_1713_, v_toBind_1714_, v_____do__lift_1715_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(lean_object* v_fvarId_1718_, lean_object* v_i_1719_, lean_object* v_toPure_1720_, lean_object* v_y_1721_, lean_object* v_k_1722_, lean_object* v_c_1723_, uint8_t v_pu_1724_, lean_object* v_inst_1725_, lean_object* v_inst_1726_, lean_object* v_f_1727_, lean_object* v_toBind_1728_, lean_object* v_____do__lift_1729_){
_start:
{
lean_object* v___x_1730_; lean_object* v___f_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1730_ = lean_box(v_pu_1724_);
lean_inc(v_toBind_1728_);
lean_inc(v_f_1727_);
lean_inc_ref(v_inst_1726_);
lean_inc(v_y_1721_);
v___f_1731_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed), 13, 12);
lean_closure_set(v___f_1731_, 0, v_fvarId_1718_);
lean_closure_set(v___f_1731_, 1, v_____do__lift_1729_);
lean_closure_set(v___f_1731_, 2, v_i_1719_);
lean_closure_set(v___f_1731_, 3, v_toPure_1720_);
lean_closure_set(v___f_1731_, 4, v_y_1721_);
lean_closure_set(v___f_1731_, 5, v_k_1722_);
lean_closure_set(v___f_1731_, 6, v_c_1723_);
lean_closure_set(v___f_1731_, 7, v___x_1730_);
lean_closure_set(v___f_1731_, 8, v_inst_1725_);
lean_closure_set(v___f_1731_, 9, v_inst_1726_);
lean_closure_set(v___f_1731_, 10, v_f_1727_);
lean_closure_set(v___f_1731_, 11, v_toBind_1728_);
v___x_1732_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_1724_, v_inst_1726_, v_f_1727_, v_y_1721_);
v___x_1733_ = lean_apply_4(v_toBind_1728_, lean_box(0), lean_box(0), v___x_1732_, v___f_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed(lean_object* v_fvarId_1734_, lean_object* v_i_1735_, lean_object* v_toPure_1736_, lean_object* v_y_1737_, lean_object* v_k_1738_, lean_object* v_c_1739_, lean_object* v_pu_1740_, lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_f_1743_, lean_object* v_toBind_1744_, lean_object* v_____do__lift_1745_){
_start:
{
uint8_t v_pu_boxed_1746_; lean_object* v_res_1747_; 
v_pu_boxed_1746_ = lean_unbox(v_pu_1740_);
v_res_1747_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(v_fvarId_1734_, v_i_1735_, v_toPure_1736_, v_y_1737_, v_k_1738_, v_c_1739_, v_pu_boxed_1746_, v_inst_1741_, v_inst_1742_, v_f_1743_, v_toBind_1744_, v_____do__lift_1745_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(lean_object* v_fvarId_1748_, lean_object* v_____do__lift_1749_, lean_object* v_i_1750_, lean_object* v_toPure_1751_, lean_object* v_y_1752_, lean_object* v_k_1753_, lean_object* v_c_1754_, uint8_t v_pu_1755_, lean_object* v_inst_1756_, lean_object* v_inst_1757_, lean_object* v_f_1758_, lean_object* v_toBind_1759_, lean_object* v_____do__lift_1760_){
_start:
{
lean_object* v___f_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_inc_ref(v_k_1753_);
v___f_1761_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed), 9, 8);
lean_closure_set(v___f_1761_, 0, v_fvarId_1748_);
lean_closure_set(v___f_1761_, 1, v_____do__lift_1749_);
lean_closure_set(v___f_1761_, 2, v_i_1750_);
lean_closure_set(v___f_1761_, 3, v_____do__lift_1760_);
lean_closure_set(v___f_1761_, 4, v_toPure_1751_);
lean_closure_set(v___f_1761_, 5, v_y_1752_);
lean_closure_set(v___f_1761_, 6, v_k_1753_);
lean_closure_set(v___f_1761_, 7, v_c_1754_);
v___x_1762_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1755_, v_inst_1756_, v_inst_1757_, v_f_1758_, v_k_1753_);
v___x_1763_ = lean_apply_4(v_toBind_1759_, lean_box(0), lean_box(0), v___x_1762_, v___f_1761_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed(lean_object* v_fvarId_1764_, lean_object* v_____do__lift_1765_, lean_object* v_i_1766_, lean_object* v_toPure_1767_, lean_object* v_y_1768_, lean_object* v_k_1769_, lean_object* v_c_1770_, lean_object* v_pu_1771_, lean_object* v_inst_1772_, lean_object* v_inst_1773_, lean_object* v_f_1774_, lean_object* v_toBind_1775_, lean_object* v_____do__lift_1776_){
_start:
{
uint8_t v_pu_boxed_1777_; lean_object* v_res_1778_; 
v_pu_boxed_1777_ = lean_unbox(v_pu_1771_);
v_res_1778_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(v_fvarId_1764_, v_____do__lift_1765_, v_i_1766_, v_toPure_1767_, v_y_1768_, v_k_1769_, v_c_1770_, v_pu_boxed_1777_, v_inst_1772_, v_inst_1773_, v_f_1774_, v_toBind_1775_, v_____do__lift_1776_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(lean_object* v_fvarId_1779_, lean_object* v_i_1780_, lean_object* v_toPure_1781_, lean_object* v_y_1782_, lean_object* v_k_1783_, lean_object* v_c_1784_, uint8_t v_pu_1785_, lean_object* v_inst_1786_, lean_object* v_inst_1787_, lean_object* v_f_1788_, lean_object* v_toBind_1789_, lean_object* v_____do__lift_1790_){
_start:
{
lean_object* v___x_1791_; lean_object* v___f_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1791_ = lean_box(v_pu_1785_);
lean_inc(v_toBind_1789_);
lean_inc(v_f_1788_);
lean_inc(v_y_1782_);
v___f_1792_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed), 13, 12);
lean_closure_set(v___f_1792_, 0, v_fvarId_1779_);
lean_closure_set(v___f_1792_, 1, v_____do__lift_1790_);
lean_closure_set(v___f_1792_, 2, v_i_1780_);
lean_closure_set(v___f_1792_, 3, v_toPure_1781_);
lean_closure_set(v___f_1792_, 4, v_y_1782_);
lean_closure_set(v___f_1792_, 5, v_k_1783_);
lean_closure_set(v___f_1792_, 6, v_c_1784_);
lean_closure_set(v___f_1792_, 7, v___x_1791_);
lean_closure_set(v___f_1792_, 8, v_inst_1786_);
lean_closure_set(v___f_1792_, 9, v_inst_1787_);
lean_closure_set(v___f_1792_, 10, v_f_1788_);
lean_closure_set(v___f_1792_, 11, v_toBind_1789_);
v___x_1793_ = lean_apply_1(v_f_1788_, v_y_1782_);
v___x_1794_ = lean_apply_4(v_toBind_1789_, lean_box(0), lean_box(0), v___x_1793_, v___f_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed(lean_object* v_fvarId_1795_, lean_object* v_i_1796_, lean_object* v_toPure_1797_, lean_object* v_y_1798_, lean_object* v_k_1799_, lean_object* v_c_1800_, lean_object* v_pu_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_f_1804_, lean_object* v_toBind_1805_, lean_object* v_____do__lift_1806_){
_start:
{
uint8_t v_pu_boxed_1807_; lean_object* v_res_1808_; 
v_pu_boxed_1807_ = lean_unbox(v_pu_1801_);
v_res_1808_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(v_fvarId_1795_, v_i_1796_, v_toPure_1797_, v_y_1798_, v_k_1799_, v_c_1800_, v_pu_boxed_1807_, v_inst_1802_, v_inst_1803_, v_f_1804_, v_toBind_1805_, v_____do__lift_1806_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(lean_object* v_fvarId_1809_, lean_object* v_____do__lift_1810_, lean_object* v_i_1811_, lean_object* v_offset_1812_, lean_object* v_____do__lift_1813_, lean_object* v_toPure_1814_, lean_object* v_y_1815_, lean_object* v_ty_1816_, lean_object* v_k_1817_, lean_object* v_c_1818_, uint8_t v_pu_1819_, lean_object* v_inst_1820_, lean_object* v_inst_1821_, lean_object* v_f_1822_, lean_object* v_toBind_1823_, lean_object* v_____do__lift_1824_){
_start:
{
lean_object* v___f_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_inc_ref(v_k_1817_);
v___f_1825_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed), 12, 11);
lean_closure_set(v___f_1825_, 0, v_fvarId_1809_);
lean_closure_set(v___f_1825_, 1, v_____do__lift_1810_);
lean_closure_set(v___f_1825_, 2, v_i_1811_);
lean_closure_set(v___f_1825_, 3, v_offset_1812_);
lean_closure_set(v___f_1825_, 4, v_____do__lift_1813_);
lean_closure_set(v___f_1825_, 5, v_____do__lift_1824_);
lean_closure_set(v___f_1825_, 6, v_toPure_1814_);
lean_closure_set(v___f_1825_, 7, v_y_1815_);
lean_closure_set(v___f_1825_, 8, v_ty_1816_);
lean_closure_set(v___f_1825_, 9, v_k_1817_);
lean_closure_set(v___f_1825_, 10, v_c_1818_);
v___x_1826_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1819_, v_inst_1820_, v_inst_1821_, v_f_1822_, v_k_1817_);
v___x_1827_ = lean_apply_4(v_toBind_1823_, lean_box(0), lean_box(0), v___x_1826_, v___f_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed(lean_object* v_fvarId_1828_, lean_object* v_____do__lift_1829_, lean_object* v_i_1830_, lean_object* v_offset_1831_, lean_object* v_____do__lift_1832_, lean_object* v_toPure_1833_, lean_object* v_y_1834_, lean_object* v_ty_1835_, lean_object* v_k_1836_, lean_object* v_c_1837_, lean_object* v_pu_1838_, lean_object* v_inst_1839_, lean_object* v_inst_1840_, lean_object* v_f_1841_, lean_object* v_toBind_1842_, lean_object* v_____do__lift_1843_){
_start:
{
uint8_t v_pu_boxed_1844_; lean_object* v_res_1845_; 
v_pu_boxed_1844_ = lean_unbox(v_pu_1838_);
v_res_1845_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(v_fvarId_1828_, v_____do__lift_1829_, v_i_1830_, v_offset_1831_, v_____do__lift_1832_, v_toPure_1833_, v_y_1834_, v_ty_1835_, v_k_1836_, v_c_1837_, v_pu_boxed_1844_, v_inst_1839_, v_inst_1840_, v_f_1841_, v_toBind_1842_, v_____do__lift_1843_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(lean_object* v_fvarId_1846_, lean_object* v_____do__lift_1847_, lean_object* v_i_1848_, lean_object* v_offset_1849_, lean_object* v_toPure_1850_, lean_object* v_y_1851_, lean_object* v_ty_1852_, lean_object* v_k_1853_, lean_object* v_c_1854_, uint8_t v_pu_1855_, lean_object* v_inst_1856_, lean_object* v_inst_1857_, lean_object* v_f_1858_, lean_object* v_toBind_1859_, lean_object* v_____do__lift_1860_){
_start:
{
lean_object* v___x_1861_; lean_object* v___f_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1861_ = lean_box(v_pu_1855_);
lean_inc(v_toBind_1859_);
lean_inc(v_f_1858_);
lean_inc_ref(v_inst_1857_);
lean_inc_ref(v_ty_1852_);
v___f_1862_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed), 16, 15);
lean_closure_set(v___f_1862_, 0, v_fvarId_1846_);
lean_closure_set(v___f_1862_, 1, v_____do__lift_1847_);
lean_closure_set(v___f_1862_, 2, v_i_1848_);
lean_closure_set(v___f_1862_, 3, v_offset_1849_);
lean_closure_set(v___f_1862_, 4, v_____do__lift_1860_);
lean_closure_set(v___f_1862_, 5, v_toPure_1850_);
lean_closure_set(v___f_1862_, 6, v_y_1851_);
lean_closure_set(v___f_1862_, 7, v_ty_1852_);
lean_closure_set(v___f_1862_, 8, v_k_1853_);
lean_closure_set(v___f_1862_, 9, v_c_1854_);
lean_closure_set(v___f_1862_, 10, v___x_1861_);
lean_closure_set(v___f_1862_, 11, v_inst_1856_);
lean_closure_set(v___f_1862_, 12, v_inst_1857_);
lean_closure_set(v___f_1862_, 13, v_f_1858_);
lean_closure_set(v___f_1862_, 14, v_toBind_1859_);
v___x_1863_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_1857_, v_f_1858_, v_ty_1852_);
v___x_1864_ = lean_apply_4(v_toBind_1859_, lean_box(0), lean_box(0), v___x_1863_, v___f_1862_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed(lean_object* v_fvarId_1865_, lean_object* v_____do__lift_1866_, lean_object* v_i_1867_, lean_object* v_offset_1868_, lean_object* v_toPure_1869_, lean_object* v_y_1870_, lean_object* v_ty_1871_, lean_object* v_k_1872_, lean_object* v_c_1873_, lean_object* v_pu_1874_, lean_object* v_inst_1875_, lean_object* v_inst_1876_, lean_object* v_f_1877_, lean_object* v_toBind_1878_, lean_object* v_____do__lift_1879_){
_start:
{
uint8_t v_pu_boxed_1880_; lean_object* v_res_1881_; 
v_pu_boxed_1880_ = lean_unbox(v_pu_1874_);
v_res_1881_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(v_fvarId_1865_, v_____do__lift_1866_, v_i_1867_, v_offset_1868_, v_toPure_1869_, v_y_1870_, v_ty_1871_, v_k_1872_, v_c_1873_, v_pu_boxed_1880_, v_inst_1875_, v_inst_1876_, v_f_1877_, v_toBind_1878_, v_____do__lift_1879_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(lean_object* v_fvarId_1882_, lean_object* v_i_1883_, lean_object* v_offset_1884_, lean_object* v_toPure_1885_, lean_object* v_y_1886_, lean_object* v_ty_1887_, lean_object* v_k_1888_, lean_object* v_c_1889_, uint8_t v_pu_1890_, lean_object* v_inst_1891_, lean_object* v_inst_1892_, lean_object* v_f_1893_, lean_object* v_toBind_1894_, lean_object* v_____do__lift_1895_){
_start:
{
lean_object* v___x_1896_; lean_object* v___f_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1896_ = lean_box(v_pu_1890_);
lean_inc(v_toBind_1894_);
lean_inc(v_f_1893_);
lean_inc(v_y_1886_);
v___f_1897_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed), 15, 14);
lean_closure_set(v___f_1897_, 0, v_fvarId_1882_);
lean_closure_set(v___f_1897_, 1, v_____do__lift_1895_);
lean_closure_set(v___f_1897_, 2, v_i_1883_);
lean_closure_set(v___f_1897_, 3, v_offset_1884_);
lean_closure_set(v___f_1897_, 4, v_toPure_1885_);
lean_closure_set(v___f_1897_, 5, v_y_1886_);
lean_closure_set(v___f_1897_, 6, v_ty_1887_);
lean_closure_set(v___f_1897_, 7, v_k_1888_);
lean_closure_set(v___f_1897_, 8, v_c_1889_);
lean_closure_set(v___f_1897_, 9, v___x_1896_);
lean_closure_set(v___f_1897_, 10, v_inst_1891_);
lean_closure_set(v___f_1897_, 11, v_inst_1892_);
lean_closure_set(v___f_1897_, 12, v_f_1893_);
lean_closure_set(v___f_1897_, 13, v_toBind_1894_);
v___x_1898_ = lean_apply_1(v_f_1893_, v_y_1886_);
v___x_1899_ = lean_apply_4(v_toBind_1894_, lean_box(0), lean_box(0), v___x_1898_, v___f_1897_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed(lean_object* v_fvarId_1900_, lean_object* v_i_1901_, lean_object* v_offset_1902_, lean_object* v_toPure_1903_, lean_object* v_y_1904_, lean_object* v_ty_1905_, lean_object* v_k_1906_, lean_object* v_c_1907_, lean_object* v_pu_1908_, lean_object* v_inst_1909_, lean_object* v_inst_1910_, lean_object* v_f_1911_, lean_object* v_toBind_1912_, lean_object* v_____do__lift_1913_){
_start:
{
uint8_t v_pu_boxed_1914_; lean_object* v_res_1915_; 
v_pu_boxed_1914_ = lean_unbox(v_pu_1908_);
v_res_1915_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(v_fvarId_1900_, v_i_1901_, v_offset_1902_, v_toPure_1903_, v_y_1904_, v_ty_1905_, v_k_1906_, v_c_1907_, v_pu_boxed_1914_, v_inst_1909_, v_inst_1910_, v_f_1911_, v_toBind_1912_, v_____do__lift_1913_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(lean_object* v_fvarId_1916_, lean_object* v_cidx_1917_, lean_object* v_toPure_1918_, lean_object* v_k_1919_, lean_object* v_c_1920_, uint8_t v_pu_1921_, lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_f_1924_, lean_object* v_toBind_1925_, lean_object* v_____do__lift_1926_){
_start:
{
lean_object* v___f_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
lean_inc_ref(v_k_1919_);
v___f_1927_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27___boxed), 7, 6);
lean_closure_set(v___f_1927_, 0, v_fvarId_1916_);
lean_closure_set(v___f_1927_, 1, v_____do__lift_1926_);
lean_closure_set(v___f_1927_, 2, v_cidx_1917_);
lean_closure_set(v___f_1927_, 3, v_toPure_1918_);
lean_closure_set(v___f_1927_, 4, v_k_1919_);
lean_closure_set(v___f_1927_, 5, v_c_1920_);
v___x_1928_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1921_, v_inst_1922_, v_inst_1923_, v_f_1924_, v_k_1919_);
v___x_1929_ = lean_apply_4(v_toBind_1925_, lean_box(0), lean_box(0), v___x_1928_, v___f_1927_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed(lean_object* v_fvarId_1930_, lean_object* v_cidx_1931_, lean_object* v_toPure_1932_, lean_object* v_k_1933_, lean_object* v_c_1934_, lean_object* v_pu_1935_, lean_object* v_inst_1936_, lean_object* v_inst_1937_, lean_object* v_f_1938_, lean_object* v_toBind_1939_, lean_object* v_____do__lift_1940_){
_start:
{
uint8_t v_pu_boxed_1941_; lean_object* v_res_1942_; 
v_pu_boxed_1941_ = lean_unbox(v_pu_1935_);
v_res_1942_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(v_fvarId_1930_, v_cidx_1931_, v_toPure_1932_, v_k_1933_, v_c_1934_, v_pu_boxed_1941_, v_inst_1936_, v_inst_1937_, v_f_1938_, v_toBind_1939_, v_____do__lift_1940_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(lean_object* v_fvarId_1943_, lean_object* v_n_1944_, uint8_t v_check_1945_, uint8_t v_persistent_1946_, lean_object* v_toPure_1947_, lean_object* v_k_1948_, lean_object* v_c_1949_, uint8_t v_pu_1950_, lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_f_1953_, lean_object* v_toBind_1954_, lean_object* v_____do__lift_1955_){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___f_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1956_ = lean_box(v_check_1945_);
v___x_1957_ = lean_box(v_persistent_1946_);
lean_inc_ref(v_k_1948_);
v___f_1958_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29___boxed), 9, 8);
lean_closure_set(v___f_1958_, 0, v_fvarId_1943_);
lean_closure_set(v___f_1958_, 1, v_____do__lift_1955_);
lean_closure_set(v___f_1958_, 2, v_n_1944_);
lean_closure_set(v___f_1958_, 3, v___x_1956_);
lean_closure_set(v___f_1958_, 4, v___x_1957_);
lean_closure_set(v___f_1958_, 5, v_toPure_1947_);
lean_closure_set(v___f_1958_, 6, v_k_1948_);
lean_closure_set(v___f_1958_, 7, v_c_1949_);
v___x_1959_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1950_, v_inst_1951_, v_inst_1952_, v_f_1953_, v_k_1948_);
v___x_1960_ = lean_apply_4(v_toBind_1954_, lean_box(0), lean_box(0), v___x_1959_, v___f_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed(lean_object* v_fvarId_1961_, lean_object* v_n_1962_, lean_object* v_check_1963_, lean_object* v_persistent_1964_, lean_object* v_toPure_1965_, lean_object* v_k_1966_, lean_object* v_c_1967_, lean_object* v_pu_1968_, lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_f_1971_, lean_object* v_toBind_1972_, lean_object* v_____do__lift_1973_){
_start:
{
uint8_t v_check_2606__boxed_1974_; uint8_t v_persistent_2607__boxed_1975_; uint8_t v_pu_boxed_1976_; lean_object* v_res_1977_; 
v_check_2606__boxed_1974_ = lean_unbox(v_check_1963_);
v_persistent_2607__boxed_1975_ = lean_unbox(v_persistent_1964_);
v_pu_boxed_1976_ = lean_unbox(v_pu_1968_);
v_res_1977_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(v_fvarId_1961_, v_n_1962_, v_check_2606__boxed_1974_, v_persistent_2607__boxed_1975_, v_toPure_1965_, v_k_1966_, v_c_1967_, v_pu_boxed_1976_, v_inst_1969_, v_inst_1970_, v_f_1971_, v_toBind_1972_, v_____do__lift_1973_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(lean_object* v_fvarId_1978_, lean_object* v_n_1979_, uint8_t v_check_1980_, uint8_t v_persistent_1981_, lean_object* v_objs_x3f_1982_, lean_object* v_toPure_1983_, lean_object* v_k_1984_, lean_object* v_c_1985_, uint8_t v_pu_1986_, lean_object* v_inst_1987_, lean_object* v_inst_1988_, lean_object* v_f_1989_, lean_object* v_toBind_1990_, lean_object* v_____do__lift_1991_){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___f_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1992_ = lean_box(v_check_1980_);
v___x_1993_ = lean_box(v_persistent_1981_);
lean_inc_ref(v_k_1984_);
v___f_1994_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed), 10, 9);
lean_closure_set(v___f_1994_, 0, v_fvarId_1978_);
lean_closure_set(v___f_1994_, 1, v_____do__lift_1991_);
lean_closure_set(v___f_1994_, 2, v_n_1979_);
lean_closure_set(v___f_1994_, 3, v___x_1992_);
lean_closure_set(v___f_1994_, 4, v___x_1993_);
lean_closure_set(v___f_1994_, 5, v_objs_x3f_1982_);
lean_closure_set(v___f_1994_, 6, v_toPure_1983_);
lean_closure_set(v___f_1994_, 7, v_k_1984_);
lean_closure_set(v___f_1994_, 8, v_c_1985_);
v___x_1995_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_1986_, v_inst_1987_, v_inst_1988_, v_f_1989_, v_k_1984_);
v___x_1996_ = lean_apply_4(v_toBind_1990_, lean_box(0), lean_box(0), v___x_1995_, v___f_1994_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed(lean_object* v_fvarId_1997_, lean_object* v_n_1998_, lean_object* v_check_1999_, lean_object* v_persistent_2000_, lean_object* v_objs_x3f_2001_, lean_object* v_toPure_2002_, lean_object* v_k_2003_, lean_object* v_c_2004_, lean_object* v_pu_2005_, lean_object* v_inst_2006_, lean_object* v_inst_2007_, lean_object* v_f_2008_, lean_object* v_toBind_2009_, lean_object* v_____do__lift_2010_){
_start:
{
uint8_t v_check_2617__boxed_2011_; uint8_t v_persistent_2618__boxed_2012_; uint8_t v_pu_boxed_2013_; lean_object* v_res_2014_; 
v_check_2617__boxed_2011_ = lean_unbox(v_check_1999_);
v_persistent_2618__boxed_2012_ = lean_unbox(v_persistent_2000_);
v_pu_boxed_2013_ = lean_unbox(v_pu_2005_);
v_res_2014_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(v_fvarId_1997_, v_n_1998_, v_check_2617__boxed_2011_, v_persistent_2618__boxed_2012_, v_objs_x3f_2001_, v_toPure_2002_, v_k_2003_, v_c_2004_, v_pu_boxed_2013_, v_inst_2006_, v_inst_2007_, v_f_2008_, v_toBind_2009_, v_____do__lift_2010_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(lean_object* v_fvarId_2015_, lean_object* v_toPure_2016_, lean_object* v_k_2017_, lean_object* v_c_2018_, uint8_t v_pu_2019_, lean_object* v_inst_2020_, lean_object* v_inst_2021_, lean_object* v_f_2022_, lean_object* v_toBind_2023_, lean_object* v_____do__lift_2024_){
_start:
{
lean_object* v___f_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_inc_ref(v_k_2017_);
v___f_2025_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed), 6, 5);
lean_closure_set(v___f_2025_, 0, v_fvarId_2015_);
lean_closure_set(v___f_2025_, 1, v_____do__lift_2024_);
lean_closure_set(v___f_2025_, 2, v_toPure_2016_);
lean_closure_set(v___f_2025_, 3, v_k_2017_);
lean_closure_set(v___f_2025_, 4, v_c_2018_);
v___x_2026_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2019_, v_inst_2020_, v_inst_2021_, v_f_2022_, v_k_2017_);
v___x_2027_ = lean_apply_4(v_toBind_2023_, lean_box(0), lean_box(0), v___x_2026_, v___f_2025_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed(lean_object* v_fvarId_2028_, lean_object* v_toPure_2029_, lean_object* v_k_2030_, lean_object* v_c_2031_, lean_object* v_pu_2032_, lean_object* v_inst_2033_, lean_object* v_inst_2034_, lean_object* v_f_2035_, lean_object* v_toBind_2036_, lean_object* v_____do__lift_2037_){
_start:
{
uint8_t v_pu_boxed_2038_; lean_object* v_res_2039_; 
v_pu_boxed_2038_ = lean_unbox(v_pu_2032_);
v_res_2039_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(v_fvarId_2028_, v_toPure_2029_, v_k_2030_, v_c_2031_, v_pu_boxed_2038_, v_inst_2033_, v_inst_2034_, v_f_2035_, v_toBind_2036_, v_____do__lift_2037_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(uint8_t v_pu_2040_, lean_object* v_inst_2041_, lean_object* v_inst_2042_, lean_object* v_f_2043_, lean_object* v_c_2044_){
_start:
{
switch(lean_obj_tag(v_c_2044_))
{
case 0:
{
lean_object* v_toApplicative_2045_; lean_object* v_toBind_2046_; lean_object* v_toPure_2047_; lean_object* v_decl_2048_; lean_object* v_k_2049_; lean_object* v___x_2050_; lean_object* v___f_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v_toApplicative_2045_ = lean_ctor_get(v_inst_2042_, 0);
v_toBind_2046_ = lean_ctor_get(v_inst_2042_, 1);
lean_inc_n(v_toBind_2046_, 2);
v_toPure_2047_ = lean_ctor_get(v_toApplicative_2045_, 1);
v_decl_2048_ = lean_ctor_get(v_c_2044_, 0);
lean_inc_ref_n(v_decl_2048_, 2);
v_k_2049_ = lean_ctor_get(v_c_2044_, 1);
lean_inc_ref(v_k_2049_);
v___x_2050_ = lean_box(v_pu_2040_);
lean_inc(v_f_2043_);
lean_inc_ref(v_inst_2042_);
lean_inc(v_inst_2041_);
lean_inc(v_toPure_2047_);
v___f_2051_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_2051_, 0, v_k_2049_);
lean_closure_set(v___f_2051_, 1, v_toPure_2047_);
lean_closure_set(v___f_2051_, 2, v_decl_2048_);
lean_closure_set(v___f_2051_, 3, v_c_2044_);
lean_closure_set(v___f_2051_, 4, v___x_2050_);
lean_closure_set(v___f_2051_, 5, v_inst_2041_);
lean_closure_set(v___f_2051_, 6, v_inst_2042_);
lean_closure_set(v___f_2051_, 7, v_f_2043_);
lean_closure_set(v___f_2051_, 8, v_toBind_2046_);
v___x_2052_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_2040_, v_inst_2041_, v_inst_2042_, v_f_2043_, v_decl_2048_);
v___x_2053_ = lean_apply_4(v_toBind_2046_, lean_box(0), lean_box(0), v___x_2052_, v___f_2051_);
return v___x_2053_;
}
case 1:
{
lean_object* v_toApplicative_2054_; lean_object* v_decl_2055_; lean_object* v_toBind_2056_; lean_object* v_toPure_2057_; lean_object* v_k_2058_; lean_object* v_params_2059_; lean_object* v_type_2060_; lean_object* v_value_2061_; lean_object* v___x_2062_; lean_object* v___f_2063_; lean_object* v___x_2064_; lean_object* v___f_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; size_t v_sz_2068_; size_t v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v_toApplicative_2054_ = lean_ctor_get(v_inst_2042_, 0);
v_decl_2055_ = lean_ctor_get(v_c_2044_, 0);
lean_inc_ref_n(v_decl_2055_, 2);
v_toBind_2056_ = lean_ctor_get(v_inst_2042_, 1);
lean_inc_n(v_toBind_2056_, 3);
v_toPure_2057_ = lean_ctor_get(v_toApplicative_2054_, 1);
v_k_2058_ = lean_ctor_get(v_c_2044_, 1);
lean_inc_ref(v_k_2058_);
v_params_2059_ = lean_ctor_get(v_decl_2055_, 2);
lean_inc_ref(v_params_2059_);
v_type_2060_ = lean_ctor_get(v_decl_2055_, 3);
lean_inc_ref(v_type_2060_);
v_value_2061_ = lean_ctor_get(v_decl_2055_, 4);
lean_inc_ref(v_value_2061_);
v___x_2062_ = lean_box(v_pu_2040_);
lean_inc_n(v_f_2043_, 2);
lean_inc_ref_n(v_inst_2042_, 3);
lean_inc_n(v_inst_2041_, 2);
lean_inc(v_toPure_2057_);
v___f_2063_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_2063_, 0, v_k_2058_);
lean_closure_set(v___f_2063_, 1, v_toPure_2057_);
lean_closure_set(v___f_2063_, 2, v_decl_2055_);
lean_closure_set(v___f_2063_, 3, v_c_2044_);
lean_closure_set(v___f_2063_, 4, v___x_2062_);
lean_closure_set(v___f_2063_, 5, v_inst_2041_);
lean_closure_set(v___f_2063_, 6, v_inst_2042_);
lean_closure_set(v___f_2063_, 7, v_f_2043_);
lean_closure_set(v___f_2063_, 8, v_toBind_2056_);
v___x_2064_ = lean_box(v_pu_2040_);
v___f_2065_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_2065_, 0, v___x_2064_);
lean_closure_set(v___f_2065_, 1, v_decl_2055_);
lean_closure_set(v___f_2065_, 2, v_inst_2041_);
lean_closure_set(v___f_2065_, 3, v_toBind_2056_);
lean_closure_set(v___f_2065_, 4, v___f_2063_);
lean_closure_set(v___f_2065_, 5, v_inst_2042_);
lean_closure_set(v___f_2065_, 6, v_f_2043_);
lean_closure_set(v___f_2065_, 7, v_value_2061_);
lean_closure_set(v___f_2065_, 8, v_type_2060_);
v___x_2066_ = lean_box(v_pu_2040_);
v___x_2067_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2067_, 0, lean_box(0));
lean_closure_set(v___x_2067_, 1, v___x_2066_);
lean_closure_set(v___x_2067_, 2, v_inst_2041_);
lean_closure_set(v___x_2067_, 3, v_inst_2042_);
lean_closure_set(v___x_2067_, 4, v_f_2043_);
v_sz_2068_ = lean_array_size(v_params_2059_);
v___x_2069_ = ((size_t)0ULL);
v___x_2070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2042_, v___x_2067_, v_sz_2068_, v___x_2069_, v_params_2059_);
v___x_2071_ = lean_apply_4(v_toBind_2056_, lean_box(0), lean_box(0), v___x_2070_, v___f_2065_);
return v___x_2071_;
}
case 2:
{
lean_object* v_toApplicative_2072_; lean_object* v_decl_2073_; lean_object* v_toBind_2074_; lean_object* v_toPure_2075_; lean_object* v_k_2076_; lean_object* v_params_2077_; lean_object* v_type_2078_; lean_object* v_value_2079_; lean_object* v___x_2080_; lean_object* v___f_2081_; lean_object* v___x_2082_; lean_object* v___f_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; size_t v_sz_2086_; size_t v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v_toApplicative_2072_ = lean_ctor_get(v_inst_2042_, 0);
v_decl_2073_ = lean_ctor_get(v_c_2044_, 0);
lean_inc_ref_n(v_decl_2073_, 2);
v_toBind_2074_ = lean_ctor_get(v_inst_2042_, 1);
lean_inc_n(v_toBind_2074_, 3);
v_toPure_2075_ = lean_ctor_get(v_toApplicative_2072_, 1);
v_k_2076_ = lean_ctor_get(v_c_2044_, 1);
lean_inc_ref(v_k_2076_);
v_params_2077_ = lean_ctor_get(v_decl_2073_, 2);
lean_inc_ref(v_params_2077_);
v_type_2078_ = lean_ctor_get(v_decl_2073_, 3);
lean_inc_ref(v_type_2078_);
v_value_2079_ = lean_ctor_get(v_decl_2073_, 4);
lean_inc_ref(v_value_2079_);
v___x_2080_ = lean_box(v_pu_2040_);
lean_inc_n(v_f_2043_, 2);
lean_inc_ref_n(v_inst_2042_, 3);
lean_inc_n(v_inst_2041_, 2);
lean_inc(v_toPure_2075_);
v___f_2081_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed), 10, 9);
lean_closure_set(v___f_2081_, 0, v_k_2076_);
lean_closure_set(v___f_2081_, 1, v_toPure_2075_);
lean_closure_set(v___f_2081_, 2, v_decl_2073_);
lean_closure_set(v___f_2081_, 3, v_c_2044_);
lean_closure_set(v___f_2081_, 4, v___x_2080_);
lean_closure_set(v___f_2081_, 5, v_inst_2041_);
lean_closure_set(v___f_2081_, 6, v_inst_2042_);
lean_closure_set(v___f_2081_, 7, v_f_2043_);
lean_closure_set(v___f_2081_, 8, v_toBind_2074_);
v___x_2082_ = lean_box(v_pu_2040_);
v___f_2083_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_2083_, 0, v___x_2082_);
lean_closure_set(v___f_2083_, 1, v_decl_2073_);
lean_closure_set(v___f_2083_, 2, v_inst_2041_);
lean_closure_set(v___f_2083_, 3, v_toBind_2074_);
lean_closure_set(v___f_2083_, 4, v___f_2081_);
lean_closure_set(v___f_2083_, 5, v_inst_2042_);
lean_closure_set(v___f_2083_, 6, v_f_2043_);
lean_closure_set(v___f_2083_, 7, v_value_2079_);
lean_closure_set(v___f_2083_, 8, v_type_2078_);
v___x_2084_ = lean_box(v_pu_2040_);
v___x_2085_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2085_, 0, lean_box(0));
lean_closure_set(v___x_2085_, 1, v___x_2084_);
lean_closure_set(v___x_2085_, 2, v_inst_2041_);
lean_closure_set(v___x_2085_, 3, v_inst_2042_);
lean_closure_set(v___x_2085_, 4, v_f_2043_);
v_sz_2086_ = lean_array_size(v_params_2077_);
v___x_2087_ = ((size_t)0ULL);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2042_, v___x_2085_, v_sz_2086_, v___x_2087_, v_params_2077_);
v___x_2089_ = lean_apply_4(v_toBind_2074_, lean_box(0), lean_box(0), v___x_2088_, v___f_2083_);
return v___x_2089_;
}
case 3:
{
lean_object* v_toApplicative_2090_; lean_object* v_toBind_2091_; lean_object* v_toPure_2092_; lean_object* v_fvarId_2093_; lean_object* v_args_2094_; lean_object* v___x_2095_; lean_object* v___f_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_toApplicative_2090_ = lean_ctor_get(v_inst_2042_, 0);
v_toBind_2091_ = lean_ctor_get(v_inst_2042_, 1);
lean_inc_n(v_toBind_2091_, 2);
v_toPure_2092_ = lean_ctor_get(v_toApplicative_2090_, 1);
lean_inc(v_toPure_2092_);
v_fvarId_2093_ = lean_ctor_get(v_c_2044_, 0);
lean_inc_n(v_fvarId_2093_, 2);
v_args_2094_ = lean_ctor_get(v_c_2044_, 1);
lean_inc_ref(v_args_2094_);
v___x_2095_ = lean_box(v_pu_2040_);
lean_inc(v_f_2043_);
v___f_2096_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_2096_, 0, v_toPure_2092_);
lean_closure_set(v___f_2096_, 1, v_c_2044_);
lean_closure_set(v___f_2096_, 2, v_fvarId_2093_);
lean_closure_set(v___f_2096_, 3, v_args_2094_);
lean_closure_set(v___f_2096_, 4, v___x_2095_);
lean_closure_set(v___f_2096_, 5, v_inst_2041_);
lean_closure_set(v___f_2096_, 6, v_inst_2042_);
lean_closure_set(v___f_2096_, 7, v_f_2043_);
lean_closure_set(v___f_2096_, 8, v_toBind_2091_);
v___x_2097_ = lean_apply_1(v_f_2043_, v_fvarId_2093_);
v___x_2098_ = lean_apply_4(v_toBind_2091_, lean_box(0), lean_box(0), v___x_2097_, v___f_2096_);
return v___x_2098_;
}
case 4:
{
lean_object* v_toApplicative_2099_; lean_object* v_cases_2100_; lean_object* v_toBind_2101_; lean_object* v_toPure_2102_; lean_object* v_typeName_2103_; lean_object* v_resultType_2104_; lean_object* v_discr_2105_; lean_object* v_alts_2106_; lean_object* v___x_2107_; lean_object* v___f_2108_; lean_object* v___f_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v_toApplicative_2099_ = lean_ctor_get(v_inst_2042_, 0);
v_cases_2100_ = lean_ctor_get(v_c_2044_, 0);
v_toBind_2101_ = lean_ctor_get(v_inst_2042_, 1);
lean_inc_n(v_toBind_2101_, 2);
v_toPure_2102_ = lean_ctor_get(v_toApplicative_2099_, 1);
v_typeName_2103_ = lean_ctor_get(v_cases_2100_, 0);
lean_inc(v_typeName_2103_);
v_resultType_2104_ = lean_ctor_get(v_cases_2100_, 1);
lean_inc_ref_n(v_resultType_2104_, 2);
v_discr_2105_ = lean_ctor_get(v_cases_2100_, 2);
lean_inc(v_discr_2105_);
v_alts_2106_ = lean_ctor_get(v_cases_2100_, 3);
lean_inc_ref(v_alts_2106_);
v___x_2107_ = lean_box(v_pu_2040_);
lean_inc_n(v_f_2043_, 2);
lean_inc_ref_n(v_inst_2042_, 2);
v___f_2108_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed), 5, 4);
lean_closure_set(v___f_2108_, 0, v___x_2107_);
lean_closure_set(v___f_2108_, 1, v_inst_2041_);
lean_closure_set(v___f_2108_, 2, v_inst_2042_);
lean_closure_set(v___f_2108_, 3, v_f_2043_);
lean_inc(v_toPure_2102_);
v___f_2109_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14), 11, 10);
lean_closure_set(v___f_2109_, 0, v_typeName_2103_);
lean_closure_set(v___f_2109_, 1, v_toPure_2102_);
lean_closure_set(v___f_2109_, 2, v_alts_2106_);
lean_closure_set(v___f_2109_, 3, v_resultType_2104_);
lean_closure_set(v___f_2109_, 4, v_discr_2105_);
lean_closure_set(v___f_2109_, 5, v_c_2044_);
lean_closure_set(v___f_2109_, 6, v_inst_2042_);
lean_closure_set(v___f_2109_, 7, v___f_2108_);
lean_closure_set(v___f_2109_, 8, v_toBind_2101_);
lean_closure_set(v___f_2109_, 9, v_f_2043_);
v___x_2110_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2042_, v_f_2043_, v_resultType_2104_);
v___x_2111_ = lean_apply_4(v_toBind_2101_, lean_box(0), lean_box(0), v___x_2110_, v___f_2109_);
return v___x_2111_;
}
case 5:
{
lean_object* v_toApplicative_2112_; lean_object* v_toBind_2113_; lean_object* v_toPure_2114_; lean_object* v_fvarId_2115_; lean_object* v___f_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_toApplicative_2112_ = lean_ctor_get(v_inst_2042_, 0);
lean_inc_ref(v_toApplicative_2112_);
lean_dec(v_inst_2041_);
v_toBind_2113_ = lean_ctor_get(v_inst_2042_, 1);
lean_inc(v_toBind_2113_);
lean_dec_ref(v_inst_2042_);
v_toPure_2114_ = lean_ctor_get(v_toApplicative_2112_, 1);
lean_inc(v_toPure_2114_);
lean_dec_ref(v_toApplicative_2112_);
v_fvarId_2115_ = lean_ctor_get(v_c_2044_, 0);
lean_inc_n(v_fvarId_2115_, 2);
v___f_2116_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed), 4, 3);
lean_closure_set(v___f_2116_, 0, v_fvarId_2115_);
lean_closure_set(v___f_2116_, 1, v_toPure_2114_);
lean_closure_set(v___f_2116_, 2, v_c_2044_);
v___x_2117_ = lean_apply_1(v_f_2043_, v_fvarId_2115_);
v___x_2118_ = lean_apply_4(v_toBind_2113_, lean_box(0), lean_box(0), v___x_2117_, v___f_2116_);
return v___x_2118_;
}
case 6:
{
lean_object* v_toApplicative_2119_; lean_object* v_toBind_2120_; lean_object* v_toPure_2121_; lean_object* v_type_2122_; lean_object* v___f_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v_toApplicative_2119_ = lean_ctor_get(v_inst_2042_, 0);
lean_dec(v_inst_2041_);
v_toBind_2120_ = lean_ctor_get(v_inst_2042_, 1);
lean_inc(v_toBind_2120_);
v_toPure_2121_ = lean_ctor_get(v_toApplicative_2119_, 1);
v_type_2122_ = lean_ctor_get(v_c_2044_, 0);
lean_inc_ref_n(v_type_2122_, 2);
lean_inc(v_toPure_2121_);
v___f_2123_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed), 4, 3);
lean_closure_set(v___f_2123_, 0, v_type_2122_);
lean_closure_set(v___f_2123_, 1, v_toPure_2121_);
lean_closure_set(v___f_2123_, 2, v_c_2044_);
v___x_2124_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2042_, v_f_2043_, v_type_2122_);
v___x_2125_ = lean_apply_4(v_toBind_2120_, lean_box(0), lean_box(0), v___x_2124_, v___f_2123_);
return v___x_2125_;
}
case 7:
{
lean_object* v_toApplicative_2126_; lean_object* v_toBind_2127_; lean_object* v_toPure_2128_; lean_object* v_fvarId_2129_; lean_object* v_i_2130_; lean_object* v_y_2131_; lean_object* v_k_2132_; lean_object* v___x_2133_; lean_object* v___f_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v_toApplicative_2126_ = lean_ctor_get(v_inst_2042_, 0);
v_toBind_2127_ = lean_ctor_get(v_inst_2042_, 1);
lean_inc_n(v_toBind_2127_, 2);
v_toPure_2128_ = lean_ctor_get(v_toApplicative_2126_, 1);
lean_inc(v_toPure_2128_);
v_fvarId_2129_ = lean_ctor_get(v_c_2044_, 0);
lean_inc_n(v_fvarId_2129_, 2);
v_i_2130_ = lean_ctor_get(v_c_2044_, 1);
lean_inc(v_i_2130_);
v_y_2131_ = lean_ctor_get(v_c_2044_, 2);
lean_inc(v_y_2131_);
v_k_2132_ = lean_ctor_get(v_c_2044_, 3);
lean_inc_ref(v_k_2132_);
v___x_2133_ = lean_box(v_pu_2040_);
lean_inc(v_f_2043_);
v___f_2134_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed), 12, 11);
lean_closure_set(v___f_2134_, 0, v_fvarId_2129_);
lean_closure_set(v___f_2134_, 1, v_i_2130_);
lean_closure_set(v___f_2134_, 2, v_toPure_2128_);
lean_closure_set(v___f_2134_, 3, v_y_2131_);
lean_closure_set(v___f_2134_, 4, v_k_2132_);
lean_closure_set(v___f_2134_, 5, v_c_2044_);
lean_closure_set(v___f_2134_, 6, v___x_2133_);
lean_closure_set(v___f_2134_, 7, v_inst_2041_);
lean_closure_set(v___f_2134_, 8, v_inst_2042_);
lean_closure_set(v___f_2134_, 9, v_f_2043_);
lean_closure_set(v___f_2134_, 10, v_toBind_2127_);
v___x_2135_ = lean_apply_1(v_f_2043_, v_fvarId_2129_);
v___x_2136_ = lean_apply_4(v_toBind_2127_, lean_box(0), lean_box(0), v___x_2135_, v___f_2134_);
return v___x_2136_;
}
case 8:
{
lean_object* v_toApplicative_2137_; lean_object* v_toBind_2138_; lean_object* v_toPure_2139_; lean_object* v_fvarId_2140_; lean_object* v_i_2141_; lean_object* v_y_2142_; lean_object* v_k_2143_; lean_object* v___x_2144_; lean_object* v___f_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_toApplicative_2137_ = lean_ctor_get(v_inst_2042_, 0);
v_toBind_2138_ = lean_ctor_get(v_inst_2042_, 1);
lean_inc_n(v_toBind_2138_, 2);
v_toPure_2139_ = lean_ctor_get(v_toApplicative_2137_, 1);
lean_inc(v_toPure_2139_);
v_fvarId_2140_ = lean_ctor_get(v_c_2044_, 0);
lean_inc_n(v_fvarId_2140_, 2);
v_i_2141_ = lean_ctor_get(v_c_2044_, 1);
lean_inc(v_i_2141_);
v_y_2142_ = lean_ctor_get(v_c_2044_, 2);
lean_inc(v_y_2142_);
v_k_2143_ = lean_ctor_get(v_c_2044_, 3);
lean_inc_ref(v_k_2143_);
v___x_2144_ = lean_box(v_pu_2040_);
lean_inc(v_f_2043_);
v___f_2145_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed), 12, 11);
lean_closure_set(v___f_2145_, 0, v_fvarId_2140_);
lean_closure_set(v___f_2145_, 1, v_i_2141_);
lean_closure_set(v___f_2145_, 2, v_toPure_2139_);
lean_closure_set(v___f_2145_, 3, v_y_2142_);
lean_closure_set(v___f_2145_, 4, v_k_2143_);
lean_closure_set(v___f_2145_, 5, v_c_2044_);
lean_closure_set(v___f_2145_, 6, v___x_2144_);
lean_closure_set(v___f_2145_, 7, v_inst_2041_);
lean_closure_set(v___f_2145_, 8, v_inst_2042_);
lean_closure_set(v___f_2145_, 9, v_f_2043_);
lean_closure_set(v___f_2145_, 10, v_toBind_2138_);
v___x_2146_ = lean_apply_1(v_f_2043_, v_fvarId_2140_);
v___x_2147_ = lean_apply_4(v_toBind_2138_, lean_box(0), lean_box(0), v___x_2146_, v___f_2145_);
return v___x_2147_;
}
case 9:
{
lean_object* v_toApplicative_2148_; lean_object* v_toBind_2149_; lean_object* v_toPure_2150_; lean_object* v_fvarId_2151_; lean_object* v_i_2152_; lean_object* v_offset_2153_; lean_object* v_y_2154_; lean_object* v_ty_2155_; lean_object* v_k_2156_; lean_object* v___x_2157_; lean_object* v___f_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v_toApplicative_2148_ = lean_ctor_get(v_inst_2042_, 0);
v_toBind_2149_ = lean_ctor_get(v_inst_2042_, 1);
lean_inc_n(v_toBind_2149_, 2);
v_toPure_2150_ = lean_ctor_get(v_toApplicative_2148_, 1);
lean_inc(v_toPure_2150_);
v_fvarId_2151_ = lean_ctor_get(v_c_2044_, 0);
lean_inc_n(v_fvarId_2151_, 2);
v_i_2152_ = lean_ctor_get(v_c_2044_, 1);
lean_inc(v_i_2152_);
v_offset_2153_ = lean_ctor_get(v_c_2044_, 2);
lean_inc(v_offset_2153_);
v_y_2154_ = lean_ctor_get(v_c_2044_, 3);
lean_inc(v_y_2154_);
v_ty_2155_ = lean_ctor_get(v_c_2044_, 4);
lean_inc_ref(v_ty_2155_);
v_k_2156_ = lean_ctor_get(v_c_2044_, 5);
lean_inc_ref(v_k_2156_);
v___x_2157_ = lean_box(v_pu_2040_);
lean_inc(v_f_2043_);
v___f_2158_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed), 14, 13);
lean_closure_set(v___f_2158_, 0, v_fvarId_2151_);
lean_closure_set(v___f_2158_, 1, v_i_2152_);
lean_closure_set(v___f_2158_, 2, v_offset_2153_);
lean_closure_set(v___f_2158_, 3, v_toPure_2150_);
lean_closure_set(v___f_2158_, 4, v_y_2154_);
lean_closure_set(v___f_2158_, 5, v_ty_2155_);
lean_closure_set(v___f_2158_, 6, v_k_2156_);
lean_closure_set(v___f_2158_, 7, v_c_2044_);
lean_closure_set(v___f_2158_, 8, v___x_2157_);
lean_closure_set(v___f_2158_, 9, v_inst_2041_);
lean_closure_set(v___f_2158_, 10, v_inst_2042_);
lean_closure_set(v___f_2158_, 11, v_f_2043_);
lean_closure_set(v___f_2158_, 12, v_toBind_2149_);
v___x_2159_ = lean_apply_1(v_f_2043_, v_fvarId_2151_);
v___x_2160_ = lean_apply_4(v_toBind_2149_, lean_box(0), lean_box(0), v___x_2159_, v___f_2158_);
return v___x_2160_;
}
case 10:
{
lean_object* v_toApplicative_2161_; lean_object* v_toBind_2162_; lean_object* v_toPure_2163_; lean_object* v_fvarId_2164_; lean_object* v_cidx_2165_; lean_object* v_k_2166_; lean_object* v___x_2167_; lean_object* v___f_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_toApplicative_2161_ = lean_ctor_get(v_inst_2042_, 0);
v_toBind_2162_ = lean_ctor_get(v_inst_2042_, 1);
lean_inc_n(v_toBind_2162_, 2);
v_toPure_2163_ = lean_ctor_get(v_toApplicative_2161_, 1);
lean_inc(v_toPure_2163_);
v_fvarId_2164_ = lean_ctor_get(v_c_2044_, 0);
lean_inc_n(v_fvarId_2164_, 2);
v_cidx_2165_ = lean_ctor_get(v_c_2044_, 1);
lean_inc(v_cidx_2165_);
v_k_2166_ = lean_ctor_get(v_c_2044_, 2);
lean_inc_ref(v_k_2166_);
v___x_2167_ = lean_box(v_pu_2040_);
lean_inc(v_f_2043_);
v___f_2168_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed), 11, 10);
lean_closure_set(v___f_2168_, 0, v_fvarId_2164_);
lean_closure_set(v___f_2168_, 1, v_cidx_2165_);
lean_closure_set(v___f_2168_, 2, v_toPure_2163_);
lean_closure_set(v___f_2168_, 3, v_k_2166_);
lean_closure_set(v___f_2168_, 4, v_c_2044_);
lean_closure_set(v___f_2168_, 5, v___x_2167_);
lean_closure_set(v___f_2168_, 6, v_inst_2041_);
lean_closure_set(v___f_2168_, 7, v_inst_2042_);
lean_closure_set(v___f_2168_, 8, v_f_2043_);
lean_closure_set(v___f_2168_, 9, v_toBind_2162_);
v___x_2169_ = lean_apply_1(v_f_2043_, v_fvarId_2164_);
v___x_2170_ = lean_apply_4(v_toBind_2162_, lean_box(0), lean_box(0), v___x_2169_, v___f_2168_);
return v___x_2170_;
}
case 11:
{
lean_object* v_toApplicative_2171_; lean_object* v_toBind_2172_; lean_object* v_toPure_2173_; lean_object* v_fvarId_2174_; lean_object* v_n_2175_; uint8_t v_check_2176_; uint8_t v_persistent_2177_; lean_object* v_k_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___f_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v_toApplicative_2171_ = lean_ctor_get(v_inst_2042_, 0);
v_toBind_2172_ = lean_ctor_get(v_inst_2042_, 1);
lean_inc_n(v_toBind_2172_, 2);
v_toPure_2173_ = lean_ctor_get(v_toApplicative_2171_, 1);
lean_inc(v_toPure_2173_);
v_fvarId_2174_ = lean_ctor_get(v_c_2044_, 0);
lean_inc_n(v_fvarId_2174_, 2);
v_n_2175_ = lean_ctor_get(v_c_2044_, 1);
lean_inc(v_n_2175_);
v_check_2176_ = lean_ctor_get_uint8(v_c_2044_, sizeof(void*)*3);
v_persistent_2177_ = lean_ctor_get_uint8(v_c_2044_, sizeof(void*)*3 + 1);
v_k_2178_ = lean_ctor_get(v_c_2044_, 2);
lean_inc_ref(v_k_2178_);
v___x_2179_ = lean_box(v_check_2176_);
v___x_2180_ = lean_box(v_persistent_2177_);
v___x_2181_ = lean_box(v_pu_2040_);
lean_inc(v_f_2043_);
v___f_2182_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed), 13, 12);
lean_closure_set(v___f_2182_, 0, v_fvarId_2174_);
lean_closure_set(v___f_2182_, 1, v_n_2175_);
lean_closure_set(v___f_2182_, 2, v___x_2179_);
lean_closure_set(v___f_2182_, 3, v___x_2180_);
lean_closure_set(v___f_2182_, 4, v_toPure_2173_);
lean_closure_set(v___f_2182_, 5, v_k_2178_);
lean_closure_set(v___f_2182_, 6, v_c_2044_);
lean_closure_set(v___f_2182_, 7, v___x_2181_);
lean_closure_set(v___f_2182_, 8, v_inst_2041_);
lean_closure_set(v___f_2182_, 9, v_inst_2042_);
lean_closure_set(v___f_2182_, 10, v_f_2043_);
lean_closure_set(v___f_2182_, 11, v_toBind_2172_);
v___x_2183_ = lean_apply_1(v_f_2043_, v_fvarId_2174_);
v___x_2184_ = lean_apply_4(v_toBind_2172_, lean_box(0), lean_box(0), v___x_2183_, v___f_2182_);
return v___x_2184_;
}
case 12:
{
lean_object* v_toApplicative_2185_; lean_object* v_toBind_2186_; lean_object* v_toPure_2187_; lean_object* v_fvarId_2188_; lean_object* v_n_2189_; uint8_t v_check_2190_; uint8_t v_persistent_2191_; lean_object* v_objs_x3f_2192_; lean_object* v_k_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___f_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v_toApplicative_2185_ = lean_ctor_get(v_inst_2042_, 0);
v_toBind_2186_ = lean_ctor_get(v_inst_2042_, 1);
lean_inc_n(v_toBind_2186_, 2);
v_toPure_2187_ = lean_ctor_get(v_toApplicative_2185_, 1);
lean_inc(v_toPure_2187_);
v_fvarId_2188_ = lean_ctor_get(v_c_2044_, 0);
lean_inc_n(v_fvarId_2188_, 2);
v_n_2189_ = lean_ctor_get(v_c_2044_, 1);
lean_inc(v_n_2189_);
v_check_2190_ = lean_ctor_get_uint8(v_c_2044_, sizeof(void*)*4);
v_persistent_2191_ = lean_ctor_get_uint8(v_c_2044_, sizeof(void*)*4 + 1);
v_objs_x3f_2192_ = lean_ctor_get(v_c_2044_, 2);
lean_inc(v_objs_x3f_2192_);
v_k_2193_ = lean_ctor_get(v_c_2044_, 3);
lean_inc_ref(v_k_2193_);
v___x_2194_ = lean_box(v_check_2190_);
v___x_2195_ = lean_box(v_persistent_2191_);
v___x_2196_ = lean_box(v_pu_2040_);
lean_inc(v_f_2043_);
v___f_2197_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed), 14, 13);
lean_closure_set(v___f_2197_, 0, v_fvarId_2188_);
lean_closure_set(v___f_2197_, 1, v_n_2189_);
lean_closure_set(v___f_2197_, 2, v___x_2194_);
lean_closure_set(v___f_2197_, 3, v___x_2195_);
lean_closure_set(v___f_2197_, 4, v_objs_x3f_2192_);
lean_closure_set(v___f_2197_, 5, v_toPure_2187_);
lean_closure_set(v___f_2197_, 6, v_k_2193_);
lean_closure_set(v___f_2197_, 7, v_c_2044_);
lean_closure_set(v___f_2197_, 8, v___x_2196_);
lean_closure_set(v___f_2197_, 9, v_inst_2041_);
lean_closure_set(v___f_2197_, 10, v_inst_2042_);
lean_closure_set(v___f_2197_, 11, v_f_2043_);
lean_closure_set(v___f_2197_, 12, v_toBind_2186_);
v___x_2198_ = lean_apply_1(v_f_2043_, v_fvarId_2188_);
v___x_2199_ = lean_apply_4(v_toBind_2186_, lean_box(0), lean_box(0), v___x_2198_, v___f_2197_);
return v___x_2199_;
}
default: 
{
lean_object* v_toApplicative_2200_; lean_object* v_toBind_2201_; lean_object* v_toPure_2202_; lean_object* v_fvarId_2203_; lean_object* v_k_2204_; lean_object* v___x_2205_; lean_object* v___f_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v_toApplicative_2200_ = lean_ctor_get(v_inst_2042_, 0);
v_toBind_2201_ = lean_ctor_get(v_inst_2042_, 1);
lean_inc_n(v_toBind_2201_, 2);
v_toPure_2202_ = lean_ctor_get(v_toApplicative_2200_, 1);
lean_inc(v_toPure_2202_);
v_fvarId_2203_ = lean_ctor_get(v_c_2044_, 0);
lean_inc_n(v_fvarId_2203_, 2);
v_k_2204_ = lean_ctor_get(v_c_2044_, 1);
lean_inc_ref(v_k_2204_);
v___x_2205_ = lean_box(v_pu_2040_);
lean_inc(v_f_2043_);
v___f_2206_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed), 10, 9);
lean_closure_set(v___f_2206_, 0, v_fvarId_2203_);
lean_closure_set(v___f_2206_, 1, v_toPure_2202_);
lean_closure_set(v___f_2206_, 2, v_k_2204_);
lean_closure_set(v___f_2206_, 3, v_c_2044_);
lean_closure_set(v___f_2206_, 4, v___x_2205_);
lean_closure_set(v___f_2206_, 5, v_inst_2041_);
lean_closure_set(v___f_2206_, 6, v_inst_2042_);
lean_closure_set(v___f_2206_, 7, v_f_2043_);
lean_closure_set(v___f_2206_, 8, v_toBind_2201_);
v___x_2207_ = lean_apply_1(v_f_2043_, v_fvarId_2203_);
v___x_2208_ = lean_apply_4(v_toBind_2201_, lean_box(0), lean_box(0), v___x_2207_, v___f_2206_);
return v___x_2208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed(lean_object* v_pu_2209_, lean_object* v_inst_2210_, lean_object* v_inst_2211_, lean_object* v_f_2212_, lean_object* v_c_2213_){
_start:
{
uint8_t v_pu_boxed_2214_; lean_object* v_res_2215_; 
v_pu_boxed_2214_ = lean_unbox(v_pu_2209_);
v_res_2215_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_boxed_2214_, v_inst_2210_, v_inst_2211_, v_f_2212_, v_c_2213_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(uint8_t v_pu_2216_, lean_object* v_inst_2217_, lean_object* v_inst_2218_, lean_object* v_f_2219_, lean_object* v_x_2220_){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2221_ = lean_box(v_pu_2216_);
lean_inc_ref(v_inst_2218_);
v___x_2222_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed), 5, 4);
lean_closure_set(v___x_2222_, 0, v___x_2221_);
lean_closure_set(v___x_2222_, 1, v_inst_2217_);
lean_closure_set(v___x_2222_, 2, v_inst_2218_);
lean_closure_set(v___x_2222_, 3, v_f_2219_);
v___x_2223_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg(v_inst_2218_, v_x_2220_, v___x_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM(lean_object* v_m_2224_, uint8_t v_pu_2225_, lean_object* v_inst_2226_, lean_object* v_inst_2227_, lean_object* v_f_2228_, lean_object* v_c_2229_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2225_, v_inst_2226_, v_inst_2227_, v_f_2228_, v_c_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___boxed(lean_object* v_m_2231_, lean_object* v_pu_2232_, lean_object* v_inst_2233_, lean_object* v_inst_2234_, lean_object* v_f_2235_, lean_object* v_c_2236_){
_start:
{
uint8_t v_pu_boxed_2237_; lean_object* v_res_2238_; 
v_pu_boxed_2237_ = lean_unbox(v_pu_2232_);
v_res_2238_ = l_Lean_Compiler_LCNF_Code_mapFVarM(v_m_2231_, v_pu_boxed_2237_, v_inst_2233_, v_inst_2234_, v_f_2235_, v_c_2236_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1(lean_object* v_inst_2239_, lean_object* v_f_2240_, lean_object* v_type_2241_, lean_object* v_toBind_2242_, lean_object* v___f_2243_, lean_object* v_____r_2244_){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2239_, v_f_2240_, v_type_2241_);
v___x_2246_ = lean_apply_4(v_toBind_2242_, lean_box(0), lean_box(0), v___x_2245_, v___f_2243_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12(lean_object* v_inst_2247_, lean_object* v_f_2248_, lean_object* v_ty_2249_, lean_object* v_toBind_2250_, lean_object* v___f_2251_, lean_object* v_____r_2252_){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2247_, v_f_2248_, v_ty_2249_);
v___x_2254_ = lean_apply_4(v_toBind_2250_, lean_box(0), lean_box(0), v___x_2253_, v___f_2251_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4(lean_object* v_toApplicative_2255_, lean_object* v_args_2256_, lean_object* v_inst_2257_, lean_object* v___f_2258_, lean_object* v_____r_2259_){
_start:
{
lean_object* v_toPure_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; 
v_toPure_2260_ = lean_ctor_get(v_toApplicative_2255_, 1);
lean_inc(v_toPure_2260_);
lean_dec_ref(v_toApplicative_2255_);
v___x_2261_ = lean_unsigned_to_nat(0u);
v___x_2262_ = lean_array_get_size(v_args_2256_);
v___x_2263_ = lean_box(0);
v___x_2264_ = lean_nat_dec_lt(v___x_2261_, v___x_2262_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; 
lean_dec(v___f_2258_);
lean_dec_ref(v_inst_2257_);
lean_dec_ref(v_args_2256_);
v___x_2265_ = lean_apply_2(v_toPure_2260_, lean_box(0), v___x_2263_);
return v___x_2265_;
}
else
{
uint8_t v___x_2266_; 
v___x_2266_ = lean_nat_dec_le(v___x_2262_, v___x_2262_);
if (v___x_2266_ == 0)
{
if (v___x_2264_ == 0)
{
lean_object* v___x_2267_; 
lean_dec(v___f_2258_);
lean_dec_ref(v_inst_2257_);
lean_dec_ref(v_args_2256_);
v___x_2267_ = lean_apply_2(v_toPure_2260_, lean_box(0), v___x_2263_);
return v___x_2267_;
}
else
{
size_t v___x_2268_; size_t v___x_2269_; lean_object* v___x_2270_; 
lean_dec(v_toPure_2260_);
v___x_2268_ = ((size_t)0ULL);
v___x_2269_ = lean_usize_of_nat(v___x_2262_);
v___x_2270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2257_, v___f_2258_, v_args_2256_, v___x_2268_, v___x_2269_, v___x_2263_);
return v___x_2270_;
}
}
else
{
size_t v___x_2271_; size_t v___x_2272_; lean_object* v___x_2273_; 
lean_dec(v_toPure_2260_);
v___x_2271_ = ((size_t)0ULL);
v___x_2272_ = lean_usize_of_nat(v___x_2262_);
v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2257_, v___f_2258_, v_args_2256_, v___x_2271_, v___x_2272_, v___x_2263_);
return v___x_2273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3(lean_object* v_inst_2274_, lean_object* v_f_2275_, lean_object* v_x_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_2274_, v_f_2275_, v___y_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10(lean_object* v_inst_2279_, lean_object* v_f_2280_, lean_object* v_y_2281_, lean_object* v_toBind_2282_, lean_object* v___f_2283_, lean_object* v_____r_2284_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2279_, v_f_2280_, v_y_2281_);
v___x_2286_ = lean_apply_4(v_toBind_2282_, lean_box(0), lean_box(0), v___x_2285_, v___f_2283_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11(lean_object* v_f_2287_, lean_object* v_y_2288_, lean_object* v_toBind_2289_, lean_object* v___f_2290_, lean_object* v_____r_2291_){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = lean_apply_1(v_f_2287_, v_y_2288_);
v___x_2293_ = lean_apply_4(v_toBind_2289_, lean_box(0), lean_box(0), v___x_2292_, v___f_2290_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7(lean_object* v_f_2294_, lean_object* v_discr_2295_, lean_object* v_toBind_2296_, lean_object* v___f_2297_, lean_object* v_____r_2298_){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2299_ = lean_apply_1(v_f_2294_, v_discr_2295_);
v___x_2300_ = lean_apply_4(v_toBind_2296_, lean_box(0), lean_box(0), v___x_2299_, v___f_2297_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6(lean_object* v_toApplicative_2301_, lean_object* v_alts_2302_, lean_object* v_inst_2303_, lean_object* v___f_2304_, lean_object* v_____r_2305_){
_start:
{
lean_object* v_toPure_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v_toPure_2306_ = lean_ctor_get(v_toApplicative_2301_, 1);
lean_inc(v_toPure_2306_);
lean_dec_ref(v_toApplicative_2301_);
v___x_2307_ = lean_unsigned_to_nat(0u);
v___x_2308_ = lean_array_get_size(v_alts_2302_);
v___x_2309_ = lean_box(0);
v___x_2310_ = lean_nat_dec_lt(v___x_2307_, v___x_2308_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; 
lean_dec(v___f_2304_);
lean_dec_ref(v_inst_2303_);
lean_dec_ref(v_alts_2302_);
v___x_2311_ = lean_apply_2(v_toPure_2306_, lean_box(0), v___x_2309_);
return v___x_2311_;
}
else
{
uint8_t v___x_2312_; 
v___x_2312_ = lean_nat_dec_le(v___x_2308_, v___x_2308_);
if (v___x_2312_ == 0)
{
if (v___x_2310_ == 0)
{
lean_object* v___x_2313_; 
lean_dec(v___f_2304_);
lean_dec_ref(v_inst_2303_);
lean_dec_ref(v_alts_2302_);
v___x_2313_ = lean_apply_2(v_toPure_2306_, lean_box(0), v___x_2309_);
return v___x_2313_;
}
else
{
size_t v___x_2314_; size_t v___x_2315_; lean_object* v___x_2316_; 
lean_dec(v_toPure_2306_);
v___x_2314_ = ((size_t)0ULL);
v___x_2315_ = lean_usize_of_nat(v___x_2308_);
v___x_2316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2303_, v___f_2304_, v_alts_2302_, v___x_2314_, v___x_2315_, v___x_2309_);
return v___x_2316_;
}
}
else
{
size_t v___x_2317_; size_t v___x_2318_; lean_object* v___x_2319_; 
lean_dec(v_toPure_2306_);
v___x_2317_ = ((size_t)0ULL);
v___x_2318_ = lean_usize_of_nat(v___x_2308_);
v___x_2319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2303_, v___f_2304_, v_alts_2302_, v___x_2317_, v___x_2318_, v___x_2309_);
return v___x_2319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8(lean_object* v_inst_2320_, lean_object* v_f_2321_, lean_object* v_x_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2320_, v_f_2321_, v___y_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5(lean_object* v_inst_2325_, lean_object* v_f_2326_, lean_object* v_x_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg), 3, 2);
lean_closure_set(v___x_2329_, 0, v_inst_2325_);
lean_closure_set(v___x_2329_, 1, v_f_2326_);
v___x_2330_ = l_Lean_Compiler_LCNF_Alt_forCodeM___redArg(v___y_2328_, v___x_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2(lean_object* v_inst_2331_, lean_object* v_f_2332_, lean_object* v_value_2333_, lean_object* v_toBind_2334_, lean_object* v___f_2335_, lean_object* v_____r_2336_){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2331_, v_f_2332_, v_value_2333_);
v___x_2338_ = lean_apply_4(v_toBind_2334_, lean_box(0), lean_box(0), v___x_2337_, v___f_2335_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg(lean_object* v_inst_2339_, lean_object* v_f_2340_, lean_object* v_c_2341_){
_start:
{
switch(lean_obj_tag(v_c_2341_))
{
case 0:
{
lean_object* v_toBind_2342_; lean_object* v_decl_2343_; lean_object* v_k_2344_; lean_object* v___f_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v_toBind_2342_ = lean_ctor_get(v_inst_2339_, 1);
lean_inc(v_toBind_2342_);
v_decl_2343_ = lean_ctor_get(v_c_2341_, 0);
lean_inc_ref(v_decl_2343_);
v_k_2344_ = lean_ctor_get(v_c_2341_, 1);
lean_inc_ref(v_k_2344_);
lean_dec_ref_known(v_c_2341_, 2);
lean_inc(v_f_2340_);
lean_inc_ref(v_inst_2339_);
v___f_2345_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2345_, 0, v_inst_2339_);
lean_closure_set(v___f_2345_, 1, v_f_2340_);
lean_closure_set(v___f_2345_, 2, v_k_2344_);
v___x_2346_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_2339_, v_f_2340_, v_decl_2343_);
v___x_2347_ = lean_apply_4(v_toBind_2342_, lean_box(0), lean_box(0), v___x_2346_, v___f_2345_);
return v___x_2347_;
}
case 3:
{
lean_object* v_toApplicative_2348_; lean_object* v_toBind_2349_; lean_object* v_fvarId_2350_; lean_object* v_args_2351_; lean_object* v___f_2352_; lean_object* v___f_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v_toApplicative_2348_ = lean_ctor_get(v_inst_2339_, 0);
lean_inc_ref(v_toApplicative_2348_);
v_toBind_2349_ = lean_ctor_get(v_inst_2339_, 1);
lean_inc(v_toBind_2349_);
v_fvarId_2350_ = lean_ctor_get(v_c_2341_, 0);
lean_inc(v_fvarId_2350_);
v_args_2351_ = lean_ctor_get(v_c_2341_, 1);
lean_inc_ref(v_args_2351_);
lean_dec_ref_known(v_c_2341_, 2);
lean_inc(v_f_2340_);
lean_inc_ref(v_inst_2339_);
v___f_2352_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8), 4, 2);
lean_closure_set(v___f_2352_, 0, v_inst_2339_);
lean_closure_set(v___f_2352_, 1, v_f_2340_);
v___f_2353_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2353_, 0, v_toApplicative_2348_);
lean_closure_set(v___f_2353_, 1, v_args_2351_);
lean_closure_set(v___f_2353_, 2, v_inst_2339_);
lean_closure_set(v___f_2353_, 3, v___f_2352_);
v___x_2354_ = lean_apply_1(v_f_2340_, v_fvarId_2350_);
v___x_2355_ = lean_apply_4(v_toBind_2349_, lean_box(0), lean_box(0), v___x_2354_, v___f_2353_);
return v___x_2355_;
}
case 4:
{
lean_object* v_cases_2356_; lean_object* v_toApplicative_2357_; lean_object* v_toBind_2358_; lean_object* v_resultType_2359_; lean_object* v_discr_2360_; lean_object* v_alts_2361_; lean_object* v___f_2362_; lean_object* v___f_2363_; lean_object* v___f_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v_cases_2356_ = lean_ctor_get(v_c_2341_, 0);
lean_inc_ref(v_cases_2356_);
lean_dec_ref_known(v_c_2341_, 1);
v_toApplicative_2357_ = lean_ctor_get(v_inst_2339_, 0);
v_toBind_2358_ = lean_ctor_get(v_inst_2339_, 1);
lean_inc_n(v_toBind_2358_, 2);
v_resultType_2359_ = lean_ctor_get(v_cases_2356_, 1);
lean_inc_ref(v_resultType_2359_);
v_discr_2360_ = lean_ctor_get(v_cases_2356_, 2);
lean_inc(v_discr_2360_);
v_alts_2361_ = lean_ctor_get(v_cases_2356_, 3);
lean_inc_ref(v_alts_2361_);
lean_dec_ref(v_cases_2356_);
lean_inc_n(v_f_2340_, 2);
lean_inc_ref_n(v_inst_2339_, 2);
v___f_2362_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5), 4, 2);
lean_closure_set(v___f_2362_, 0, v_inst_2339_);
lean_closure_set(v___f_2362_, 1, v_f_2340_);
lean_inc_ref(v_toApplicative_2357_);
v___f_2363_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6), 5, 4);
lean_closure_set(v___f_2363_, 0, v_toApplicative_2357_);
lean_closure_set(v___f_2363_, 1, v_alts_2361_);
lean_closure_set(v___f_2363_, 2, v_inst_2339_);
lean_closure_set(v___f_2363_, 3, v___f_2362_);
v___f_2364_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7), 5, 4);
lean_closure_set(v___f_2364_, 0, v_f_2340_);
lean_closure_set(v___f_2364_, 1, v_discr_2360_);
lean_closure_set(v___f_2364_, 2, v_toBind_2358_);
lean_closure_set(v___f_2364_, 3, v___f_2363_);
v___x_2365_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2339_, v_f_2340_, v_resultType_2359_);
v___x_2366_ = lean_apply_4(v_toBind_2358_, lean_box(0), lean_box(0), v___x_2365_, v___f_2364_);
return v___x_2366_;
}
case 5:
{
lean_object* v_fvarId_2367_; lean_object* v___x_2368_; 
lean_dec_ref(v_inst_2339_);
v_fvarId_2367_ = lean_ctor_get(v_c_2341_, 0);
lean_inc(v_fvarId_2367_);
lean_dec_ref_known(v_c_2341_, 1);
v___x_2368_ = lean_apply_1(v_f_2340_, v_fvarId_2367_);
return v___x_2368_;
}
case 6:
{
lean_object* v_type_2369_; lean_object* v___x_2370_; 
v_type_2369_ = lean_ctor_get(v_c_2341_, 0);
lean_inc_ref(v_type_2369_);
lean_dec_ref_known(v_c_2341_, 1);
v___x_2370_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2339_, v_f_2340_, v_type_2369_);
return v___x_2370_;
}
case 7:
{
lean_object* v_toBind_2371_; lean_object* v_fvarId_2372_; lean_object* v_y_2373_; lean_object* v_k_2374_; lean_object* v___f_2375_; lean_object* v___f_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v_toBind_2371_ = lean_ctor_get(v_inst_2339_, 1);
lean_inc_n(v_toBind_2371_, 2);
v_fvarId_2372_ = lean_ctor_get(v_c_2341_, 0);
lean_inc(v_fvarId_2372_);
v_y_2373_ = lean_ctor_get(v_c_2341_, 2);
lean_inc(v_y_2373_);
v_k_2374_ = lean_ctor_get(v_c_2341_, 3);
lean_inc_ref(v_k_2374_);
lean_dec_ref_known(v_c_2341_, 4);
lean_inc_n(v_f_2340_, 2);
lean_inc_ref(v_inst_2339_);
v___f_2375_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2375_, 0, v_inst_2339_);
lean_closure_set(v___f_2375_, 1, v_f_2340_);
lean_closure_set(v___f_2375_, 2, v_k_2374_);
v___f_2376_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10), 6, 5);
lean_closure_set(v___f_2376_, 0, v_inst_2339_);
lean_closure_set(v___f_2376_, 1, v_f_2340_);
lean_closure_set(v___f_2376_, 2, v_y_2373_);
lean_closure_set(v___f_2376_, 3, v_toBind_2371_);
lean_closure_set(v___f_2376_, 4, v___f_2375_);
v___x_2377_ = lean_apply_1(v_f_2340_, v_fvarId_2372_);
v___x_2378_ = lean_apply_4(v_toBind_2371_, lean_box(0), lean_box(0), v___x_2377_, v___f_2376_);
return v___x_2378_;
}
case 8:
{
lean_object* v_toBind_2379_; lean_object* v_fvarId_2380_; lean_object* v_y_2381_; lean_object* v_k_2382_; lean_object* v___f_2383_; lean_object* v___f_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v_toBind_2379_ = lean_ctor_get(v_inst_2339_, 1);
lean_inc_n(v_toBind_2379_, 2);
v_fvarId_2380_ = lean_ctor_get(v_c_2341_, 0);
lean_inc(v_fvarId_2380_);
v_y_2381_ = lean_ctor_get(v_c_2341_, 2);
lean_inc(v_y_2381_);
v_k_2382_ = lean_ctor_get(v_c_2341_, 3);
lean_inc_ref(v_k_2382_);
lean_dec_ref_known(v_c_2341_, 4);
lean_inc_n(v_f_2340_, 2);
v___f_2383_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2383_, 0, v_inst_2339_);
lean_closure_set(v___f_2383_, 1, v_f_2340_);
lean_closure_set(v___f_2383_, 2, v_k_2382_);
v___f_2384_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11), 5, 4);
lean_closure_set(v___f_2384_, 0, v_f_2340_);
lean_closure_set(v___f_2384_, 1, v_y_2381_);
lean_closure_set(v___f_2384_, 2, v_toBind_2379_);
lean_closure_set(v___f_2384_, 3, v___f_2383_);
v___x_2385_ = lean_apply_1(v_f_2340_, v_fvarId_2380_);
v___x_2386_ = lean_apply_4(v_toBind_2379_, lean_box(0), lean_box(0), v___x_2385_, v___f_2384_);
return v___x_2386_;
}
case 9:
{
lean_object* v_toBind_2387_; lean_object* v_fvarId_2388_; lean_object* v_y_2389_; lean_object* v_ty_2390_; lean_object* v_k_2391_; lean_object* v___f_2392_; lean_object* v___f_2393_; lean_object* v___f_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v_toBind_2387_ = lean_ctor_get(v_inst_2339_, 1);
lean_inc_n(v_toBind_2387_, 3);
v_fvarId_2388_ = lean_ctor_get(v_c_2341_, 0);
lean_inc(v_fvarId_2388_);
v_y_2389_ = lean_ctor_get(v_c_2341_, 3);
lean_inc(v_y_2389_);
v_ty_2390_ = lean_ctor_get(v_c_2341_, 4);
lean_inc_ref(v_ty_2390_);
v_k_2391_ = lean_ctor_get(v_c_2341_, 5);
lean_inc_ref(v_k_2391_);
lean_dec_ref_known(v_c_2341_, 6);
lean_inc_n(v_f_2340_, 3);
lean_inc_ref(v_inst_2339_);
v___f_2392_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2392_, 0, v_inst_2339_);
lean_closure_set(v___f_2392_, 1, v_f_2340_);
lean_closure_set(v___f_2392_, 2, v_k_2391_);
v___f_2393_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12), 6, 5);
lean_closure_set(v___f_2393_, 0, v_inst_2339_);
lean_closure_set(v___f_2393_, 1, v_f_2340_);
lean_closure_set(v___f_2393_, 2, v_ty_2390_);
lean_closure_set(v___f_2393_, 3, v_toBind_2387_);
lean_closure_set(v___f_2393_, 4, v___f_2392_);
v___f_2394_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11), 5, 4);
lean_closure_set(v___f_2394_, 0, v_f_2340_);
lean_closure_set(v___f_2394_, 1, v_y_2389_);
lean_closure_set(v___f_2394_, 2, v_toBind_2387_);
lean_closure_set(v___f_2394_, 3, v___f_2393_);
v___x_2395_ = lean_apply_1(v_f_2340_, v_fvarId_2388_);
v___x_2396_ = lean_apply_4(v_toBind_2387_, lean_box(0), lean_box(0), v___x_2395_, v___f_2394_);
return v___x_2396_;
}
case 10:
{
lean_object* v_toBind_2397_; lean_object* v_fvarId_2398_; lean_object* v_k_2399_; lean_object* v___f_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v_toBind_2397_ = lean_ctor_get(v_inst_2339_, 1);
lean_inc(v_toBind_2397_);
v_fvarId_2398_ = lean_ctor_get(v_c_2341_, 0);
lean_inc(v_fvarId_2398_);
v_k_2399_ = lean_ctor_get(v_c_2341_, 2);
lean_inc_ref(v_k_2399_);
lean_dec_ref_known(v_c_2341_, 3);
lean_inc(v_f_2340_);
v___f_2400_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2400_, 0, v_inst_2339_);
lean_closure_set(v___f_2400_, 1, v_f_2340_);
lean_closure_set(v___f_2400_, 2, v_k_2399_);
v___x_2401_ = lean_apply_1(v_f_2340_, v_fvarId_2398_);
v___x_2402_ = lean_apply_4(v_toBind_2397_, lean_box(0), lean_box(0), v___x_2401_, v___f_2400_);
return v___x_2402_;
}
case 11:
{
lean_object* v_toBind_2403_; lean_object* v_fvarId_2404_; lean_object* v_k_2405_; lean_object* v___f_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v_toBind_2403_ = lean_ctor_get(v_inst_2339_, 1);
lean_inc(v_toBind_2403_);
v_fvarId_2404_ = lean_ctor_get(v_c_2341_, 0);
lean_inc(v_fvarId_2404_);
v_k_2405_ = lean_ctor_get(v_c_2341_, 2);
lean_inc_ref(v_k_2405_);
lean_dec_ref_known(v_c_2341_, 3);
lean_inc(v_f_2340_);
v___f_2406_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2406_, 0, v_inst_2339_);
lean_closure_set(v___f_2406_, 1, v_f_2340_);
lean_closure_set(v___f_2406_, 2, v_k_2405_);
v___x_2407_ = lean_apply_1(v_f_2340_, v_fvarId_2404_);
v___x_2408_ = lean_apply_4(v_toBind_2403_, lean_box(0), lean_box(0), v___x_2407_, v___f_2406_);
return v___x_2408_;
}
case 12:
{
lean_object* v_toBind_2409_; lean_object* v_fvarId_2410_; lean_object* v_k_2411_; lean_object* v___f_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v_toBind_2409_ = lean_ctor_get(v_inst_2339_, 1);
lean_inc(v_toBind_2409_);
v_fvarId_2410_ = lean_ctor_get(v_c_2341_, 0);
lean_inc(v_fvarId_2410_);
v_k_2411_ = lean_ctor_get(v_c_2341_, 3);
lean_inc_ref(v_k_2411_);
lean_dec_ref_known(v_c_2341_, 4);
lean_inc(v_f_2340_);
v___f_2412_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2412_, 0, v_inst_2339_);
lean_closure_set(v___f_2412_, 1, v_f_2340_);
lean_closure_set(v___f_2412_, 2, v_k_2411_);
v___x_2413_ = lean_apply_1(v_f_2340_, v_fvarId_2410_);
v___x_2414_ = lean_apply_4(v_toBind_2409_, lean_box(0), lean_box(0), v___x_2413_, v___f_2412_);
return v___x_2414_;
}
case 13:
{
lean_object* v_toBind_2415_; lean_object* v_fvarId_2416_; lean_object* v_k_2417_; lean_object* v___f_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v_toBind_2415_ = lean_ctor_get(v_inst_2339_, 1);
lean_inc(v_toBind_2415_);
v_fvarId_2416_ = lean_ctor_get(v_c_2341_, 0);
lean_inc(v_fvarId_2416_);
v_k_2417_ = lean_ctor_get(v_c_2341_, 1);
lean_inc_ref(v_k_2417_);
lean_dec_ref_known(v_c_2341_, 2);
lean_inc(v_f_2340_);
v___f_2418_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2418_, 0, v_inst_2339_);
lean_closure_set(v___f_2418_, 1, v_f_2340_);
lean_closure_set(v___f_2418_, 2, v_k_2417_);
v___x_2419_ = lean_apply_1(v_f_2340_, v_fvarId_2416_);
v___x_2420_ = lean_apply_4(v_toBind_2415_, lean_box(0), lean_box(0), v___x_2419_, v___f_2418_);
return v___x_2420_;
}
default: 
{
lean_object* v_decl_2421_; lean_object* v_toApplicative_2422_; lean_object* v_toBind_2423_; lean_object* v_k_2424_; lean_object* v_params_2425_; lean_object* v_type_2426_; lean_object* v_value_2427_; lean_object* v_toPure_2428_; lean_object* v___f_2429_; lean_object* v___f_2430_; lean_object* v___f_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; 
v_decl_2421_ = lean_ctor_get(v_c_2341_, 0);
lean_inc_ref(v_decl_2421_);
v_toApplicative_2422_ = lean_ctor_get(v_inst_2339_, 0);
v_toBind_2423_ = lean_ctor_get(v_inst_2339_, 1);
lean_inc_n(v_toBind_2423_, 3);
v_k_2424_ = lean_ctor_get(v_c_2341_, 1);
lean_inc_ref(v_k_2424_);
lean_dec_ref(v_c_2341_);
v_params_2425_ = lean_ctor_get(v_decl_2421_, 2);
lean_inc_ref(v_params_2425_);
v_type_2426_ = lean_ctor_get(v_decl_2421_, 3);
lean_inc_ref(v_type_2426_);
v_value_2427_ = lean_ctor_get(v_decl_2421_, 4);
lean_inc_ref(v_value_2427_);
lean_dec_ref(v_decl_2421_);
v_toPure_2428_ = lean_ctor_get(v_toApplicative_2422_, 1);
lean_inc_n(v_f_2340_, 3);
lean_inc_ref_n(v_inst_2339_, 3);
v___f_2429_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2429_, 0, v_inst_2339_);
lean_closure_set(v___f_2429_, 1, v_f_2340_);
lean_closure_set(v___f_2429_, 2, v_k_2424_);
v___f_2430_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2430_, 0, v_inst_2339_);
lean_closure_set(v___f_2430_, 1, v_f_2340_);
lean_closure_set(v___f_2430_, 2, v_value_2427_);
lean_closure_set(v___f_2430_, 3, v_toBind_2423_);
lean_closure_set(v___f_2430_, 4, v___f_2429_);
v___f_2431_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2431_, 0, v_inst_2339_);
lean_closure_set(v___f_2431_, 1, v_f_2340_);
lean_closure_set(v___f_2431_, 2, v_type_2426_);
lean_closure_set(v___f_2431_, 3, v_toBind_2423_);
lean_closure_set(v___f_2431_, 4, v___f_2430_);
v___x_2432_ = lean_unsigned_to_nat(0u);
v___x_2433_ = lean_array_get_size(v_params_2425_);
v___x_2434_ = lean_box(0);
v___x_2435_ = lean_nat_dec_lt(v___x_2432_, v___x_2433_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_inc(v_toPure_2428_);
lean_dec_ref(v_params_2425_);
lean_dec(v_f_2340_);
lean_dec_ref(v_inst_2339_);
v___x_2436_ = lean_apply_2(v_toPure_2428_, lean_box(0), v___x_2434_);
v___x_2437_ = lean_apply_4(v_toBind_2423_, lean_box(0), lean_box(0), v___x_2436_, v___f_2431_);
return v___x_2437_;
}
else
{
lean_object* v___f_2438_; uint8_t v___x_2439_; 
lean_inc_ref(v_inst_2339_);
v___f_2438_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2438_, 0, v_inst_2339_);
lean_closure_set(v___f_2438_, 1, v_f_2340_);
v___x_2439_ = lean_nat_dec_le(v___x_2433_, v___x_2433_);
if (v___x_2439_ == 0)
{
if (v___x_2435_ == 0)
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
lean_inc(v_toPure_2428_);
lean_dec_ref(v___f_2438_);
lean_dec_ref(v_params_2425_);
lean_dec_ref(v_inst_2339_);
v___x_2440_ = lean_apply_2(v_toPure_2428_, lean_box(0), v___x_2434_);
v___x_2441_ = lean_apply_4(v_toBind_2423_, lean_box(0), lean_box(0), v___x_2440_, v___f_2431_);
return v___x_2441_;
}
else
{
size_t v___x_2442_; size_t v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2442_ = ((size_t)0ULL);
v___x_2443_ = lean_usize_of_nat(v___x_2433_);
v___x_2444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2339_, v___f_2438_, v_params_2425_, v___x_2442_, v___x_2443_, v___x_2434_);
v___x_2445_ = lean_apply_4(v_toBind_2423_, lean_box(0), lean_box(0), v___x_2444_, v___f_2431_);
return v___x_2445_;
}
}
else
{
size_t v___x_2446_; size_t v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2446_ = ((size_t)0ULL);
v___x_2447_ = lean_usize_of_nat(v___x_2433_);
v___x_2448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2339_, v___f_2438_, v_params_2425_, v___x_2446_, v___x_2447_, v___x_2434_);
v___x_2449_ = lean_apply_4(v_toBind_2423_, lean_box(0), lean_box(0), v___x_2448_, v___f_2431_);
return v___x_2449_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0(lean_object* v_inst_2450_, lean_object* v_f_2451_, lean_object* v_k_2452_, lean_object* v_____r_2453_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2450_, v_f_2451_, v_k_2452_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM(lean_object* v_m_2455_, uint8_t v_pu_2456_, lean_object* v_inst_2457_, lean_object* v_f_2458_, lean_object* v_c_2459_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2457_, v_f_2458_, v_c_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___boxed(lean_object* v_m_2461_, lean_object* v_pu_2462_, lean_object* v_inst_2463_, lean_object* v_f_2464_, lean_object* v_c_2465_){
_start:
{
uint8_t v_pu_boxed_2466_; lean_object* v_res_2467_; 
v_pu_boxed_2466_ = lean_unbox(v_pu_2462_);
v_res_2467_ = l_Lean_Compiler_LCNF_Code_forFVarM(v_m_2461_, v_pu_boxed_2466_, v_inst_2463_, v_f_2464_, v_c_2465_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(uint8_t v_pu_2468_, lean_object* v_m_2469_, lean_object* v_inst_2470_, lean_object* v_inst_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2468_, v_inst_2470_, v_inst_2471_, v___y_2472_, v___y_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed(lean_object* v_pu_2475_, lean_object* v_m_2476_, lean_object* v_inst_2477_, lean_object* v_inst_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
uint8_t v_pu_boxed_2481_; lean_object* v_res_2482_; 
v_pu_boxed_2481_ = lean_unbox(v_pu_2475_);
v_res_2482_ = l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(v_pu_boxed_2481_, v_m_2476_, v_inst_2477_, v_inst_2478_, v___y_2479_, v___y_2480_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__1(lean_object* v_m_2483_, lean_object* v_inst_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2484_, v___y_2485_, v___y_2486_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode(uint8_t v_pu_2489_){
_start:
{
lean_object* v___x_2490_; lean_object* v___f_2491_; lean_object* v___f_2492_; lean_object* v___x_2493_; 
v___x_2490_ = lean_box(v_pu_2489_);
v___f_2491_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2491_, 0, v___x_2490_);
v___f_2492_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0));
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___f_2491_);
lean_ctor_set(v___x_2493_, 1, v___f_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___boxed(lean_object* v_pu_2494_){
_start:
{
uint8_t v_pu_boxed_2495_; lean_object* v_res_2496_; 
v_pu_boxed_2495_ = lean_unbox(v_pu_2494_);
v_res_2496_ = l_Lean_Compiler_LCNF_instTraverseFVarCode(v_pu_boxed_2495_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(uint8_t v_pu_2497_, lean_object* v_decl_2498_, lean_object* v_____do__lift_2499_, lean_object* v_params_2500_, lean_object* v_inst_2501_, lean_object* v_____do__lift_2502_){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = lean_box(v_pu_2497_);
v___x_2504_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed), 10, 5);
lean_closure_set(v___x_2504_, 0, v___x_2503_);
lean_closure_set(v___x_2504_, 1, v_decl_2498_);
lean_closure_set(v___x_2504_, 2, v_____do__lift_2499_);
lean_closure_set(v___x_2504_, 3, v_params_2500_);
lean_closure_set(v___x_2504_, 4, v_____do__lift_2502_);
v___x_2505_ = lean_apply_2(v_inst_2501_, lean_box(0), v___x_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed(lean_object* v_pu_2506_, lean_object* v_decl_2507_, lean_object* v_____do__lift_2508_, lean_object* v_params_2509_, lean_object* v_inst_2510_, lean_object* v_____do__lift_2511_){
_start:
{
uint8_t v_pu_boxed_2512_; lean_object* v_res_2513_; 
v_pu_boxed_2512_ = lean_unbox(v_pu_2506_);
v_res_2513_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(v_pu_boxed_2512_, v_decl_2507_, v_____do__lift_2508_, v_params_2509_, v_inst_2510_, v_____do__lift_2511_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(uint8_t v_pu_2514_, lean_object* v_decl_2515_, lean_object* v_params_2516_, lean_object* v_inst_2517_, lean_object* v_inst_2518_, lean_object* v_f_2519_, lean_object* v_value_2520_, lean_object* v_toBind_2521_, lean_object* v_____do__lift_2522_){
_start:
{
lean_object* v___x_2523_; lean_object* v___f_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2523_ = lean_box(v_pu_2514_);
lean_inc(v_inst_2517_);
v___f_2524_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2524_, 0, v___x_2523_);
lean_closure_set(v___f_2524_, 1, v_decl_2515_);
lean_closure_set(v___f_2524_, 2, v_____do__lift_2522_);
lean_closure_set(v___f_2524_, 3, v_params_2516_);
lean_closure_set(v___f_2524_, 4, v_inst_2517_);
v___x_2525_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2514_, v_inst_2517_, v_inst_2518_, v_f_2519_, v_value_2520_);
v___x_2526_ = lean_apply_4(v_toBind_2521_, lean_box(0), lean_box(0), v___x_2525_, v___f_2524_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed(lean_object* v_pu_2527_, lean_object* v_decl_2528_, lean_object* v_params_2529_, lean_object* v_inst_2530_, lean_object* v_inst_2531_, lean_object* v_f_2532_, lean_object* v_value_2533_, lean_object* v_toBind_2534_, lean_object* v_____do__lift_2535_){
_start:
{
uint8_t v_pu_boxed_2536_; lean_object* v_res_2537_; 
v_pu_boxed_2536_ = lean_unbox(v_pu_2527_);
v_res_2537_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(v_pu_boxed_2536_, v_decl_2528_, v_params_2529_, v_inst_2530_, v_inst_2531_, v_f_2532_, v_value_2533_, v_toBind_2534_, v_____do__lift_2535_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(uint8_t v_pu_2538_, lean_object* v_decl_2539_, lean_object* v_inst_2540_, lean_object* v_inst_2541_, lean_object* v_f_2542_, lean_object* v_value_2543_, lean_object* v_toBind_2544_, lean_object* v_type_2545_, lean_object* v_params_2546_){
_start:
{
lean_object* v___x_2547_; lean_object* v___f_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2547_ = lean_box(v_pu_2538_);
lean_inc(v_toBind_2544_);
lean_inc(v_f_2542_);
lean_inc_ref(v_inst_2541_);
v___f_2548_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2548_, 0, v___x_2547_);
lean_closure_set(v___f_2548_, 1, v_decl_2539_);
lean_closure_set(v___f_2548_, 2, v_params_2546_);
lean_closure_set(v___f_2548_, 3, v_inst_2540_);
lean_closure_set(v___f_2548_, 4, v_inst_2541_);
lean_closure_set(v___f_2548_, 5, v_f_2542_);
lean_closure_set(v___f_2548_, 6, v_value_2543_);
lean_closure_set(v___f_2548_, 7, v_toBind_2544_);
v___x_2549_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2541_, v_f_2542_, v_type_2545_);
v___x_2550_ = lean_apply_4(v_toBind_2544_, lean_box(0), lean_box(0), v___x_2549_, v___f_2548_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed(lean_object* v_pu_2551_, lean_object* v_decl_2552_, lean_object* v_inst_2553_, lean_object* v_inst_2554_, lean_object* v_f_2555_, lean_object* v_value_2556_, lean_object* v_toBind_2557_, lean_object* v_type_2558_, lean_object* v_params_2559_){
_start:
{
uint8_t v_pu_boxed_2560_; lean_object* v_res_2561_; 
v_pu_boxed_2560_ = lean_unbox(v_pu_2551_);
v_res_2561_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(v_pu_boxed_2560_, v_decl_2552_, v_inst_2553_, v_inst_2554_, v_f_2555_, v_value_2556_, v_toBind_2557_, v_type_2558_, v_params_2559_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(uint8_t v_pu_2562_, lean_object* v_inst_2563_, lean_object* v_inst_2564_, lean_object* v_f_2565_, lean_object* v_decl_2566_){
_start:
{
lean_object* v_toBind_2567_; lean_object* v_params_2568_; lean_object* v_type_2569_; lean_object* v_value_2570_; lean_object* v___x_2571_; lean_object* v___f_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; size_t v_sz_2575_; size_t v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v_toBind_2567_ = lean_ctor_get(v_inst_2564_, 1);
lean_inc_n(v_toBind_2567_, 2);
v_params_2568_ = lean_ctor_get(v_decl_2566_, 2);
lean_inc_ref(v_params_2568_);
v_type_2569_ = lean_ctor_get(v_decl_2566_, 3);
lean_inc_ref(v_type_2569_);
v_value_2570_ = lean_ctor_get(v_decl_2566_, 4);
lean_inc_ref(v_value_2570_);
v___x_2571_ = lean_box(v_pu_2562_);
lean_inc(v_f_2565_);
lean_inc_ref_n(v_inst_2564_, 2);
lean_inc(v_inst_2563_);
v___f_2572_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2572_, 0, v___x_2571_);
lean_closure_set(v___f_2572_, 1, v_decl_2566_);
lean_closure_set(v___f_2572_, 2, v_inst_2563_);
lean_closure_set(v___f_2572_, 3, v_inst_2564_);
lean_closure_set(v___f_2572_, 4, v_f_2565_);
lean_closure_set(v___f_2572_, 5, v_value_2570_);
lean_closure_set(v___f_2572_, 6, v_toBind_2567_);
lean_closure_set(v___f_2572_, 7, v_type_2569_);
v___x_2573_ = lean_box(v_pu_2562_);
v___x_2574_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_2574_, 0, lean_box(0));
lean_closure_set(v___x_2574_, 1, v___x_2573_);
lean_closure_set(v___x_2574_, 2, v_inst_2563_);
lean_closure_set(v___x_2574_, 3, v_inst_2564_);
lean_closure_set(v___x_2574_, 4, v_f_2565_);
v_sz_2575_ = lean_array_size(v_params_2568_);
v___x_2576_ = ((size_t)0ULL);
v___x_2577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2564_, v___x_2574_, v_sz_2575_, v___x_2576_, v_params_2568_);
v___x_2578_ = lean_apply_4(v_toBind_2567_, lean_box(0), lean_box(0), v___x_2577_, v___f_2572_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___boxed(lean_object* v_pu_2579_, lean_object* v_inst_2580_, lean_object* v_inst_2581_, lean_object* v_f_2582_, lean_object* v_decl_2583_){
_start:
{
uint8_t v_pu_boxed_2584_; lean_object* v_res_2585_; 
v_pu_boxed_2584_ = lean_unbox(v_pu_2579_);
v_res_2585_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_boxed_2584_, v_inst_2580_, v_inst_2581_, v_f_2582_, v_decl_2583_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM(lean_object* v_m_2586_, uint8_t v_pu_2587_, lean_object* v_inst_2588_, lean_object* v_inst_2589_, lean_object* v_f_2590_, lean_object* v_decl_2591_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2587_, v_inst_2588_, v_inst_2589_, v_f_2590_, v_decl_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___boxed(lean_object* v_m_2593_, lean_object* v_pu_2594_, lean_object* v_inst_2595_, lean_object* v_inst_2596_, lean_object* v_f_2597_, lean_object* v_decl_2598_){
_start:
{
uint8_t v_pu_boxed_2599_; lean_object* v_res_2600_; 
v_pu_boxed_2599_ = lean_unbox(v_pu_2594_);
v_res_2600_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM(v_m_2593_, v_pu_boxed_2599_, v_inst_2595_, v_inst_2596_, v_f_2597_, v_decl_2598_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0(lean_object* v_inst_2601_, lean_object* v_f_2602_, lean_object* v_value_2603_, lean_object* v_____r_2604_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_2601_, v_f_2602_, v_value_2603_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1(lean_object* v_inst_2606_, lean_object* v_f_2607_, lean_object* v_type_2608_, lean_object* v_toBind_2609_, lean_object* v___f_2610_, lean_object* v_____r_2611_){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2606_, v_f_2607_, v_type_2608_);
v___x_2613_ = lean_apply_4(v_toBind_2609_, lean_box(0), lean_box(0), v___x_2612_, v___f_2610_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2(lean_object* v_inst_2614_, lean_object* v_f_2615_, lean_object* v_x_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_2614_, v_f_2615_, v___y_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(lean_object* v_inst_2619_, lean_object* v_f_2620_, lean_object* v_decl_2621_){
_start:
{
lean_object* v_toApplicative_2622_; lean_object* v_toBind_2623_; lean_object* v_params_2624_; lean_object* v_type_2625_; lean_object* v_value_2626_; lean_object* v_toPure_2627_; lean_object* v___f_2628_; lean_object* v___f_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; uint8_t v___x_2633_; 
v_toApplicative_2622_ = lean_ctor_get(v_inst_2619_, 0);
v_toBind_2623_ = lean_ctor_get(v_inst_2619_, 1);
lean_inc_n(v_toBind_2623_, 2);
v_params_2624_ = lean_ctor_get(v_decl_2621_, 2);
lean_inc_ref(v_params_2624_);
v_type_2625_ = lean_ctor_get(v_decl_2621_, 3);
lean_inc_ref(v_type_2625_);
v_value_2626_ = lean_ctor_get(v_decl_2621_, 4);
lean_inc_ref(v_value_2626_);
lean_dec_ref(v_decl_2621_);
v_toPure_2627_ = lean_ctor_get(v_toApplicative_2622_, 1);
lean_inc_n(v_f_2620_, 2);
lean_inc_ref_n(v_inst_2619_, 2);
v___f_2628_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2628_, 0, v_inst_2619_);
lean_closure_set(v___f_2628_, 1, v_f_2620_);
lean_closure_set(v___f_2628_, 2, v_value_2626_);
v___f_2629_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2629_, 0, v_inst_2619_);
lean_closure_set(v___f_2629_, 1, v_f_2620_);
lean_closure_set(v___f_2629_, 2, v_type_2625_);
lean_closure_set(v___f_2629_, 3, v_toBind_2623_);
lean_closure_set(v___f_2629_, 4, v___f_2628_);
v___x_2630_ = lean_unsigned_to_nat(0u);
v___x_2631_ = lean_array_get_size(v_params_2624_);
v___x_2632_ = lean_box(0);
v___x_2633_ = lean_nat_dec_lt(v___x_2630_, v___x_2631_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_inc(v_toPure_2627_);
lean_dec_ref(v_params_2624_);
lean_dec(v_f_2620_);
lean_dec_ref(v_inst_2619_);
v___x_2634_ = lean_apply_2(v_toPure_2627_, lean_box(0), v___x_2632_);
v___x_2635_ = lean_apply_4(v_toBind_2623_, lean_box(0), lean_box(0), v___x_2634_, v___f_2629_);
return v___x_2635_;
}
else
{
lean_object* v___f_2636_; uint8_t v___x_2637_; 
lean_inc_ref(v_inst_2619_);
v___f_2636_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_2636_, 0, v_inst_2619_);
lean_closure_set(v___f_2636_, 1, v_f_2620_);
v___x_2637_ = lean_nat_dec_le(v___x_2631_, v___x_2631_);
if (v___x_2637_ == 0)
{
if (v___x_2633_ == 0)
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
lean_inc(v_toPure_2627_);
lean_dec_ref(v___f_2636_);
lean_dec_ref(v_params_2624_);
lean_dec_ref(v_inst_2619_);
v___x_2638_ = lean_apply_2(v_toPure_2627_, lean_box(0), v___x_2632_);
v___x_2639_ = lean_apply_4(v_toBind_2623_, lean_box(0), lean_box(0), v___x_2638_, v___f_2629_);
return v___x_2639_;
}
else
{
size_t v___x_2640_; size_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2640_ = ((size_t)0ULL);
v___x_2641_ = lean_usize_of_nat(v___x_2631_);
v___x_2642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2619_, v___f_2636_, v_params_2624_, v___x_2640_, v___x_2641_, v___x_2632_);
v___x_2643_ = lean_apply_4(v_toBind_2623_, lean_box(0), lean_box(0), v___x_2642_, v___f_2629_);
return v___x_2643_;
}
}
else
{
size_t v___x_2644_; size_t v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2644_ = ((size_t)0ULL);
v___x_2645_ = lean_usize_of_nat(v___x_2631_);
v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2619_, v___f_2636_, v_params_2624_, v___x_2644_, v___x_2645_, v___x_2632_);
v___x_2647_ = lean_apply_4(v_toBind_2623_, lean_box(0), lean_box(0), v___x_2646_, v___f_2629_);
return v___x_2647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM(lean_object* v_m_2648_, uint8_t v_pu_2649_, lean_object* v_inst_2650_, lean_object* v_f_2651_, lean_object* v_decl_2652_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2650_, v_f_2651_, v_decl_2652_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___boxed(lean_object* v_m_2654_, lean_object* v_pu_2655_, lean_object* v_inst_2656_, lean_object* v_f_2657_, lean_object* v_decl_2658_){
_start:
{
uint8_t v_pu_boxed_2659_; lean_object* v_res_2660_; 
v_pu_boxed_2659_ = lean_unbox(v_pu_2655_);
v_res_2660_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM(v_m_2654_, v_pu_boxed_2659_, v_inst_2656_, v_f_2657_, v_decl_2658_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(uint8_t v_pu_2661_, lean_object* v_m_2662_, lean_object* v_inst_2663_, lean_object* v_inst_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2661_, v_inst_2663_, v_inst_2664_, v___y_2665_, v___y_2666_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed(lean_object* v_pu_2668_, lean_object* v_m_2669_, lean_object* v_inst_2670_, lean_object* v_inst_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
uint8_t v_pu_boxed_2674_; lean_object* v_res_2675_; 
v_pu_boxed_2674_ = lean_unbox(v_pu_2668_);
v_res_2675_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(v_pu_boxed_2674_, v_m_2669_, v_inst_2670_, v_inst_2671_, v___y_2672_, v___y_2673_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__1(lean_object* v_m_2676_, lean_object* v_inst_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2677_, v___y_2678_, v___y_2679_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(uint8_t v_pu_2682_){
_start:
{
lean_object* v___x_2683_; lean_object* v___f_2684_; lean_object* v___f_2685_; lean_object* v___x_2686_; 
v___x_2683_ = lean_box(v_pu_2682_);
v___f_2684_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2684_, 0, v___x_2683_);
v___f_2685_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0));
v___x_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___f_2684_);
lean_ctor_set(v___x_2686_, 1, v___f_2685_);
return v___x_2686_;
}
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(lean_object* v_i_2708_, lean_object* v_toPure_2709_, uint8_t v_pu_2710_, lean_object* v_inst_2711_, lean_object* v_f_2712_, lean_object* v_y_2713_, lean_object* v_toBind_2714_, lean_object* v_____do__lift_2715_){
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed(lean_object* v_i_2719_, lean_object* v_toPure_2720_, lean_object* v_pu_2721_, lean_object* v_inst_2722_, lean_object* v_f_2723_, lean_object* v_y_2724_, lean_object* v_toBind_2725_, lean_object* v_____do__lift_2726_){
_start:
{
uint8_t v_pu_boxed_2727_; lean_object* v_res_2728_; 
v_pu_boxed_2727_ = lean_unbox(v_pu_2721_);
v_res_2728_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(v_i_2719_, v_toPure_2720_, v_pu_boxed_2727_, v_inst_2722_, v_f_2723_, v_y_2724_, v_toBind_2725_, v_____do__lift_2726_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5(lean_object* v_____do__lift_2729_, lean_object* v_i_2730_, lean_object* v_toPure_2731_, lean_object* v_____do__lift_2732_){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_2733_, 0, v_____do__lift_2729_);
lean_ctor_set(v___x_2733_, 1, v_i_2730_);
lean_ctor_set(v___x_2733_, 2, v_____do__lift_2732_);
v___x_2734_ = lean_apply_2(v_toPure_2731_, lean_box(0), v___x_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6(lean_object* v_i_2735_, lean_object* v_toPure_2736_, lean_object* v_f_2737_, lean_object* v_y_2738_, lean_object* v_toBind_2739_, lean_object* v_____do__lift_2740_){
_start:
{
lean_object* v___f_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___f_2741_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5), 4, 3);
lean_closure_set(v___f_2741_, 0, v_____do__lift_2740_);
lean_closure_set(v___f_2741_, 1, v_i_2735_);
lean_closure_set(v___f_2741_, 2, v_toPure_2736_);
v___x_2742_ = lean_apply_1(v_f_2737_, v_y_2738_);
v___x_2743_ = lean_apply_4(v_toBind_2739_, lean_box(0), lean_box(0), v___x_2742_, v___f_2741_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7(lean_object* v_____do__lift_2744_, lean_object* v_i_2745_, lean_object* v_offset_2746_, lean_object* v_____do__lift_2747_, lean_object* v_toPure_2748_, lean_object* v_____do__lift_2749_){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v___x_2750_, 0, v_____do__lift_2744_);
lean_ctor_set(v___x_2750_, 1, v_i_2745_);
lean_ctor_set(v___x_2750_, 2, v_offset_2746_);
lean_ctor_set(v___x_2750_, 3, v_____do__lift_2747_);
lean_ctor_set(v___x_2750_, 4, v_____do__lift_2749_);
v___x_2751_ = lean_apply_2(v_toPure_2748_, lean_box(0), v___x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8(lean_object* v_____do__lift_2752_, lean_object* v_i_2753_, lean_object* v_offset_2754_, lean_object* v_toPure_2755_, lean_object* v_inst_2756_, lean_object* v_f_2757_, lean_object* v_ty_2758_, lean_object* v_toBind_2759_, lean_object* v_____do__lift_2760_){
_start:
{
lean_object* v___f_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___f_2761_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7), 6, 5);
lean_closure_set(v___f_2761_, 0, v_____do__lift_2752_);
lean_closure_set(v___f_2761_, 1, v_i_2753_);
lean_closure_set(v___f_2761_, 2, v_offset_2754_);
lean_closure_set(v___f_2761_, 3, v_____do__lift_2760_);
lean_closure_set(v___f_2761_, 4, v_toPure_2755_);
v___x_2762_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_2756_, v_f_2757_, v_ty_2758_);
v___x_2763_ = lean_apply_4(v_toBind_2759_, lean_box(0), lean_box(0), v___x_2762_, v___f_2761_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9(lean_object* v_i_2764_, lean_object* v_offset_2765_, lean_object* v_toPure_2766_, lean_object* v_inst_2767_, lean_object* v_f_2768_, lean_object* v_ty_2769_, lean_object* v_toBind_2770_, lean_object* v_y_2771_, lean_object* v_____do__lift_2772_){
_start:
{
lean_object* v___f_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
lean_inc(v_toBind_2770_);
lean_inc(v_f_2768_);
v___f_2773_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8), 9, 8);
lean_closure_set(v___f_2773_, 0, v_____do__lift_2772_);
lean_closure_set(v___f_2773_, 1, v_i_2764_);
lean_closure_set(v___f_2773_, 2, v_offset_2765_);
lean_closure_set(v___f_2773_, 3, v_toPure_2766_);
lean_closure_set(v___f_2773_, 4, v_inst_2767_);
lean_closure_set(v___f_2773_, 5, v_f_2768_);
lean_closure_set(v___f_2773_, 6, v_ty_2769_);
lean_closure_set(v___f_2773_, 7, v_toBind_2770_);
v___x_2774_ = lean_apply_1(v_f_2768_, v_y_2771_);
v___x_2775_ = lean_apply_4(v_toBind_2770_, lean_box(0), lean_box(0), v___x_2774_, v___f_2773_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10(lean_object* v_cidx_2776_, lean_object* v_toPure_2777_, lean_object* v_____do__lift_2778_){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2779_, 0, v_____do__lift_2778_);
lean_ctor_set(v___x_2779_, 1, v_cidx_2776_);
v___x_2780_ = lean_apply_2(v_toPure_2777_, lean_box(0), v___x_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(lean_object* v_n_2781_, uint8_t v_check_2782_, uint8_t v_persistent_2783_, lean_object* v_toPure_2784_, lean_object* v_____do__lift_2785_){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v___x_2786_, 0, v_____do__lift_2785_);
lean_ctor_set(v___x_2786_, 1, v_n_2781_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*2, v_check_2782_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*2 + 1, v_persistent_2783_);
v___x_2787_ = lean_apply_2(v_toPure_2784_, lean_box(0), v___x_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed(lean_object* v_n_2788_, lean_object* v_check_2789_, lean_object* v_persistent_2790_, lean_object* v_toPure_2791_, lean_object* v_____do__lift_2792_){
_start:
{
uint8_t v_check_923__boxed_2793_; uint8_t v_persistent_924__boxed_2794_; lean_object* v_res_2795_; 
v_check_923__boxed_2793_ = lean_unbox(v_check_2789_);
v_persistent_924__boxed_2794_ = lean_unbox(v_persistent_2790_);
v_res_2795_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(v_n_2788_, v_check_923__boxed_2793_, v_persistent_924__boxed_2794_, v_toPure_2791_, v_____do__lift_2792_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(lean_object* v_n_2796_, uint8_t v_check_2797_, uint8_t v_persistent_2798_, lean_object* v_objs_x3f_2799_, lean_object* v_toPure_2800_, lean_object* v_____do__lift_2801_){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = lean_alloc_ctor(8, 3, 2);
lean_ctor_set(v___x_2802_, 0, v_____do__lift_2801_);
lean_ctor_set(v___x_2802_, 1, v_n_2796_);
lean_ctor_set(v___x_2802_, 2, v_objs_x3f_2799_);
lean_ctor_set_uint8(v___x_2802_, sizeof(void*)*3, v_check_2797_);
lean_ctor_set_uint8(v___x_2802_, sizeof(void*)*3 + 1, v_persistent_2798_);
v___x_2803_ = lean_apply_2(v_toPure_2800_, lean_box(0), v___x_2802_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed(lean_object* v_n_2804_, lean_object* v_check_2805_, lean_object* v_persistent_2806_, lean_object* v_objs_x3f_2807_, lean_object* v_toPure_2808_, lean_object* v_____do__lift_2809_){
_start:
{
uint8_t v_check_939__boxed_2810_; uint8_t v_persistent_940__boxed_2811_; lean_object* v_res_2812_; 
v_check_939__boxed_2810_ = lean_unbox(v_check_2805_);
v_persistent_940__boxed_2811_ = lean_unbox(v_persistent_2806_);
v_res_2812_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(v_n_2804_, v_check_939__boxed_2810_, v_persistent_940__boxed_2811_, v_objs_x3f_2807_, v_toPure_2808_, v_____do__lift_2809_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13(lean_object* v_toPure_2813_, lean_object* v_____do__lift_2814_){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2815_, 0, v_____do__lift_2814_);
v___x_2816_ = lean_apply_2(v_toPure_2813_, lean_box(0), v___x_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(uint8_t v_pu_2817_, lean_object* v_m_2818_, lean_object* v_inst_2819_, lean_object* v_inst_2820_, lean_object* v_f_2821_, lean_object* v_decl_2822_){
_start:
{
switch(lean_obj_tag(v_decl_2822_))
{
case 0:
{
lean_object* v_toApplicative_2823_; lean_object* v_toBind_2824_; lean_object* v_toPure_2825_; lean_object* v_decl_2826_; lean_object* v___f_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v_toApplicative_2823_ = lean_ctor_get(v_inst_2820_, 0);
v_toBind_2824_ = lean_ctor_get(v_inst_2820_, 1);
lean_inc(v_toBind_2824_);
v_toPure_2825_ = lean_ctor_get(v_toApplicative_2823_, 1);
v_decl_2826_ = lean_ctor_get(v_decl_2822_, 0);
lean_inc_ref(v_decl_2826_);
lean_dec_ref_known(v_decl_2822_, 1);
lean_inc(v_toPure_2825_);
v___f_2827_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0), 2, 1);
lean_closure_set(v___f_2827_, 0, v_toPure_2825_);
v___x_2828_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(v_pu_2817_, v_inst_2819_, v_inst_2820_, v_f_2821_, v_decl_2826_);
v___x_2829_ = lean_apply_4(v_toBind_2824_, lean_box(0), lean_box(0), v___x_2828_, v___f_2827_);
return v___x_2829_;
}
case 1:
{
lean_object* v_toApplicative_2830_; lean_object* v_toBind_2831_; lean_object* v_toPure_2832_; lean_object* v_decl_2833_; lean_object* v___f_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v_toApplicative_2830_ = lean_ctor_get(v_inst_2820_, 0);
v_toBind_2831_ = lean_ctor_get(v_inst_2820_, 1);
lean_inc(v_toBind_2831_);
v_toPure_2832_ = lean_ctor_get(v_toApplicative_2830_, 1);
v_decl_2833_ = lean_ctor_get(v_decl_2822_, 0);
lean_inc_ref(v_decl_2833_);
lean_dec_ref_known(v_decl_2822_, 1);
lean_inc(v_toPure_2832_);
v___f_2834_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1), 2, 1);
lean_closure_set(v___f_2834_, 0, v_toPure_2832_);
v___x_2835_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2817_, v_inst_2819_, v_inst_2820_, v_f_2821_, v_decl_2833_);
v___x_2836_ = lean_apply_4(v_toBind_2831_, lean_box(0), lean_box(0), v___x_2835_, v___f_2834_);
return v___x_2836_;
}
case 2:
{
lean_object* v_toApplicative_2837_; lean_object* v_toBind_2838_; lean_object* v_toPure_2839_; lean_object* v_decl_2840_; lean_object* v___f_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v_toApplicative_2837_ = lean_ctor_get(v_inst_2820_, 0);
v_toBind_2838_ = lean_ctor_get(v_inst_2820_, 1);
lean_inc(v_toBind_2838_);
v_toPure_2839_ = lean_ctor_get(v_toApplicative_2837_, 1);
v_decl_2840_ = lean_ctor_get(v_decl_2822_, 0);
lean_inc_ref(v_decl_2840_);
lean_dec_ref_known(v_decl_2822_, 1);
lean_inc(v_toPure_2839_);
v___f_2841_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2), 2, 1);
lean_closure_set(v___f_2841_, 0, v_toPure_2839_);
v___x_2842_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(v_pu_2817_, v_inst_2819_, v_inst_2820_, v_f_2821_, v_decl_2840_);
v___x_2843_ = lean_apply_4(v_toBind_2838_, lean_box(0), lean_box(0), v___x_2842_, v___f_2841_);
return v___x_2843_;
}
case 3:
{
lean_object* v_toApplicative_2844_; lean_object* v_toBind_2845_; lean_object* v_toPure_2846_; lean_object* v_fvarId_2847_; lean_object* v_i_2848_; lean_object* v_y_2849_; lean_object* v___x_2850_; lean_object* v___f_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_toApplicative_2844_ = lean_ctor_get(v_inst_2820_, 0);
lean_dec(v_inst_2819_);
v_toBind_2845_ = lean_ctor_get(v_inst_2820_, 1);
lean_inc_n(v_toBind_2845_, 2);
v_toPure_2846_ = lean_ctor_get(v_toApplicative_2844_, 1);
lean_inc(v_toPure_2846_);
v_fvarId_2847_ = lean_ctor_get(v_decl_2822_, 0);
lean_inc(v_fvarId_2847_);
v_i_2848_ = lean_ctor_get(v_decl_2822_, 1);
lean_inc(v_i_2848_);
v_y_2849_ = lean_ctor_get(v_decl_2822_, 2);
lean_inc(v_y_2849_);
lean_dec_ref_known(v_decl_2822_, 3);
v___x_2850_ = lean_box(v_pu_2817_);
lean_inc(v_f_2821_);
v___f_2851_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed), 8, 7);
lean_closure_set(v___f_2851_, 0, v_i_2848_);
lean_closure_set(v___f_2851_, 1, v_toPure_2846_);
lean_closure_set(v___f_2851_, 2, v___x_2850_);
lean_closure_set(v___f_2851_, 3, v_inst_2820_);
lean_closure_set(v___f_2851_, 4, v_f_2821_);
lean_closure_set(v___f_2851_, 5, v_y_2849_);
lean_closure_set(v___f_2851_, 6, v_toBind_2845_);
v___x_2852_ = lean_apply_1(v_f_2821_, v_fvarId_2847_);
v___x_2853_ = lean_apply_4(v_toBind_2845_, lean_box(0), lean_box(0), v___x_2852_, v___f_2851_);
return v___x_2853_;
}
case 4:
{
lean_object* v_toApplicative_2854_; lean_object* v_toBind_2855_; lean_object* v_toPure_2856_; lean_object* v_fvarId_2857_; lean_object* v_i_2858_; lean_object* v_y_2859_; lean_object* v___f_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v_toApplicative_2854_ = lean_ctor_get(v_inst_2820_, 0);
lean_inc_ref(v_toApplicative_2854_);
lean_dec(v_inst_2819_);
v_toBind_2855_ = lean_ctor_get(v_inst_2820_, 1);
lean_inc_n(v_toBind_2855_, 2);
lean_dec_ref(v_inst_2820_);
v_toPure_2856_ = lean_ctor_get(v_toApplicative_2854_, 1);
lean_inc(v_toPure_2856_);
lean_dec_ref(v_toApplicative_2854_);
v_fvarId_2857_ = lean_ctor_get(v_decl_2822_, 0);
lean_inc(v_fvarId_2857_);
v_i_2858_ = lean_ctor_get(v_decl_2822_, 1);
lean_inc(v_i_2858_);
v_y_2859_ = lean_ctor_get(v_decl_2822_, 2);
lean_inc(v_y_2859_);
lean_dec_ref_known(v_decl_2822_, 3);
lean_inc(v_f_2821_);
v___f_2860_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6), 6, 5);
lean_closure_set(v___f_2860_, 0, v_i_2858_);
lean_closure_set(v___f_2860_, 1, v_toPure_2856_);
lean_closure_set(v___f_2860_, 2, v_f_2821_);
lean_closure_set(v___f_2860_, 3, v_y_2859_);
lean_closure_set(v___f_2860_, 4, v_toBind_2855_);
v___x_2861_ = lean_apply_1(v_f_2821_, v_fvarId_2857_);
v___x_2862_ = lean_apply_4(v_toBind_2855_, lean_box(0), lean_box(0), v___x_2861_, v___f_2860_);
return v___x_2862_;
}
case 5:
{
lean_object* v_toApplicative_2863_; lean_object* v_toBind_2864_; lean_object* v_toPure_2865_; lean_object* v_fvarId_2866_; lean_object* v_i_2867_; lean_object* v_offset_2868_; lean_object* v_y_2869_; lean_object* v_ty_2870_; lean_object* v___f_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v_toApplicative_2863_ = lean_ctor_get(v_inst_2820_, 0);
lean_dec(v_inst_2819_);
v_toBind_2864_ = lean_ctor_get(v_inst_2820_, 1);
lean_inc_n(v_toBind_2864_, 2);
v_toPure_2865_ = lean_ctor_get(v_toApplicative_2863_, 1);
lean_inc(v_toPure_2865_);
v_fvarId_2866_ = lean_ctor_get(v_decl_2822_, 0);
lean_inc(v_fvarId_2866_);
v_i_2867_ = lean_ctor_get(v_decl_2822_, 1);
lean_inc(v_i_2867_);
v_offset_2868_ = lean_ctor_get(v_decl_2822_, 2);
lean_inc(v_offset_2868_);
v_y_2869_ = lean_ctor_get(v_decl_2822_, 3);
lean_inc(v_y_2869_);
v_ty_2870_ = lean_ctor_get(v_decl_2822_, 4);
lean_inc_ref(v_ty_2870_);
lean_dec_ref_known(v_decl_2822_, 5);
lean_inc(v_f_2821_);
v___f_2871_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9), 9, 8);
lean_closure_set(v___f_2871_, 0, v_i_2867_);
lean_closure_set(v___f_2871_, 1, v_offset_2868_);
lean_closure_set(v___f_2871_, 2, v_toPure_2865_);
lean_closure_set(v___f_2871_, 3, v_inst_2820_);
lean_closure_set(v___f_2871_, 4, v_f_2821_);
lean_closure_set(v___f_2871_, 5, v_ty_2870_);
lean_closure_set(v___f_2871_, 6, v_toBind_2864_);
lean_closure_set(v___f_2871_, 7, v_y_2869_);
v___x_2872_ = lean_apply_1(v_f_2821_, v_fvarId_2866_);
v___x_2873_ = lean_apply_4(v_toBind_2864_, lean_box(0), lean_box(0), v___x_2872_, v___f_2871_);
return v___x_2873_;
}
case 6:
{
lean_object* v_toApplicative_2874_; lean_object* v_toBind_2875_; lean_object* v_toPure_2876_; lean_object* v_fvarId_2877_; lean_object* v_cidx_2878_; lean_object* v___f_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v_toApplicative_2874_ = lean_ctor_get(v_inst_2820_, 0);
lean_inc_ref(v_toApplicative_2874_);
lean_dec(v_inst_2819_);
v_toBind_2875_ = lean_ctor_get(v_inst_2820_, 1);
lean_inc(v_toBind_2875_);
lean_dec_ref(v_inst_2820_);
v_toPure_2876_ = lean_ctor_get(v_toApplicative_2874_, 1);
lean_inc(v_toPure_2876_);
lean_dec_ref(v_toApplicative_2874_);
v_fvarId_2877_ = lean_ctor_get(v_decl_2822_, 0);
lean_inc(v_fvarId_2877_);
v_cidx_2878_ = lean_ctor_get(v_decl_2822_, 1);
lean_inc(v_cidx_2878_);
lean_dec_ref_known(v_decl_2822_, 2);
v___f_2879_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10), 3, 2);
lean_closure_set(v___f_2879_, 0, v_cidx_2878_);
lean_closure_set(v___f_2879_, 1, v_toPure_2876_);
v___x_2880_ = lean_apply_1(v_f_2821_, v_fvarId_2877_);
v___x_2881_ = lean_apply_4(v_toBind_2875_, lean_box(0), lean_box(0), v___x_2880_, v___f_2879_);
return v___x_2881_;
}
case 7:
{
lean_object* v_toApplicative_2882_; lean_object* v_toBind_2883_; lean_object* v_toPure_2884_; lean_object* v_fvarId_2885_; lean_object* v_n_2886_; uint8_t v_check_2887_; uint8_t v_persistent_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___f_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v_toApplicative_2882_ = lean_ctor_get(v_inst_2820_, 0);
lean_inc_ref(v_toApplicative_2882_);
lean_dec(v_inst_2819_);
v_toBind_2883_ = lean_ctor_get(v_inst_2820_, 1);
lean_inc(v_toBind_2883_);
lean_dec_ref(v_inst_2820_);
v_toPure_2884_ = lean_ctor_get(v_toApplicative_2882_, 1);
lean_inc(v_toPure_2884_);
lean_dec_ref(v_toApplicative_2882_);
v_fvarId_2885_ = lean_ctor_get(v_decl_2822_, 0);
lean_inc(v_fvarId_2885_);
v_n_2886_ = lean_ctor_get(v_decl_2822_, 1);
lean_inc(v_n_2886_);
v_check_2887_ = lean_ctor_get_uint8(v_decl_2822_, sizeof(void*)*2);
v_persistent_2888_ = lean_ctor_get_uint8(v_decl_2822_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_decl_2822_, 2);
v___x_2889_ = lean_box(v_check_2887_);
v___x_2890_ = lean_box(v_persistent_2888_);
v___f_2891_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed), 5, 4);
lean_closure_set(v___f_2891_, 0, v_n_2886_);
lean_closure_set(v___f_2891_, 1, v___x_2889_);
lean_closure_set(v___f_2891_, 2, v___x_2890_);
lean_closure_set(v___f_2891_, 3, v_toPure_2884_);
v___x_2892_ = lean_apply_1(v_f_2821_, v_fvarId_2885_);
v___x_2893_ = lean_apply_4(v_toBind_2883_, lean_box(0), lean_box(0), v___x_2892_, v___f_2891_);
return v___x_2893_;
}
case 8:
{
lean_object* v_toApplicative_2894_; lean_object* v_toBind_2895_; lean_object* v_toPure_2896_; lean_object* v_fvarId_2897_; lean_object* v_n_2898_; uint8_t v_check_2899_; uint8_t v_persistent_2900_; lean_object* v_objs_x3f_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___f_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v_toApplicative_2894_ = lean_ctor_get(v_inst_2820_, 0);
lean_inc_ref(v_toApplicative_2894_);
lean_dec(v_inst_2819_);
v_toBind_2895_ = lean_ctor_get(v_inst_2820_, 1);
lean_inc(v_toBind_2895_);
lean_dec_ref(v_inst_2820_);
v_toPure_2896_ = lean_ctor_get(v_toApplicative_2894_, 1);
lean_inc(v_toPure_2896_);
lean_dec_ref(v_toApplicative_2894_);
v_fvarId_2897_ = lean_ctor_get(v_decl_2822_, 0);
lean_inc(v_fvarId_2897_);
v_n_2898_ = lean_ctor_get(v_decl_2822_, 1);
lean_inc(v_n_2898_);
v_check_2899_ = lean_ctor_get_uint8(v_decl_2822_, sizeof(void*)*3);
v_persistent_2900_ = lean_ctor_get_uint8(v_decl_2822_, sizeof(void*)*3 + 1);
v_objs_x3f_2901_ = lean_ctor_get(v_decl_2822_, 2);
lean_inc(v_objs_x3f_2901_);
lean_dec_ref_known(v_decl_2822_, 3);
v___x_2902_ = lean_box(v_check_2899_);
v___x_2903_ = lean_box(v_persistent_2900_);
v___f_2904_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed), 6, 5);
lean_closure_set(v___f_2904_, 0, v_n_2898_);
lean_closure_set(v___f_2904_, 1, v___x_2902_);
lean_closure_set(v___f_2904_, 2, v___x_2903_);
lean_closure_set(v___f_2904_, 3, v_objs_x3f_2901_);
lean_closure_set(v___f_2904_, 4, v_toPure_2896_);
v___x_2905_ = lean_apply_1(v_f_2821_, v_fvarId_2897_);
v___x_2906_ = lean_apply_4(v_toBind_2895_, lean_box(0), lean_box(0), v___x_2905_, v___f_2904_);
return v___x_2906_;
}
default: 
{
lean_object* v_toApplicative_2907_; lean_object* v_toBind_2908_; lean_object* v_toPure_2909_; lean_object* v_fvarId_2910_; lean_object* v___f_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v_toApplicative_2907_ = lean_ctor_get(v_inst_2820_, 0);
lean_inc_ref(v_toApplicative_2907_);
lean_dec(v_inst_2819_);
v_toBind_2908_ = lean_ctor_get(v_inst_2820_, 1);
lean_inc(v_toBind_2908_);
lean_dec_ref(v_inst_2820_);
v_toPure_2909_ = lean_ctor_get(v_toApplicative_2907_, 1);
lean_inc(v_toPure_2909_);
lean_dec_ref(v_toApplicative_2907_);
v_fvarId_2910_ = lean_ctor_get(v_decl_2822_, 0);
lean_inc(v_fvarId_2910_);
lean_dec_ref_known(v_decl_2822_, 1);
v___f_2911_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13), 2, 1);
lean_closure_set(v___f_2911_, 0, v_toPure_2909_);
v___x_2912_ = lean_apply_1(v_f_2821_, v_fvarId_2910_);
v___x_2913_ = lean_apply_4(v_toBind_2908_, lean_box(0), lean_box(0), v___x_2912_, v___f_2911_);
return v___x_2913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed(lean_object* v_pu_2914_, lean_object* v_m_2915_, lean_object* v_inst_2916_, lean_object* v_inst_2917_, lean_object* v_f_2918_, lean_object* v_decl_2919_){
_start:
{
uint8_t v_pu_boxed_2920_; lean_object* v_res_2921_; 
v_pu_boxed_2920_ = lean_unbox(v_pu_2914_);
v_res_2921_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(v_pu_boxed_2920_, v_m_2915_, v_inst_2916_, v_inst_2917_, v_f_2918_, v_decl_2919_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15(lean_object* v_inst_2922_, lean_object* v_f_2923_, lean_object* v_y_2924_, lean_object* v_____r_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_2922_, v_f_2923_, v_y_2924_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16(lean_object* v_f_2927_, lean_object* v_y_2928_, lean_object* v_____r_2929_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = lean_apply_1(v_f_2927_, v_y_2928_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17(lean_object* v_inst_2931_, lean_object* v_f_2932_, lean_object* v_ty_2933_, lean_object* v_____r_2934_){
_start:
{
lean_object* v___x_2935_; 
v___x_2935_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_2931_, v_f_2932_, v_ty_2933_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18(lean_object* v_f_2936_, lean_object* v_y_2937_, lean_object* v_toBind_2938_, lean_object* v___f_2939_, lean_object* v_____r_2940_){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = lean_apply_1(v_f_2936_, v_y_2937_);
v___x_2942_ = lean_apply_4(v_toBind_2938_, lean_box(0), lean_box(0), v___x_2941_, v___f_2939_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__19(lean_object* v_m_2943_, lean_object* v_inst_2944_, lean_object* v_f_2945_, lean_object* v_decl_2946_){
_start:
{
switch(lean_obj_tag(v_decl_2946_))
{
case 0:
{
lean_object* v_decl_2947_; lean_object* v___x_2948_; 
v_decl_2947_ = lean_ctor_get(v_decl_2946_, 0);
lean_inc_ref(v_decl_2947_);
lean_dec_ref_known(v_decl_2946_, 1);
v___x_2948_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_2944_, v_f_2945_, v_decl_2947_);
return v___x_2948_;
}
case 1:
{
lean_object* v_decl_2949_; lean_object* v___x_2950_; 
v_decl_2949_ = lean_ctor_get(v_decl_2946_, 0);
lean_inc_ref(v_decl_2949_);
lean_dec_ref_known(v_decl_2946_, 1);
v___x_2950_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2944_, v_f_2945_, v_decl_2949_);
return v___x_2950_;
}
case 2:
{
lean_object* v_decl_2951_; lean_object* v___x_2952_; 
v_decl_2951_ = lean_ctor_get(v_decl_2946_, 0);
lean_inc_ref(v_decl_2951_);
lean_dec_ref_known(v_decl_2946_, 1);
v___x_2952_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_2944_, v_f_2945_, v_decl_2951_);
return v___x_2952_;
}
case 3:
{
lean_object* v_toBind_2953_; lean_object* v_fvarId_2954_; lean_object* v_y_2955_; lean_object* v___f_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v_toBind_2953_ = lean_ctor_get(v_inst_2944_, 1);
lean_inc(v_toBind_2953_);
v_fvarId_2954_ = lean_ctor_get(v_decl_2946_, 0);
lean_inc(v_fvarId_2954_);
v_y_2955_ = lean_ctor_get(v_decl_2946_, 2);
lean_inc(v_y_2955_);
lean_dec_ref_known(v_decl_2946_, 3);
lean_inc(v_f_2945_);
v___f_2956_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15), 4, 3);
lean_closure_set(v___f_2956_, 0, v_inst_2944_);
lean_closure_set(v___f_2956_, 1, v_f_2945_);
lean_closure_set(v___f_2956_, 2, v_y_2955_);
v___x_2957_ = lean_apply_1(v_f_2945_, v_fvarId_2954_);
v___x_2958_ = lean_apply_4(v_toBind_2953_, lean_box(0), lean_box(0), v___x_2957_, v___f_2956_);
return v___x_2958_;
}
case 4:
{
lean_object* v_toBind_2959_; lean_object* v_fvarId_2960_; lean_object* v_y_2961_; lean_object* v___f_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v_toBind_2959_ = lean_ctor_get(v_inst_2944_, 1);
lean_inc(v_toBind_2959_);
lean_dec_ref(v_inst_2944_);
v_fvarId_2960_ = lean_ctor_get(v_decl_2946_, 0);
lean_inc(v_fvarId_2960_);
v_y_2961_ = lean_ctor_get(v_decl_2946_, 2);
lean_inc(v_y_2961_);
lean_dec_ref_known(v_decl_2946_, 3);
lean_inc(v_f_2945_);
v___f_2962_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16), 3, 2);
lean_closure_set(v___f_2962_, 0, v_f_2945_);
lean_closure_set(v___f_2962_, 1, v_y_2961_);
v___x_2963_ = lean_apply_1(v_f_2945_, v_fvarId_2960_);
v___x_2964_ = lean_apply_4(v_toBind_2959_, lean_box(0), lean_box(0), v___x_2963_, v___f_2962_);
return v___x_2964_;
}
case 5:
{
lean_object* v_toBind_2965_; lean_object* v_fvarId_2966_; lean_object* v_y_2967_; lean_object* v_ty_2968_; lean_object* v___f_2969_; lean_object* v___f_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v_toBind_2965_ = lean_ctor_get(v_inst_2944_, 1);
lean_inc_n(v_toBind_2965_, 2);
v_fvarId_2966_ = lean_ctor_get(v_decl_2946_, 0);
lean_inc(v_fvarId_2966_);
v_y_2967_ = lean_ctor_get(v_decl_2946_, 3);
lean_inc(v_y_2967_);
v_ty_2968_ = lean_ctor_get(v_decl_2946_, 4);
lean_inc_ref(v_ty_2968_);
lean_dec_ref_known(v_decl_2946_, 5);
lean_inc_n(v_f_2945_, 2);
v___f_2969_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17), 4, 3);
lean_closure_set(v___f_2969_, 0, v_inst_2944_);
lean_closure_set(v___f_2969_, 1, v_f_2945_);
lean_closure_set(v___f_2969_, 2, v_ty_2968_);
v___f_2970_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18), 5, 4);
lean_closure_set(v___f_2970_, 0, v_f_2945_);
lean_closure_set(v___f_2970_, 1, v_y_2967_);
lean_closure_set(v___f_2970_, 2, v_toBind_2965_);
lean_closure_set(v___f_2970_, 3, v___f_2969_);
v___x_2971_ = lean_apply_1(v_f_2945_, v_fvarId_2966_);
v___x_2972_ = lean_apply_4(v_toBind_2965_, lean_box(0), lean_box(0), v___x_2971_, v___f_2970_);
return v___x_2972_;
}
default: 
{
lean_object* v_fvarId_2973_; lean_object* v___x_2974_; 
lean_dec_ref(v_inst_2944_);
v_fvarId_2973_ = lean_ctor_get(v_decl_2946_, 0);
lean_inc(v_fvarId_2973_);
lean_dec_ref(v_decl_2946_);
v___x_2974_ = lean_apply_1(v_f_2945_, v_fvarId_2973_);
return v___x_2974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(uint8_t v_pu_2976_){
_start:
{
lean_object* v___x_2977_; lean_object* v___f_2978_; lean_object* v___f_2979_; lean_object* v___x_2980_; 
v___x_2977_ = lean_box(v_pu_2976_);
v___f_2978_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed), 6, 1);
lean_closure_set(v___f_2978_, 0, v___x_2977_);
v___f_2979_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0));
v___x_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___f_2978_);
lean_ctor_set(v___x_2980_, 1, v___f_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___boxed(lean_object* v_pu_2981_){
_start:
{
uint8_t v_pu_boxed_2982_; lean_object* v_res_2983_; 
v_pu_boxed_2982_ = lean_unbox(v_pu_2981_);
v_res_2983_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(v_pu_boxed_2982_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0(lean_object* v_ctorName_2984_, lean_object* v_params_2985_, lean_object* v_toPure_2986_, lean_object* v_____do__lift_2987_){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2988_, 0, v_ctorName_2984_);
lean_ctor_set(v___x_2988_, 1, v_params_2985_);
lean_ctor_set(v___x_2988_, 2, v_____do__lift_2987_);
v___x_2989_ = lean_apply_2(v_toPure_2986_, lean_box(0), v___x_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(lean_object* v_ctorName_2990_, lean_object* v_toPure_2991_, uint8_t v_pu_2992_, lean_object* v_inst_2993_, lean_object* v_inst_2994_, lean_object* v_f_2995_, lean_object* v_code_2996_, lean_object* v_toBind_2997_, lean_object* v_params_2998_){
_start:
{
lean_object* v___f_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___f_2999_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0), 4, 3);
lean_closure_set(v___f_2999_, 0, v_ctorName_2990_);
lean_closure_set(v___f_2999_, 1, v_params_2998_);
lean_closure_set(v___f_2999_, 2, v_toPure_2991_);
v___x_3000_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_2992_, v_inst_2993_, v_inst_2994_, v_f_2995_, v_code_2996_);
v___x_3001_ = lean_apply_4(v_toBind_2997_, lean_box(0), lean_box(0), v___x_3000_, v___f_2999_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed(lean_object* v_ctorName_3002_, lean_object* v_toPure_3003_, lean_object* v_pu_3004_, lean_object* v_inst_3005_, lean_object* v_inst_3006_, lean_object* v_f_3007_, lean_object* v_code_3008_, lean_object* v_toBind_3009_, lean_object* v_params_3010_){
_start:
{
uint8_t v_pu_boxed_3011_; lean_object* v_res_3012_; 
v_pu_boxed_3011_ = lean_unbox(v_pu_3004_);
v_res_3012_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(v_ctorName_3002_, v_toPure_3003_, v_pu_boxed_3011_, v_inst_3005_, v_inst_3006_, v_f_3007_, v_code_3008_, v_toBind_3009_, v_params_3010_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2(lean_object* v_info_3013_, lean_object* v_toPure_3014_, lean_object* v_____do__lift_3015_){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3016_, 0, v_info_3013_);
lean_ctor_set(v___x_3016_, 1, v_____do__lift_3015_);
v___x_3017_ = lean_apply_2(v_toPure_3014_, lean_box(0), v___x_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3(lean_object* v_toPure_3018_, lean_object* v_____do__lift_3019_){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3020_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3020_, 0, v_____do__lift_3019_);
v___x_3021_ = lean_apply_2(v_toPure_3018_, lean_box(0), v___x_3020_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(uint8_t v_pu_3022_, lean_object* v_m_3023_, lean_object* v_inst_3024_, lean_object* v_inst_3025_, lean_object* v_f_3026_, lean_object* v_alt_3027_){
_start:
{
switch(lean_obj_tag(v_alt_3027_))
{
case 0:
{
lean_object* v_toApplicative_3028_; lean_object* v_toBind_3029_; lean_object* v_toPure_3030_; lean_object* v_ctorName_3031_; lean_object* v_params_3032_; lean_object* v_code_3033_; lean_object* v___x_3034_; lean_object* v___f_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; size_t v_sz_3038_; size_t v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v_toApplicative_3028_ = lean_ctor_get(v_inst_3025_, 0);
v_toBind_3029_ = lean_ctor_get(v_inst_3025_, 1);
lean_inc_n(v_toBind_3029_, 2);
v_toPure_3030_ = lean_ctor_get(v_toApplicative_3028_, 1);
v_ctorName_3031_ = lean_ctor_get(v_alt_3027_, 0);
lean_inc(v_ctorName_3031_);
v_params_3032_ = lean_ctor_get(v_alt_3027_, 1);
lean_inc_ref(v_params_3032_);
v_code_3033_ = lean_ctor_get(v_alt_3027_, 2);
lean_inc_ref(v_code_3033_);
lean_dec_ref_known(v_alt_3027_, 3);
v___x_3034_ = lean_box(v_pu_3022_);
lean_inc(v_f_3026_);
lean_inc_ref_n(v_inst_3025_, 2);
lean_inc(v_inst_3024_);
lean_inc(v_toPure_3030_);
v___f_3035_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed), 9, 8);
lean_closure_set(v___f_3035_, 0, v_ctorName_3031_);
lean_closure_set(v___f_3035_, 1, v_toPure_3030_);
lean_closure_set(v___f_3035_, 2, v___x_3034_);
lean_closure_set(v___f_3035_, 3, v_inst_3024_);
lean_closure_set(v___f_3035_, 4, v_inst_3025_);
lean_closure_set(v___f_3035_, 5, v_f_3026_);
lean_closure_set(v___f_3035_, 6, v_code_3033_);
lean_closure_set(v___f_3035_, 7, v_toBind_3029_);
v___x_3036_ = lean_box(v_pu_3022_);
v___x_3037_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(v___x_3037_, 0, lean_box(0));
lean_closure_set(v___x_3037_, 1, v___x_3036_);
lean_closure_set(v___x_3037_, 2, v_inst_3024_);
lean_closure_set(v___x_3037_, 3, v_inst_3025_);
lean_closure_set(v___x_3037_, 4, v_f_3026_);
v_sz_3038_ = lean_array_size(v_params_3032_);
v___x_3039_ = ((size_t)0ULL);
v___x_3040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3025_, v___x_3037_, v_sz_3038_, v___x_3039_, v_params_3032_);
v___x_3041_ = lean_apply_4(v_toBind_3029_, lean_box(0), lean_box(0), v___x_3040_, v___f_3035_);
return v___x_3041_;
}
case 1:
{
lean_object* v_toApplicative_3042_; lean_object* v_toBind_3043_; lean_object* v_toPure_3044_; lean_object* v_info_3045_; lean_object* v_code_3046_; lean_object* v___f_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v_toApplicative_3042_ = lean_ctor_get(v_inst_3025_, 0);
v_toBind_3043_ = lean_ctor_get(v_inst_3025_, 1);
lean_inc(v_toBind_3043_);
v_toPure_3044_ = lean_ctor_get(v_toApplicative_3042_, 1);
v_info_3045_ = lean_ctor_get(v_alt_3027_, 0);
lean_inc_ref(v_info_3045_);
v_code_3046_ = lean_ctor_get(v_alt_3027_, 1);
lean_inc_ref(v_code_3046_);
lean_dec_ref_known(v_alt_3027_, 2);
lean_inc(v_toPure_3044_);
v___f_3047_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2), 3, 2);
lean_closure_set(v___f_3047_, 0, v_info_3045_);
lean_closure_set(v___f_3047_, 1, v_toPure_3044_);
v___x_3048_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_3022_, v_inst_3024_, v_inst_3025_, v_f_3026_, v_code_3046_);
v___x_3049_ = lean_apply_4(v_toBind_3043_, lean_box(0), lean_box(0), v___x_3048_, v___f_3047_);
return v___x_3049_;
}
default: 
{
lean_object* v_toApplicative_3050_; lean_object* v_toBind_3051_; lean_object* v_toPure_3052_; lean_object* v_code_3053_; lean_object* v___f_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v_toApplicative_3050_ = lean_ctor_get(v_inst_3025_, 0);
v_toBind_3051_ = lean_ctor_get(v_inst_3025_, 1);
lean_inc(v_toBind_3051_);
v_toPure_3052_ = lean_ctor_get(v_toApplicative_3050_, 1);
v_code_3053_ = lean_ctor_get(v_alt_3027_, 0);
lean_inc_ref(v_code_3053_);
lean_dec_ref_known(v_alt_3027_, 1);
lean_inc(v_toPure_3052_);
v___f_3054_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3), 2, 1);
lean_closure_set(v___f_3054_, 0, v_toPure_3052_);
v___x_3055_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(v_pu_3022_, v_inst_3024_, v_inst_3025_, v_f_3026_, v_code_3053_);
v___x_3056_ = lean_apply_4(v_toBind_3051_, lean_box(0), lean_box(0), v___x_3055_, v___f_3054_);
return v___x_3056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed(lean_object* v_pu_3057_, lean_object* v_m_3058_, lean_object* v_inst_3059_, lean_object* v_inst_3060_, lean_object* v_f_3061_, lean_object* v_alt_3062_){
_start:
{
uint8_t v_pu_boxed_3063_; lean_object* v_res_3064_; 
v_pu_boxed_3063_ = lean_unbox(v_pu_3057_);
v_res_3064_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(v_pu_boxed_3063_, v_m_3058_, v_inst_3059_, v_inst_3060_, v_f_3061_, v_alt_3062_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5(lean_object* v_inst_3065_, lean_object* v_f_3066_, lean_object* v_code_3067_, lean_object* v_____r_3068_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_3065_, v_f_3066_, v_code_3067_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__7(lean_object* v_m_3070_, lean_object* v_inst_3071_, lean_object* v_f_3072_, lean_object* v_alt_3073_){
_start:
{
switch(lean_obj_tag(v_alt_3073_))
{
case 0:
{
lean_object* v_toApplicative_3074_; lean_object* v_toBind_3075_; lean_object* v_params_3076_; lean_object* v_code_3077_; lean_object* v_toPure_3078_; lean_object* v___f_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; uint8_t v___x_3083_; 
v_toApplicative_3074_ = lean_ctor_get(v_inst_3071_, 0);
v_toBind_3075_ = lean_ctor_get(v_inst_3071_, 1);
lean_inc(v_toBind_3075_);
v_params_3076_ = lean_ctor_get(v_alt_3073_, 1);
lean_inc_ref(v_params_3076_);
v_code_3077_ = lean_ctor_get(v_alt_3073_, 2);
lean_inc_ref(v_code_3077_);
lean_dec_ref_known(v_alt_3073_, 3);
v_toPure_3078_ = lean_ctor_get(v_toApplicative_3074_, 1);
lean_inc(v_f_3072_);
lean_inc_ref(v_inst_3071_);
v___f_3079_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5), 4, 3);
lean_closure_set(v___f_3079_, 0, v_inst_3071_);
lean_closure_set(v___f_3079_, 1, v_f_3072_);
lean_closure_set(v___f_3079_, 2, v_code_3077_);
v___x_3080_ = lean_unsigned_to_nat(0u);
v___x_3081_ = lean_array_get_size(v_params_3076_);
v___x_3082_ = lean_box(0);
v___x_3083_ = lean_nat_dec_lt(v___x_3080_, v___x_3081_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
lean_inc(v_toPure_3078_);
lean_dec_ref(v_params_3076_);
lean_dec(v_f_3072_);
lean_dec_ref(v_inst_3071_);
v___x_3084_ = lean_apply_2(v_toPure_3078_, lean_box(0), v___x_3082_);
v___x_3085_ = lean_apply_4(v_toBind_3075_, lean_box(0), lean_box(0), v___x_3084_, v___f_3079_);
return v___x_3085_;
}
else
{
lean_object* v___f_3086_; uint8_t v___x_3087_; 
lean_inc_ref(v_inst_3071_);
v___f_3086_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_3086_, 0, v_inst_3071_);
lean_closure_set(v___f_3086_, 1, v_f_3072_);
v___x_3087_ = lean_nat_dec_le(v___x_3081_, v___x_3081_);
if (v___x_3087_ == 0)
{
if (v___x_3083_ == 0)
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
lean_inc(v_toPure_3078_);
lean_dec_ref(v___f_3086_);
lean_dec_ref(v_params_3076_);
lean_dec_ref(v_inst_3071_);
v___x_3088_ = lean_apply_2(v_toPure_3078_, lean_box(0), v___x_3082_);
v___x_3089_ = lean_apply_4(v_toBind_3075_, lean_box(0), lean_box(0), v___x_3088_, v___f_3079_);
return v___x_3089_;
}
else
{
size_t v___x_3090_; size_t v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3090_ = ((size_t)0ULL);
v___x_3091_ = lean_usize_of_nat(v___x_3081_);
v___x_3092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3071_, v___f_3086_, v_params_3076_, v___x_3090_, v___x_3091_, v___x_3082_);
v___x_3093_ = lean_apply_4(v_toBind_3075_, lean_box(0), lean_box(0), v___x_3092_, v___f_3079_);
return v___x_3093_;
}
}
else
{
size_t v___x_3094_; size_t v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3094_ = ((size_t)0ULL);
v___x_3095_ = lean_usize_of_nat(v___x_3081_);
v___x_3096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3071_, v___f_3086_, v_params_3076_, v___x_3094_, v___x_3095_, v___x_3082_);
v___x_3097_ = lean_apply_4(v_toBind_3075_, lean_box(0), lean_box(0), v___x_3096_, v___f_3079_);
return v___x_3097_;
}
}
}
case 1:
{
lean_object* v_code_3098_; lean_object* v___x_3099_; 
v_code_3098_ = lean_ctor_get(v_alt_3073_, 1);
lean_inc_ref(v_code_3098_);
lean_dec_ref_known(v_alt_3073_, 2);
v___x_3099_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_3071_, v_f_3072_, v_code_3098_);
return v___x_3099_;
}
default: 
{
lean_object* v_code_3100_; lean_object* v___x_3101_; 
v_code_3100_ = lean_ctor_get(v_alt_3073_, 0);
lean_inc_ref(v_code_3100_);
lean_dec_ref_known(v_alt_3073_, 1);
v___x_3101_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_3071_, v_f_3072_, v_code_3100_);
return v___x_3101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt(uint8_t v_pu_3103_){
_start:
{
lean_object* v___x_3104_; lean_object* v___f_3105_; lean_object* v___f_3106_; lean_object* v___x_3107_; 
v___x_3104_ = lean_box(v_pu_3103_);
v___f_3105_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed), 6, 1);
lean_closure_set(v___f_3105_, 0, v___x_3104_);
v___f_3106_ = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0));
v___x_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___f_3105_);
lean_ctor_set(v___x_3107_, 1, v___f_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___boxed(lean_object* v_pu_3108_){
_start:
{
uint8_t v_pu_boxed_3109_; lean_object* v_res_3110_; 
v_pu_boxed_3109_ = lean_unbox(v_pu_3108_);
v_res_3110_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt(v_pu_boxed_3109_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(lean_object* v_toPure_3113_, lean_object* v_____do__lift_3114_){
_start:
{
if (lean_obj_tag(v_____do__lift_3114_) == 0)
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = lean_box(0);
v___x_3116_ = lean_apply_2(v_toPure_3113_, lean_box(0), v___x_3115_);
return v___x_3116_;
}
else
{
lean_object* v_val_3117_; uint8_t v___x_3118_; 
v_val_3117_ = lean_ctor_get(v_____do__lift_3114_, 0);
v___x_3118_ = lean_unbox(v_val_3117_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0));
v___x_3120_ = lean_apply_2(v_toPure_3113_, lean_box(0), v___x_3119_);
return v___x_3120_;
}
else
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = lean_box(0);
v___x_3122_ = lean_apply_2(v_toPure_3113_, lean_box(0), v___x_3121_);
return v___x_3122_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed(lean_object* v_toPure_3123_, lean_object* v_____do__lift_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(v_toPure_3123_, v_____do__lift_3124_);
lean_dec(v_____do__lift_3124_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(lean_object* v_toPure_3126_, uint8_t v_____do__lift_3127_){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3128_ = lean_box(v_____do__lift_3127_);
v___x_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
v___x_3130_ = lean_apply_2(v_toPure_3126_, lean_box(0), v___x_3129_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed(lean_object* v_toPure_3131_, lean_object* v_____do__lift_3132_){
_start:
{
uint8_t v_____do__lift_371__boxed_3133_; lean_object* v_res_3134_; 
v_____do__lift_371__boxed_3133_ = lean_unbox(v_____do__lift_3132_);
v_res_3134_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(v_toPure_3131_, v_____do__lift_371__boxed_3133_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(lean_object* v_inst_3135_, lean_object* v_f_3136_, lean_object* v_fvar_3137_){
_start:
{
lean_object* v_toApplicative_3138_; lean_object* v_toBind_3139_; lean_object* v_toPure_3140_; lean_object* v___x_3141_; lean_object* v___f_3142_; lean_object* v___f_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v_toApplicative_3138_ = lean_ctor_get(v_inst_3135_, 0);
lean_inc_ref(v_toApplicative_3138_);
v_toBind_3139_ = lean_ctor_get(v_inst_3135_, 1);
lean_inc_n(v_toBind_3139_, 2);
lean_dec_ref(v_inst_3135_);
v_toPure_3140_ = lean_ctor_get(v_toApplicative_3138_, 1);
lean_inc_n(v_toPure_3140_, 2);
lean_dec_ref(v_toApplicative_3138_);
v___x_3141_ = lean_apply_1(v_f_3136_, v_fvar_3137_);
v___f_3142_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3142_, 0, v_toPure_3140_);
v___f_3143_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3143_, 0, v_toPure_3140_);
v___x_3144_ = lean_apply_4(v_toBind_3139_, lean_box(0), lean_box(0), v___x_3141_, v___f_3143_);
v___x_3145_ = lean_apply_4(v_toBind_3139_, lean_box(0), lean_box(0), v___x_3144_, v___f_3142_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go(lean_object* v_m_3146_, lean_object* v_inst_3147_, lean_object* v_f_3148_, lean_object* v_fvar_3149_){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(v_inst_3147_, v_f_3148_, v_fvar_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(lean_object* v_toPure_3151_, lean_object* v_____do__lift_3152_){
_start:
{
if (lean_obj_tag(v_____do__lift_3152_) == 0)
{
uint8_t v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3153_ = 1;
v___x_3154_ = lean_box(v___x_3153_);
v___x_3155_ = lean_apply_2(v_toPure_3151_, lean_box(0), v___x_3154_);
return v___x_3155_;
}
else
{
uint8_t v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3156_ = 0;
v___x_3157_ = lean_box(v___x_3156_);
v___x_3158_ = lean_apply_2(v_toPure_3151_, lean_box(0), v___x_3157_);
return v___x_3158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed(lean_object* v_toPure_3159_, lean_object* v_____do__lift_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(v_toPure_3159_, v_____do__lift_3160_);
lean_dec(v_____do__lift_3160_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg(lean_object* v_inst_3162_, lean_object* v_inst_3163_, lean_object* v_f_3164_, lean_object* v_x_3165_){
_start:
{
lean_object* v_toApplicative_3166_; lean_object* v_toBind_3167_; lean_object* v_forFVarM_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3189_; 
v_toApplicative_3166_ = lean_ctor_get(v_inst_3162_, 0);
v_toBind_3167_ = lean_ctor_get(v_inst_3162_, 1);
lean_inc(v_toBind_3167_);
v_forFVarM_3168_ = lean_ctor_get(v_inst_3163_, 1);
v_isSharedCheck_3189_ = !lean_is_exclusive(v_inst_3163_);
if (v_isSharedCheck_3189_ == 0)
{
lean_object* v_unused_3190_; 
v_unused_3190_ = lean_ctor_get(v_inst_3163_, 0);
lean_dec(v_unused_3190_);
v___x_3170_ = v_inst_3163_;
v_isShared_3171_ = v_isSharedCheck_3189_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_forFVarM_3168_);
lean_dec(v_inst_3163_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3189_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___f_3172_; lean_object* v___f_3173_; lean_object* v___f_3174_; lean_object* v___f_3175_; lean_object* v___f_3176_; lean_object* v___x_3178_; 
lean_inc_ref_n(v_inst_3162_, 5);
v___f_3172_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3172_, 0, v_inst_3162_);
v___f_3173_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3173_, 0, v_inst_3162_);
v___f_3174_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3174_, 0, v_inst_3162_);
v___f_3175_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3175_, 0, v_inst_3162_);
v___f_3176_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3176_, 0, v_inst_3162_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 1, v___f_3173_);
lean_ctor_set(v___x_3170_, 0, v___f_3172_);
v___x_3178_ = v___x_3170_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___f_3172_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v___f_3173_);
v___x_3178_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v_toPure_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___f_3186_; lean_object* v___x_3187_; 
lean_inc_ref_n(v_inst_3162_, 2);
v___x_3179_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3179_, 0, lean_box(0));
lean_closure_set(v___x_3179_, 1, v_inst_3162_);
v___x_3180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3178_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
lean_ctor_set(v___x_3180_, 2, v___f_3174_);
lean_ctor_set(v___x_3180_, 3, v___f_3175_);
lean_ctor_set(v___x_3180_, 4, v___f_3176_);
v___x_3181_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3181_, 0, lean_box(0));
lean_closure_set(v___x_3181_, 1, v_inst_3162_);
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3180_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v_toPure_3183_ = lean_ctor_get(v_toApplicative_3166_, 1);
lean_inc(v_toPure_3183_);
v___x_3184_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go), 4, 3);
lean_closure_set(v___x_3184_, 0, lean_box(0));
lean_closure_set(v___x_3184_, 1, v_inst_3162_);
lean_closure_set(v___x_3184_, 2, v_f_3164_);
v___x_3185_ = lean_apply_4(v_forFVarM_3168_, lean_box(0), v___x_3182_, v___x_3184_, v_x_3165_);
v___f_3186_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3186_, 0, v_toPure_3183_);
v___x_3187_ = lean_apply_4(v_toBind_3167_, lean_box(0), lean_box(0), v___x_3185_, v___f_3186_);
return v___x_3187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM(lean_object* v_m_3191_, lean_object* v_00_u03b1_3192_, lean_object* v_inst_3193_, lean_object* v_inst_3194_, lean_object* v_f_3195_, lean_object* v_x_3196_){
_start:
{
lean_object* v___x_3197_; 
v___x_3197_ = l_Lean_Compiler_LCNF_anyFVarM___redArg(v_inst_3193_, v_inst_3194_, v_f_3195_, v_x_3196_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(lean_object* v_toPure_3198_, lean_object* v_____do__lift_3199_){
_start:
{
if (lean_obj_tag(v_____do__lift_3199_) == 0)
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = lean_box(0);
v___x_3201_ = lean_apply_2(v_toPure_3198_, lean_box(0), v___x_3200_);
return v___x_3201_;
}
else
{
lean_object* v_val_3202_; uint8_t v___x_3203_; 
v_val_3202_ = lean_ctor_get(v_____do__lift_3199_, 0);
v___x_3203_ = lean_unbox(v_val_3202_);
if (v___x_3203_ == 0)
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3204_ = lean_box(0);
v___x_3205_ = lean_apply_2(v_toPure_3198_, lean_box(0), v___x_3204_);
return v___x_3205_;
}
else
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0));
v___x_3207_ = lean_apply_2(v_toPure_3198_, lean_box(0), v___x_3206_);
return v___x_3207_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed(lean_object* v_toPure_3208_, lean_object* v_____do__lift_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(v_toPure_3208_, v_____do__lift_3209_);
lean_dec(v_____do__lift_3209_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(lean_object* v_inst_3211_, lean_object* v_f_3212_, lean_object* v_fvar_3213_){
_start:
{
lean_object* v_toApplicative_3214_; lean_object* v_toBind_3215_; lean_object* v_toPure_3216_; lean_object* v___x_3217_; lean_object* v___f_3218_; lean_object* v___f_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v_toApplicative_3214_ = lean_ctor_get(v_inst_3211_, 0);
lean_inc_ref(v_toApplicative_3214_);
v_toBind_3215_ = lean_ctor_get(v_inst_3211_, 1);
lean_inc_n(v_toBind_3215_, 2);
lean_dec_ref(v_inst_3211_);
v_toPure_3216_ = lean_ctor_get(v_toApplicative_3214_, 1);
lean_inc_n(v_toPure_3216_, 2);
lean_dec_ref(v_toApplicative_3214_);
v___x_3217_ = lean_apply_1(v_f_3212_, v_fvar_3213_);
v___f_3218_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3218_, 0, v_toPure_3216_);
v___f_3219_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3219_, 0, v_toPure_3216_);
v___x_3220_ = lean_apply_4(v_toBind_3215_, lean_box(0), lean_box(0), v___x_3217_, v___f_3219_);
v___x_3221_ = lean_apply_4(v_toBind_3215_, lean_box(0), lean_box(0), v___x_3220_, v___f_3218_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go(lean_object* v_m_3222_, lean_object* v_inst_3223_, lean_object* v_f_3224_, lean_object* v_fvar_3225_){
_start:
{
lean_object* v___x_3226_; 
v___x_3226_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(v_inst_3223_, v_f_3224_, v_fvar_3225_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(lean_object* v_toPure_3227_, lean_object* v_____do__lift_3228_){
_start:
{
if (lean_obj_tag(v_____do__lift_3228_) == 1)
{
uint8_t v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = 1;
v___x_3230_ = lean_box(v___x_3229_);
v___x_3231_ = lean_apply_2(v_toPure_3227_, lean_box(0), v___x_3230_);
return v___x_3231_;
}
else
{
uint8_t v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = 0;
v___x_3233_ = lean_box(v___x_3232_);
v___x_3234_ = lean_apply_2(v_toPure_3227_, lean_box(0), v___x_3233_);
return v___x_3234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed(lean_object* v_toPure_3235_, lean_object* v_____do__lift_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(v_toPure_3235_, v_____do__lift_3236_);
lean_dec(v_____do__lift_3236_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg(lean_object* v_inst_3238_, lean_object* v_inst_3239_, lean_object* v_f_3240_, lean_object* v_x_3241_){
_start:
{
lean_object* v_toApplicative_3242_; lean_object* v_toBind_3243_; lean_object* v_forFVarM_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3265_; 
v_toApplicative_3242_ = lean_ctor_get(v_inst_3238_, 0);
v_toBind_3243_ = lean_ctor_get(v_inst_3238_, 1);
lean_inc(v_toBind_3243_);
v_forFVarM_3244_ = lean_ctor_get(v_inst_3239_, 1);
v_isSharedCheck_3265_ = !lean_is_exclusive(v_inst_3239_);
if (v_isSharedCheck_3265_ == 0)
{
lean_object* v_unused_3266_; 
v_unused_3266_ = lean_ctor_get(v_inst_3239_, 0);
lean_dec(v_unused_3266_);
v___x_3246_ = v_inst_3239_;
v_isShared_3247_ = v_isSharedCheck_3265_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_forFVarM_3244_);
lean_dec(v_inst_3239_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3265_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___f_3248_; lean_object* v___f_3249_; lean_object* v___f_3250_; lean_object* v___f_3251_; lean_object* v___f_3252_; lean_object* v___x_3254_; 
lean_inc_ref_n(v_inst_3238_, 5);
v___f_3248_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3248_, 0, v_inst_3238_);
v___f_3249_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3249_, 0, v_inst_3238_);
v___f_3250_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3250_, 0, v_inst_3238_);
v___f_3251_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3251_, 0, v_inst_3238_);
v___f_3252_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3252_, 0, v_inst_3238_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 1, v___f_3249_);
lean_ctor_set(v___x_3246_, 0, v___f_3248_);
v___x_3254_ = v___x_3246_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___f_3248_);
lean_ctor_set(v_reuseFailAlloc_3264_, 1, v___f_3249_);
v___x_3254_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v_toPure_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___f_3262_; lean_object* v___x_3263_; 
lean_inc_ref_n(v_inst_3238_, 2);
v___x_3255_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3255_, 0, lean_box(0));
lean_closure_set(v___x_3255_, 1, v_inst_3238_);
v___x_3256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3254_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
lean_ctor_set(v___x_3256_, 2, v___f_3250_);
lean_ctor_set(v___x_3256_, 3, v___f_3251_);
lean_ctor_set(v___x_3256_, 4, v___f_3252_);
v___x_3257_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3257_, 0, lean_box(0));
lean_closure_set(v___x_3257_, 1, v_inst_3238_);
v___x_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3256_);
lean_ctor_set(v___x_3258_, 1, v___x_3257_);
v_toPure_3259_ = lean_ctor_get(v_toApplicative_3242_, 1);
lean_inc(v_toPure_3259_);
v___x_3260_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go), 4, 3);
lean_closure_set(v___x_3260_, 0, lean_box(0));
lean_closure_set(v___x_3260_, 1, v_inst_3238_);
lean_closure_set(v___x_3260_, 2, v_f_3240_);
v___x_3261_ = lean_apply_4(v_forFVarM_3244_, lean_box(0), v___x_3258_, v___x_3260_, v_x_3241_);
v___f_3262_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3262_, 0, v_toPure_3259_);
v___x_3263_ = lean_apply_4(v_toBind_3243_, lean_box(0), lean_box(0), v___x_3261_, v___f_3262_);
return v___x_3263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM(lean_object* v_m_3267_, lean_object* v_00_u03b1_3268_, lean_object* v_inst_3269_, lean_object* v_inst_3270_, lean_object* v_f_3271_, lean_object* v_x_3272_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Lean_Compiler_LCNF_allFVarM___redArg(v_inst_3269_, v_inst_3270_, v_f_3271_, v_x_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(lean_object* v_f_3274_, lean_object* v_x_3275_){
_start:
{
lean_object* v___x_3276_; uint8_t v___x_3277_; 
v___x_3276_ = lean_apply_1(v_f_3274_, v_x_3275_);
v___x_3277_ = lean_unbox(v___x_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed(lean_object* v_f_3278_, lean_object* v_x_3279_){
_start:
{
uint8_t v_res_3280_; lean_object* v_r_3281_; 
v_res_3280_ = l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(v_f_3278_, v_x_3279_);
v_r_3281_ = lean_box(v_res_3280_);
return v_r_3281_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar___redArg(lean_object* v_inst_3301_, lean_object* v_f_3302_, lean_object* v_x_3303_){
_start:
{
lean_object* v___f_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___f_3304_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3304_, 0, v_f_3302_);
v___x_3305_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9));
v___x_3306_ = l_Lean_Compiler_LCNF_anyFVarM___redArg(v___x_3305_, v_inst_3301_, v___f_3304_, v_x_3303_);
v___x_3307_ = lean_unbox(v___x_3306_);
lean_dec(v___x_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___boxed(lean_object* v_inst_3308_, lean_object* v_f_3309_, lean_object* v_x_3310_){
_start:
{
uint8_t v_res_3311_; lean_object* v_r_3312_; 
v_res_3311_ = l_Lean_Compiler_LCNF_anyFVar___redArg(v_inst_3308_, v_f_3309_, v_x_3310_);
v_r_3312_ = lean_box(v_res_3311_);
return v_r_3312_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar(lean_object* v_00_u03b1_3313_, lean_object* v_inst_3314_, lean_object* v_f_3315_, lean_object* v_x_3316_){
_start:
{
uint8_t v___x_3317_; 
v___x_3317_ = l_Lean_Compiler_LCNF_anyFVar___redArg(v_inst_3314_, v_f_3315_, v_x_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___boxed(lean_object* v_00_u03b1_3318_, lean_object* v_inst_3319_, lean_object* v_f_3320_, lean_object* v_x_3321_){
_start:
{
uint8_t v_res_3322_; lean_object* v_r_3323_; 
v_res_3322_ = l_Lean_Compiler_LCNF_anyFVar(v_00_u03b1_3318_, v_inst_3319_, v_f_3320_, v_x_3321_);
v_r_3323_ = lean_box(v_res_3322_);
return v_r_3323_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar___redArg(lean_object* v_inst_3324_, lean_object* v_f_3325_, lean_object* v_x_3326_){
_start:
{
lean_object* v___f_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; uint8_t v___x_3330_; 
v___f_3327_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3327_, 0, v_f_3325_);
v___x_3328_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9));
v___x_3329_ = l_Lean_Compiler_LCNF_allFVarM___redArg(v___x_3328_, v_inst_3324_, v___f_3327_, v_x_3326_);
v___x_3330_ = lean_unbox(v___x_3329_);
lean_dec(v___x_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___redArg___boxed(lean_object* v_inst_3331_, lean_object* v_f_3332_, lean_object* v_x_3333_){
_start:
{
uint8_t v_res_3334_; lean_object* v_r_3335_; 
v_res_3334_ = l_Lean_Compiler_LCNF_allFVar___redArg(v_inst_3331_, v_f_3332_, v_x_3333_);
v_r_3335_ = lean_box(v_res_3334_);
return v_r_3335_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar(lean_object* v_00_u03b1_3336_, lean_object* v_inst_3337_, lean_object* v_f_3338_, lean_object* v_x_3339_){
_start:
{
uint8_t v___x_3340_; 
v___x_3340_ = l_Lean_Compiler_LCNF_allFVar___redArg(v_inst_3337_, v_f_3338_, v_x_3339_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___boxed(lean_object* v_00_u03b1_3341_, lean_object* v_inst_3342_, lean_object* v_f_3343_, lean_object* v_x_3344_){
_start:
{
uint8_t v_res_3345_; lean_object* v_r_3346_; 
v_res_3345_ = l_Lean_Compiler_LCNF_allFVar(v_00_u03b1_3341_, v_inst_3342_, v_f_3343_, v_x_3344_);
v_r_3346_ = lean_box(v_res_3345_);
return v_r_3346_;
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
