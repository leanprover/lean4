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
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Compiler.LCNF.Expr.mapFVarM"};
static const lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Compiler.LCNF.FVarUtil"};
static const lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Compiler.LCNF.Expr.forFVarM"};
static const lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0_value;
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(uint8_t, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* l_OptionT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_pure(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_anyFVar___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_anyFVar___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_anyFVar___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_anyFVar___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_anyFVar___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_anyFVar___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_anyFVar___redArg___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_Lean_instBEqFVarId_beq(x_2, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_3);
x_7 = l_Lean_Expr_fvar___override(x_4);
x_8 = lean_apply_2(x_5, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_apply_2(x_5, lean_box(0), x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; size_t x_13; size_t x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_13 = lean_ptr_addr(x_4);
x_14 = lean_ptr_addr(x_2);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
x_8 = x_15;
goto block_12;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = lean_ptr_addr(x_5);
x_17 = lean_ptr_addr(x_6);
x_18 = lean_usize_dec_eq(x_16, x_17);
x_8 = x_18;
goto block_12;
}
block_12:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_3);
x_9 = l_Lean_Expr_app___override(x_2, x_6);
x_10 = lean_apply_2(x_7, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_11 = lean_apply_2(x_7, lean_box(0), x_3);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; size_t x_18; size_t x_19; uint8_t x_20; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec_ref(x_1);
x_18 = lean_ptr_addr(x_6);
x_19 = lean_ptr_addr(x_3);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
x_10 = x_20;
goto block_17;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = lean_ptr_addr(x_7);
x_22 = lean_ptr_addr(x_8);
x_23 = lean_usize_dec_eq(x_21, x_22);
x_10 = x_23;
goto block_17;
}
block_17:
{
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_5);
x_11 = l_Lean_Expr_lam___override(x_2, x_3, x_8, x_4);
x_12 = lean_apply_2(x_9, lean_box(0), x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = l_Lean_instBEqBinderInfo_beq(x_4, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_5);
x_14 = l_Lean_Expr_lam___override(x_2, x_3, x_8, x_4);
x_15 = lean_apply_2(x_9, lean_box(0), x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
x_16 = lean_apply_2(x_9, lean_box(0), x_5);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
x_10 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; size_t x_18; size_t x_19; uint8_t x_20; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec_ref(x_1);
x_18 = lean_ptr_addr(x_6);
x_19 = lean_ptr_addr(x_3);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
x_10 = x_20;
goto block_17;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = lean_ptr_addr(x_7);
x_22 = lean_ptr_addr(x_8);
x_23 = lean_usize_dec_eq(x_21, x_22);
x_10 = x_23;
goto block_17;
}
block_17:
{
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_5);
x_11 = l_Lean_Expr_forallE___override(x_2, x_3, x_8, x_4);
x_12 = lean_apply_2(x_9, lean_box(0), x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = l_Lean_instBEqBinderInfo_beq(x_4, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_5);
x_14 = l_Lean_Expr_forallE___override(x_2, x_3, x_8, x_4);
x_15 = lean_apply_2(x_9, lean_box(0), x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
x_16 = lean_apply_2(x_9, lean_box(0), x_5);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
x_10 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2));
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_unsigned_to_nat(30u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_box(x_3);
lean_inc_ref(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3___boxed), 8, 7);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_11);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_5);
lean_closure_set(x_12, 6, x_6);
x_13 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(x_7, x_8, x_6);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_13, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_box(x_3);
lean_inc_ref(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5___boxed), 8, 7);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_11);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_5);
lean_closure_set(x_12, 6, x_6);
x_13 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(x_7, x_8, x_6);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_13, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasFVar(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_3);
return x_7;
}
else
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
lean_inc(x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_3);
x_12 = lean_apply_1(x_2, x_8);
x_13 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_14 = l_Lean_instInhabitedExpr;
x_15 = l_instInhabitedOfMonad___redArg(x_1, x_14);
x_16 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3;
x_17 = l_panic___redArg(x_15, x_16);
return x_17;
}
case 5:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_21);
lean_inc(x_2);
lean_inc_ref(x_1);
lean_inc_ref(x_18);
lean_inc_ref(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__2), 8, 7);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_3);
lean_closure_set(x_22, 2, x_18);
lean_closure_set(x_22, 3, x_19);
lean_closure_set(x_22, 4, x_1);
lean_closure_set(x_22, 5, x_2);
lean_closure_set(x_22, 6, x_21);
x_23 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(x_1, x_2, x_18);
x_24 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_23, x_22);
return x_24;
}
case 6:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_27);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_box(x_28);
lean_inc(x_30);
lean_inc(x_2);
lean_inc_ref(x_1);
lean_inc_ref(x_26);
lean_inc_ref(x_29);
x_32 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4___boxed), 10, 9);
lean_closure_set(x_32, 0, x_29);
lean_closure_set(x_32, 1, x_25);
lean_closure_set(x_32, 2, x_31);
lean_closure_set(x_32, 3, x_3);
lean_closure_set(x_32, 4, x_26);
lean_closure_set(x_32, 5, x_27);
lean_closure_set(x_32, 6, x_1);
lean_closure_set(x_32, 7, x_2);
lean_closure_set(x_32, 8, x_30);
x_33 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(x_1, x_2, x_26);
x_34 = lean_apply_4(x_30, lean_box(0), lean_box(0), x_33, x_32);
return x_34;
}
case 7:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_37);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_box(x_38);
lean_inc(x_40);
lean_inc(x_2);
lean_inc_ref(x_1);
lean_inc_ref(x_36);
lean_inc_ref(x_39);
x_42 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(x_42, 0, x_39);
lean_closure_set(x_42, 1, x_35);
lean_closure_set(x_42, 2, x_41);
lean_closure_set(x_42, 3, x_3);
lean_closure_set(x_42, 4, x_36);
lean_closure_set(x_42, 5, x_37);
lean_closure_set(x_42, 6, x_1);
lean_closure_set(x_42, 7, x_2);
lean_closure_set(x_42, 8, x_40);
x_43 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(x_1, x_2, x_36);
x_44 = lean_apply_4(x_40, lean_box(0), lean_box(0), x_43, x_42);
return x_44;
}
case 8:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_45 = l_Lean_instInhabitedExpr;
x_46 = l_instInhabitedOfMonad___redArg(x_1, x_45);
x_47 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3;
x_48 = l_panic___redArg(x_46, x_47);
return x_48;
}
case 11:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_49 = l_Lean_instInhabitedExpr;
x_50 = l_instInhabitedOfMonad___redArg(x_1, x_49);
x_51 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3;
x_52 = l_panic___redArg(x_50, x_51);
return x_52;
}
default: 
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
x_53 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_53);
lean_dec_ref(x_1);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_apply_2(x_54, lean_box(0), x_3);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_3);
lean_closure_set(x_9, 4, x_4);
x_10 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(x_5, x_6, x_4);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Expr_mapFVarM(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2));
x_2 = lean_unsigned_to_nat(40u);
x_3 = lean_unsigned_to_nat(49u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_11; 
x_11 = l_Lean_Expr_hasFVar(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
else
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_1);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec_ref(x_3);
x_17 = lean_apply_1(x_2, x_16);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_18 = lean_box(0);
x_19 = l_instInhabitedOfMonad___redArg(x_1, x_18);
x_20 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1;
x_21 = l_panic___redArg(x_19, x_20);
return x_21;
}
case 5:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_23);
lean_dec_ref(x_3);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_2);
lean_inc_ref(x_1);
x_25 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__1), 4, 3);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_2);
lean_closure_set(x_25, 2, x_23);
x_26 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(x_1, x_2, x_22);
x_27 = lean_apply_4(x_24, lean_box(0), lean_box(0), x_26, x_25);
return x_27;
}
case 6:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_29);
lean_dec_ref(x_3);
x_4 = x_28;
x_5 = x_29;
goto block_10;
}
case 7:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_31);
lean_dec_ref(x_3);
x_4 = x_30;
x_5 = x_31;
goto block_10;
}
case 8:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_32 = lean_box(0);
x_33 = l_instInhabitedOfMonad___redArg(x_1, x_32);
x_34 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1;
x_35 = l_panic___redArg(x_33, x_34);
return x_35;
}
case 11:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = l_instInhabitedOfMonad___redArg(x_1, x_36);
x_38 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1;
x_39 = l_panic___redArg(x_37, x_38);
return x_39;
}
default: 
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_40 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_40);
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_box(0);
x_43 = lean_apply_2(x_41, lean_box(0), x_42);
return x_43;
}
}
}
block_10:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_2);
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_5);
x_8 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(x_1, x_2, x_4);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(x_1, x_2, x_4);
x_6 = lean_apply_2(x_3, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_box(0);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__0), 3, 2);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_11);
x_14 = lean_apply_1(x_3, x_12);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_14, x_13);
return x_15;
}
default: 
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_19);
x_20 = lean_box(x_1);
lean_inc(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_4);
lean_closure_set(x_21, 2, x_18);
x_22 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(x_2, x_3, x_19);
x_23 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_22, x_21);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l_Lean_Compiler_LCNF_Arg_mapFVarM(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_3);
x_11 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(x_1, x_2, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Compiler_LCNF_Arg_forFVarM(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0___boxed), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarArg___closed__0));
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instTraverseFVarArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_1, x_2, x_4);
x_6 = lean_apply_2(x_3, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(x_1, x_2, x_4);
x_6 = lean_apply_2(x_3, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(x_1, x_2, x_3, x_5);
x_7 = lean_apply_2(x_4, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_box(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7___boxed), 5, 4);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_3);
x_11 = lean_array_size(x_4);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_5, x_6, x_11, x_12, x_4);
x_14 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_13, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(x_1, x_2, x_3, x_5);
x_7 = lean_apply_2(x_4, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(x_1, x_2, x_3, x_4, x_5, x_7);
x_9 = lean_apply_2(x_6, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
x_9 = lean_unbox(x_5);
x_10 = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(x_8, x_2, x_3, x_4, x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_box(x_1);
x_12 = lean_box(x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed), 7, 6);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_10);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
lean_closure_set(x_13, 5, x_5);
x_14 = lean_array_size(x_6);
x_15 = 0;
x_16 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_7, x_8, x_14, x_15, x_6);
x_17 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_16, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox(x_4);
x_13 = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(x_11, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(x_1, x_2, x_3, x_5);
x_7 = lean_apply_2(x_4, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(x_1, x_2, x_4);
x_6 = lean_apply_2(x_3, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_box(x_1);
lean_inc(x_3);
lean_inc_ref(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
x_10 = lean_box(x_1);
lean_inc(x_7);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_7);
x_18 = lean_box(x_1);
lean_inc(x_7);
lean_inc(x_4);
x_19 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed), 4, 3);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_4);
lean_closure_set(x_19, 2, x_7);
switch (lean_obj_tag(x_4)) {
case 2:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_24 = lean_ctor_get(x_4, 2);
lean_inc(x_24);
lean_dec_ref(x_4);
x_25 = lean_apply_1(x_3, x_24);
x_26 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_25, x_19);
return x_26;
}
case 3:
{
lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_19);
lean_dec(x_3);
x_27 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_27);
lean_dec_ref(x_4);
x_28 = lean_array_size(x_27);
x_29 = 0;
x_30 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_2, x_9, x_28, x_29, x_27);
x_31 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_30, x_11);
return x_31;
}
case 4:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec_ref(x_19);
lean_dec_ref(x_11);
lean_inc(x_7);
x_32 = lean_ctor_get(x_4, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_33);
x_34 = lean_box(x_1);
lean_inc(x_6);
x_35 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3___boxed), 8, 7);
lean_closure_set(x_35, 0, x_34);
lean_closure_set(x_35, 1, x_4);
lean_closure_set(x_35, 2, x_7);
lean_closure_set(x_35, 3, x_33);
lean_closure_set(x_35, 4, x_2);
lean_closure_set(x_35, 5, x_9);
lean_closure_set(x_35, 6, x_6);
x_36 = lean_apply_1(x_3, x_32);
x_37 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_36, x_35);
return x_37;
}
case 5:
{
lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_19);
lean_dec(x_3);
x_38 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_38);
lean_dec_ref(x_4);
x_39 = lean_array_size(x_38);
x_40 = 0;
x_41 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_2, x_9, x_39, x_40, x_38);
x_42 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_41, x_11);
return x_42;
}
case 6:
{
lean_object* x_43; 
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
lean_dec_ref(x_4);
x_20 = x_43;
goto block_23;
}
case 7:
{
lean_object* x_44; 
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_44 = lean_ctor_get(x_4, 1);
lean_inc(x_44);
lean_dec_ref(x_4);
x_20 = x_44;
goto block_23;
}
case 8:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_45 = lean_ctor_get(x_4, 2);
lean_inc(x_45);
lean_dec_ref(x_4);
x_46 = lean_apply_1(x_3, x_45);
x_47 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_46, x_19);
return x_47;
}
case 9:
{
lean_object* x_48; 
lean_dec_ref(x_19);
lean_dec(x_3);
x_48 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_48);
lean_dec_ref(x_4);
x_12 = x_48;
goto block_17;
}
case 10:
{
lean_object* x_49; 
lean_dec_ref(x_19);
lean_dec(x_3);
x_49 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_4);
x_12 = x_49;
goto block_17;
}
case 11:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_19);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_inc(x_7);
lean_dec_ref(x_2);
x_50 = lean_ctor_get(x_4, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_4, 1);
lean_inc(x_51);
x_52 = lean_box(x_1);
x_53 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8___boxed), 5, 4);
lean_closure_set(x_53, 0, x_52);
lean_closure_set(x_53, 1, x_4);
lean_closure_set(x_53, 2, x_50);
lean_closure_set(x_53, 3, x_7);
x_54 = lean_apply_1(x_3, x_51);
x_55 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_54, x_53);
return x_55;
}
case 12:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_19);
lean_dec_ref(x_11);
lean_inc(x_7);
x_56 = lean_ctor_get(x_4, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_57);
x_58 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_59 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_59);
x_60 = lean_box(x_1);
x_61 = lean_box(x_58);
lean_inc(x_6);
x_62 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed), 10, 9);
lean_closure_set(x_62, 0, x_60);
lean_closure_set(x_62, 1, x_4);
lean_closure_set(x_62, 2, x_57);
lean_closure_set(x_62, 3, x_61);
lean_closure_set(x_62, 4, x_7);
lean_closure_set(x_62, 5, x_59);
lean_closure_set(x_62, 6, x_2);
lean_closure_set(x_62, 7, x_9);
lean_closure_set(x_62, 8, x_6);
x_63 = lean_apply_1(x_3, x_56);
x_64 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_63, x_62);
return x_64;
}
case 13:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_19);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_inc(x_7);
lean_dec_ref(x_2);
x_65 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_4, 1);
lean_inc(x_66);
x_67 = lean_box(x_1);
x_68 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6___boxed), 5, 4);
lean_closure_set(x_68, 0, x_67);
lean_closure_set(x_68, 1, x_4);
lean_closure_set(x_68, 2, x_65);
lean_closure_set(x_68, 3, x_7);
x_69 = lean_apply_1(x_3, x_66);
x_70 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_69, x_68);
return x_70;
}
case 14:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_19);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_inc(x_7);
lean_dec_ref(x_2);
x_71 = lean_ctor_get(x_4, 0);
lean_inc(x_71);
x_72 = lean_box(x_1);
x_73 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9___boxed), 4, 3);
lean_closure_set(x_73, 0, x_72);
lean_closure_set(x_73, 1, x_4);
lean_closure_set(x_73, 2, x_7);
x_74 = lean_apply_1(x_3, x_71);
x_75 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_74, x_73);
return x_75;
}
default: 
{
lean_object* x_76; 
lean_dec_ref(x_19);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_inc(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_76 = lean_apply_2(x_7, lean_box(0), x_4);
return x_76;
}
}
block_17:
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_size(x_12);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_2, x_9, x_13, x_14, x_12);
x_16 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_15, x_11);
return x_16;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_apply_1(x_3, x_20);
x_22 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_21, x_19);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l_Lean_Compiler_LCNF_LetValue_mapFVarM(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_1);
x_8 = lean_box(0);
x_9 = lean_nat_dec_lt(x_6, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_10 = lean_apply_2(x_2, lean_box(0), x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
if (x_9 == 0)
{
lean_object* x_12; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_12 = lean_apply_2(x_2, lean_box(0), x_8);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_3, x_4, x_1, x_13, x_14, x_8);
return x_15;
}
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
lean_dec(x_2);
x_16 = 0;
x_17 = lean_usize_of_nat(x_7);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_3, x_4, x_1, x_16, x_17, x_8);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_2);
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0), 4, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
switch (lean_obj_tag(x_3)) {
case 2:
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_23 = lean_ctor_get(x_3, 2);
lean_inc(x_23);
lean_dec_ref(x_3);
x_24 = lean_apply_1(x_2, x_23);
return x_24;
}
case 3:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_2);
x_25 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_25);
lean_dec_ref(x_3);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_array_get_size(x_25);
x_28 = lean_box(0);
x_29 = lean_nat_dec_lt(x_26, x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec_ref(x_25);
lean_dec_ref(x_7);
lean_inc(x_6);
lean_dec_ref(x_1);
x_30 = lean_apply_2(x_6, lean_box(0), x_28);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_27, x_27);
if (x_31 == 0)
{
if (x_29 == 0)
{
lean_object* x_32; 
lean_dec_ref(x_25);
lean_dec_ref(x_7);
lean_inc(x_6);
lean_dec_ref(x_1);
x_32 = lean_apply_2(x_6, lean_box(0), x_28);
return x_32;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_27);
x_35 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_7, x_25, x_33, x_34, x_28);
return x_35;
}
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; 
x_36 = 0;
x_37 = lean_usize_of_nat(x_27);
x_38 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_7, x_25, x_36, x_37, x_28);
return x_38;
}
}
}
case 4:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc(x_6);
lean_inc(x_5);
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_40);
lean_dec_ref(x_3);
x_41 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3), 5, 4);
lean_closure_set(x_41, 0, x_40);
lean_closure_set(x_41, 1, x_6);
lean_closure_set(x_41, 2, x_1);
lean_closure_set(x_41, 3, x_7);
x_42 = lean_apply_1(x_2, x_39);
x_43 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_42, x_41);
return x_43;
}
case 5:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_2);
x_44 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_44);
lean_dec_ref(x_3);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_array_get_size(x_44);
x_47 = lean_box(0);
x_48 = lean_nat_dec_lt(x_45, x_46);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec_ref(x_44);
lean_dec_ref(x_7);
lean_inc(x_6);
lean_dec_ref(x_1);
x_49 = lean_apply_2(x_6, lean_box(0), x_47);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_46, x_46);
if (x_50 == 0)
{
if (x_48 == 0)
{
lean_object* x_51; 
lean_dec_ref(x_44);
lean_dec_ref(x_7);
lean_inc(x_6);
lean_dec_ref(x_1);
x_51 = lean_apply_2(x_6, lean_box(0), x_47);
return x_51;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_46);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_7, x_44, x_52, x_53, x_47);
return x_54;
}
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; 
x_55 = 0;
x_56 = lean_usize_of_nat(x_46);
x_57 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_7, x_44, x_55, x_56, x_47);
return x_57;
}
}
}
case 6:
{
lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_58 = lean_ctor_get(x_3, 1);
lean_inc(x_58);
lean_dec_ref(x_3);
x_59 = lean_apply_1(x_2, x_58);
return x_59;
}
case 7:
{
lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_60 = lean_ctor_get(x_3, 1);
lean_inc(x_60);
lean_dec_ref(x_3);
x_61 = lean_apply_1(x_2, x_60);
return x_61;
}
case 8:
{
lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_62 = lean_ctor_get(x_3, 2);
lean_inc(x_62);
lean_dec_ref(x_3);
x_63 = lean_apply_1(x_2, x_62);
return x_63;
}
case 9:
{
lean_object* x_64; 
lean_dec(x_2);
x_64 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_64);
lean_dec_ref(x_3);
x_8 = x_64;
goto block_22;
}
case 10:
{
lean_object* x_65; 
lean_dec(x_2);
x_65 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_3);
x_8 = x_65;
goto block_22;
}
case 11:
{
lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_66 = lean_ctor_get(x_3, 1);
lean_inc(x_66);
lean_dec_ref(x_3);
x_67 = lean_apply_1(x_2, x_66);
return x_67;
}
case 12:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_inc(x_6);
lean_inc(x_5);
x_68 = lean_ctor_get(x_3, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_69);
lean_dec_ref(x_3);
x_70 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3), 5, 4);
lean_closure_set(x_70, 0, x_69);
lean_closure_set(x_70, 1, x_6);
lean_closure_set(x_70, 2, x_1);
lean_closure_set(x_70, 3, x_7);
x_71 = lean_apply_1(x_2, x_68);
x_72 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_71, x_70);
return x_72;
}
case 13:
{
lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_73 = lean_ctor_get(x_3, 1);
lean_inc(x_73);
lean_dec_ref(x_3);
x_74 = lean_apply_1(x_2, x_73);
return x_74;
}
case 14:
{
lean_object* x_75; lean_object* x_76; 
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_75 = lean_ctor_get(x_3, 0);
lean_inc(x_75);
lean_dec_ref(x_3);
x_76 = lean_apply_1(x_2, x_75);
return x_76;
}
default: 
{
lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_7);
lean_inc(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_77 = lean_box(0);
x_78 = lean_apply_2(x_6, lean_box(0), x_77);
return x_78;
}
}
block_22:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_8);
x_11 = lean_box(0);
x_12 = lean_nat_dec_lt(x_9, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_inc(x_6);
lean_dec_ref(x_1);
x_13 = lean_apply_2(x_6, lean_box(0), x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_10, x_10);
if (x_14 == 0)
{
if (x_12 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_inc(x_6);
lean_dec_ref(x_1);
x_15 = lean_apply_2(x_6, lean_box(0), x_11);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_10);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_7, x_8, x_16, x_17, x_11);
return x_18;
}
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_10);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_7, x_8, x_19, x_20, x_11);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Compiler_LCNF_LetValue_forFVarM(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0___boxed), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarLetValue___closed__0));
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instTraverseFVarLetValue(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_5);
x_8 = lean_apply_2(x_4, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_3);
x_11 = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(x_1, x_4, x_5, x_6);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 3);
lean_inc(x_8);
x_9 = lean_box(x_1);
lean_inc(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1___boxed), 8, 7);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_4);
lean_closure_set(x_10, 5, x_8);
lean_closure_set(x_10, 6, x_6);
x_11 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(x_3, x_4, x_7);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_mapFVarM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l_Lean_Compiler_LCNF_LetDecl_mapFVarM(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
lean_dec_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_6);
x_8 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(x_1, x_2, x_5);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Compiler_LCNF_LetDecl_forFVarM(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0___boxed), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___closed__0));
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_7);
x_8 = lean_box(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(x_3, x_4, x_7);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_mapFVarM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l_Lean_Compiler_LCNF_Param_mapFVarM(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Compiler_LCNF_Param_forFVarM(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0___boxed), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarParam___closed__0));
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instTraverseFVarParam(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = lean_ptr_addr(x_4);
x_13 = lean_ptr_addr(x_6);
x_14 = lean_usize_dec_eq(x_12, x_13);
if (x_14 == 0)
{
x_7 = x_14;
goto block_11;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = lean_ptr_addr(x_5);
x_16 = lean_ptr_addr(x_1);
x_17 = lean_usize_dec_eq(x_15, x_16);
x_7 = x_17;
goto block_11;
}
block_11:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_10 = lean_apply_2(x_2, lean_box(0), x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_25; size_t x_26; uint8_t x_27; 
x_25 = lean_ptr_addr(x_8);
x_26 = lean_ptr_addr(x_1);
x_27 = lean_usize_dec_eq(x_25, x_26);
if (x_27 == 0)
{
x_10 = x_27;
goto block_24;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_eq(x_2, x_2);
x_10 = x_28;
goto block_24;
}
block_24:
{
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_7);
x_11 = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_3);
lean_ctor_set(x_11, 3, x_9);
x_12 = lean_apply_2(x_4, lean_box(0), x_11);
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ptr_addr(x_5);
x_14 = lean_ptr_addr(x_3);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_7);
x_16 = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_3);
lean_ctor_set(x_16, 3, x_9);
x_17 = lean_apply_2(x_4, lean_box(0), x_16);
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = lean_ptr_addr(x_6);
x_19 = lean_ptr_addr(x_9);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_7);
x_21 = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_3);
lean_ctor_set(x_21, 3, x_9);
x_22 = lean_apply_2(x_4, lean_box(0), x_21);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec_ref(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_apply_2(x_4, lean_box(0), x_7);
return x_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed), 10, 5);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_8);
x_11 = lean_apply_2(x_5, lean_box(0), x_10);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_instBEqFVarId_beq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_3);
x_6 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_apply_2(x_2, lean_box(0), x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_36; size_t x_37; uint8_t x_38; 
x_36 = lean_ptr_addr(x_11);
x_37 = lean_ptr_addr(x_1);
x_38 = lean_usize_dec_eq(x_36, x_37);
if (x_38 == 0)
{
x_13 = x_38;
goto block_35;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_eq(x_2, x_2);
x_13 = x_39;
goto block_35;
}
block_35:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_10);
x_14 = lean_alloc_ctor(8, 6, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_4);
lean_ctor_set(x_14, 4, x_5);
lean_ctor_set(x_14, 5, x_12);
x_15 = lean_apply_2(x_6, lean_box(0), x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_eq(x_3, x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_10);
x_17 = lean_alloc_ctor(8, 6, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_3);
lean_ctor_set(x_17, 3, x_4);
lean_ctor_set(x_17, 4, x_5);
lean_ctor_set(x_17, 5, x_12);
x_18 = lean_apply_2(x_6, lean_box(0), x_17);
return x_18;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_ptr_addr(x_7);
x_20 = lean_ptr_addr(x_4);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_10);
x_22 = lean_alloc_ctor(8, 6, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_22, 3, x_4);
lean_ctor_set(x_22, 4, x_5);
lean_ctor_set(x_22, 5, x_12);
x_23 = lean_apply_2(x_6, lean_box(0), x_22);
return x_23;
}
else
{
size_t x_24; size_t x_25; uint8_t x_26; 
x_24 = lean_ptr_addr(x_8);
x_25 = lean_ptr_addr(x_5);
x_26 = lean_usize_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_10);
x_27 = lean_alloc_ctor(8, 6, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 2, x_3);
lean_ctor_set(x_27, 3, x_4);
lean_ctor_set(x_27, 4, x_5);
lean_ctor_set(x_27, 5, x_12);
x_28 = lean_apply_2(x_6, lean_box(0), x_27);
return x_28;
}
else
{
size_t x_29; size_t x_30; uint8_t x_31; 
x_29 = lean_ptr_addr(x_9);
x_30 = lean_ptr_addr(x_12);
x_31 = lean_usize_dec_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_10);
x_32 = lean_alloc_ctor(8, 6, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_2);
lean_ctor_set(x_32, 2, x_3);
lean_ctor_set(x_32, 3, x_4);
lean_ctor_set(x_32, 4, x_5);
lean_ctor_set(x_32, 5, x_12);
x_33 = lean_apply_2(x_6, lean_box(0), x_32);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec_ref(x_12);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_apply_2(x_6, lean_box(0), x_10);
return x_34;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_14; size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = lean_ptr_addr(x_7);
x_19 = lean_ptr_addr(x_9);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
x_14 = x_20;
goto block_17;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = lean_ptr_addr(x_8);
x_22 = lean_ptr_addr(x_2);
x_23 = lean_usize_dec_eq(x_21, x_22);
x_14 = x_23;
goto block_17;
}
block_13:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_10, 2, x_3);
lean_ctor_set(x_10, 3, x_9);
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_apply_2(x_4, lean_box(0), x_11);
return x_12;
}
block_17:
{
if (x_14 == 0)
{
lean_dec_ref(x_6);
goto block_13;
}
else
{
uint8_t x_15; 
x_15 = l_Lean_instBEqFVarId_beq(x_5, x_3);
if (x_15 == 0)
{
lean_dec_ref(x_6);
goto block_13;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_9);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_16 = lean_apply_2(x_4, lean_box(0), x_6);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
lean_inc_ref(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed), 9, 8);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_5);
lean_closure_set(x_12, 6, x_6);
lean_closure_set(x_12, 7, x_7);
x_13 = lean_array_size(x_6);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_8, x_9, x_13, x_14, x_6);
x_16 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_15, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_9);
lean_inc(x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13), 11, 10);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_5);
lean_closure_set(x_12, 6, x_6);
lean_closure_set(x_12, 7, x_7);
lean_closure_set(x_12, 8, x_8);
lean_closure_set(x_12, 9, x_9);
x_13 = lean_apply_1(x_10, x_3);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_13, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_12; 
x_12 = l_Lean_instBEqFVarId_beq(x_4, x_1);
if (x_12 == 0)
{
x_7 = x_12;
goto block_11;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ptr_addr(x_5);
x_14 = lean_ptr_addr(x_6);
x_15 = lean_usize_dec_eq(x_13, x_14);
x_7 = x_15;
goto block_11;
}
block_11:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_3);
x_8 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec_ref(x_6);
lean_dec(x_1);
x_10 = lean_apply_2(x_2, lean_box(0), x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
lean_inc_ref(x_4);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed), 6, 5);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
x_12 = lean_box(x_5);
lean_inc_ref(x_7);
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Arg_mapFVarM___boxed), 6, 5);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_8);
x_14 = lean_array_size(x_4);
x_15 = 0;
x_16 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_7, x_13, x_14, x_15, x_4);
x_17 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_16, x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
x_12 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = lean_ptr_addr(x_4);
x_13 = lean_ptr_addr(x_6);
x_14 = lean_usize_dec_eq(x_12, x_13);
if (x_14 == 0)
{
x_7 = x_14;
goto block_11;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = lean_ptr_addr(x_5);
x_16 = lean_ptr_addr(x_1);
x_17 = lean_usize_dec_eq(x_15, x_16);
x_7 = x_17;
goto block_11;
}
block_11:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_3);
x_8 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_10 = lean_apply_2(x_2, lean_box(0), x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = lean_ptr_addr(x_4);
x_13 = lean_ptr_addr(x_6);
x_14 = lean_usize_dec_eq(x_12, x_13);
if (x_14 == 0)
{
x_7 = x_14;
goto block_11;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = lean_ptr_addr(x_5);
x_16 = lean_ptr_addr(x_1);
x_17 = lean_usize_dec_eq(x_15, x_16);
x_7 = x_17;
goto block_11;
}
block_11:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_3);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_10 = lean_apply_2(x_2, lean_box(0), x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; 
x_5 = lean_ptr_addr(x_1);
x_6 = lean_ptr_addr(x_4);
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_3);
x_8 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_8, 0, x_4);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec_ref(x_4);
x_10 = lean_apply_2(x_2, lean_box(0), x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
x_12 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(x_5, x_6, x_7, x_8, x_3);
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
x_12 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed), 6, 5);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
x_12 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(x_5, x_6, x_7, x_8, x_3);
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
x_12 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_box(x_1);
lean_inc(x_5);
lean_inc(x_4);
x_12 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed), 8, 7);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_5);
lean_closure_set(x_12, 6, x_6);
x_13 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(x_1, x_4, x_7, x_8, x_9);
x_14 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_13, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_box(x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_4);
x_12 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed), 10, 9);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_5);
lean_closure_set(x_12, 6, x_6);
lean_closure_set(x_12, 7, x_7);
lean_closure_set(x_12, 8, x_8);
x_13 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(x_6, x_7, x_9);
x_14 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_13, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed), 6, 5);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
x_12 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(x_5, x_6, x_7, x_8, x_3);
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
x_12 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc_ref(x_5);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed), 9, 8);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_13);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_4);
lean_closure_set(x_14, 5, x_5);
lean_closure_set(x_14, 6, x_6);
lean_closure_set(x_14, 7, x_7);
x_15 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(x_8, x_9, x_10, x_11, x_5);
x_16 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_15, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_8);
x_15 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_box(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed), 13, 12);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_4);
lean_closure_set(x_14, 5, x_5);
lean_closure_set(x_14, 6, x_6);
lean_closure_set(x_14, 7, x_13);
lean_closure_set(x_14, 8, x_8);
lean_closure_set(x_14, 9, x_9);
lean_closure_set(x_14, 10, x_10);
lean_closure_set(x_14, 11, x_11);
x_15 = lean_apply_1(x_10, x_3);
x_16 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_15, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
x_14 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc_ref(x_8);
x_17 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed), 12, 11);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_4);
lean_closure_set(x_17, 4, x_16);
lean_closure_set(x_17, 5, x_5);
lean_closure_set(x_17, 6, x_6);
lean_closure_set(x_17, 7, x_7);
lean_closure_set(x_17, 8, x_8);
lean_closure_set(x_17, 9, x_9);
lean_closure_set(x_17, 10, x_10);
x_18 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(x_11, x_12, x_13, x_14, x_8);
x_19 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_18, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_11);
x_18 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_box(x_10);
lean_inc(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc_ref(x_6);
x_17 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed), 16, 15);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_15);
lean_closure_set(x_17, 4, x_4);
lean_closure_set(x_17, 5, x_5);
lean_closure_set(x_17, 6, x_6);
lean_closure_set(x_17, 7, x_7);
lean_closure_set(x_17, 8, x_8);
lean_closure_set(x_17, 9, x_9);
lean_closure_set(x_17, 10, x_16);
lean_closure_set(x_17, 11, x_11);
lean_closure_set(x_17, 12, x_12);
lean_closure_set(x_17, 13, x_13);
lean_closure_set(x_17, 14, x_14);
x_18 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(x_12, x_13, x_6);
x_19 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_18, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_10);
x_17 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_box(x_9);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_4);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed), 15, 14);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_4);
lean_closure_set(x_16, 5, x_5);
lean_closure_set(x_16, 6, x_6);
lean_closure_set(x_16, 7, x_7);
lean_closure_set(x_16, 8, x_8);
lean_closure_set(x_16, 9, x_15);
lean_closure_set(x_16, 10, x_10);
lean_closure_set(x_16, 11, x_11);
lean_closure_set(x_16, 12, x_12);
lean_closure_set(x_16, 13, x_13);
x_17 = lean_apply_1(x_12, x_4);
x_18 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_17, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_9);
x_16 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_10);
x_11 = lean_box(x_1);
lean_inc(x_7);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_9);
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed), 10, 9);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_9);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_2);
lean_closure_set(x_12, 6, x_3);
lean_closure_set(x_12, 7, x_4);
lean_closure_set(x_12, 8, x_7);
x_13 = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(x_1, x_2, x_3, x_4, x_9);
x_14 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_13, x_12);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_16, 3);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_22);
x_23 = lean_box(x_1);
lean_inc(x_17);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_16);
lean_inc(x_18);
x_24 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed), 10, 9);
lean_closure_set(x_24, 0, x_18);
lean_closure_set(x_24, 1, x_5);
lean_closure_set(x_24, 2, x_19);
lean_closure_set(x_24, 3, x_16);
lean_closure_set(x_24, 4, x_23);
lean_closure_set(x_24, 5, x_2);
lean_closure_set(x_24, 6, x_3);
lean_closure_set(x_24, 7, x_4);
lean_closure_set(x_24, 8, x_17);
x_25 = lean_box(x_1);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_17);
lean_inc(x_2);
x_26 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_16);
lean_closure_set(x_26, 2, x_2);
lean_closure_set(x_26, 3, x_17);
lean_closure_set(x_26, 4, x_24);
lean_closure_set(x_26, 5, x_3);
lean_closure_set(x_26, 6, x_4);
lean_closure_set(x_26, 7, x_22);
lean_closure_set(x_26, 8, x_21);
x_27 = lean_box(x_1);
lean_inc_ref(x_3);
x_28 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(x_28, 0, lean_box(0));
lean_closure_set(x_28, 1, x_27);
lean_closure_set(x_28, 2, x_2);
lean_closure_set(x_28, 3, x_3);
lean_closure_set(x_28, 4, x_4);
x_29 = lean_array_size(x_20);
x_30 = 0;
x_31 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_3, x_28, x_29, x_30, x_20);
x_32 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_31, x_26);
return x_32;
}
case 2:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; 
x_33 = lean_ctor_get(x_3, 0);
x_34 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_34, 2);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_34, 3);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_34, 4);
lean_inc_ref(x_40);
x_41 = lean_box(x_1);
lean_inc(x_35);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_34);
lean_inc(x_36);
x_42 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed), 10, 9);
lean_closure_set(x_42, 0, x_36);
lean_closure_set(x_42, 1, x_5);
lean_closure_set(x_42, 2, x_37);
lean_closure_set(x_42, 3, x_34);
lean_closure_set(x_42, 4, x_41);
lean_closure_set(x_42, 5, x_2);
lean_closure_set(x_42, 6, x_3);
lean_closure_set(x_42, 7, x_4);
lean_closure_set(x_42, 8, x_35);
x_43 = lean_box(x_1);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_35);
lean_inc(x_2);
x_44 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed), 10, 9);
lean_closure_set(x_44, 0, x_43);
lean_closure_set(x_44, 1, x_34);
lean_closure_set(x_44, 2, x_2);
lean_closure_set(x_44, 3, x_35);
lean_closure_set(x_44, 4, x_42);
lean_closure_set(x_44, 5, x_3);
lean_closure_set(x_44, 6, x_4);
lean_closure_set(x_44, 7, x_40);
lean_closure_set(x_44, 8, x_39);
x_45 = lean_box(x_1);
lean_inc_ref(x_3);
x_46 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(x_46, 0, lean_box(0));
lean_closure_set(x_46, 1, x_45);
lean_closure_set(x_46, 2, x_2);
lean_closure_set(x_46, 3, x_3);
lean_closure_set(x_46, 4, x_4);
x_47 = lean_array_size(x_38);
x_48 = 0;
x_49 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_3, x_46, x_47, x_48, x_38);
x_50 = lean_apply_4(x_35, lean_box(0), lean_box(0), x_49, x_44);
return x_50;
}
case 3:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_3, 0);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_5, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_55);
x_56 = lean_box(x_1);
lean_inc(x_52);
lean_inc(x_4);
lean_inc(x_54);
x_57 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed), 10, 9);
lean_closure_set(x_57, 0, x_53);
lean_closure_set(x_57, 1, x_5);
lean_closure_set(x_57, 2, x_54);
lean_closure_set(x_57, 3, x_55);
lean_closure_set(x_57, 4, x_56);
lean_closure_set(x_57, 5, x_2);
lean_closure_set(x_57, 6, x_3);
lean_closure_set(x_57, 7, x_4);
lean_closure_set(x_57, 8, x_52);
x_58 = lean_apply_1(x_4, x_54);
x_59 = lean_apply_4(x_52, lean_box(0), lean_box(0), x_58, x_57);
return x_59;
}
case 4:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = lean_ctor_get(x_3, 0);
x_61 = lean_ctor_get(x_5, 0);
x_62 = lean_ctor_get(x_3, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 1);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_61, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 3);
lean_inc_ref(x_67);
x_68 = lean_box(x_1);
lean_inc(x_4);
lean_inc_ref(x_3);
x_69 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed), 5, 4);
lean_closure_set(x_69, 0, x_68);
lean_closure_set(x_69, 1, x_2);
lean_closure_set(x_69, 2, x_3);
lean_closure_set(x_69, 3, x_4);
lean_inc(x_4);
lean_inc(x_62);
lean_inc_ref(x_3);
lean_inc_ref(x_65);
lean_inc(x_63);
x_70 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14), 11, 10);
lean_closure_set(x_70, 0, x_64);
lean_closure_set(x_70, 1, x_63);
lean_closure_set(x_70, 2, x_66);
lean_closure_set(x_70, 3, x_5);
lean_closure_set(x_70, 4, x_67);
lean_closure_set(x_70, 5, x_65);
lean_closure_set(x_70, 6, x_3);
lean_closure_set(x_70, 7, x_69);
lean_closure_set(x_70, 8, x_62);
lean_closure_set(x_70, 9, x_4);
x_71 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(x_3, x_4, x_65);
x_72 = lean_apply_4(x_62, lean_box(0), lean_box(0), x_71, x_70);
return x_72;
}
case 5:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_73);
lean_dec(x_2);
x_74 = lean_ctor_get(x_3, 1);
lean_inc(x_74);
lean_dec_ref(x_3);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = lean_ctor_get(x_5, 0);
lean_inc(x_76);
lean_inc(x_76);
x_77 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed), 4, 3);
lean_closure_set(x_77, 0, x_76);
lean_closure_set(x_77, 1, x_75);
lean_closure_set(x_77, 2, x_5);
x_78 = lean_apply_1(x_4, x_76);
x_79 = lean_apply_4(x_74, lean_box(0), lean_box(0), x_78, x_77);
return x_79;
}
case 6:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_80 = lean_ctor_get(x_3, 0);
lean_dec(x_2);
x_81 = lean_ctor_get(x_3, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
x_83 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_83);
lean_inc(x_82);
lean_inc_ref(x_83);
x_84 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed), 4, 3);
lean_closure_set(x_84, 0, x_83);
lean_closure_set(x_84, 1, x_82);
lean_closure_set(x_84, 2, x_5);
x_85 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(x_3, x_4, x_83);
x_86 = lean_apply_4(x_81, lean_box(0), lean_box(0), x_85, x_84);
return x_86;
}
case 7:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_87 = lean_ctor_get(x_3, 0);
x_88 = lean_ctor_get(x_3, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_5, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_5, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_5, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_93);
x_94 = lean_box(x_1);
lean_inc(x_88);
lean_inc(x_4);
lean_inc(x_90);
x_95 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed), 12, 11);
lean_closure_set(x_95, 0, x_91);
lean_closure_set(x_95, 1, x_89);
lean_closure_set(x_95, 2, x_92);
lean_closure_set(x_95, 3, x_93);
lean_closure_set(x_95, 4, x_5);
lean_closure_set(x_95, 5, x_90);
lean_closure_set(x_95, 6, x_94);
lean_closure_set(x_95, 7, x_2);
lean_closure_set(x_95, 8, x_3);
lean_closure_set(x_95, 9, x_4);
lean_closure_set(x_95, 10, x_88);
x_96 = lean_apply_1(x_4, x_90);
x_97 = lean_apply_4(x_88, lean_box(0), lean_box(0), x_96, x_95);
return x_97;
}
default: 
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_98 = lean_ctor_get(x_3, 0);
x_99 = lean_ctor_get(x_3, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_5, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_5, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_5, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_5, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_5, 4);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_5, 5);
lean_inc_ref(x_106);
x_107 = lean_box(x_1);
lean_inc(x_99);
lean_inc(x_4);
lean_inc(x_101);
x_108 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed), 14, 13);
lean_closure_set(x_108, 0, x_102);
lean_closure_set(x_108, 1, x_103);
lean_closure_set(x_108, 2, x_100);
lean_closure_set(x_108, 3, x_104);
lean_closure_set(x_108, 4, x_105);
lean_closure_set(x_108, 5, x_106);
lean_closure_set(x_108, 6, x_5);
lean_closure_set(x_108, 7, x_101);
lean_closure_set(x_108, 8, x_107);
lean_closure_set(x_108, 9, x_2);
lean_closure_set(x_108, 10, x_3);
lean_closure_set(x_108, 11, x_4);
lean_closure_set(x_108, 12, x_99);
x_109 = lean_apply_1(x_4, x_101);
x_110 = lean_apply_4(x_99, lean_box(0), lean_box(0), x_109, x_108);
return x_110;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(x_1);
lean_inc_ref(x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed), 5, 4);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_4);
x_8 = l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg(x_3, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_mapFVarM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l_Lean_Compiler_LCNF_Code_mapFVarM(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(x_1, x_2, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_1);
x_8 = lean_box(0);
x_9 = lean_nat_dec_lt(x_6, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_apply_2(x_10, lean_box(0), x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_7, x_7);
if (x_12 == 0)
{
if (x_9 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = lean_apply_2(x_13, lean_box(0), x_8);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
lean_dec_ref(x_2);
x_15 = 0;
x_16 = lean_usize_of_nat(x_7);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_3, x_4, x_1, x_15, x_16, x_8);
return x_17;
}
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
lean_dec_ref(x_2);
x_18 = 0;
x_19 = lean_usize_of_nat(x_7);
x_20 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_3, x_4, x_1, x_18, x_19, x_8);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_1(x_1, x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(x_1, x_2, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_1(x_1, x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_1);
x_8 = lean_box(0);
x_9 = lean_nat_dec_lt(x_6, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_apply_2(x_10, lean_box(0), x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_7, x_7);
if (x_12 == 0)
{
if (x_9 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = lean_apply_2(x_13, lean_box(0), x_8);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
lean_dec_ref(x_2);
x_15 = 0;
x_16 = lean_usize_of_nat(x_7);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_3, x_4, x_1, x_15, x_16, x_8);
return x_17;
}
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
lean_dec_ref(x_2);
x_18 = 0;
x_19 = lean_usize_of_nat(x_7);
x_20 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_3, x_4, x_1, x_18, x_19, x_8);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Compiler_LCNF_Alt_forCodeM___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(x_1, x_2, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_6);
x_8 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(x_1, x_2, x_5);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
case 3:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8), 4, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4), 5, 4);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_10);
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, x_14);
x_16 = lean_apply_1(x_2, x_12);
x_17 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_16, x_15);
return x_17;
}
case 4:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_3);
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_18, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 3);
lean_inc_ref(x_23);
lean_dec_ref(x_18);
lean_inc(x_2);
lean_inc_ref(x_1);
x_24 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5), 4, 2);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_inc_ref(x_1);
lean_inc_ref(x_19);
x_25 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6), 5, 4);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_19);
lean_closure_set(x_25, 2, x_1);
lean_closure_set(x_25, 3, x_24);
lean_inc(x_20);
lean_inc(x_2);
x_26 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7), 5, 4);
lean_closure_set(x_26, 0, x_2);
lean_closure_set(x_26, 1, x_22);
lean_closure_set(x_26, 2, x_20);
lean_closure_set(x_26, 3, x_25);
x_27 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(x_1, x_2, x_21);
x_28 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_27, x_26);
return x_28;
}
case 5:
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_1);
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
lean_dec_ref(x_3);
x_30 = lean_apply_1(x_2, x_29);
return x_30;
}
case 6:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_31);
lean_dec_ref(x_3);
x_32 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(x_1, x_2, x_31);
return x_32;
}
case 7:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_36);
lean_dec_ref(x_3);
lean_inc(x_2);
x_37 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(x_37, 0, x_1);
lean_closure_set(x_37, 1, x_2);
lean_closure_set(x_37, 2, x_36);
lean_inc(x_33);
lean_inc(x_2);
x_38 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10), 5, 4);
lean_closure_set(x_38, 0, x_2);
lean_closure_set(x_38, 1, x_35);
lean_closure_set(x_38, 2, x_33);
lean_closure_set(x_38, 3, x_37);
x_39 = lean_apply_1(x_2, x_34);
x_40 = lean_apply_4(x_33, lean_box(0), lean_box(0), x_39, x_38);
return x_40;
}
case 8:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_3, 5);
lean_inc_ref(x_45);
lean_dec_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_46 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(x_46, 0, x_1);
lean_closure_set(x_46, 1, x_2);
lean_closure_set(x_46, 2, x_45);
lean_inc(x_41);
lean_inc(x_2);
x_47 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11), 6, 5);
lean_closure_set(x_47, 0, x_1);
lean_closure_set(x_47, 1, x_2);
lean_closure_set(x_47, 2, x_44);
lean_closure_set(x_47, 3, x_41);
lean_closure_set(x_47, 4, x_46);
lean_inc(x_41);
lean_inc(x_2);
x_48 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10), 5, 4);
lean_closure_set(x_48, 0, x_2);
lean_closure_set(x_48, 1, x_43);
lean_closure_set(x_48, 2, x_41);
lean_closure_set(x_48, 3, x_47);
x_49 = lean_apply_1(x_2, x_42);
x_50 = lean_apply_4(x_41, lean_box(0), lean_box(0), x_49, x_48);
return x_50;
}
default: 
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_51 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_54);
lean_dec_ref(x_3);
x_55 = lean_ctor_get(x_51, 2);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_51, 3);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_51, 4);
lean_inc_ref(x_57);
lean_dec_ref(x_51);
lean_inc(x_2);
lean_inc_ref(x_1);
x_58 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(x_58, 0, x_1);
lean_closure_set(x_58, 1, x_2);
lean_closure_set(x_58, 2, x_54);
lean_inc(x_53);
lean_inc(x_2);
lean_inc_ref(x_1);
x_59 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2), 6, 5);
lean_closure_set(x_59, 0, x_1);
lean_closure_set(x_59, 1, x_2);
lean_closure_set(x_59, 2, x_57);
lean_closure_set(x_59, 3, x_53);
lean_closure_set(x_59, 4, x_58);
lean_inc(x_53);
lean_inc(x_2);
lean_inc_ref(x_1);
x_60 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1), 6, 5);
lean_closure_set(x_60, 0, x_1);
lean_closure_set(x_60, 1, x_2);
lean_closure_set(x_60, 2, x_56);
lean_closure_set(x_60, 3, x_53);
lean_closure_set(x_60, 4, x_59);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_array_get_size(x_55);
x_63 = lean_box(0);
x_64 = lean_nat_dec_lt(x_61, x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_55);
lean_inc_ref(x_52);
lean_dec(x_2);
lean_dec_ref(x_1);
x_65 = lean_ctor_get(x_52, 1);
lean_inc(x_65);
lean_dec_ref(x_52);
x_66 = lean_apply_2(x_65, lean_box(0), x_63);
x_67 = lean_apply_4(x_53, lean_box(0), lean_box(0), x_66, x_60);
return x_67;
}
else
{
lean_object* x_68; uint8_t x_69; 
lean_inc_ref(x_1);
x_68 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3), 4, 2);
lean_closure_set(x_68, 0, x_1);
lean_closure_set(x_68, 1, x_2);
x_69 = lean_nat_dec_le(x_62, x_62);
if (x_69 == 0)
{
if (x_64 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_68);
lean_dec_ref(x_55);
lean_inc_ref(x_52);
lean_dec_ref(x_1);
x_70 = lean_ctor_get(x_52, 1);
lean_inc(x_70);
lean_dec_ref(x_52);
x_71 = lean_apply_2(x_70, lean_box(0), x_63);
x_72 = lean_apply_4(x_53, lean_box(0), lean_box(0), x_71, x_60);
return x_72;
}
else
{
size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; 
x_73 = 0;
x_74 = lean_usize_of_nat(x_62);
x_75 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_68, x_55, x_73, x_74, x_63);
x_76 = lean_apply_4(x_53, lean_box(0), lean_box(0), x_75, x_60);
return x_76;
}
}
else
{
size_t x_77; size_t x_78; lean_object* x_79; lean_object* x_80; 
x_77 = 0;
x_78 = lean_usize_of_nat(x_62);
x_79 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_68, x_55, x_77, x_78, x_63);
x_80 = lean_apply_4(x_53, lean_box(0), lean_box(0), x_79, x_60);
return x_80;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Compiler_LCNF_Code_forFVarM(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0));
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCode___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instTraverseFVarCode(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed), 10, 5);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_6);
x_9 = lean_apply_2(x_5, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_box(x_1);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
x_12 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(x_1, x_4, x_5, x_6, x_7);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_box(x_1);
lean_inc(x_7);
lean_inc(x_5);
lean_inc_ref(x_4);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
lean_closure_set(x_11, 5, x_5);
lean_closure_set(x_11, 6, x_6);
lean_closure_set(x_11, 7, x_7);
x_12 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(x_4, x_5, x_8);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_5, 4);
lean_inc_ref(x_9);
x_10 = lean_box(x_1);
lean_inc(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed), 9, 8);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
lean_closure_set(x_11, 5, x_9);
lean_closure_set(x_11, 6, x_6);
lean_closure_set(x_11, 7, x_8);
x_12 = lean_box(x_1);
lean_inc_ref(x_3);
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_4);
x_14 = lean_array_size(x_7);
x_15 = 0;
x_16 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_3, x_13, x_14, x_15, x_7);
x_17 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_16, x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_mapFVarM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l_Lean_Compiler_LCNF_FunDecl_mapFVarM(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(x_1, x_2, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Param_forFVarM___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_8);
lean_dec_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0), 4, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_8);
lean_inc(x_5);
lean_inc(x_2);
lean_inc_ref(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1), 6, 5);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_7);
lean_closure_set(x_10, 3, x_5);
lean_closure_set(x_10, 4, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_6);
x_13 = lean_box(0);
x_14 = lean_nat_dec_lt(x_11, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_6);
lean_inc_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec_ref(x_4);
x_16 = lean_apply_2(x_15, lean_box(0), x_13);
x_17 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_16, x_10);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_inc_ref(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2), 4, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
x_19 = lean_nat_dec_le(x_12, x_12);
if (x_19 == 0)
{
if (x_14 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_18);
lean_dec_ref(x_6);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_dec_ref(x_4);
x_21 = lean_apply_2(x_20, lean_box(0), x_13);
x_22 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_21, x_10);
return x_22;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_12);
x_25 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_18, x_6, x_23, x_24, x_13);
x_26 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_25, x_10);
return x_26;
}
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_12);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_18, x_6, x_27, x_28, x_13);
x_30 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_29, x_10);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Compiler_LCNF_FunDecl_forFVarM(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0));
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_apply_2(x_3, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3), 4, 3);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_2);
x_8 = lean_apply_1(x_3, x_4);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_6);
x_8 = lean_apply_2(x_5, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5), 6, 5);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_9);
lean_closure_set(x_10, 4, x_4);
x_11 = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(x_5, x_6, x_7);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_7);
lean_inc(x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6), 9, 8);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_4);
lean_closure_set(x_10, 5, x_5);
lean_closure_set(x_10, 6, x_6);
lean_closure_set(x_10, 7, x_7);
x_11 = lean_apply_1(x_5, x_8);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_6);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0), 2, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(x_1, x_3, x_4, x_5, x_10);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_6);
lean_inc(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1), 2, 1);
lean_closure_set(x_18, 0, x_16);
x_19 = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(x_1, x_3, x_4, x_5, x_17);
x_20 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_19, x_18);
return x_20;
}
case 2:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_24);
lean_dec_ref(x_6);
lean_inc(x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2), 2, 1);
lean_closure_set(x_25, 0, x_23);
x_26 = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(x_1, x_3, x_4, x_5, x_24);
x_27 = lean_apply_4(x_22, lean_box(0), lean_box(0), x_26, x_25);
return x_27;
}
case 3:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_28);
lean_dec(x_3);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_dec_ref(x_4);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_ctor_get(x_6, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_6, 2);
lean_inc(x_33);
lean_dec_ref(x_6);
lean_inc(x_29);
lean_inc(x_5);
x_34 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4), 6, 5);
lean_closure_set(x_34, 0, x_32);
lean_closure_set(x_34, 1, x_30);
lean_closure_set(x_34, 2, x_5);
lean_closure_set(x_34, 3, x_33);
lean_closure_set(x_34, 4, x_29);
x_35 = lean_apply_1(x_5, x_31);
x_36 = lean_apply_4(x_29, lean_box(0), lean_box(0), x_35, x_34);
return x_36;
}
default: 
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_4, 0);
lean_dec(x_3);
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_6, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_6, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_6, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_6, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_6, 4);
lean_inc_ref(x_44);
lean_dec_ref(x_6);
lean_inc(x_38);
lean_inc(x_5);
x_45 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7), 9, 8);
lean_closure_set(x_45, 0, x_41);
lean_closure_set(x_45, 1, x_42);
lean_closure_set(x_45, 2, x_39);
lean_closure_set(x_45, 3, x_4);
lean_closure_set(x_45, 4, x_5);
lean_closure_set(x_45, 5, x_44);
lean_closure_set(x_45, 6, x_38);
lean_closure_set(x_45, 7, x_43);
x_46 = lean_apply_1(x_5, x_40);
x_47 = lean_apply_4(x_38, lean_box(0), lean_box(0), x_46, x_45);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_1(x_1, x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(x_2, x_3, x_5);
return x_6;
}
case 3:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
lean_dec_ref(x_4);
lean_inc(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9), 3, 2);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_apply_1(x_3, x_8);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_10);
return x_12;
}
case 4:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 4);
lean_inc_ref(x_16);
lean_dec_ref(x_4);
lean_inc(x_3);
x_17 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10), 4, 3);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_16);
lean_inc(x_13);
lean_inc(x_3);
x_18 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11), 5, 4);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_15);
lean_closure_set(x_18, 2, x_13);
lean_closure_set(x_18, 3, x_17);
x_19 = lean_apply_1(x_3, x_14);
x_20 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_19, x_18);
return x_20;
}
default: 
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_21);
lean_dec_ref(x_4);
x_22 = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(x_2, x_3, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8___boxed), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0));
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_apply_2(x_3, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0), 4, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_2);
x_11 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(x_3, x_4, x_5, x_6, x_7);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_12);
lean_dec_ref(x_6);
x_13 = lean_box(x_1);
lean_inc(x_8);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed), 9, 8);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_13);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_4);
lean_closure_set(x_14, 5, x_5);
lean_closure_set(x_14, 6, x_12);
lean_closure_set(x_14, 7, x_8);
x_15 = lean_box(x_1);
lean_inc_ref(x_4);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Param_mapFVarM___boxed), 6, 5);
lean_closure_set(x_16, 0, lean_box(0));
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_5);
x_17 = lean_array_size(x_11);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_4, x_16, x_17, x_18, x_11);
x_20 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_19, x_14);
return x_20;
}
case 1:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_25);
lean_dec_ref(x_6);
lean_inc(x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2), 3, 2);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_23);
x_27 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(x_1, x_3, x_4, x_5, x_25);
x_28 = lean_apply_4(x_22, lean_box(0), lean_box(0), x_27, x_26);
return x_28;
}
default: 
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
x_32 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_32);
lean_dec_ref(x_6);
lean_inc(x_31);
x_33 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3), 2, 1);
lean_closure_set(x_33, 0, x_31);
x_34 = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(x_1, x_3, x_4, x_5, x_32);
x_35 = lean_apply_4(x_30, lean_box(0), lean_box(0), x_34, x_33);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_8);
lean_dec_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5), 4, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_7);
x_12 = lean_box(0);
x_13 = lean_nat_dec_lt(x_10, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_7);
lean_inc_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec_ref(x_5);
x_15 = lean_apply_2(x_14, lean_box(0), x_12);
x_16 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_15, x_9);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_2);
x_17 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2), 4, 2);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_3);
x_18 = lean_nat_dec_le(x_11, x_11);
if (x_18 == 0)
{
if (x_13 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_17);
lean_dec_ref(x_7);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec_ref(x_5);
x_20 = lean_apply_2(x_19, lean_box(0), x_12);
x_21 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_20, x_9);
return x_21;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_11);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_2, x_17, x_7, x_22, x_23, x_12);
x_25 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_24, x_9);
return x_25;
}
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_11);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_2, x_17, x_7, x_26, x_27, x_12);
x_29 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_28, x_9);
return x_29;
}
}
}
case 1:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_4);
x_31 = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(x_2, x_3, x_30);
return x_31;
}
default: 
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_32);
lean_dec_ref(x_4);
x_33 = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(x_2, x_3, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0));
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instTraverseFVarAlt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instTraverseFVarAlt(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_unbox(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = ((lean_object*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0));
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_apply_2(x_1, lean_box(0), x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_apply_1(x_2, x_3);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_6);
lean_inc(x_5);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_9);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
else
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
lean_inc_ref(x_1);
x_10 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_10, 0, x_1);
lean_inc_ref(x_1);
x_11 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc_ref(x_1);
x_12 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_12, 0, x_1);
lean_inc_ref(x_1);
x_13 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_13, 0, x_1);
lean_inc_ref(x_1);
x_14 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_14, 0, x_1);
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_2, 0, x_10);
lean_inc_ref(x_1);
x_15 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_15, 0, lean_box(0));
lean_closure_set(x_15, 1, x_1);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set(x_16, 4, x_14);
lean_inc_ref(x_1);
x_17 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_17, 0, lean_box(0));
lean_closure_set(x_17, 1, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go), 4, 3);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_3);
x_21 = lean_apply_4(x_8, lean_box(0), x_18, x_20, x_4);
x_22 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_22, 0, x_19);
x_23 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec(x_2);
lean_inc_ref(x_1);
x_25 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_25, 0, x_1);
lean_inc_ref(x_1);
x_26 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_26, 0, x_1);
lean_inc_ref(x_1);
x_27 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_27, 0, x_1);
lean_inc_ref(x_1);
x_28 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_28, 0, x_1);
lean_inc_ref(x_1);
x_29 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_29, 0, x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_26);
lean_inc_ref(x_1);
x_31 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_31, 0, lean_box(0));
lean_closure_set(x_31, 1, x_1);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_28);
lean_ctor_set(x_32, 4, x_29);
lean_inc_ref(x_1);
x_33 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_33, 0, lean_box(0));
lean_closure_set(x_33, 1, x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
x_36 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go), 4, 3);
lean_closure_set(x_36, 0, lean_box(0));
lean_closure_set(x_36, 1, x_1);
lean_closure_set(x_36, 2, x_3);
x_37 = lean_apply_4(x_24, lean_box(0), x_34, x_36, x_4);
x_38 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_38, 0, x_35);
x_39 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_37, x_38);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVarM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_anyFVarM___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_unbox(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = ((lean_object*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0));
x_10 = lean_apply_2(x_1, lean_box(0), x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_apply_1(x_2, x_3);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_6);
lean_inc(x_5);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_9);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
else
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
lean_inc_ref(x_1);
x_10 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_10, 0, x_1);
lean_inc_ref(x_1);
x_11 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc_ref(x_1);
x_12 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_12, 0, x_1);
lean_inc_ref(x_1);
x_13 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_13, 0, x_1);
lean_inc_ref(x_1);
x_14 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_14, 0, x_1);
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_2, 0, x_10);
lean_inc_ref(x_1);
x_15 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_15, 0, lean_box(0));
lean_closure_set(x_15, 1, x_1);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set(x_16, 4, x_14);
lean_inc_ref(x_1);
x_17 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_17, 0, lean_box(0));
lean_closure_set(x_17, 1, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go), 4, 3);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_3);
x_21 = lean_apply_4(x_8, lean_box(0), x_18, x_20, x_4);
x_22 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_22, 0, x_19);
x_23 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec(x_2);
lean_inc_ref(x_1);
x_25 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_25, 0, x_1);
lean_inc_ref(x_1);
x_26 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_26, 0, x_1);
lean_inc_ref(x_1);
x_27 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_27, 0, x_1);
lean_inc_ref(x_1);
x_28 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_28, 0, x_1);
lean_inc_ref(x_1);
x_29 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_29, 0, x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_26);
lean_inc_ref(x_1);
x_31 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_31, 0, lean_box(0));
lean_closure_set(x_31, 1, x_1);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_28);
lean_ctor_set(x_32, 4, x_29);
lean_inc_ref(x_1);
x_33 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_33, 0, lean_box(0));
lean_closure_set(x_33, 1, x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
x_36 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go), 4, 3);
lean_closure_set(x_36, 0, lean_box(0));
lean_closure_set(x_36, 1, x_1);
lean_closure_set(x_36, 2, x_3);
x_37 = lean_apply_4(x_24, lean_box(0), x_34, x_36, x_4);
x_38 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_38, 0, x_35);
x_39 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_37, x_38);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_allFVarM___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_unbox(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9));
x_6 = l_Lean_Compiler_LCNF_anyFVarM___redArg(x_5, x_1, x_4, x_3);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_LCNF_anyFVar___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_anyFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Compiler_LCNF_anyFVar___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_Compiler_LCNF_anyFVar(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9));
x_6 = l_Lean_Compiler_LCNF_allFVarM___redArg(x_5, x_1, x_4, x_3);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_LCNF_allFVar___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Compiler_LCNF_allFVar___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_Compiler_LCNF_allFVar(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
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
l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3 = _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3);
l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
