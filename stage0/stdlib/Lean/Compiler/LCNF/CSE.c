// Lean compiler output
// Module: Lean.Compiler.LCNF.CSE
// Imports: public import Lean.Compiler.LCNF.ToExpr public import Lean.Compiler.LCNF.PassManager public import Lean.Compiler.NeverExtractAttr
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_hasNeverExtractAttribute(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDecl_toExpr(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedPass;
lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__5_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__6_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__7_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__8_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_liftIOCore___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__9_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__10_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__11_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__12_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__12_value),((lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__11_value)} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__13_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__13_value),((lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__10_value)} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__14_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__14_value),((lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__9_value)} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__15_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__15_value),((lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__8_value)} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__16_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__16_value),((lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__7_value)} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__17 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__17_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_get___boxed, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__17_value)} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__18 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__18_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_cse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_cse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_cse___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_cse___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_cse___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_cse___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cse"};
static const lean_object* l_Lean_Compiler_LCNF_cse___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_cse___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_cse___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_cse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 49, 41, 139, 179, 196, 98, 180)}};
static const lean_object* l_Lean_Compiler_LCNF_cse___lam__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_cse___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_cse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 157, 206, 101, 61, 42, 158, 65)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "CSE"};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 241, 162, 70, 52, 204, 58, 196)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(80, 145, 243, 57, 198, 247, 31, 201)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(41, 218, 202, 84, 172, 168, 56, 40)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(247, 149, 188, 74, 23, 157, 6, 80)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 84, 48, 37, 32, 47, 255, 126)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(15, 132, 28, 179, 158, 97, 118, 4)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(122, 189, 198, 10, 231, 174, 147, 87)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(155, 200, 81, 146, 37, 229, 50, 233)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(157, 172, 166, 12, 2, 139, 250, 210)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(104, 77, 241, 237, 129, 174, 13, 226)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 219, 168, 59, 126, 239, 35, 28)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)(((size_t)(527537415) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(88, 198, 142, 231, 46, 91, 164, 15)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 231, 117, 212, 69, 228, 211, 198)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 204, 244, 99, 77, 146, 130, 118)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(82, 70, 16, 107, 153, 37, 132, 83)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___lam__0(lean_object* v_____do__lift_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v_subst_8_; lean_object* v___x_9_; 
v_subst_8_ = lean_ctor_get(v_____do__lift_1_, 1);
lean_inc_ref(v_subst_8_);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v_subst_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___lam__0___boxed(lean_object* v_____do__lift_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___lam__0(v_____do__lift_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
lean_dec(v___y_13_);
lean_dec_ref(v___y_12_);
lean_dec(v___y_11_);
lean_dec_ref(v_____do__lift_10_);
return v_res_17_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__0(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_instMonadEIO(lean_box(0));
return v___x_18_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_obj_once(&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__0, &l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__0_once, _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__0);
v___x_20_ = l_StateRefT_x27_instMonad___redArg(v___x_19_);
return v___x_20_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse(void){
_start:
{
lean_object* v___x_49_; lean_object* v_toApplicative_50_; lean_object* v_toFunctor_51_; lean_object* v_toSeq_52_; lean_object* v_toSeqLeft_53_; lean_object* v_toSeqRight_54_; lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___x_59_; lean_object* v___f_60_; lean_object* v___f_61_; lean_object* v___f_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v_toApplicative_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_96_; 
v___x_49_ = lean_obj_once(&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1, &l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1_once, _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1);
v_toApplicative_50_ = lean_ctor_get(v___x_49_, 0);
v_toFunctor_51_ = lean_ctor_get(v_toApplicative_50_, 0);
v_toSeq_52_ = lean_ctor_get(v_toApplicative_50_, 2);
v_toSeqLeft_53_ = lean_ctor_get(v_toApplicative_50_, 3);
v_toSeqRight_54_ = lean_ctor_get(v_toApplicative_50_, 4);
v___f_55_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__2));
v___f_56_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__3));
lean_inc_ref_n(v_toFunctor_51_, 2);
v___f_57_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_57_, 0, v_toFunctor_51_);
v___f_58_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_58_, 0, v_toFunctor_51_);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v___f_57_);
lean_ctor_set(v___x_59_, 1, v___f_58_);
lean_inc(v_toSeqRight_54_);
v___f_60_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_60_, 0, v_toSeqRight_54_);
lean_inc(v_toSeqLeft_53_);
v___f_61_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_61_, 0, v_toSeqLeft_53_);
lean_inc(v_toSeq_52_);
v___f_62_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_62_, 0, v_toSeq_52_);
v___x_63_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_63_, 0, v___x_59_);
lean_ctor_set(v___x_63_, 1, v___f_55_);
lean_ctor_set(v___x_63_, 2, v___f_62_);
lean_ctor_set(v___x_63_, 3, v___f_61_);
lean_ctor_set(v___x_63_, 4, v___f_60_);
v___x_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___f_56_);
v___x_65_ = l_StateRefT_x27_instMonad___redArg(v___x_64_);
v_toApplicative_66_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_96_ == 0)
{
lean_object* v_unused_97_; 
v_unused_97_ = lean_ctor_get(v___x_65_, 1);
lean_dec(v_unused_97_);
v___x_68_ = v___x_65_;
v_isShared_69_ = v_isSharedCheck_96_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_toApplicative_66_);
lean_dec(v___x_65_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_96_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v_toFunctor_70_; lean_object* v_toSeq_71_; lean_object* v_toSeqLeft_72_; lean_object* v_toSeqRight_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_94_; 
v_toFunctor_70_ = lean_ctor_get(v_toApplicative_66_, 0);
v_toSeq_71_ = lean_ctor_get(v_toApplicative_66_, 2);
v_toSeqLeft_72_ = lean_ctor_get(v_toApplicative_66_, 3);
v_toSeqRight_73_ = lean_ctor_get(v_toApplicative_66_, 4);
v_isSharedCheck_94_ = !lean_is_exclusive(v_toApplicative_66_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; 
v_unused_95_ = lean_ctor_get(v_toApplicative_66_, 1);
lean_dec(v_unused_95_);
v___x_75_ = v_toApplicative_66_;
v_isShared_76_ = v_isSharedCheck_94_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_toSeqRight_73_);
lean_inc(v_toSeqLeft_72_);
lean_inc(v_toSeq_71_);
lean_inc(v_toFunctor_70_);
lean_dec(v_toApplicative_66_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_94_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___f_77_; lean_object* v___f_78_; lean_object* v___f_79_; lean_object* v___f_80_; lean_object* v___f_81_; lean_object* v___x_82_; lean_object* v___f_83_; lean_object* v___f_84_; lean_object* v___f_85_; lean_object* v___x_87_; 
v___f_77_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__4));
v___f_78_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__5));
v___f_79_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__6));
lean_inc_ref(v_toFunctor_70_);
v___f_80_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_80_, 0, v_toFunctor_70_);
v___f_81_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_81_, 0, v_toFunctor_70_);
v___x_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_82_, 0, v___f_80_);
lean_ctor_set(v___x_82_, 1, v___f_81_);
v___f_83_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_83_, 0, v_toSeqRight_73_);
v___f_84_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_84_, 0, v_toSeqLeft_72_);
v___f_85_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_85_, 0, v_toSeq_71_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 4, v___f_83_);
lean_ctor_set(v___x_75_, 3, v___f_84_);
lean_ctor_set(v___x_75_, 2, v___f_85_);
lean_ctor_set(v___x_75_, 1, v___f_78_);
lean_ctor_set(v___x_75_, 0, v___x_82_);
v___x_87_ = v___x_75_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v___f_78_);
lean_ctor_set(v_reuseFailAlloc_93_, 2, v___f_85_);
lean_ctor_set(v_reuseFailAlloc_93_, 3, v___f_84_);
lean_ctor_set(v_reuseFailAlloc_93_, 4, v___f_83_);
v___x_87_ = v_reuseFailAlloc_93_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_89_; 
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 1, v___f_79_);
lean_ctor_set(v___x_68_, 0, v___x_87_);
v___x_89_ = v___x_68_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_87_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v___f_79_);
v___x_89_ = v_reuseFailAlloc_92_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__18));
v___x_91_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_91_, 0, lean_box(0));
lean_closure_set(v___x_91_, 1, lean_box(0));
lean_closure_set(v___x_91_, 2, lean_box(0));
lean_closure_set(v___x_91_, 3, v___x_89_);
lean_closure_set(v___x_91_, 4, lean_box(0));
lean_closure_set(v___x_91_, 5, lean_box(0));
lean_closure_set(v___x_91_, 6, v___x_90_);
lean_closure_set(v___x_91_, 7, v___f_77_);
return v___x_91_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0(lean_object* v_f_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___x_105_; lean_object* v_map_106_; lean_object* v_subst_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_118_; 
v___x_105_ = lean_st_ref_take(v___y_99_);
v_map_106_ = lean_ctor_get(v___x_105_, 0);
v_subst_107_ = lean_ctor_get(v___x_105_, 1);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_118_ == 0)
{
v___x_109_ = v___x_105_;
v_isShared_110_ = v_isSharedCheck_118_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_subst_107_);
lean_inc(v_map_106_);
lean_dec(v___x_105_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_118_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_111_ = lean_apply_1(v_f_98_, v_subst_107_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_111_);
v___x_113_ = v___x_109_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_map_106_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v___x_111_);
v___x_113_ = v_reuseFailAlloc_117_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = lean_st_ref_set(v___y_99_, v___x_113_);
v___x_115_ = lean_box(0);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0___boxed(lean_object* v_f_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0(v_f_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec(v___y_120_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___redArg(lean_object* v_a_129_){
_start:
{
lean_object* v___x_131_; lean_object* v_subst_132_; lean_object* v___x_133_; 
v___x_131_ = lean_st_ref_get(v_a_129_);
v_subst_132_ = lean_ctor_get(v___x_131_, 1);
lean_inc_ref(v_subst_132_);
lean_dec(v___x_131_);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v_subst_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___redArg___boxed(lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Compiler_LCNF_CSE_getSubst___redArg(v_a_134_);
lean_dec(v_a_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst(lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_143_; lean_object* v_subst_144_; lean_object* v___x_145_; 
v___x_143_ = lean_st_ref_get(v_a_137_);
v_subst_144_ = lean_ctor_get(v___x_143_, 1);
lean_inc_ref(v_subst_144_);
lean_dec(v___x_143_);
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v_subst_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___boxed(lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Compiler_LCNF_CSE_getSubst(v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg(lean_object* v_value_155_, lean_object* v_fvarId_156_, lean_object* v_a_157_){
_start:
{
lean_object* v___x_159_; lean_object* v_map_160_; lean_object* v_subst_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_174_; 
v___x_159_ = lean_st_ref_take(v_a_157_);
v_map_160_ = lean_ctor_get(v___x_159_, 0);
v_subst_161_ = lean_ctor_get(v___x_159_, 1);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_174_ == 0)
{
v___x_163_ = v___x_159_;
v_isShared_164_ = v_isSharedCheck_174_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_subst_161_);
lean_inc(v_map_160_);
lean_dec(v___x_159_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_174_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_165_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0));
v___x_166_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1));
v___x_167_ = l_Lean_PersistentHashMap_insert___redArg(v___x_165_, v___x_166_, v_map_160_, v_value_155_, v_fvarId_156_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_167_);
v___x_169_ = v___x_163_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_subst_161_);
v___x_169_ = v_reuseFailAlloc_173_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_st_ref_set(v_a_157_, v___x_169_);
v___x_171_ = lean_box(0);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg___boxed(lean_object* v_value_175_, lean_object* v_fvarId_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Compiler_LCNF_CSE_addEntry___redArg(v_value_175_, v_fvarId_176_, v_a_177_);
lean_dec(v_a_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry(lean_object* v_value_180_, lean_object* v_fvarId_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v___x_188_; lean_object* v_map_189_; lean_object* v_subst_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_203_; 
v___x_188_ = lean_st_ref_take(v_a_182_);
v_map_189_ = lean_ctor_get(v___x_188_, 0);
v_subst_190_ = lean_ctor_get(v___x_188_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_203_ == 0)
{
v___x_192_ = v___x_188_;
v_isShared_193_ = v_isSharedCheck_203_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_subst_190_);
lean_inc(v_map_189_);
lean_dec(v___x_188_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_203_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_194_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0));
v___x_195_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1));
v___x_196_ = l_Lean_PersistentHashMap_insert___redArg(v___x_194_, v___x_195_, v_map_189_, v_value_180_, v_fvarId_181_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_196_);
v___x_198_ = v___x_192_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_subst_190_);
v___x_198_ = v_reuseFailAlloc_202_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = lean_st_ref_set(v_a_182_, v___x_198_);
v___x_200_ = lean_box(0);
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___boxed(lean_object* v_value_204_, lean_object* v_fvarId_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Compiler_LCNF_CSE_addEntry(v_value_204_, v_fvarId_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(lean_object* v_a_213_, lean_object* v_map_214_, lean_object* v_a_x3f_215_){
_start:
{
lean_object* v___x_217_; lean_object* v_subst_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_228_; 
v___x_217_ = lean_st_ref_take(v_a_213_);
v_subst_218_ = lean_ctor_get(v___x_217_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; 
v_unused_229_ = lean_ctor_get(v___x_217_, 0);
lean_dec(v_unused_229_);
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_228_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_subst_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_228_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v_map_214_);
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_map_214_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_subst_218_);
v___x_223_ = v_reuseFailAlloc_227_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_st_ref_set(v_a_213_, v___x_223_);
v___x_225_ = lean_box(0);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0___boxed(lean_object* v_a_230_, lean_object* v_map_231_, lean_object* v_a_x3f_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(v_a_230_, v_map_231_, v_a_x3f_232_);
lean_dec(v_a_x3f_232_);
lean_dec(v_a_230_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg(lean_object* v_x_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v___x_242_; lean_object* v_map_243_; lean_object* v_r_244_; 
v___x_242_ = lean_st_ref_get(v_a_236_);
v_map_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc_ref(v_map_243_);
lean_dec(v___x_242_);
lean_inc(v_a_240_);
lean_inc_ref(v_a_239_);
lean_inc(v_a_238_);
lean_inc_ref(v_a_237_);
lean_inc(v_a_236_);
v_r_244_ = lean_apply_6(v_x_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, lean_box(0));
if (lean_obj_tag(v_r_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_261_; 
v_a_245_ = lean_ctor_get(v_r_244_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v_r_244_);
if (v_isSharedCheck_261_ == 0)
{
v___x_247_ = v_r_244_;
v_isShared_248_ = v_isSharedCheck_261_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v_r_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_261_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
lean_inc(v_a_245_);
if (v_isShared_248_ == 0)
{
lean_ctor_set_tag(v___x_247_, 1);
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_260_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
v___x_251_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(v_a_236_, v_map_243_, v___x_250_);
lean_dec_ref(v___x_250_);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_258_ == 0)
{
lean_object* v_unused_259_; 
v_unused_259_ = lean_ctor_get(v___x_251_, 0);
lean_dec(v_unused_259_);
v___x_253_ = v___x_251_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_dec(v___x_251_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v_a_245_);
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_245_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
v_a_262_ = lean_ctor_get(v_r_244_, 0);
lean_inc(v_a_262_);
lean_dec_ref(v_r_244_);
v___x_263_ = lean_box(0);
v___x_264_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(v_a_236_, v_map_243_, v___x_263_);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; 
v_unused_272_ = lean_ctor_get(v___x_264_, 0);
lean_dec(v_unused_272_);
v___x_266_ = v___x_264_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_dec(v___x_264_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
lean_ctor_set_tag(v___x_266_, 1);
lean_ctor_set(v___x_266_, 0, v_a_262_);
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_262_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___boxed(lean_object* v_x_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg(v_x_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec(v_a_274_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope(lean_object* v_00_u03b1_281_, lean_object* v_x_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_289_; lean_object* v_map_290_; lean_object* v_r_291_; 
v___x_289_ = lean_st_ref_get(v_a_283_);
v_map_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc_ref(v_map_290_);
lean_dec(v___x_289_);
lean_inc(v_a_287_);
lean_inc_ref(v_a_286_);
lean_inc(v_a_285_);
lean_inc_ref(v_a_284_);
lean_inc(v_a_283_);
v_r_291_ = lean_apply_6(v_x_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, lean_box(0));
if (lean_obj_tag(v_r_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_308_; 
v_a_292_ = lean_ctor_get(v_r_291_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v_r_291_);
if (v_isSharedCheck_308_ == 0)
{
v___x_294_ = v_r_291_;
v_isShared_295_ = v_isSharedCheck_308_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v_r_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_308_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
lean_inc(v_a_292_);
if (v_isShared_295_ == 0)
{
lean_ctor_set_tag(v___x_294_, 1);
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_307_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
v___x_298_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(v_a_283_, v_map_290_, v___x_297_);
lean_dec_ref(v___x_297_);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v___x_298_, 0);
lean_dec(v_unused_306_);
v___x_300_ = v___x_298_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_dec(v___x_298_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v_a_292_);
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_292_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
v_a_309_ = lean_ctor_get(v_r_291_, 0);
lean_inc(v_a_309_);
lean_dec_ref(v_r_291_);
v___x_310_ = lean_box(0);
v___x_311_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(v_a_283_, v_map_290_, v___x_310_);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_318_ == 0)
{
lean_object* v_unused_319_; 
v_unused_319_ = lean_ctor_get(v___x_311_, 0);
lean_dec(v_unused_319_);
v___x_313_ = v___x_311_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_dec(v___x_311_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set_tag(v___x_313_, 1);
lean_ctor_set(v___x_313_, 0, v_a_309_);
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_309_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___boxed(lean_object* v_00_u03b1_320_, lean_object* v_x_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Compiler_LCNF_CSE_withNewScope(v_00_u03b1_320_, v_x_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
if (lean_obj_tag(v_x_330_) == 0)
{
return v_x_329_;
}
else
{
lean_object* v_key_331_; lean_object* v_value_332_; lean_object* v_tail_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_356_; 
v_key_331_ = lean_ctor_get(v_x_330_, 0);
v_value_332_ = lean_ctor_get(v_x_330_, 1);
v_tail_333_ = lean_ctor_get(v_x_330_, 2);
v_isSharedCheck_356_ = !lean_is_exclusive(v_x_330_);
if (v_isSharedCheck_356_ == 0)
{
v___x_335_ = v_x_330_;
v_isShared_336_ = v_isSharedCheck_356_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_tail_333_);
lean_inc(v_value_332_);
lean_inc(v_key_331_);
lean_dec(v_x_330_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_356_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v_fold_341_; uint64_t v___x_342_; uint64_t v___x_343_; uint64_t v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_337_ = lean_array_get_size(v_x_329_);
v___x_338_ = l_Lean_instHashableFVarId_hash(v_key_331_);
v___x_339_ = 32ULL;
v___x_340_ = lean_uint64_shift_right(v___x_338_, v___x_339_);
v_fold_341_ = lean_uint64_xor(v___x_338_, v___x_340_);
v___x_342_ = 16ULL;
v___x_343_ = lean_uint64_shift_right(v_fold_341_, v___x_342_);
v___x_344_ = lean_uint64_xor(v_fold_341_, v___x_343_);
v___x_345_ = lean_uint64_to_usize(v___x_344_);
v___x_346_ = lean_usize_of_nat(v___x_337_);
v___x_347_ = ((size_t)1ULL);
v___x_348_ = lean_usize_sub(v___x_346_, v___x_347_);
v___x_349_ = lean_usize_land(v___x_345_, v___x_348_);
v___x_350_ = lean_array_uget_borrowed(v_x_329_, v___x_349_);
lean_inc(v___x_350_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 2, v___x_350_);
v___x_352_ = v___x_335_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_key_331_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_value_332_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v___x_350_);
v___x_352_ = v_reuseFailAlloc_355_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; 
v___x_353_ = lean_array_uset(v_x_329_, v___x_349_, v___x_352_);
v_x_329_ = v___x_353_;
v_x_330_ = v_tail_333_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2___redArg(lean_object* v_i_357_, lean_object* v_source_358_, lean_object* v_target_359_){
_start:
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = lean_array_get_size(v_source_358_);
v___x_361_ = lean_nat_dec_lt(v_i_357_, v___x_360_);
if (v___x_361_ == 0)
{
lean_dec_ref(v_source_358_);
lean_dec(v_i_357_);
return v_target_359_;
}
else
{
lean_object* v_es_362_; lean_object* v___x_363_; lean_object* v_source_364_; lean_object* v_target_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_es_362_ = lean_array_fget(v_source_358_, v_i_357_);
v___x_363_ = lean_box(0);
v_source_364_ = lean_array_fset(v_source_358_, v_i_357_, v___x_363_);
v_target_365_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3___redArg(v_target_359_, v_es_362_);
v___x_366_ = lean_unsigned_to_nat(1u);
v___x_367_ = lean_nat_add(v_i_357_, v___x_366_);
lean_dec(v_i_357_);
v_i_357_ = v___x_367_;
v_source_358_ = v_source_364_;
v_target_359_ = v_target_365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1___redArg(lean_object* v_data_369_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v_nbuckets_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_370_ = lean_array_get_size(v_data_369_);
v___x_371_ = lean_unsigned_to_nat(2u);
v_nbuckets_372_ = lean_nat_mul(v___x_370_, v___x_371_);
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_box(0);
v___x_375_ = lean_mk_array(v_nbuckets_372_, v___x_374_);
v___x_376_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2___redArg(v___x_373_, v_data_369_, v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(lean_object* v_a_377_, lean_object* v_b_378_, lean_object* v_x_379_){
_start:
{
if (lean_obj_tag(v_x_379_) == 0)
{
lean_dec(v_b_378_);
lean_dec(v_a_377_);
return v_x_379_;
}
else
{
lean_object* v_key_380_; lean_object* v_value_381_; lean_object* v_tail_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_394_; 
v_key_380_ = lean_ctor_get(v_x_379_, 0);
v_value_381_ = lean_ctor_get(v_x_379_, 1);
v_tail_382_ = lean_ctor_get(v_x_379_, 2);
v_isSharedCheck_394_ = !lean_is_exclusive(v_x_379_);
if (v_isSharedCheck_394_ == 0)
{
v___x_384_ = v_x_379_;
v_isShared_385_ = v_isSharedCheck_394_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_tail_382_);
lean_inc(v_value_381_);
lean_inc(v_key_380_);
lean_dec(v_x_379_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_394_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
uint8_t v___x_386_; 
v___x_386_ = l_Lean_instBEqFVarId_beq(v_key_380_, v_a_377_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_387_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(v_a_377_, v_b_378_, v_tail_382_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 2, v___x_387_);
v___x_389_ = v___x_384_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_key_380_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_value_381_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
else
{
lean_object* v___x_392_; 
lean_dec(v_value_381_);
lean_dec(v_key_380_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 1, v_b_378_);
lean_ctor_set(v___x_384_, 0, v_a_377_);
v___x_392_ = v___x_384_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_377_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_b_378_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_tail_382_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(lean_object* v_a_395_, lean_object* v_x_396_){
_start:
{
if (lean_obj_tag(v_x_396_) == 0)
{
uint8_t v___x_397_; 
v___x_397_ = 0;
return v___x_397_;
}
else
{
lean_object* v_key_398_; lean_object* v_tail_399_; uint8_t v___x_400_; 
v_key_398_ = lean_ctor_get(v_x_396_, 0);
v_tail_399_ = lean_ctor_get(v_x_396_, 2);
v___x_400_ = l_Lean_instBEqFVarId_beq(v_key_398_, v_a_395_);
if (v___x_400_ == 0)
{
v_x_396_ = v_tail_399_;
goto _start;
}
else
{
return v___x_400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg___boxed(lean_object* v_a_402_, lean_object* v_x_403_){
_start:
{
uint8_t v_res_404_; lean_object* v_r_405_; 
v_res_404_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(v_a_402_, v_x_403_);
lean_dec(v_x_403_);
lean_dec(v_a_402_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(lean_object* v_m_406_, lean_object* v_a_407_, lean_object* v_b_408_){
_start:
{
lean_object* v_size_409_; lean_object* v_buckets_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_453_; 
v_size_409_ = lean_ctor_get(v_m_406_, 0);
v_buckets_410_ = lean_ctor_get(v_m_406_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v_m_406_);
if (v_isSharedCheck_453_ == 0)
{
v___x_412_ = v_m_406_;
v_isShared_413_ = v_isSharedCheck_453_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_buckets_410_);
lean_inc(v_size_409_);
lean_dec(v_m_406_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_453_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; uint64_t v___x_415_; uint64_t v___x_416_; uint64_t v___x_417_; uint64_t v_fold_418_; uint64_t v___x_419_; uint64_t v___x_420_; uint64_t v___x_421_; size_t v___x_422_; size_t v___x_423_; size_t v___x_424_; size_t v___x_425_; size_t v___x_426_; lean_object* v_bkt_427_; uint8_t v___x_428_; 
v___x_414_ = lean_array_get_size(v_buckets_410_);
v___x_415_ = l_Lean_instHashableFVarId_hash(v_a_407_);
v___x_416_ = 32ULL;
v___x_417_ = lean_uint64_shift_right(v___x_415_, v___x_416_);
v_fold_418_ = lean_uint64_xor(v___x_415_, v___x_417_);
v___x_419_ = 16ULL;
v___x_420_ = lean_uint64_shift_right(v_fold_418_, v___x_419_);
v___x_421_ = lean_uint64_xor(v_fold_418_, v___x_420_);
v___x_422_ = lean_uint64_to_usize(v___x_421_);
v___x_423_ = lean_usize_of_nat(v___x_414_);
v___x_424_ = ((size_t)1ULL);
v___x_425_ = lean_usize_sub(v___x_423_, v___x_424_);
v___x_426_ = lean_usize_land(v___x_422_, v___x_425_);
v_bkt_427_ = lean_array_uget_borrowed(v_buckets_410_, v___x_426_);
v___x_428_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(v_a_407_, v_bkt_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v_size_x27_430_; lean_object* v___x_431_; lean_object* v_buckets_x27_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_429_ = lean_unsigned_to_nat(1u);
v_size_x27_430_ = lean_nat_add(v_size_409_, v___x_429_);
lean_dec(v_size_409_);
lean_inc(v_bkt_427_);
v___x_431_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_431_, 0, v_a_407_);
lean_ctor_set(v___x_431_, 1, v_b_408_);
lean_ctor_set(v___x_431_, 2, v_bkt_427_);
v_buckets_x27_432_ = lean_array_uset(v_buckets_410_, v___x_426_, v___x_431_);
v___x_433_ = lean_unsigned_to_nat(4u);
v___x_434_ = lean_nat_mul(v_size_x27_430_, v___x_433_);
v___x_435_ = lean_unsigned_to_nat(3u);
v___x_436_ = lean_nat_div(v___x_434_, v___x_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_array_get_size(v_buckets_x27_432_);
v___x_438_ = lean_nat_dec_le(v___x_436_, v___x_437_);
lean_dec(v___x_436_);
if (v___x_438_ == 0)
{
lean_object* v_val_439_; lean_object* v___x_441_; 
v_val_439_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1___redArg(v_buckets_x27_432_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v_val_439_);
lean_ctor_set(v___x_412_, 0, v_size_x27_430_);
v___x_441_ = v___x_412_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_size_x27_430_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_val_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
else
{
lean_object* v___x_444_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v_buckets_x27_432_);
lean_ctor_set(v___x_412_, 0, v_size_x27_430_);
v___x_444_ = v___x_412_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_size_x27_430_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_buckets_x27_432_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_object* v___x_446_; lean_object* v_buckets_x27_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
lean_inc(v_bkt_427_);
v___x_446_ = lean_box(0);
v_buckets_x27_447_ = lean_array_uset(v_buckets_410_, v___x_426_, v___x_446_);
v___x_448_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(v_a_407_, v_b_408_, v_bkt_427_);
v___x_449_ = lean_array_uset(v_buckets_x27_447_, v___x_426_, v___x_448_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v___x_449_);
v___x_451_ = v___x_412_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_size_409_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(lean_object* v_decl_454_, lean_object* v_fvarId_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
uint8_t v___x_459_; lean_object* v___x_460_; 
v___x_459_ = 0;
v___x_460_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_459_, v_decl_454_, v_a_457_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_482_; 
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v___x_460_, 0);
lean_dec(v_unused_483_);
v___x_462_ = v___x_460_;
v_isShared_463_ = v_isSharedCheck_482_;
goto v_resetjp_461_;
}
else
{
lean_dec(v___x_460_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_482_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v_fvarId_465_; lean_object* v_map_466_; lean_object* v_subst_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_481_; 
v___x_464_ = lean_st_ref_take(v_a_456_);
v_fvarId_465_ = lean_ctor_get(v_decl_454_, 0);
lean_inc(v_fvarId_465_);
lean_dec_ref(v_decl_454_);
v_map_466_ = lean_ctor_get(v___x_464_, 0);
v_subst_467_ = lean_ctor_get(v___x_464_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_481_ == 0)
{
v___x_469_ = v___x_464_;
v_isShared_470_ = v_isSharedCheck_481_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_subst_467_);
lean_inc(v_map_466_);
lean_dec(v___x_464_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_481_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_471_, 0, v_fvarId_455_);
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(v_subst_467_, v_fvarId_465_, v___x_471_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 1, v___x_472_);
v___x_474_ = v___x_469_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_map_466_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_472_);
v___x_474_ = v_reuseFailAlloc_480_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_475_ = lean_st_ref_set(v_a_456_, v___x_474_);
v___x_476_ = lean_box(0);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_476_);
v___x_478_ = v___x_462_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_455_);
lean_dec_ref(v_decl_454_);
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg___boxed(lean_object* v_decl_484_, lean_object* v_fvarId_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(v_decl_484_, v_fvarId_485_, v_a_486_, v_a_487_);
lean_dec(v_a_487_);
lean_dec(v_a_486_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet(lean_object* v_decl_490_, lean_object* v_fvarId_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(v_decl_490_, v_fvarId_491_, v_a_492_, v_a_494_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___boxed(lean_object* v_decl_499_, lean_object* v_fvarId_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Compiler_LCNF_CSE_replaceLet(v_decl_499_, v_fvarId_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_501_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0(lean_object* v_00_u03b2_508_, lean_object* v_m_509_, lean_object* v_a_510_, lean_object* v_b_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(v_m_509_, v_a_510_, v_b_511_);
return v___x_512_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0(lean_object* v_00_u03b2_513_, lean_object* v_a_514_, lean_object* v_x_515_){
_start:
{
uint8_t v___x_516_; 
v___x_516_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(v_a_514_, v_x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___boxed(lean_object* v_00_u03b2_517_, lean_object* v_a_518_, lean_object* v_x_519_){
_start:
{
uint8_t v_res_520_; lean_object* v_r_521_; 
v_res_520_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0(v_00_u03b2_517_, v_a_518_, v_x_519_);
lean_dec(v_x_519_);
lean_dec(v_a_518_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1(lean_object* v_00_u03b2_522_, lean_object* v_data_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1___redArg(v_data_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2(lean_object* v_00_u03b2_525_, lean_object* v_a_526_, lean_object* v_b_527_, lean_object* v_x_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(v_a_526_, v_b_527_, v_x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_530_, lean_object* v_i_531_, lean_object* v_source_532_, lean_object* v_target_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2___redArg(v_i_531_, v_source_532_, v_target_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_535_, lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3___redArg(v_x_536_, v_x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(lean_object* v_decl_539_, lean_object* v_fvarId_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
uint8_t v___x_544_; uint8_t v___x_545_; lean_object* v___x_546_; 
v___x_544_ = 0;
v___x_545_ = 1;
v___x_546_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_544_, v_decl_539_, v___x_545_, v_a_542_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_568_; 
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; 
v_unused_569_ = lean_ctor_get(v___x_546_, 0);
lean_dec(v_unused_569_);
v___x_548_ = v___x_546_;
v_isShared_549_ = v_isSharedCheck_568_;
goto v_resetjp_547_;
}
else
{
lean_dec(v___x_546_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_568_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v_fvarId_550_; lean_object* v___x_551_; lean_object* v_map_552_; lean_object* v_subst_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_567_; 
v_fvarId_550_ = lean_ctor_get(v_decl_539_, 0);
lean_inc(v_fvarId_550_);
lean_dec_ref(v_decl_539_);
v___x_551_ = lean_st_ref_take(v_a_541_);
v_map_552_ = lean_ctor_get(v___x_551_, 0);
v_subst_553_ = lean_ctor_get(v___x_551_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_567_ == 0)
{
v___x_555_ = v___x_551_;
v_isShared_556_ = v_isSharedCheck_567_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_subst_553_);
lean_inc(v_map_552_);
lean_dec(v___x_551_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_567_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v_fvarId_540_);
v___x_558_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(v_subst_553_, v_fvarId_550_, v___x_557_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v___x_558_);
v___x_560_ = v___x_555_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_map_552_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_558_);
v___x_560_ = v_reuseFailAlloc_566_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_561_ = lean_st_ref_set(v_a_541_, v___x_560_);
v___x_562_ = lean_box(0);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_562_);
v___x_564_ = v___x_548_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_540_);
lean_dec_ref(v_decl_539_);
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg___boxed(lean_object* v_decl_570_, lean_object* v_fvarId_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(v_decl_570_, v_fvarId_571_, v_a_572_, v_a_573_);
lean_dec(v_a_573_);
lean_dec(v_a_572_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun(lean_object* v_decl_576_, lean_object* v_fvarId_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(v_decl_576_, v_fvarId_577_, v_a_578_, v_a_580_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___boxed(lean_object* v_decl_585_, lean_object* v_fvarId_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Compiler_LCNF_CSE_replaceFun(v_decl_585_, v_fvarId_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec(v_a_587_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(lean_object* v_v_594_, lean_object* v_a_595_){
_start:
{
switch(lean_obj_tag(v_v_594_))
{
case 0:
{
lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_605_; 
v_isSharedCheck_605_ = !lean_is_exclusive(v_v_594_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; 
v_unused_606_ = lean_ctor_get(v_v_594_, 0);
lean_dec(v_unused_606_);
v___x_598_ = v_v_594_;
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
else
{
lean_dec(v_v_594_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
uint8_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_600_ = 0;
v___x_601_ = lean_box(v___x_600_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_601_);
v___x_603_ = v___x_598_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
case 3:
{
lean_object* v_declName_607_; lean_object* v___x_608_; lean_object* v_env_609_; uint8_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_declName_607_ = lean_ctor_get(v_v_594_, 0);
lean_inc(v_declName_607_);
lean_dec_ref(v_v_594_);
v___x_608_ = lean_st_ref_get(v_a_595_);
v_env_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc_ref(v_env_609_);
lean_dec(v___x_608_);
v___x_610_ = l_Lean_hasNeverExtractAttribute(v_env_609_, v_declName_607_);
v___x_611_ = lean_box(v___x_610_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
default: 
{
uint8_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
lean_dec(v_v_594_);
v___x_613_ = 0;
v___x_614_ = lean_box(v___x_613_);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg___boxed(lean_object* v_v_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(v_v_616_, v_a_617_);
lean_dec(v_a_617_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract(lean_object* v_v_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(v_v_620_, v_a_624_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___boxed(lean_object* v_v_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract(v_v_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(lean_object* v_a_634_, lean_object* v_map_635_, lean_object* v_a_x3f_636_){
_start:
{
lean_object* v___x_638_; lean_object* v_subst_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_649_; 
v___x_638_ = lean_st_ref_take(v_a_634_);
v_subst_639_ = lean_ctor_get(v___x_638_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; 
v_unused_650_ = lean_ctor_get(v___x_638_, 0);
lean_dec(v_unused_650_);
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_649_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_subst_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_649_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v_map_635_);
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_map_635_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_subst_639_);
v___x_644_ = v_reuseFailAlloc_648_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_st_ref_set(v_a_634_, v___x_644_);
v___x_646_ = lean_box(0);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
return v___x_647_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0___boxed(lean_object* v_a_651_, lean_object* v_map_652_, lean_object* v_a_x3f_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(v_a_651_, v_map_652_, v_a_x3f_653_);
lean_dec(v_a_x3f_653_);
lean_dec(v_a_651_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(uint8_t v_pu_656_, uint8_t v_t_657_, lean_object* v_args_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; lean_object* v_subst_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_661_ = lean_st_ref_get(v___y_659_);
v_subst_662_ = lean_ctor_get(v___x_661_, 1);
lean_inc_ref(v_subst_662_);
lean_dec(v___x_661_);
v___x_663_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_656_, v_subst_662_, v_args_658_, v_t_657_);
lean_dec_ref(v_subst_662_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg___boxed(lean_object* v_pu_665_, lean_object* v_t_666_, lean_object* v_args_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
uint8_t v_pu_boxed_670_; uint8_t v_t_boxed_671_; lean_object* v_res_672_; 
v_pu_boxed_670_ = lean_unbox(v_pu_665_);
v_t_boxed_671_ = lean_unbox(v_t_666_);
v_res_672_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v_pu_boxed_670_, v_t_boxed_671_, v_args_667_, v___y_668_);
lean_dec(v___y_668_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(uint8_t v_pu_673_, uint8_t v_t_674_, lean_object* v_decl_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_type_679_; lean_object* v_value_680_; lean_object* v___x_681_; lean_object* v_subst_682_; lean_object* v___x_683_; lean_object* v_subst_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_type_679_ = lean_ctor_get(v_decl_675_, 2);
v_value_680_ = lean_ctor_get(v_decl_675_, 3);
v___x_681_ = lean_st_ref_get(v___y_676_);
v_subst_682_ = lean_ctor_get(v___x_681_, 1);
lean_inc_ref(v_subst_682_);
lean_dec(v___x_681_);
v___x_683_ = lean_st_ref_get(v___y_676_);
v_subst_684_ = lean_ctor_get(v___x_683_, 1);
lean_inc_ref(v_subst_684_);
lean_dec(v___x_683_);
lean_inc_ref(v_type_679_);
v___x_685_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_673_, v_subst_682_, v_t_674_, v_type_679_);
lean_dec_ref(v_subst_682_);
lean_inc(v_value_680_);
v___x_686_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_673_, v_subst_684_, v_value_680_, v_t_674_);
lean_dec_ref(v_subst_684_);
v___x_687_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_673_, v_decl_675_, v___x_685_, v___x_686_, v___y_677_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg___boxed(lean_object* v_pu_688_, lean_object* v_t_689_, lean_object* v_decl_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
uint8_t v_pu_boxed_694_; uint8_t v_t_boxed_695_; lean_object* v_res_696_; 
v_pu_boxed_694_ = lean_unbox(v_pu_688_);
v_t_boxed_695_ = lean_unbox(v_t_689_);
v_res_696_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v_pu_boxed_694_, v_t_boxed_695_, v_decl_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec(v___y_691_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(lean_object* v___y_697_, lean_object* v_map_698_, lean_object* v_a_x3f_699_){
_start:
{
lean_object* v___x_701_; lean_object* v_subst_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_712_; 
v___x_701_ = lean_st_ref_take(v___y_697_);
v_subst_702_ = lean_ctor_get(v___x_701_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v___x_701_, 0);
lean_dec(v_unused_713_);
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_712_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_subst_702_);
lean_dec(v___x_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_712_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v_map_698_);
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_map_698_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_subst_702_);
v___x_707_ = v_reuseFailAlloc_711_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_708_ = lean_st_ref_set(v___y_697_, v___x_707_);
v___x_709_ = lean_box(0);
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0___boxed(lean_object* v___y_714_, lean_object* v_map_715_, lean_object* v_a_x3f_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_714_, v_map_715_, v_a_x3f_716_);
lean_dec(v_a_x3f_716_);
lean_dec(v___y_714_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(uint8_t v_pu_719_, uint8_t v_t_720_, lean_object* v_i_721_, lean_object* v_as_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = lean_array_get_size(v_as_722_);
v___x_727_ = lean_nat_dec_lt(v_i_721_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; 
lean_dec(v_i_721_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v_as_722_);
return v___x_728_;
}
else
{
lean_object* v_a_729_; lean_object* v_type_730_; lean_object* v___x_731_; lean_object* v_subst_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_a_729_ = lean_array_fget_borrowed(v_as_722_, v_i_721_);
v_type_730_ = lean_ctor_get(v_a_729_, 2);
v___x_731_ = lean_st_ref_get(v___y_723_);
v_subst_732_ = lean_ctor_get(v___x_731_, 1);
lean_inc_ref(v_subst_732_);
lean_dec(v___x_731_);
lean_inc_ref(v_type_730_);
v___x_733_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_719_, v_subst_732_, v_t_720_, v_type_730_);
lean_dec_ref(v_subst_732_);
lean_inc(v_a_729_);
v___x_734_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_719_, v_a_729_, v___x_733_, v___y_724_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; size_t v___x_736_; size_t v___x_737_; uint8_t v___x_738_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref(v___x_734_);
v___x_736_ = lean_ptr_addr(v_a_729_);
v___x_737_ = lean_ptr_addr(v_a_735_);
v___x_738_ = lean_usize_dec_eq(v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_unsigned_to_nat(1u);
v___x_740_ = lean_nat_add(v_i_721_, v___x_739_);
v___x_741_ = lean_array_fset(v_as_722_, v_i_721_, v_a_735_);
lean_dec(v_i_721_);
v_i_721_ = v___x_740_;
v_as_722_ = v___x_741_;
goto _start;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; 
lean_dec(v_a_735_);
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = lean_nat_add(v_i_721_, v___x_743_);
lean_dec(v_i_721_);
v_i_721_ = v___x_744_;
goto _start;
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec_ref(v_as_722_);
lean_dec(v_i_721_);
v_a_746_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_734_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_734_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg___boxed(lean_object* v_pu_754_, lean_object* v_t_755_, lean_object* v_i_756_, lean_object* v_as_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
uint8_t v_pu_boxed_761_; uint8_t v_t_boxed_762_; lean_object* v_res_763_; 
v_pu_boxed_761_ = lean_unbox(v_pu_754_);
v_t_boxed_762_ = lean_unbox(v_t_755_);
v_res_763_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(v_pu_boxed_761_, v_t_boxed_762_, v_i_756_, v_as_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec(v___y_758_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(uint8_t v_pu_764_, uint8_t v_t_765_, lean_object* v_ps_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(v_pu_764_, v_t_765_, v___x_773_, v_ps_766_, v___y_767_, v___y_769_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___boxed(lean_object* v_pu_775_, lean_object* v_t_776_, lean_object* v_ps_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
uint8_t v_pu_boxed_784_; uint8_t v_t_boxed_785_; lean_object* v_res_786_; 
v_pu_boxed_784_ = lean_unbox(v_pu_775_);
v_t_boxed_785_ = lean_unbox(v_t_776_);
v_res_786_ = l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(v_pu_boxed_784_, v_t_boxed_785_, v_ps_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(lean_object* v_keys_787_, lean_object* v_vals_788_, lean_object* v_i_789_, lean_object* v_k_790_){
_start:
{
lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_791_ = lean_array_get_size(v_keys_787_);
v___x_792_ = lean_nat_dec_lt(v_i_789_, v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; 
lean_dec(v_i_789_);
v___x_793_ = lean_box(0);
return v___x_793_;
}
else
{
lean_object* v_k_x27_794_; uint8_t v___x_795_; 
v_k_x27_794_ = lean_array_fget_borrowed(v_keys_787_, v_i_789_);
v___x_795_ = lean_expr_eqv(v_k_790_, v_k_x27_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_unsigned_to_nat(1u);
v___x_797_ = lean_nat_add(v_i_789_, v___x_796_);
lean_dec(v_i_789_);
v_i_789_ = v___x_797_;
goto _start;
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_array_fget_borrowed(v_vals_788_, v_i_789_);
lean_dec(v_i_789_);
lean_inc(v___x_799_);
v___x_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_keys_801_, lean_object* v_vals_802_, lean_object* v_i_803_, lean_object* v_k_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(v_keys_801_, v_vals_802_, v_i_803_, v_k_804_);
lean_dec_ref(v_k_804_);
lean_dec_ref(v_vals_802_);
lean_dec_ref(v_keys_801_);
return v_res_805_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_806_; size_t v___x_807_; size_t v___x_808_; 
v___x_806_ = ((size_t)5ULL);
v___x_807_ = ((size_t)1ULL);
v___x_808_ = lean_usize_shift_left(v___x_807_, v___x_806_);
return v___x_808_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_809_; size_t v___x_810_; size_t v___x_811_; 
v___x_809_ = ((size_t)1ULL);
v___x_810_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__0);
v___x_811_ = lean_usize_sub(v___x_810_, v___x_809_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(lean_object* v_x_812_, size_t v_x_813_, lean_object* v_x_814_){
_start:
{
if (lean_obj_tag(v_x_812_) == 0)
{
lean_object* v_es_815_; lean_object* v___x_816_; size_t v___x_817_; size_t v___x_818_; size_t v___x_819_; lean_object* v_j_820_; lean_object* v___x_821_; 
v_es_815_ = lean_ctor_get(v_x_812_, 0);
v___x_816_ = lean_box(2);
v___x_817_ = ((size_t)5ULL);
v___x_818_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1);
v___x_819_ = lean_usize_land(v_x_813_, v___x_818_);
v_j_820_ = lean_usize_to_nat(v___x_819_);
v___x_821_ = lean_array_get_borrowed(v___x_816_, v_es_815_, v_j_820_);
lean_dec(v_j_820_);
switch(lean_obj_tag(v___x_821_))
{
case 0:
{
lean_object* v_key_822_; lean_object* v_val_823_; uint8_t v___x_824_; 
v_key_822_ = lean_ctor_get(v___x_821_, 0);
v_val_823_ = lean_ctor_get(v___x_821_, 1);
v___x_824_ = lean_expr_eqv(v_x_814_, v_key_822_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; 
v___x_825_ = lean_box(0);
return v___x_825_;
}
else
{
lean_object* v___x_826_; 
lean_inc(v_val_823_);
v___x_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_826_, 0, v_val_823_);
return v___x_826_;
}
}
case 1:
{
lean_object* v_node_827_; size_t v___x_828_; 
v_node_827_ = lean_ctor_get(v___x_821_, 0);
v___x_828_ = lean_usize_shift_right(v_x_813_, v___x_817_);
v_x_812_ = v_node_827_;
v_x_813_ = v___x_828_;
goto _start;
}
default: 
{
lean_object* v___x_830_; 
v___x_830_ = lean_box(0);
return v___x_830_;
}
}
}
else
{
lean_object* v_ks_831_; lean_object* v_vs_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_ks_831_ = lean_ctor_get(v_x_812_, 0);
v_vs_832_ = lean_ctor_get(v_x_812_, 1);
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(v_ks_831_, v_vs_832_, v___x_833_, v_x_814_);
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___boxed(lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
size_t v_x_15783__boxed_838_; lean_object* v_res_839_; 
v_x_15783__boxed_838_ = lean_unbox_usize(v_x_836_);
lean_dec(v_x_836_);
v_res_839_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_835_, v_x_15783__boxed_838_, v_x_837_);
lean_dec_ref(v_x_837_);
lean_dec_ref(v_x_835_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
uint64_t v___x_842_; size_t v___x_843_; lean_object* v___x_844_; 
v___x_842_ = l_Lean_Expr_hash(v_x_841_);
v___x_843_ = lean_uint64_to_usize(v___x_842_);
v___x_844_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_840_, v___x_843_, v_x_841_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg___boxed(lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_x_845_, v_x_846_);
lean_dec_ref(v_x_846_);
lean_dec_ref(v_x_845_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v_x_851_){
_start:
{
lean_object* v_ks_852_; lean_object* v_vs_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_877_; 
v_ks_852_ = lean_ctor_get(v_x_848_, 0);
v_vs_853_ = lean_ctor_get(v_x_848_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_x_848_);
if (v_isSharedCheck_877_ == 0)
{
v___x_855_ = v_x_848_;
v_isShared_856_ = v_isSharedCheck_877_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_vs_853_);
lean_inc(v_ks_852_);
lean_dec(v_x_848_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_877_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = lean_array_get_size(v_ks_852_);
v___x_858_ = lean_nat_dec_lt(v_x_849_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
lean_dec(v_x_849_);
v___x_859_ = lean_array_push(v_ks_852_, v_x_850_);
v___x_860_ = lean_array_push(v_vs_853_, v_x_851_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v___x_860_);
lean_ctor_set(v___x_855_, 0, v___x_859_);
v___x_862_ = v___x_855_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
else
{
lean_object* v_k_x27_864_; uint8_t v___x_865_; 
v_k_x27_864_ = lean_array_fget_borrowed(v_ks_852_, v_x_849_);
v___x_865_ = lean_expr_eqv(v_x_850_, v_k_x27_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_867_; 
if (v_isShared_856_ == 0)
{
v___x_867_ = v___x_855_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_ks_852_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_vs_853_);
v___x_867_ = v_reuseFailAlloc_871_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_unsigned_to_nat(1u);
v___x_869_ = lean_nat_add(v_x_849_, v___x_868_);
lean_dec(v_x_849_);
v_x_848_ = v___x_867_;
v_x_849_ = v___x_869_;
goto _start;
}
}
else
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_872_ = lean_array_fset(v_ks_852_, v_x_849_, v_x_850_);
v___x_873_ = lean_array_fset(v_vs_853_, v_x_849_, v_x_851_);
lean_dec(v_x_849_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v___x_873_);
lean_ctor_set(v___x_855_, 0, v___x_872_);
v___x_875_ = v___x_855_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(lean_object* v_n_878_, lean_object* v_k_879_, lean_object* v_v_880_){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(v_n_878_, v___x_881_, v_k_879_, v_v_880_);
return v___x_882_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(lean_object* v_x_884_, size_t v_x_885_, size_t v_x_886_, lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
if (lean_obj_tag(v_x_884_) == 0)
{
lean_object* v_es_889_; size_t v___x_890_; size_t v___x_891_; size_t v___x_892_; size_t v___x_893_; lean_object* v_j_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_es_889_ = lean_ctor_get(v_x_884_, 0);
v___x_890_ = ((size_t)5ULL);
v___x_891_ = ((size_t)1ULL);
v___x_892_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1);
v___x_893_ = lean_usize_land(v_x_885_, v___x_892_);
v_j_894_ = lean_usize_to_nat(v___x_893_);
v___x_895_ = lean_array_get_size(v_es_889_);
v___x_896_ = lean_nat_dec_lt(v_j_894_, v___x_895_);
if (v___x_896_ == 0)
{
lean_dec(v_j_894_);
lean_dec(v_x_888_);
lean_dec_ref(v_x_887_);
return v_x_884_;
}
else
{
lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_933_; 
lean_inc_ref(v_es_889_);
v_isSharedCheck_933_ = !lean_is_exclusive(v_x_884_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; 
v_unused_934_ = lean_ctor_get(v_x_884_, 0);
lean_dec(v_unused_934_);
v___x_898_ = v_x_884_;
v_isShared_899_ = v_isSharedCheck_933_;
goto v_resetjp_897_;
}
else
{
lean_dec(v_x_884_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_933_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_v_900_; lean_object* v___x_901_; lean_object* v_xs_x27_902_; lean_object* v___y_904_; 
v_v_900_ = lean_array_fget(v_es_889_, v_j_894_);
v___x_901_ = lean_box(0);
v_xs_x27_902_ = lean_array_fset(v_es_889_, v_j_894_, v___x_901_);
switch(lean_obj_tag(v_v_900_))
{
case 0:
{
lean_object* v_key_909_; lean_object* v_val_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_920_; 
v_key_909_ = lean_ctor_get(v_v_900_, 0);
v_val_910_ = lean_ctor_get(v_v_900_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_v_900_);
if (v_isSharedCheck_920_ == 0)
{
v___x_912_ = v_v_900_;
v_isShared_913_ = v_isSharedCheck_920_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_val_910_);
lean_inc(v_key_909_);
lean_dec(v_v_900_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_920_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
uint8_t v___x_914_; 
v___x_914_ = lean_expr_eqv(v_x_887_, v_key_909_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; 
lean_del_object(v___x_912_);
v___x_915_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_909_, v_val_910_, v_x_887_, v_x_888_);
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
v___y_904_ = v___x_916_;
goto v___jp_903_;
}
else
{
lean_object* v___x_918_; 
lean_dec(v_val_910_);
lean_dec(v_key_909_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v_x_888_);
lean_ctor_set(v___x_912_, 0, v_x_887_);
v___x_918_ = v___x_912_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_x_887_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_x_888_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
v___y_904_ = v___x_918_;
goto v___jp_903_;
}
}
}
}
case 1:
{
lean_object* v_node_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_931_; 
v_node_921_ = lean_ctor_get(v_v_900_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v_v_900_);
if (v_isSharedCheck_931_ == 0)
{
v___x_923_ = v_v_900_;
v_isShared_924_ = v_isSharedCheck_931_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_node_921_);
lean_dec(v_v_900_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_931_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
size_t v___x_925_; size_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_925_ = lean_usize_shift_right(v_x_885_, v___x_890_);
v___x_926_ = lean_usize_add(v_x_886_, v___x_891_);
v___x_927_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_node_921_, v___x_925_, v___x_926_, v_x_887_, v_x_888_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_927_);
v___x_929_ = v___x_923_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
v___y_904_ = v___x_929_;
goto v___jp_903_;
}
}
}
default: 
{
lean_object* v___x_932_; 
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v_x_887_);
lean_ctor_set(v___x_932_, 1, v_x_888_);
v___y_904_ = v___x_932_;
goto v___jp_903_;
}
}
v___jp_903_:
{
lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_905_ = lean_array_fset(v_xs_x27_902_, v_j_894_, v___y_904_);
lean_dec(v_j_894_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_905_);
v___x_907_ = v___x_898_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
else
{
lean_object* v_ks_935_; lean_object* v_vs_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_956_; 
v_ks_935_ = lean_ctor_get(v_x_884_, 0);
v_vs_936_ = lean_ctor_get(v_x_884_, 1);
v_isSharedCheck_956_ = !lean_is_exclusive(v_x_884_);
if (v_isSharedCheck_956_ == 0)
{
v___x_938_ = v_x_884_;
v_isShared_939_ = v_isSharedCheck_956_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_vs_936_);
lean_inc(v_ks_935_);
lean_dec(v_x_884_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_956_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_ks_935_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_vs_936_);
v___x_941_ = v_reuseFailAlloc_955_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v_newNode_942_; uint8_t v___y_944_; size_t v___x_950_; uint8_t v___x_951_; 
v_newNode_942_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(v___x_941_, v_x_887_, v_x_888_);
v___x_950_ = ((size_t)7ULL);
v___x_951_ = lean_usize_dec_le(v___x_950_, v_x_886_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
v___x_952_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_942_);
v___x_953_ = lean_unsigned_to_nat(4u);
v___x_954_ = lean_nat_dec_lt(v___x_952_, v___x_953_);
lean_dec(v___x_952_);
v___y_944_ = v___x_954_;
goto v___jp_943_;
}
else
{
v___y_944_ = v___x_951_;
goto v___jp_943_;
}
v___jp_943_:
{
if (v___y_944_ == 0)
{
lean_object* v_ks_945_; lean_object* v_vs_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_ks_945_ = lean_ctor_get(v_newNode_942_, 0);
lean_inc_ref(v_ks_945_);
v_vs_946_ = lean_ctor_get(v_newNode_942_, 1);
lean_inc_ref(v_vs_946_);
lean_dec_ref(v_newNode_942_);
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0);
v___x_949_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_x_886_, v_ks_945_, v_vs_946_, v___x_947_, v___x_948_);
lean_dec_ref(v_vs_946_);
lean_dec_ref(v_ks_945_);
return v___x_949_;
}
else
{
return v_newNode_942_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(size_t v_depth_957_, lean_object* v_keys_958_, lean_object* v_vals_959_, lean_object* v_i_960_, lean_object* v_entries_961_){
_start:
{
lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_962_ = lean_array_get_size(v_keys_958_);
v___x_963_ = lean_nat_dec_lt(v_i_960_, v___x_962_);
if (v___x_963_ == 0)
{
lean_dec(v_i_960_);
return v_entries_961_;
}
else
{
lean_object* v_k_964_; lean_object* v_v_965_; uint64_t v___x_966_; size_t v_h_967_; size_t v___x_968_; lean_object* v___x_969_; size_t v___x_970_; size_t v___x_971_; size_t v___x_972_; size_t v_h_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_k_964_ = lean_array_fget_borrowed(v_keys_958_, v_i_960_);
v_v_965_ = lean_array_fget_borrowed(v_vals_959_, v_i_960_);
v___x_966_ = l_Lean_Expr_hash(v_k_964_);
v_h_967_ = lean_uint64_to_usize(v___x_966_);
v___x_968_ = ((size_t)5ULL);
v___x_969_ = lean_unsigned_to_nat(1u);
v___x_970_ = ((size_t)1ULL);
v___x_971_ = lean_usize_sub(v_depth_957_, v___x_970_);
v___x_972_ = lean_usize_mul(v___x_968_, v___x_971_);
v_h_973_ = lean_usize_shift_right(v_h_967_, v___x_972_);
v___x_974_ = lean_nat_add(v_i_960_, v___x_969_);
lean_dec(v_i_960_);
lean_inc(v_v_965_);
lean_inc(v_k_964_);
v___x_975_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_entries_961_, v_h_973_, v_depth_957_, v_k_964_, v_v_965_);
v_i_960_ = v___x_974_;
v_entries_961_ = v___x_975_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_depth_977_, lean_object* v_keys_978_, lean_object* v_vals_979_, lean_object* v_i_980_, lean_object* v_entries_981_){
_start:
{
size_t v_depth_boxed_982_; lean_object* v_res_983_; 
v_depth_boxed_982_ = lean_unbox_usize(v_depth_977_);
lean_dec(v_depth_977_);
v_res_983_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_depth_boxed_982_, v_keys_978_, v_vals_979_, v_i_980_, v_entries_981_);
lean_dec_ref(v_vals_979_);
lean_dec_ref(v_keys_978_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___boxed(lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_x_987_, lean_object* v_x_988_){
_start:
{
size_t v_x_15930__boxed_989_; size_t v_x_15931__boxed_990_; lean_object* v_res_991_; 
v_x_15930__boxed_989_ = lean_unbox_usize(v_x_985_);
lean_dec(v_x_985_);
v_x_15931__boxed_990_ = lean_unbox_usize(v_x_986_);
lean_dec(v_x_986_);
v_res_991_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_984_, v_x_15930__boxed_989_, v_x_15931__boxed_990_, v_x_987_, v_x_988_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(lean_object* v_x_992_, lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
uint64_t v___x_995_; size_t v___x_996_; size_t v___x_997_; lean_object* v___x_998_; 
v___x_995_ = l_Lean_Expr_hash(v_x_993_);
v___x_996_ = lean_uint64_to_usize(v___x_995_);
v___x_997_ = ((size_t)1ULL);
v___x_998_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_992_, v___x_996_, v___x_997_, v_x_993_, v_x_994_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(uint8_t v_shouldElimFunDecls_1001_, lean_object* v_i_1002_, lean_object* v_as_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = lean_array_get_size(v_as_1003_);
v___x_1011_ = lean_nat_dec_lt(v_i_1002_, v___x_1010_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; 
lean_dec(v_i_1002_);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v_as_1003_);
return v___x_1012_;
}
else
{
lean_object* v_a_1013_; lean_object* v_a_1015_; 
v_a_1013_ = lean_array_fget_borrowed(v_as_1003_, v_i_1002_);
if (lean_obj_tag(v_a_1013_) == 0)
{
lean_object* v_params_1026_; lean_object* v_code_1027_; lean_object* v___x_1028_; lean_object* v_map_1029_; uint8_t v___x_1030_; uint8_t v___x_1031_; lean_object* v_a_1033_; lean_object* v___x_1052_; 
v_params_1026_ = lean_ctor_get(v_a_1013_, 1);
v_code_1027_ = lean_ctor_get(v_a_1013_, 2);
v___x_1028_ = lean_st_ref_get(v___y_1004_);
v_map_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc_ref(v_map_1029_);
lean_dec(v___x_1028_);
v___x_1030_ = 0;
v___x_1031_ = 0;
lean_inc_ref(v_params_1026_);
v___x_1052_ = l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(v___x_1030_, v___x_1031_, v_params_1026_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref(v___x_1052_);
lean_inc_ref(v_code_1027_);
v___x_1054_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1001_, v_code_1027_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1072_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1072_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1072_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
lean_inc_ref(v_a_1013_);
v___x_1059_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v___x_1030_, v_a_1013_, v_a_1053_, v_a_1055_);
lean_inc_ref(v___x_1059_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set_tag(v___x_1057_, 1);
lean_ctor_set(v___x_1057_, 0, v___x_1059_);
v___x_1061_ = v___x_1057_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; 
v___x_1062_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_1004_, v_map_1029_, v___x_1061_);
lean_dec_ref(v___x_1061_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_dec_ref(v___x_1062_);
v_a_1015_ = v___x_1059_;
goto v___jp_1014_;
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec_ref(v___x_1059_);
lean_dec_ref(v_as_1003_);
lean_dec(v_i_1002_);
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
}
else
{
lean_object* v_a_1073_; 
lean_dec(v_a_1053_);
lean_dec_ref(v_as_1003_);
lean_dec(v_i_1002_);
v_a_1073_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1073_);
lean_dec_ref(v___x_1054_);
v_a_1033_ = v_a_1073_;
goto v___jp_1032_;
}
}
else
{
lean_object* v_a_1074_; 
lean_dec_ref(v_as_1003_);
lean_dec(v_i_1002_);
v_a_1074_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1074_);
lean_dec_ref(v___x_1052_);
v_a_1033_ = v_a_1074_;
goto v___jp_1032_;
}
v___jp_1032_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_box(0);
v___x_1035_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_1004_, v_map_1029_, v___x_1034_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; 
v_unused_1043_ = lean_ctor_get(v___x_1035_, 0);
lean_dec(v_unused_1043_);
v___x_1037_ = v___x_1035_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_dec(v___x_1035_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 1);
lean_ctor_set(v___x_1037_, 0, v_a_1033_);
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1033_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec_ref(v_a_1033_);
v_a_1044_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1035_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1035_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
else
{
lean_object* v_code_1075_; lean_object* v___x_1076_; lean_object* v_map_1077_; lean_object* v___x_1078_; 
v_code_1075_ = lean_ctor_get(v_a_1013_, 0);
v___x_1076_ = lean_st_ref_get(v___y_1004_);
v_map_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc_ref(v_map_1077_);
lean_dec(v___x_1076_);
lean_inc_ref(v_code_1075_);
v___x_1078_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1001_, v_code_1075_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1096_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1096_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1096_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
lean_inc_ref(v_a_1013_);
v___x_1083_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1013_, v_a_1079_);
lean_inc_ref(v___x_1083_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set_tag(v___x_1081_, 1);
lean_ctor_set(v___x_1081_, 0, v___x_1083_);
v___x_1085_ = v___x_1081_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; 
v___x_1086_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_1004_, v_map_1077_, v___x_1085_);
lean_dec_ref(v___x_1085_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_dec_ref(v___x_1086_);
v_a_1015_ = v___x_1083_;
goto v___jp_1014_;
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v___x_1083_);
lean_dec_ref(v_as_1003_);
lean_dec(v_i_1002_);
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec_ref(v_as_1003_);
lean_dec(v_i_1002_);
v_a_1097_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1097_);
lean_dec_ref(v___x_1078_);
v___x_1098_ = lean_box(0);
v___x_1099_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_1004_, v_map_1077_, v___x_1098_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1106_ == 0)
{
lean_object* v_unused_1107_; 
v_unused_1107_ = lean_ctor_get(v___x_1099_, 0);
lean_dec(v_unused_1107_);
v___x_1101_ = v___x_1099_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_dec(v___x_1099_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set_tag(v___x_1101_, 1);
lean_ctor_set(v___x_1101_, 0, v_a_1097_);
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1097_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v_a_1097_);
v_a_1108_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1099_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1099_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
v___jp_1014_:
{
size_t v___x_1016_; size_t v___x_1017_; uint8_t v___x_1018_; 
v___x_1016_ = lean_ptr_addr(v_a_1013_);
v___x_1017_ = lean_ptr_addr(v_a_1015_);
v___x_1018_ = lean_usize_dec_eq(v___x_1016_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = lean_unsigned_to_nat(1u);
v___x_1020_ = lean_nat_add(v_i_1002_, v___x_1019_);
v___x_1021_ = lean_array_fset(v_as_1003_, v_i_1002_, v_a_1015_);
lean_dec(v_i_1002_);
v_i_1002_ = v___x_1020_;
v_as_1003_ = v___x_1021_;
goto _start;
}
else
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_dec_ref(v_a_1015_);
v___x_1023_ = lean_unsigned_to_nat(1u);
v___x_1024_ = lean_nat_add(v_i_1002_, v___x_1023_);
lean_dec(v_i_1002_);
v_i_1002_ = v___x_1024_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(uint8_t v_shouldElimFunDecls_1116_, lean_object* v_code_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
switch(lean_obj_tag(v_code_1117_))
{
case 0:
{
lean_object* v_decl_1124_; lean_object* v_k_1125_; uint8_t v___x_1126_; uint8_t v___x_1127_; lean_object* v___x_1128_; 
v_decl_1124_ = lean_ctor_get(v_code_1117_, 0);
v_k_1125_ = lean_ctor_get(v_code_1117_, 1);
v___x_1126_ = 0;
v___x_1127_ = 0;
lean_inc_ref(v_decl_1124_);
v___x_1128_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v___x_1126_, v___x_1127_, v_decl_1124_, v_a_1118_, v_a_1120_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v_fvarId_1130_; lean_object* v_value_1131_; lean_object* v___x_1132_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref(v___x_1128_);
v_fvarId_1130_ = lean_ctor_get(v_a_1129_, 0);
v_value_1131_ = lean_ctor_get(v_a_1129_, 3);
lean_inc(v_value_1131_);
v___x_1132_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(v_value_1131_, v_a_1122_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; uint8_t v___x_1134_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = lean_unbox(v_a_1133_);
lean_dec(v_a_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v_map_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1135_ = lean_st_ref_get(v_a_1118_);
v_map_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc_ref(v_map_1136_);
lean_dec(v___x_1135_);
lean_inc(v_value_1131_);
v___x_1137_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v___x_1126_, v_value_1131_);
v___x_1138_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_map_1136_, v___x_1137_);
lean_dec_ref(v_map_1136_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v___x_1139_; lean_object* v_map_1140_; lean_object* v_subst_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1179_; 
v___x_1139_ = lean_st_ref_take(v_a_1118_);
v_map_1140_ = lean_ctor_get(v___x_1139_, 0);
v_subst_1141_ = lean_ctor_get(v___x_1139_, 1);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1143_ = v___x_1139_;
v_isShared_1144_ = v_isSharedCheck_1179_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_subst_1141_);
lean_inc(v_map_1140_);
lean_dec(v___x_1139_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1179_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
lean_inc(v_fvarId_1130_);
v___x_1145_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_map_1140_, v___x_1137_, v_fvarId_1130_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v___x_1145_);
v___x_1147_ = v___x_1143_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_subst_1141_);
v___x_1147_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = lean_st_ref_set(v_a_1118_, v___x_1147_);
lean_inc_ref(v_k_1125_);
v___x_1149_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1116_, v_k_1125_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1177_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1177_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1177_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
uint8_t v___y_1155_; size_t v___x_1171_; size_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1171_ = lean_ptr_addr(v_k_1125_);
v___x_1172_ = lean_ptr_addr(v_a_1150_);
v___x_1173_ = lean_usize_dec_eq(v___x_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
v___y_1155_ = v___x_1173_;
goto v___jp_1154_;
}
else
{
size_t v___x_1174_; size_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1174_ = lean_ptr_addr(v_decl_1124_);
v___x_1175_ = lean_ptr_addr(v_a_1129_);
v___x_1176_ = lean_usize_dec_eq(v___x_1174_, v___x_1175_);
v___y_1155_ = v___x_1176_;
goto v___jp_1154_;
}
v___jp_1154_:
{
if (v___y_1155_ == 0)
{
lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1165_; 
v_isSharedCheck_1165_ = !lean_is_exclusive(v_code_1117_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; lean_object* v_unused_1167_; 
v_unused_1166_ = lean_ctor_get(v_code_1117_, 1);
lean_dec(v_unused_1166_);
v_unused_1167_ = lean_ctor_get(v_code_1117_, 0);
lean_dec(v_unused_1167_);
v___x_1157_ = v_code_1117_;
v_isShared_1158_ = v_isSharedCheck_1165_;
goto v_resetjp_1156_;
}
else
{
lean_dec(v_code_1117_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1165_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 1, v_a_1150_);
lean_ctor_set(v___x_1157_, 0, v_a_1129_);
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1129_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_a_1150_);
v___x_1160_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1162_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1160_);
v___x_1162_ = v___x_1152_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
else
{
lean_object* v___x_1169_; 
lean_dec(v_a_1150_);
lean_dec(v_a_1129_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v_code_1117_);
v___x_1169_ = v___x_1152_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_code_1117_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
else
{
lean_dec(v_a_1129_);
lean_dec_ref(v_code_1117_);
return v___x_1149_;
}
}
}
}
else
{
lean_object* v_val_1180_; lean_object* v___x_1181_; 
lean_inc_ref(v_k_1125_);
lean_dec_ref(v___x_1137_);
lean_dec_ref(v_code_1117_);
v_val_1180_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_val_1180_);
lean_dec_ref(v___x_1138_);
v___x_1181_ = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(v_a_1129_, v_val_1180_, v_a_1118_, v_a_1120_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_dec_ref(v___x_1181_);
v_code_1117_ = v_k_1125_;
goto _start;
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_dec_ref(v_k_1125_);
v_a_1183_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1181_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1181_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
else
{
lean_object* v___x_1191_; 
lean_inc_ref(v_k_1125_);
v___x_1191_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1116_, v_k_1125_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1219_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1219_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1219_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
uint8_t v___y_1197_; size_t v___x_1213_; size_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1213_ = lean_ptr_addr(v_k_1125_);
v___x_1214_ = lean_ptr_addr(v_a_1192_);
v___x_1215_ = lean_usize_dec_eq(v___x_1213_, v___x_1214_);
if (v___x_1215_ == 0)
{
v___y_1197_ = v___x_1215_;
goto v___jp_1196_;
}
else
{
size_t v___x_1216_; size_t v___x_1217_; uint8_t v___x_1218_; 
v___x_1216_ = lean_ptr_addr(v_decl_1124_);
v___x_1217_ = lean_ptr_addr(v_a_1129_);
v___x_1218_ = lean_usize_dec_eq(v___x_1216_, v___x_1217_);
v___y_1197_ = v___x_1218_;
goto v___jp_1196_;
}
v___jp_1196_:
{
if (v___y_1197_ == 0)
{
lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1207_; 
v_isSharedCheck_1207_ = !lean_is_exclusive(v_code_1117_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; lean_object* v_unused_1209_; 
v_unused_1208_ = lean_ctor_get(v_code_1117_, 1);
lean_dec(v_unused_1208_);
v_unused_1209_ = lean_ctor_get(v_code_1117_, 0);
lean_dec(v_unused_1209_);
v___x_1199_ = v_code_1117_;
v_isShared_1200_ = v_isSharedCheck_1207_;
goto v_resetjp_1198_;
}
else
{
lean_dec(v_code_1117_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1207_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 1, v_a_1192_);
lean_ctor_set(v___x_1199_, 0, v_a_1129_);
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1129_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_a_1192_);
v___x_1202_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1204_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1202_);
v___x_1204_ = v___x_1194_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
else
{
lean_object* v___x_1211_; 
lean_dec(v_a_1192_);
lean_dec(v_a_1129_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v_code_1117_);
v___x_1211_ = v___x_1194_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_code_1117_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
else
{
lean_dec(v_a_1129_);
lean_dec_ref(v_code_1117_);
return v___x_1191_;
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec(v_a_1129_);
lean_dec_ref(v_code_1117_);
v_a_1220_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1132_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1132_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec_ref(v_code_1117_);
v_a_1228_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1128_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1128_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
case 1:
{
lean_object* v_decl_1236_; lean_object* v_k_1237_; lean_object* v___x_1238_; 
v_decl_1236_ = lean_ctor_get(v_code_1117_, 0);
v_k_1237_ = lean_ctor_get(v_code_1117_, 1);
lean_inc_ref(v_decl_1236_);
v___x_1238_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_1116_, v_decl_1236_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1238_) == 0)
{
if (v_shouldElimFunDecls_1116_ == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1240_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref(v___x_1238_);
lean_inc_ref(v_k_1237_);
v___x_1240_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1116_, v_k_1237_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1268_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1268_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1268_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
uint8_t v___y_1246_; size_t v___x_1262_; size_t v___x_1263_; uint8_t v___x_1264_; 
v___x_1262_ = lean_ptr_addr(v_k_1237_);
v___x_1263_ = lean_ptr_addr(v_a_1241_);
v___x_1264_ = lean_usize_dec_eq(v___x_1262_, v___x_1263_);
if (v___x_1264_ == 0)
{
v___y_1246_ = v___x_1264_;
goto v___jp_1245_;
}
else
{
size_t v___x_1265_; size_t v___x_1266_; uint8_t v___x_1267_; 
v___x_1265_ = lean_ptr_addr(v_decl_1236_);
v___x_1266_ = lean_ptr_addr(v_a_1239_);
v___x_1267_ = lean_usize_dec_eq(v___x_1265_, v___x_1266_);
v___y_1246_ = v___x_1267_;
goto v___jp_1245_;
}
v___jp_1245_:
{
if (v___y_1246_ == 0)
{
lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1256_; 
v_isSharedCheck_1256_ = !lean_is_exclusive(v_code_1117_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; lean_object* v_unused_1258_; 
v_unused_1257_ = lean_ctor_get(v_code_1117_, 1);
lean_dec(v_unused_1257_);
v_unused_1258_ = lean_ctor_get(v_code_1117_, 0);
lean_dec(v_unused_1258_);
v___x_1248_ = v_code_1117_;
v_isShared_1249_ = v_isSharedCheck_1256_;
goto v_resetjp_1247_;
}
else
{
lean_dec(v_code_1117_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1256_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 1, v_a_1241_);
lean_ctor_set(v___x_1248_, 0, v_a_1239_);
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1239_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_a_1241_);
v___x_1251_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1253_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1251_);
v___x_1253_ = v___x_1243_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
else
{
lean_object* v___x_1260_; 
lean_dec(v_a_1241_);
lean_dec(v_a_1239_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v_code_1117_);
v___x_1260_ = v___x_1243_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_code_1117_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
else
{
lean_dec(v_a_1239_);
lean_dec_ref(v_code_1117_);
return v___x_1240_;
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1270_; lean_object* v_map_1271_; uint8_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_a_1269_ = lean_ctor_get(v___x_1238_, 0);
lean_inc_n(v_a_1269_, 2);
lean_dec_ref(v___x_1238_);
v___x_1270_ = lean_st_ref_get(v_a_1118_);
v_map_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc_ref(v_map_1271_);
lean_dec(v___x_1270_);
v___x_1272_ = 0;
v___x_1273_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___closed__0));
v___x_1274_ = l_Lean_Compiler_LCNF_FunDecl_toExpr(v___x_1272_, v_a_1269_, v___x_1273_);
v___x_1275_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_map_1271_, v___x_1274_);
lean_dec_ref(v_map_1271_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_fvarId_1276_; lean_object* v___x_1277_; lean_object* v_map_1278_; lean_object* v_subst_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1317_; 
v_fvarId_1276_ = lean_ctor_get(v_a_1269_, 0);
v___x_1277_ = lean_st_ref_take(v_a_1118_);
v_map_1278_ = lean_ctor_get(v___x_1277_, 0);
v_subst_1279_ = lean_ctor_get(v___x_1277_, 1);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1281_ = v___x_1277_;
v_isShared_1282_ = v_isSharedCheck_1317_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_subst_1279_);
lean_inc(v_map_1278_);
lean_dec(v___x_1277_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1317_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; lean_object* v___x_1285_; 
lean_inc(v_fvarId_1276_);
v___x_1283_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_map_1278_, v___x_1274_, v_fvarId_1276_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1283_);
v___x_1285_ = v___x_1281_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_subst_1279_);
v___x_1285_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = lean_st_ref_set(v_a_1118_, v___x_1285_);
lean_inc_ref(v_k_1237_);
v___x_1287_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1116_, v_k_1237_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1315_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1315_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1315_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
uint8_t v___y_1293_; size_t v___x_1309_; size_t v___x_1310_; uint8_t v___x_1311_; 
v___x_1309_ = lean_ptr_addr(v_k_1237_);
v___x_1310_ = lean_ptr_addr(v_a_1288_);
v___x_1311_ = lean_usize_dec_eq(v___x_1309_, v___x_1310_);
if (v___x_1311_ == 0)
{
v___y_1293_ = v___x_1311_;
goto v___jp_1292_;
}
else
{
size_t v___x_1312_; size_t v___x_1313_; uint8_t v___x_1314_; 
v___x_1312_ = lean_ptr_addr(v_decl_1236_);
v___x_1313_ = lean_ptr_addr(v_a_1269_);
v___x_1314_ = lean_usize_dec_eq(v___x_1312_, v___x_1313_);
v___y_1293_ = v___x_1314_;
goto v___jp_1292_;
}
v___jp_1292_:
{
if (v___y_1293_ == 0)
{
lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1303_; 
v_isSharedCheck_1303_ = !lean_is_exclusive(v_code_1117_);
if (v_isSharedCheck_1303_ == 0)
{
lean_object* v_unused_1304_; lean_object* v_unused_1305_; 
v_unused_1304_ = lean_ctor_get(v_code_1117_, 1);
lean_dec(v_unused_1304_);
v_unused_1305_ = lean_ctor_get(v_code_1117_, 0);
lean_dec(v_unused_1305_);
v___x_1295_ = v_code_1117_;
v_isShared_1296_ = v_isSharedCheck_1303_;
goto v_resetjp_1294_;
}
else
{
lean_dec(v_code_1117_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1303_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 1, v_a_1288_);
lean_ctor_set(v___x_1295_, 0, v_a_1269_);
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1269_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_a_1288_);
v___x_1298_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_object* v___x_1300_; 
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1298_);
v___x_1300_ = v___x_1290_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
else
{
lean_object* v___x_1307_; 
lean_dec(v_a_1288_);
lean_dec(v_a_1269_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v_code_1117_);
v___x_1307_ = v___x_1290_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_code_1117_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
else
{
lean_dec(v_a_1269_);
lean_dec_ref(v_code_1117_);
return v___x_1287_;
}
}
}
}
else
{
lean_object* v_val_1318_; lean_object* v___x_1319_; 
lean_inc_ref(v_k_1237_);
lean_dec_ref(v___x_1274_);
lean_dec_ref(v_code_1117_);
v_val_1318_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_val_1318_);
lean_dec_ref(v___x_1275_);
v___x_1319_ = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(v_a_1269_, v_val_1318_, v_a_1118_, v_a_1120_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_dec_ref(v___x_1319_);
v_code_1117_ = v_k_1237_;
goto _start;
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec_ref(v_k_1237_);
v_a_1321_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1319_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1319_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec_ref(v_code_1117_);
v_a_1329_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1238_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1238_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
case 2:
{
lean_object* v_decl_1337_; lean_object* v_k_1338_; lean_object* v___x_1339_; 
v_decl_1337_ = lean_ctor_get(v_code_1117_, 0);
v_k_1338_ = lean_ctor_get(v_code_1117_, 1);
lean_inc_ref(v_decl_1337_);
v___x_1339_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_1116_, v_decl_1337_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1341_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref(v___x_1339_);
lean_inc_ref(v_k_1338_);
v___x_1341_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1116_, v_k_1338_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1369_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1369_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1369_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
uint8_t v___y_1347_; size_t v___x_1363_; size_t v___x_1364_; uint8_t v___x_1365_; 
v___x_1363_ = lean_ptr_addr(v_k_1338_);
v___x_1364_ = lean_ptr_addr(v_a_1342_);
v___x_1365_ = lean_usize_dec_eq(v___x_1363_, v___x_1364_);
if (v___x_1365_ == 0)
{
v___y_1347_ = v___x_1365_;
goto v___jp_1346_;
}
else
{
size_t v___x_1366_; size_t v___x_1367_; uint8_t v___x_1368_; 
v___x_1366_ = lean_ptr_addr(v_decl_1337_);
v___x_1367_ = lean_ptr_addr(v_a_1340_);
v___x_1368_ = lean_usize_dec_eq(v___x_1366_, v___x_1367_);
v___y_1347_ = v___x_1368_;
goto v___jp_1346_;
}
v___jp_1346_:
{
if (v___y_1347_ == 0)
{
lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1357_; 
v_isSharedCheck_1357_ = !lean_is_exclusive(v_code_1117_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; lean_object* v_unused_1359_; 
v_unused_1358_ = lean_ctor_get(v_code_1117_, 1);
lean_dec(v_unused_1358_);
v_unused_1359_ = lean_ctor_get(v_code_1117_, 0);
lean_dec(v_unused_1359_);
v___x_1349_ = v_code_1117_;
v_isShared_1350_ = v_isSharedCheck_1357_;
goto v_resetjp_1348_;
}
else
{
lean_dec(v_code_1117_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1357_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 1, v_a_1342_);
lean_ctor_set(v___x_1349_, 0, v_a_1340_);
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1340_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_a_1342_);
v___x_1352_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1352_);
v___x_1354_ = v___x_1344_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_object* v___x_1361_; 
lean_dec(v_a_1342_);
lean_dec(v_a_1340_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v_code_1117_);
v___x_1361_ = v___x_1344_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_code_1117_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
else
{
lean_dec(v_a_1340_);
lean_dec_ref(v_code_1117_);
return v___x_1341_;
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v_code_1117_);
v_a_1370_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1339_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1339_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_1378_; lean_object* v_args_1379_; lean_object* v___x_1380_; lean_object* v_subst_1381_; uint8_t v___x_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; 
v_fvarId_1378_ = lean_ctor_get(v_code_1117_, 0);
v_args_1379_ = lean_ctor_get(v_code_1117_, 1);
v___x_1380_ = lean_st_ref_get(v_a_1118_);
v_subst_1381_ = lean_ctor_get(v___x_1380_, 1);
lean_inc_ref(v_subst_1381_);
lean_dec(v___x_1380_);
v___x_1382_ = 0;
v___x_1383_ = 0;
lean_inc(v_fvarId_1378_);
v___x_1384_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1381_, v_fvarId_1378_, v___x_1383_);
lean_dec_ref(v_subst_1381_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_fvarId_1385_; lean_object* v___x_1386_; 
v_fvarId_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_fvarId_1385_);
lean_dec_ref(v___x_1384_);
lean_inc_ref(v_args_1379_);
v___x_1386_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v___x_1382_, v___x_1383_, v_args_1379_, v_a_1118_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1412_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1412_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1412_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
uint8_t v___y_1392_; uint8_t v___x_1408_; 
v___x_1408_ = l_Lean_instBEqFVarId_beq(v_fvarId_1378_, v_fvarId_1385_);
if (v___x_1408_ == 0)
{
v___y_1392_ = v___x_1408_;
goto v___jp_1391_;
}
else
{
size_t v___x_1409_; size_t v___x_1410_; uint8_t v___x_1411_; 
v___x_1409_ = lean_ptr_addr(v_args_1379_);
v___x_1410_ = lean_ptr_addr(v_a_1387_);
v___x_1411_ = lean_usize_dec_eq(v___x_1409_, v___x_1410_);
v___y_1392_ = v___x_1411_;
goto v___jp_1391_;
}
v___jp_1391_:
{
if (v___y_1392_ == 0)
{
lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1402_; 
v_isSharedCheck_1402_ = !lean_is_exclusive(v_code_1117_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; lean_object* v_unused_1404_; 
v_unused_1403_ = lean_ctor_get(v_code_1117_, 1);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_code_1117_, 0);
lean_dec(v_unused_1404_);
v___x_1394_ = v_code_1117_;
v_isShared_1395_ = v_isSharedCheck_1402_;
goto v_resetjp_1393_;
}
else
{
lean_dec(v_code_1117_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1402_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 1, v_a_1387_);
lean_ctor_set(v___x_1394_, 0, v_fvarId_1385_);
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_fvarId_1385_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_a_1387_);
v___x_1397_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1399_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1397_);
v___x_1399_ = v___x_1389_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
else
{
lean_object* v___x_1406_; 
lean_dec(v_a_1387_);
lean_dec(v_fvarId_1385_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v_code_1117_);
v___x_1406_ = v___x_1389_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_code_1117_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec(v_fvarId_1385_);
lean_dec_ref(v_code_1117_);
v_a_1413_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1386_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1386_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
else
{
lean_object* v___x_1421_; 
lean_dec_ref(v_code_1117_);
v___x_1421_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1382_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
return v___x_1421_;
}
}
case 4:
{
lean_object* v_cases_1422_; lean_object* v_typeName_1423_; lean_object* v_resultType_1424_; lean_object* v_discr_1425_; lean_object* v_alts_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1479_; 
v_cases_1422_ = lean_ctor_get(v_code_1117_, 0);
lean_inc_ref(v_cases_1422_);
v_typeName_1423_ = lean_ctor_get(v_cases_1422_, 0);
v_resultType_1424_ = lean_ctor_get(v_cases_1422_, 1);
v_discr_1425_ = lean_ctor_get(v_cases_1422_, 2);
v_alts_1426_ = lean_ctor_get(v_cases_1422_, 3);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_cases_1422_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1428_ = v_cases_1422_;
v_isShared_1429_ = v_isSharedCheck_1479_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_alts_1426_);
lean_inc(v_discr_1425_);
lean_inc(v_resultType_1424_);
lean_inc(v_typeName_1423_);
lean_dec(v_cases_1422_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1479_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v_subst_1431_; uint8_t v___x_1432_; uint8_t v___x_1433_; lean_object* v___x_1434_; 
v___x_1430_ = lean_st_ref_get(v_a_1118_);
v_subst_1431_ = lean_ctor_get(v___x_1430_, 1);
lean_inc_ref(v_subst_1431_);
lean_dec(v___x_1430_);
v___x_1432_ = 0;
v___x_1433_ = 0;
lean_inc(v_discr_1425_);
v___x_1434_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1431_, v_discr_1425_, v___x_1433_);
lean_dec_ref(v_subst_1431_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_fvarId_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1477_; 
v_fvarId_1435_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1437_ = v___x_1434_;
v_isShared_1438_ = v_isSharedCheck_1477_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_fvarId_1435_);
lean_dec(v___x_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1477_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1439_ = lean_st_ref_get(v_a_1118_);
v___x_1440_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1426_);
v___x_1441_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(v_shouldElimFunDecls_1116_, v___x_1440_, v_alts_1426_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1468_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1468_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1468_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v_subst_1446_; lean_object* v___x_1447_; uint8_t v___y_1459_; size_t v___x_1462_; size_t v___x_1463_; uint8_t v___x_1464_; 
v_subst_1446_ = lean_ctor_get(v___x_1439_, 1);
lean_inc_ref(v_subst_1446_);
lean_dec(v___x_1439_);
lean_inc_ref(v_resultType_1424_);
v___x_1447_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_1432_, v_subst_1446_, v___x_1433_, v_resultType_1424_);
lean_dec_ref(v_subst_1446_);
v___x_1462_ = lean_ptr_addr(v_alts_1426_);
lean_dec_ref(v_alts_1426_);
v___x_1463_ = lean_ptr_addr(v_a_1442_);
v___x_1464_ = lean_usize_dec_eq(v___x_1462_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_dec_ref(v_resultType_1424_);
v___y_1459_ = v___x_1464_;
goto v___jp_1458_;
}
else
{
size_t v___x_1465_; size_t v___x_1466_; uint8_t v___x_1467_; 
v___x_1465_ = lean_ptr_addr(v_resultType_1424_);
lean_dec_ref(v_resultType_1424_);
v___x_1466_ = lean_ptr_addr(v___x_1447_);
v___x_1467_ = lean_usize_dec_eq(v___x_1465_, v___x_1466_);
v___y_1459_ = v___x_1467_;
goto v___jp_1458_;
}
v___jp_1448_:
{
lean_object* v___x_1450_; 
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 3, v_a_1442_);
lean_ctor_set(v___x_1428_, 2, v_fvarId_1435_);
lean_ctor_set(v___x_1428_, 1, v___x_1447_);
v___x_1450_ = v___x_1428_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_typeName_1423_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_fvarId_1435_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v_a_1442_);
v___x_1450_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set_tag(v___x_1437_, 4);
lean_ctor_set(v___x_1437_, 0, v___x_1450_);
v___x_1452_ = v___x_1437_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1454_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1452_);
v___x_1454_ = v___x_1444_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1452_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
v___jp_1458_:
{
if (v___y_1459_ == 0)
{
lean_dec(v_discr_1425_);
lean_dec_ref(v_code_1117_);
goto v___jp_1448_;
}
else
{
uint8_t v___x_1460_; 
v___x_1460_ = l_Lean_instBEqFVarId_beq(v_discr_1425_, v_fvarId_1435_);
lean_dec(v_discr_1425_);
if (v___x_1460_ == 0)
{
lean_dec_ref(v_code_1117_);
goto v___jp_1448_;
}
else
{
lean_object* v___x_1461_; 
lean_dec_ref(v___x_1447_);
lean_del_object(v___x_1444_);
lean_dec(v_a_1442_);
lean_del_object(v___x_1437_);
lean_dec(v_fvarId_1435_);
lean_del_object(v___x_1428_);
lean_dec(v_typeName_1423_);
v___x_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1461_, 0, v_code_1117_);
return v___x_1461_;
}
}
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec(v___x_1439_);
lean_del_object(v___x_1437_);
lean_dec(v_fvarId_1435_);
lean_del_object(v___x_1428_);
lean_dec_ref(v_alts_1426_);
lean_dec(v_discr_1425_);
lean_dec_ref(v_resultType_1424_);
lean_dec(v_typeName_1423_);
lean_dec_ref(v_code_1117_);
v_a_1469_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1441_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1441_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
else
{
lean_object* v___x_1478_; 
lean_del_object(v___x_1428_);
lean_dec_ref(v_alts_1426_);
lean_dec(v_discr_1425_);
lean_dec_ref(v_resultType_1424_);
lean_dec(v_typeName_1423_);
lean_dec_ref(v_code_1117_);
v___x_1478_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1432_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
return v___x_1478_;
}
}
}
case 5:
{
lean_object* v_fvarId_1480_; lean_object* v___x_1481_; lean_object* v_subst_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; 
v_fvarId_1480_ = lean_ctor_get(v_code_1117_, 0);
v___x_1481_ = lean_st_ref_get(v_a_1118_);
v_subst_1482_ = lean_ctor_get(v___x_1481_, 1);
lean_inc_ref(v_subst_1482_);
lean_dec(v___x_1481_);
v___x_1483_ = 0;
lean_inc(v_fvarId_1480_);
v___x_1484_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1482_, v_fvarId_1480_, v___x_1483_);
lean_dec_ref(v_subst_1482_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_fvarId_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1504_; 
v_fvarId_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1504_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_fvarId_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1504_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
uint8_t v___x_1489_; 
v___x_1489_ = l_Lean_instBEqFVarId_beq(v_fvarId_1480_, v_fvarId_1485_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1499_; 
v_isSharedCheck_1499_ = !lean_is_exclusive(v_code_1117_);
if (v_isSharedCheck_1499_ == 0)
{
lean_object* v_unused_1500_; 
v_unused_1500_ = lean_ctor_get(v_code_1117_, 0);
lean_dec(v_unused_1500_);
v___x_1491_ = v_code_1117_;
v_isShared_1492_ = v_isSharedCheck_1499_;
goto v_resetjp_1490_;
}
else
{
lean_dec(v_code_1117_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1499_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v_fvarId_1485_);
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_fvarId_1485_);
v___x_1494_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1496_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1494_);
v___x_1496_ = v___x_1487_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
else
{
lean_object* v___x_1502_; 
lean_dec(v_fvarId_1485_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v_code_1117_);
v___x_1502_ = v___x_1487_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_code_1117_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
else
{
uint8_t v___x_1505_; lean_object* v___x_1506_; 
lean_dec_ref(v_code_1117_);
v___x_1505_ = 0;
v___x_1506_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1505_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
return v___x_1506_;
}
}
default: 
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1507_, 0, v_code_1117_);
return v___x_1507_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(uint8_t v_shouldElimFunDecls_1508_, lean_object* v_decl_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v_params_1516_; lean_object* v_type_1517_; lean_object* v_value_1518_; lean_object* v___x_1519_; lean_object* v_subst_1520_; uint8_t v___x_1521_; uint8_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_params_1516_ = lean_ctor_get(v_decl_1509_, 2);
v_type_1517_ = lean_ctor_get(v_decl_1509_, 3);
v_value_1518_ = lean_ctor_get(v_decl_1509_, 4);
v___x_1519_ = lean_st_ref_get(v_a_1510_);
v_subst_1520_ = lean_ctor_get(v___x_1519_, 1);
lean_inc_ref(v_subst_1520_);
lean_dec(v___x_1519_);
v___x_1521_ = 0;
v___x_1522_ = 0;
lean_inc_ref(v_type_1517_);
v___x_1523_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_1521_, v_subst_1520_, v___x_1522_, v_type_1517_);
lean_dec_ref(v_subst_1520_);
lean_inc_ref(v_params_1516_);
v___x_1524_ = l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(v___x_1521_, v___x_1522_, v_params_1516_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1526_; lean_object* v_map_1527_; lean_object* v_r_1528_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref(v___x_1524_);
v___x_1526_ = lean_st_ref_get(v_a_1510_);
v_map_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc_ref(v_map_1527_);
lean_dec(v___x_1526_);
lean_inc_ref(v_value_1518_);
v_r_1528_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1508_, v_value_1518_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v_r_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1546_; 
v_a_1529_ = lean_ctor_get(v_r_1528_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_r_1528_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1531_ = v_r_1528_;
v_isShared_1532_ = v_isSharedCheck_1546_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v_r_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1546_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
lean_inc(v_a_1529_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 1);
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1535_; 
v___x_1535_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(v_a_1510_, v_map_1527_, v___x_1534_);
lean_dec_ref(v___x_1534_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v___x_1536_; 
lean_dec_ref(v___x_1535_);
v___x_1536_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1521_, v_decl_1509_, v___x_1523_, v_a_1525_, v_a_1529_, v_a_1512_);
return v___x_1536_;
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_dec(v_a_1529_);
lean_dec(v_a_1525_);
lean_dec_ref(v___x_1523_);
lean_dec_ref(v_decl_1509_);
v_a_1537_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1535_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1535_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec(v_a_1525_);
lean_dec_ref(v___x_1523_);
lean_dec_ref(v_decl_1509_);
v_a_1547_ = lean_ctor_get(v_r_1528_, 0);
lean_inc(v_a_1547_);
lean_dec_ref(v_r_1528_);
v___x_1548_ = lean_box(0);
v___x_1549_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(v_a_1510_, v_map_1527_, v___x_1548_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1556_ == 0)
{
lean_object* v_unused_1557_; 
v_unused_1557_ = lean_ctor_get(v___x_1549_, 0);
lean_dec(v_unused_1557_);
v___x_1551_ = v___x_1549_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_dec(v___x_1549_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 1);
lean_ctor_set(v___x_1551_, 0, v_a_1547_);
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1547_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec(v_a_1547_);
v_a_1558_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1549_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1549_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref(v___x_1523_);
lean_dec_ref(v_decl_1509_);
v_a_1566_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1524_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1524_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___boxed(lean_object* v_shouldElimFunDecls_1574_, lean_object* v_decl_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1582_; lean_object* v_res_1583_; 
v_shouldElimFunDecls_boxed_1582_ = lean_unbox(v_shouldElimFunDecls_1574_);
v_res_1583_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_boxed_1582_, v_decl_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
lean_dec(v_a_1576_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___boxed(lean_object* v_shouldElimFunDecls_1584_, lean_object* v_i_1585_, lean_object* v_as_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1593_; lean_object* v_res_1594_; 
v_shouldElimFunDecls_boxed_1593_ = lean_unbox(v_shouldElimFunDecls_1584_);
v_res_1594_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(v_shouldElimFunDecls_boxed_1593_, v_i_1585_, v_as_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___boxed(lean_object* v_shouldElimFunDecls_1595_, lean_object* v_code_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1603_; lean_object* v_res_1604_; 
v_shouldElimFunDecls_boxed_1603_ = lean_unbox(v_shouldElimFunDecls_1595_);
v_res_1604_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_boxed_1603_, v_code_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec(v_a_1597_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2(uint8_t v_pu_1605_, uint8_t v_t_1606_, lean_object* v_decl_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v_pu_1605_, v_t_1606_, v_decl_1607_, v___y_1608_, v___y_1610_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___boxed(lean_object* v_pu_1615_, lean_object* v_t_1616_, lean_object* v_decl_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
uint8_t v_pu_boxed_1624_; uint8_t v_t_boxed_1625_; lean_object* v_res_1626_; 
v_pu_boxed_1624_ = lean_unbox(v_pu_1615_);
v_t_boxed_1625_ = lean_unbox(v_t_1616_);
v_res_1626_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2(v_pu_boxed_1624_, v_t_boxed_1625_, v_decl_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5(uint8_t v_pu_1627_, uint8_t v_t_1628_, lean_object* v_args_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v_pu_1627_, v_t_1628_, v_args_1629_, v___y_1630_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___boxed(lean_object* v_pu_1637_, lean_object* v_t_1638_, lean_object* v_args_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
uint8_t v_pu_boxed_1646_; uint8_t v_t_boxed_1647_; lean_object* v_res_1648_; 
v_pu_boxed_1646_ = lean_unbox(v_pu_1637_);
v_t_boxed_1647_ = lean_unbox(v_t_1638_);
v_res_1648_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5(v_pu_boxed_1646_, v_t_boxed_1647_, v_args_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3(lean_object* v_00_u03b2_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_x_1650_, v_x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___boxed(lean_object* v_00_u03b2_1653_, lean_object* v_x_1654_, lean_object* v_x_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3(v_00_u03b2_1653_, v_x_1654_, v_x_1655_);
lean_dec_ref(v_x_1655_);
lean_dec_ref(v_x_1654_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4(lean_object* v_00_u03b2_1657_, lean_object* v_x_1658_, lean_object* v_x_1659_, lean_object* v_x_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_x_1658_, v_x_1659_, v_x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(uint8_t v_pu_1662_, uint8_t v_t_1663_, lean_object* v_i_1664_, lean_object* v_as_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(v_pu_1662_, v_t_1663_, v_i_1664_, v_as_1665_, v___y_1666_, v___y_1668_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___boxed(lean_object* v_pu_1673_, lean_object* v_t_1674_, lean_object* v_i_1675_, lean_object* v_as_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
uint8_t v_pu_boxed_1683_; uint8_t v_t_boxed_1684_; lean_object* v_res_1685_; 
v_pu_boxed_1683_ = lean_unbox(v_pu_1673_);
v_t_boxed_1684_ = lean_unbox(v_t_1674_);
v_res_1685_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(v_pu_boxed_1683_, v_t_boxed_1684_, v_i_1675_, v_as_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4(lean_object* v_00_u03b2_1686_, lean_object* v_x_1687_, size_t v_x_1688_, lean_object* v_x_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_1687_, v_x_1688_, v_x_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1691_, lean_object* v_x_1692_, lean_object* v_x_1693_, lean_object* v_x_1694_){
_start:
{
size_t v_x_17289__boxed_1695_; lean_object* v_res_1696_; 
v_x_17289__boxed_1695_ = lean_unbox_usize(v_x_1693_);
lean_dec(v_x_1693_);
v_res_1696_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4(v_00_u03b2_1691_, v_x_1692_, v_x_17289__boxed_1695_, v_x_1694_);
lean_dec_ref(v_x_1694_);
lean_dec_ref(v_x_1692_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6(lean_object* v_00_u03b2_1697_, lean_object* v_x_1698_, size_t v_x_1699_, size_t v_x_1700_, lean_object* v_x_1701_, lean_object* v_x_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_1698_, v_x_1699_, v_x_1700_, v_x_1701_, v_x_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1704_, lean_object* v_x_1705_, lean_object* v_x_1706_, lean_object* v_x_1707_, lean_object* v_x_1708_, lean_object* v_x_1709_){
_start:
{
size_t v_x_17300__boxed_1710_; size_t v_x_17301__boxed_1711_; lean_object* v_res_1712_; 
v_x_17300__boxed_1710_ = lean_unbox_usize(v_x_1706_);
lean_dec(v_x_1706_);
v_x_17301__boxed_1711_ = lean_unbox_usize(v_x_1707_);
lean_dec(v_x_1707_);
v_res_1712_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6(v_00_u03b2_1704_, v_x_1705_, v_x_17300__boxed_1710_, v_x_17301__boxed_1711_, v_x_1708_, v_x_1709_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1713_, lean_object* v_keys_1714_, lean_object* v_vals_1715_, lean_object* v_heq_1716_, lean_object* v_i_1717_, lean_object* v_k_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(v_keys_1714_, v_vals_1715_, v_i_1717_, v_k_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1720_, lean_object* v_keys_1721_, lean_object* v_vals_1722_, lean_object* v_heq_1723_, lean_object* v_i_1724_, lean_object* v_k_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6(v_00_u03b2_1720_, v_keys_1721_, v_vals_1722_, v_heq_1723_, v_i_1724_, v_k_1725_);
lean_dec_ref(v_k_1725_);
lean_dec_ref(v_vals_1722_);
lean_dec_ref(v_keys_1721_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_1727_, lean_object* v_n_1728_, lean_object* v_k_1729_, lean_object* v_v_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(v_n_1728_, v_k_1729_, v_v_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_1732_, size_t v_depth_1733_, lean_object* v_keys_1734_, lean_object* v_vals_1735_, lean_object* v_heq_1736_, lean_object* v_i_1737_, lean_object* v_entries_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_depth_1733_, v_keys_1734_, v_vals_1735_, v_i_1737_, v_entries_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1740_, lean_object* v_depth_1741_, lean_object* v_keys_1742_, lean_object* v_vals_1743_, lean_object* v_heq_1744_, lean_object* v_i_1745_, lean_object* v_entries_1746_){
_start:
{
size_t v_depth_boxed_1747_; lean_object* v_res_1748_; 
v_depth_boxed_1747_ = lean_unbox_usize(v_depth_1741_);
lean_dec(v_depth_1741_);
v_res_1748_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10(v_00_u03b2_1740_, v_depth_boxed_1747_, v_keys_1742_, v_vals_1743_, v_heq_1744_, v_i_1745_, v_entries_1746_);
lean_dec_ref(v_vals_1743_);
lean_dec_ref(v_keys_1742_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_1749_, lean_object* v_x_1750_, lean_object* v_x_1751_, lean_object* v_x_1752_, lean_object* v_x_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(v_x_1750_, v_x_1751_, v_x_1752_, v_x_1753_);
return v___x_1754_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__0(void){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1755_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__1(void){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__0, &l_Lean_Compiler_LCNF_Code_cse___closed__0_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__0);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
return v___x_1757_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__2(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = lean_box(0);
v___x_1759_ = lean_unsigned_to_nat(16u);
v___x_1760_ = lean_mk_array(v___x_1759_, v___x_1758_);
return v___x_1760_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__3(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__2, &l_Lean_Compiler_LCNF_Code_cse___closed__2_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__2);
v___x_1762_ = lean_unsigned_to_nat(0u);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v___x_1761_);
return v___x_1763_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__4(void){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__3, &l_Lean_Compiler_LCNF_Code_cse___closed__3_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__3);
v___x_1765_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__1, &l_Lean_Compiler_LCNF_Code_cse___closed__1_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__1);
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
lean_ctor_set(v___x_1766_, 1, v___x_1764_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse(uint8_t v_shouldElimFunDecls_1767_, lean_object* v_code_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__4, &l_Lean_Compiler_LCNF_Code_cse___closed__4_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__4);
v___x_1775_ = lean_st_mk_ref(v___x_1774_);
v___x_1776_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1767_, v_code_1768_, v___x_1775_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1785_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1785_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1785_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1781_; lean_object* v___x_1783_; 
v___x_1781_ = lean_st_ref_get(v___x_1775_);
lean_dec(v___x_1775_);
lean_dec(v___x_1781_);
if (v_isShared_1780_ == 0)
{
v___x_1783_ = v___x_1779_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1777_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
else
{
lean_dec(v___x_1775_);
return v___x_1776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse___boxed(lean_object* v_shouldElimFunDecls_1786_, lean_object* v_code_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1793_; lean_object* v_res_1794_; 
v_shouldElimFunDecls_boxed_1793_ = lean_unbox(v_shouldElimFunDecls_1786_);
v_res_1794_ = l_Lean_Compiler_LCNF_Code_cse(v_shouldElimFunDecls_boxed_1793_, v_code_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(lean_object* v_f_1795_, lean_object* v_v_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
if (lean_obj_tag(v_v_1796_) == 0)
{
lean_object* v_code_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1826_; 
v_code_1802_ = lean_ctor_get(v_v_1796_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_v_1796_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1804_ = v_v_1796_;
v_isShared_1805_ = v_isSharedCheck_1826_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_code_1802_);
lean_dec(v_v_1796_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1826_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; 
lean_inc(v___y_1800_);
lean_inc_ref(v___y_1799_);
lean_inc(v___y_1798_);
lean_inc_ref(v___y_1797_);
v___x_1806_ = lean_apply_6(v_f_1795_, v_code_1802_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, lean_box(0));
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1817_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1817_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1817_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v_a_1807_);
v___x_1812_ = v___x_1804_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1814_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1812_);
v___x_1814_ = v___x_1809_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_del_object(v___x_1804_);
v_a_1818_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1806_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1806_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
else
{
lean_object* v___x_1827_; 
lean_dec_ref(v_f_1795_);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v_v_1796_);
return v___x_1827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg___boxed(lean_object* v_f_1828_, lean_object* v_v_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v_f_1828_, v_v_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0(uint8_t v_pu_1836_, lean_object* v_f_1837_, lean_object* v_v_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v_f_1837_, v_v_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___boxed(lean_object* v_pu_1845_, lean_object* v_f_1846_, lean_object* v_v_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
uint8_t v_pu_boxed_1853_; lean_object* v_res_1854_; 
v_pu_boxed_1853_ = lean_unbox(v_pu_1845_);
v_res_1854_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0(v_pu_boxed_1853_, v_f_1846_, v_v_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0(uint8_t v_shouldElimFunDecls_1855_, lean_object* v_x_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Lean_Compiler_LCNF_Code_cse(v_shouldElimFunDecls_1855_, v_x_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed(lean_object* v_shouldElimFunDecls_1863_, lean_object* v_x_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1870_; lean_object* v_res_1871_; 
v_shouldElimFunDecls_boxed_1870_ = lean_unbox(v_shouldElimFunDecls_1863_);
v_res_1871_ = l_Lean_Compiler_LCNF_Decl_cse___lam__0(v_shouldElimFunDecls_boxed_1870_, v_x_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse(uint8_t v_shouldElimFunDecls_1872_, lean_object* v_decl_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v_toSignature_1879_; lean_object* v_value_1880_; uint8_t v_recursive_1881_; lean_object* v_inlineAttr_x3f_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1908_; 
v_toSignature_1879_ = lean_ctor_get(v_decl_1873_, 0);
v_value_1880_ = lean_ctor_get(v_decl_1873_, 1);
v_recursive_1881_ = lean_ctor_get_uint8(v_decl_1873_, sizeof(void*)*3);
v_inlineAttr_x3f_1882_ = lean_ctor_get(v_decl_1873_, 2);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_decl_1873_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1884_ = v_decl_1873_;
v_isShared_1885_ = v_isSharedCheck_1908_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_inlineAttr_x3f_1882_);
lean_inc(v_value_1880_);
lean_inc(v_toSignature_1879_);
lean_dec(v_decl_1873_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1908_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___f_1887_; lean_object* v___x_1888_; 
v___x_1886_ = lean_box(v_shouldElimFunDecls_1872_);
v___f_1887_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1887_, 0, v___x_1886_);
v___x_1888_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v___f_1887_, v_value_1880_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1899_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1899_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1899_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 1, v_a_1889_);
v___x_1894_ = v___x_1884_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_toSignature_1879_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_a_1889_);
lean_ctor_set(v_reuseFailAlloc_1898_, 2, v_inlineAttr_x3f_1882_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, sizeof(void*)*3, v_recursive_1881_);
v___x_1894_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1896_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1894_);
v___x_1896_ = v___x_1891_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_del_object(v___x_1884_);
lean_dec(v_inlineAttr_x3f_1882_);
lean_dec_ref(v_toSignature_1879_);
v_a_1900_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1888_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1888_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___boxed(lean_object* v_shouldElimFunDecls_1909_, lean_object* v_decl_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1916_; lean_object* v_res_1917_; 
v_shouldElimFunDecls_boxed_1916_ = lean_unbox(v_shouldElimFunDecls_1909_);
v_res_1917_ = l_Lean_Compiler_LCNF_Decl_cse(v_shouldElimFunDecls_boxed_1916_, v_decl_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
lean_dec(v_a_1914_);
lean_dec_ref(v_a_1913_);
lean_dec(v_a_1912_);
lean_dec_ref(v_a_1911_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___lam__0(uint8_t v_shouldElimFunDecls_1921_, uint8_t v_phase_1922_, lean_object* v_occurrence_1923_, lean_object* v_h_1924_){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1925_ = ((lean_object*)(l_Lean_Compiler_LCNF_cse___lam__0___closed__1));
v___x_1926_ = lean_box(v_shouldElimFunDecls_1921_);
v___x_1927_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_cse___boxed), 7, 1);
lean_closure_set(v___x_1927_, 0, v___x_1926_);
v___x_1928_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1925_, v_phase_1922_, v___x_1927_, v_occurrence_1923_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___lam__0___boxed(lean_object* v_shouldElimFunDecls_1929_, lean_object* v_phase_1930_, lean_object* v_occurrence_1931_, lean_object* v_h_1932_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1933_; uint8_t v_phase_boxed_1934_; lean_object* v_res_1935_; 
v_shouldElimFunDecls_boxed_1933_ = lean_unbox(v_shouldElimFunDecls_1929_);
v_phase_boxed_1934_ = lean_unbox(v_phase_1930_);
v_res_1935_ = l_Lean_Compiler_LCNF_cse___lam__0(v_shouldElimFunDecls_boxed_1933_, v_phase_boxed_1934_, v_occurrence_1931_, v_h_1932_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse(uint8_t v_phase_1936_, uint8_t v_shouldElimFunDecls_1937_, lean_object* v_occurrence_1938_){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___f_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; lean_object* v___x_1944_; 
v___x_1939_ = lean_box(v_shouldElimFunDecls_1937_);
v___x_1940_ = lean_box(v_phase_1936_);
v___f_1941_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_cse___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1941_, 0, v___x_1939_);
lean_closure_set(v___f_1941_, 1, v___x_1940_);
lean_closure_set(v___f_1941_, 2, v_occurrence_1938_);
v___x_1942_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_1943_ = 0;
v___x_1944_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_1942_, v_phase_1936_, v___x_1943_, v___f_1941_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___boxed(lean_object* v_phase_1945_, lean_object* v_shouldElimFunDecls_1946_, lean_object* v_occurrence_1947_){
_start:
{
uint8_t v_phase_boxed_1948_; uint8_t v_shouldElimFunDecls_boxed_1949_; lean_object* v_res_1950_; 
v_phase_boxed_1948_ = lean_unbox(v_phase_1945_);
v_shouldElimFunDecls_boxed_1949_ = lean_unbox(v_shouldElimFunDecls_1946_);
v_res_1950_ = l_Lean_Compiler_LCNF_cse(v_phase_boxed_1948_, v_shouldElimFunDecls_boxed_1949_, v_occurrence_1947_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2021_; uint8_t v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2021_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_));
v___x_2022_ = 1;
v___x_2023_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_));
v___x_2024_ = l_Lean_registerTraceClass(v___x_2021_, v___x_2022_, v___x_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2____boxed(lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_();
return v_res_2026_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_NeverExtractAttr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_CSE(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_NeverExtractAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse);
res = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_CSE(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_ToExpr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_NeverExtractAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_CSE(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_NeverExtractAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_CSE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_CSE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_CSE(builtin);
}
#ifdef __cplusplus
}
#endif
