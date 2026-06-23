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
size_t lean_usize_sub(size_t, size_t);
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
lean_dec_ref_known(v_r_244_, 1);
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
lean_dec_ref_known(v_r_291_, 1);
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
lean_dec_ref_known(v_v_594_, 3);
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
lean_dec_ref_known(v___x_734_, 1);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(lean_object* v_x_806_, size_t v_x_807_, lean_object* v_x_808_){
_start:
{
if (lean_obj_tag(v_x_806_) == 0)
{
lean_object* v_es_809_; lean_object* v___x_810_; size_t v___x_811_; size_t v___x_812_; lean_object* v_j_813_; lean_object* v___x_814_; 
v_es_809_ = lean_ctor_get(v_x_806_, 0);
v___x_810_ = lean_box(2);
v___x_811_ = ((size_t)31ULL);
v___x_812_ = lean_usize_land(v_x_807_, v___x_811_);
v_j_813_ = lean_usize_to_nat(v___x_812_);
v___x_814_ = lean_array_get_borrowed(v___x_810_, v_es_809_, v_j_813_);
lean_dec(v_j_813_);
switch(lean_obj_tag(v___x_814_))
{
case 0:
{
lean_object* v_key_815_; lean_object* v_val_816_; uint8_t v___x_817_; 
v_key_815_ = lean_ctor_get(v___x_814_, 0);
v_val_816_ = lean_ctor_get(v___x_814_, 1);
v___x_817_ = lean_expr_eqv(v_x_808_, v_key_815_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; 
v___x_818_ = lean_box(0);
return v___x_818_;
}
else
{
lean_object* v___x_819_; 
lean_inc(v_val_816_);
v___x_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_819_, 0, v_val_816_);
return v___x_819_;
}
}
case 1:
{
lean_object* v_node_820_; size_t v___x_821_; size_t v___x_822_; 
v_node_820_ = lean_ctor_get(v___x_814_, 0);
v___x_821_ = ((size_t)5ULL);
v___x_822_ = lean_usize_shift_right(v_x_807_, v___x_821_);
v_x_806_ = v_node_820_;
v_x_807_ = v___x_822_;
goto _start;
}
default: 
{
lean_object* v___x_824_; 
v___x_824_ = lean_box(0);
return v___x_824_;
}
}
}
else
{
lean_object* v_ks_825_; lean_object* v_vs_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_ks_825_ = lean_ctor_get(v_x_806_, 0);
v_vs_826_ = lean_ctor_get(v_x_806_, 1);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(v_ks_825_, v_vs_826_, v___x_827_, v_x_808_);
return v___x_828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___boxed(lean_object* v_x_829_, lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
size_t v_x_15767__boxed_832_; lean_object* v_res_833_; 
v_x_15767__boxed_832_ = lean_unbox_usize(v_x_830_);
lean_dec(v_x_830_);
v_res_833_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_829_, v_x_15767__boxed_832_, v_x_831_);
lean_dec_ref(v_x_831_);
lean_dec_ref(v_x_829_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
uint64_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; 
v___x_836_ = l_Lean_Expr_hash(v_x_835_);
v___x_837_ = lean_uint64_to_usize(v___x_836_);
v___x_838_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_834_, v___x_837_, v_x_835_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg___boxed(lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_x_839_, v_x_840_);
lean_dec_ref(v_x_840_);
lean_dec_ref(v_x_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
lean_object* v_ks_846_; lean_object* v_vs_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_871_; 
v_ks_846_ = lean_ctor_get(v_x_842_, 0);
v_vs_847_ = lean_ctor_get(v_x_842_, 1);
v_isSharedCheck_871_ = !lean_is_exclusive(v_x_842_);
if (v_isSharedCheck_871_ == 0)
{
v___x_849_ = v_x_842_;
v_isShared_850_ = v_isSharedCheck_871_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_vs_847_);
lean_inc(v_ks_846_);
lean_dec(v_x_842_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_871_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_851_ = lean_array_get_size(v_ks_846_);
v___x_852_ = lean_nat_dec_lt(v_x_843_, v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
lean_dec(v_x_843_);
v___x_853_ = lean_array_push(v_ks_846_, v_x_844_);
v___x_854_ = lean_array_push(v_vs_847_, v_x_845_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v___x_854_);
lean_ctor_set(v___x_849_, 0, v___x_853_);
v___x_856_ = v___x_849_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
else
{
lean_object* v_k_x27_858_; uint8_t v___x_859_; 
v_k_x27_858_ = lean_array_fget_borrowed(v_ks_846_, v_x_843_);
v___x_859_ = lean_expr_eqv(v_x_844_, v_k_x27_858_);
if (v___x_859_ == 0)
{
lean_object* v___x_861_; 
if (v_isShared_850_ == 0)
{
v___x_861_ = v___x_849_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_ks_846_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_vs_847_);
v___x_861_ = v_reuseFailAlloc_865_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_unsigned_to_nat(1u);
v___x_863_ = lean_nat_add(v_x_843_, v___x_862_);
lean_dec(v_x_843_);
v_x_842_ = v___x_861_;
v_x_843_ = v___x_863_;
goto _start;
}
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_866_ = lean_array_fset(v_ks_846_, v_x_843_, v_x_844_);
v___x_867_ = lean_array_fset(v_vs_847_, v_x_843_, v_x_845_);
lean_dec(v_x_843_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v___x_867_);
lean_ctor_set(v___x_849_, 0, v___x_866_);
v___x_869_ = v___x_849_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(lean_object* v_n_872_, lean_object* v_k_873_, lean_object* v_v_874_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_unsigned_to_nat(0u);
v___x_876_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(v_n_872_, v___x_875_, v_k_873_, v_v_874_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(lean_object* v_x_878_, size_t v_x_879_, size_t v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
if (lean_obj_tag(v_x_878_) == 0)
{
lean_object* v_es_883_; size_t v___x_884_; size_t v___x_885_; lean_object* v_j_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v_es_883_ = lean_ctor_get(v_x_878_, 0);
v___x_884_ = ((size_t)31ULL);
v___x_885_ = lean_usize_land(v_x_879_, v___x_884_);
v_j_886_ = lean_usize_to_nat(v___x_885_);
v___x_887_ = lean_array_get_size(v_es_883_);
v___x_888_ = lean_nat_dec_lt(v_j_886_, v___x_887_);
if (v___x_888_ == 0)
{
lean_dec(v_j_886_);
lean_dec(v_x_882_);
lean_dec_ref(v_x_881_);
return v_x_878_;
}
else
{
lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_927_; 
lean_inc_ref(v_es_883_);
v_isSharedCheck_927_ = !lean_is_exclusive(v_x_878_);
if (v_isSharedCheck_927_ == 0)
{
lean_object* v_unused_928_; 
v_unused_928_ = lean_ctor_get(v_x_878_, 0);
lean_dec(v_unused_928_);
v___x_890_ = v_x_878_;
v_isShared_891_ = v_isSharedCheck_927_;
goto v_resetjp_889_;
}
else
{
lean_dec(v_x_878_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_927_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_v_892_; lean_object* v___x_893_; lean_object* v_xs_x27_894_; lean_object* v___y_896_; 
v_v_892_ = lean_array_fget(v_es_883_, v_j_886_);
v___x_893_ = lean_box(0);
v_xs_x27_894_ = lean_array_fset(v_es_883_, v_j_886_, v___x_893_);
switch(lean_obj_tag(v_v_892_))
{
case 0:
{
lean_object* v_key_901_; lean_object* v_val_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_912_; 
v_key_901_ = lean_ctor_get(v_v_892_, 0);
v_val_902_ = lean_ctor_get(v_v_892_, 1);
v_isSharedCheck_912_ = !lean_is_exclusive(v_v_892_);
if (v_isSharedCheck_912_ == 0)
{
v___x_904_ = v_v_892_;
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_val_902_);
lean_inc(v_key_901_);
lean_dec(v_v_892_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
uint8_t v___x_906_; 
v___x_906_ = lean_expr_eqv(v_x_881_, v_key_901_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; 
lean_del_object(v___x_904_);
v___x_907_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_901_, v_val_902_, v_x_881_, v_x_882_);
v___x_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
v___y_896_ = v___x_908_;
goto v___jp_895_;
}
else
{
lean_object* v___x_910_; 
lean_dec(v_val_902_);
lean_dec(v_key_901_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v_x_882_);
lean_ctor_set(v___x_904_, 0, v_x_881_);
v___x_910_ = v___x_904_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_x_881_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_x_882_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
v___y_896_ = v___x_910_;
goto v___jp_895_;
}
}
}
}
case 1:
{
lean_object* v_node_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_925_; 
v_node_913_ = lean_ctor_get(v_v_892_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v_v_892_);
if (v_isSharedCheck_925_ == 0)
{
v___x_915_ = v_v_892_;
v_isShared_916_ = v_isSharedCheck_925_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_node_913_);
lean_dec(v_v_892_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_925_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
size_t v___x_917_; size_t v___x_918_; size_t v___x_919_; size_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_917_ = ((size_t)5ULL);
v___x_918_ = lean_usize_shift_right(v_x_879_, v___x_917_);
v___x_919_ = ((size_t)1ULL);
v___x_920_ = lean_usize_add(v_x_880_, v___x_919_);
v___x_921_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_node_913_, v___x_918_, v___x_920_, v_x_881_, v_x_882_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_921_);
v___x_923_ = v___x_915_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
v___y_896_ = v___x_923_;
goto v___jp_895_;
}
}
}
default: 
{
lean_object* v___x_926_; 
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_x_881_);
lean_ctor_set(v___x_926_, 1, v_x_882_);
v___y_896_ = v___x_926_;
goto v___jp_895_;
}
}
v___jp_895_:
{
lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_897_ = lean_array_fset(v_xs_x27_894_, v_j_886_, v___y_896_);
lean_dec(v_j_886_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_897_);
v___x_899_ = v___x_890_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
else
{
lean_object* v_ks_929_; lean_object* v_vs_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_950_; 
v_ks_929_ = lean_ctor_get(v_x_878_, 0);
v_vs_930_ = lean_ctor_get(v_x_878_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_x_878_);
if (v_isSharedCheck_950_ == 0)
{
v___x_932_ = v_x_878_;
v_isShared_933_ = v_isSharedCheck_950_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_vs_930_);
lean_inc(v_ks_929_);
lean_dec(v_x_878_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_950_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_ks_929_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_vs_930_);
v___x_935_ = v_reuseFailAlloc_949_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v_newNode_936_; uint8_t v___y_938_; size_t v___x_944_; uint8_t v___x_945_; 
v_newNode_936_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(v___x_935_, v_x_881_, v_x_882_);
v___x_944_ = ((size_t)7ULL);
v___x_945_ = lean_usize_dec_le(v___x_944_, v_x_880_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_946_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_936_);
v___x_947_ = lean_unsigned_to_nat(4u);
v___x_948_ = lean_nat_dec_lt(v___x_946_, v___x_947_);
lean_dec(v___x_946_);
v___y_938_ = v___x_948_;
goto v___jp_937_;
}
else
{
v___y_938_ = v___x_945_;
goto v___jp_937_;
}
v___jp_937_:
{
if (v___y_938_ == 0)
{
lean_object* v_ks_939_; lean_object* v_vs_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_ks_939_ = lean_ctor_get(v_newNode_936_, 0);
lean_inc_ref(v_ks_939_);
v_vs_940_ = lean_ctor_get(v_newNode_936_, 1);
lean_inc_ref(v_vs_940_);
lean_dec_ref(v_newNode_936_);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0);
v___x_943_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_x_880_, v_ks_939_, v_vs_940_, v___x_941_, v___x_942_);
lean_dec_ref(v_vs_940_);
lean_dec_ref(v_ks_939_);
return v___x_943_;
}
else
{
return v_newNode_936_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(size_t v_depth_951_, lean_object* v_keys_952_, lean_object* v_vals_953_, lean_object* v_i_954_, lean_object* v_entries_955_){
_start:
{
lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_956_ = lean_array_get_size(v_keys_952_);
v___x_957_ = lean_nat_dec_lt(v_i_954_, v___x_956_);
if (v___x_957_ == 0)
{
lean_dec(v_i_954_);
return v_entries_955_;
}
else
{
lean_object* v_k_958_; lean_object* v_v_959_; uint64_t v___x_960_; size_t v_h_961_; size_t v___x_962_; lean_object* v___x_963_; size_t v___x_964_; size_t v___x_965_; size_t v___x_966_; size_t v_h_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_k_958_ = lean_array_fget_borrowed(v_keys_952_, v_i_954_);
v_v_959_ = lean_array_fget_borrowed(v_vals_953_, v_i_954_);
v___x_960_ = l_Lean_Expr_hash(v_k_958_);
v_h_961_ = lean_uint64_to_usize(v___x_960_);
v___x_962_ = ((size_t)5ULL);
v___x_963_ = lean_unsigned_to_nat(1u);
v___x_964_ = ((size_t)1ULL);
v___x_965_ = lean_usize_sub(v_depth_951_, v___x_964_);
v___x_966_ = lean_usize_mul(v___x_962_, v___x_965_);
v_h_967_ = lean_usize_shift_right(v_h_961_, v___x_966_);
v___x_968_ = lean_nat_add(v_i_954_, v___x_963_);
lean_dec(v_i_954_);
lean_inc(v_v_959_);
lean_inc(v_k_958_);
v___x_969_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_entries_955_, v_h_967_, v_depth_951_, v_k_958_, v_v_959_);
v_i_954_ = v___x_968_;
v_entries_955_ = v___x_969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_depth_971_, lean_object* v_keys_972_, lean_object* v_vals_973_, lean_object* v_i_974_, lean_object* v_entries_975_){
_start:
{
size_t v_depth_boxed_976_; lean_object* v_res_977_; 
v_depth_boxed_976_ = lean_unbox_usize(v_depth_971_);
lean_dec(v_depth_971_);
v_res_977_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_depth_boxed_976_, v_keys_972_, v_vals_973_, v_i_974_, v_entries_975_);
lean_dec_ref(v_vals_973_);
lean_dec_ref(v_keys_972_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___boxed(lean_object* v_x_978_, lean_object* v_x_979_, lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v_x_982_){
_start:
{
size_t v_x_15902__boxed_983_; size_t v_x_15903__boxed_984_; lean_object* v_res_985_; 
v_x_15902__boxed_983_ = lean_unbox_usize(v_x_979_);
lean_dec(v_x_979_);
v_x_15903__boxed_984_ = lean_unbox_usize(v_x_980_);
lean_dec(v_x_980_);
v_res_985_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_978_, v_x_15902__boxed_983_, v_x_15903__boxed_984_, v_x_981_, v_x_982_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(lean_object* v_x_986_, lean_object* v_x_987_, lean_object* v_x_988_){
_start:
{
uint64_t v___x_989_; size_t v___x_990_; size_t v___x_991_; lean_object* v___x_992_; 
v___x_989_ = l_Lean_Expr_hash(v_x_987_);
v___x_990_ = lean_uint64_to_usize(v___x_989_);
v___x_991_ = ((size_t)1ULL);
v___x_992_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_986_, v___x_990_, v___x_991_, v_x_987_, v_x_988_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(uint8_t v_shouldElimFunDecls_995_, lean_object* v_i_996_, lean_object* v_as_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = lean_array_get_size(v_as_997_);
v___x_1005_ = lean_nat_dec_lt(v_i_996_, v___x_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; 
lean_dec(v_i_996_);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v_as_997_);
return v___x_1006_;
}
else
{
lean_object* v_a_1007_; lean_object* v_a_1009_; 
v_a_1007_ = lean_array_fget_borrowed(v_as_997_, v_i_996_);
if (lean_obj_tag(v_a_1007_) == 0)
{
lean_object* v_params_1020_; lean_object* v_code_1021_; lean_object* v___x_1022_; lean_object* v_map_1023_; uint8_t v___x_1024_; uint8_t v___x_1025_; lean_object* v_a_1027_; lean_object* v___x_1046_; 
v_params_1020_ = lean_ctor_get(v_a_1007_, 1);
v_code_1021_ = lean_ctor_get(v_a_1007_, 2);
v___x_1022_ = lean_st_ref_get(v___y_998_);
v_map_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc_ref(v_map_1023_);
lean_dec(v___x_1022_);
v___x_1024_ = 0;
v___x_1025_ = 0;
lean_inc_ref(v_params_1020_);
v___x_1046_ = l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(v___x_1024_, v___x_1025_, v_params_1020_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1048_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
lean_inc_ref(v_code_1021_);
v___x_1048_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_995_, v_code_1021_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1066_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1051_ = v___x_1048_;
v_isShared_1052_ = v_isSharedCheck_1066_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1066_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
lean_inc_ref(v_a_1007_);
v___x_1053_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v___x_1024_, v_a_1007_, v_a_1047_, v_a_1049_);
lean_inc_ref(v___x_1053_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 1);
lean_ctor_set(v___x_1051_, 0, v___x_1053_);
v___x_1055_ = v___x_1051_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; 
v___x_1056_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_998_, v_map_1023_, v___x_1055_);
lean_dec_ref(v___x_1055_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_dec_ref_known(v___x_1056_, 1);
v_a_1009_ = v___x_1053_;
goto v___jp_1008_;
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec_ref(v___x_1053_);
lean_dec_ref(v_as_997_);
lean_dec(v_i_996_);
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
}
else
{
lean_object* v_a_1067_; 
lean_dec(v_a_1047_);
lean_dec_ref(v_as_997_);
lean_dec(v_i_996_);
v_a_1067_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1048_, 1);
v_a_1027_ = v_a_1067_;
goto v___jp_1026_;
}
}
else
{
lean_object* v_a_1068_; 
lean_dec_ref(v_as_997_);
lean_dec(v_i_996_);
v_a_1068_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1046_, 1);
v_a_1027_ = v_a_1068_;
goto v___jp_1026_;
}
v___jp_1026_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_box(0);
v___x_1029_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_998_, v_map_1023_, v___x_1028_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; 
v_unused_1037_ = lean_ctor_get(v___x_1029_, 0);
lean_dec(v_unused_1037_);
v___x_1031_ = v___x_1029_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_dec(v___x_1029_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set_tag(v___x_1031_, 1);
lean_ctor_set(v___x_1031_, 0, v_a_1027_);
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1027_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v_a_1027_);
v_a_1038_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1029_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1029_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
else
{
lean_object* v_code_1069_; lean_object* v___x_1070_; lean_object* v_map_1071_; lean_object* v___x_1072_; 
v_code_1069_ = lean_ctor_get(v_a_1007_, 0);
v___x_1070_ = lean_st_ref_get(v___y_998_);
v_map_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc_ref(v_map_1071_);
lean_dec(v___x_1070_);
lean_inc_ref(v_code_1069_);
v___x_1072_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_995_, v_code_1069_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1090_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1090_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1090_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
lean_inc_ref(v_a_1007_);
v___x_1077_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1007_, v_a_1073_);
lean_inc_ref(v___x_1077_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set_tag(v___x_1075_, 1);
lean_ctor_set(v___x_1075_, 0, v___x_1077_);
v___x_1079_ = v___x_1075_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1080_; 
v___x_1080_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_998_, v_map_1071_, v___x_1079_);
lean_dec_ref(v___x_1079_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_dec_ref_known(v___x_1080_, 1);
v_a_1009_ = v___x_1077_;
goto v___jp_1008_;
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec_ref(v___x_1077_);
lean_dec_ref(v_as_997_);
lean_dec(v_i_996_);
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_dec_ref(v_as_997_);
lean_dec(v_i_996_);
v_a_1091_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1092_ = lean_box(0);
v___x_1093_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_998_, v_map_1071_, v___x_1092_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v___x_1093_, 0);
lean_dec(v_unused_1101_);
v___x_1095_ = v___x_1093_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_dec(v___x_1093_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 1);
lean_ctor_set(v___x_1095_, 0, v_a_1091_);
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1091_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec(v_a_1091_);
v_a_1102_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1093_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1093_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
v___jp_1008_:
{
size_t v___x_1010_; size_t v___x_1011_; uint8_t v___x_1012_; 
v___x_1010_ = lean_ptr_addr(v_a_1007_);
v___x_1011_ = lean_ptr_addr(v_a_1009_);
v___x_1012_ = lean_usize_dec_eq(v___x_1010_, v___x_1011_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1013_ = lean_unsigned_to_nat(1u);
v___x_1014_ = lean_nat_add(v_i_996_, v___x_1013_);
v___x_1015_ = lean_array_fset(v_as_997_, v_i_996_, v_a_1009_);
lean_dec(v_i_996_);
v_i_996_ = v___x_1014_;
v_as_997_ = v___x_1015_;
goto _start;
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_dec_ref(v_a_1009_);
v___x_1017_ = lean_unsigned_to_nat(1u);
v___x_1018_ = lean_nat_add(v_i_996_, v___x_1017_);
lean_dec(v_i_996_);
v_i_996_ = v___x_1018_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(uint8_t v_shouldElimFunDecls_1110_, lean_object* v_code_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
switch(lean_obj_tag(v_code_1111_))
{
case 0:
{
lean_object* v_decl_1118_; lean_object* v_k_1119_; uint8_t v___x_1120_; uint8_t v___x_1121_; lean_object* v___x_1122_; 
v_decl_1118_ = lean_ctor_get(v_code_1111_, 0);
v_k_1119_ = lean_ctor_get(v_code_1111_, 1);
v___x_1120_ = 0;
v___x_1121_ = 0;
lean_inc_ref(v_decl_1118_);
v___x_1122_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v___x_1120_, v___x_1121_, v_decl_1118_, v_a_1112_, v_a_1114_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v_fvarId_1124_; lean_object* v_value_1125_; lean_object* v___x_1126_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
v_fvarId_1124_ = lean_ctor_get(v_a_1123_, 0);
v_value_1125_ = lean_ctor_get(v_a_1123_, 3);
lean_inc(v_value_1125_);
v___x_1126_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(v_value_1125_, v_a_1116_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; uint8_t v___x_1128_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v___x_1126_, 1);
v___x_1128_ = lean_unbox(v_a_1127_);
lean_dec(v_a_1127_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v_map_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1129_ = lean_st_ref_get(v_a_1112_);
v_map_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc_ref(v_map_1130_);
lean_dec(v___x_1129_);
lean_inc(v_value_1125_);
v___x_1131_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v___x_1120_, v_value_1125_);
v___x_1132_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_map_1130_, v___x_1131_);
lean_dec_ref(v_map_1130_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v___x_1133_; lean_object* v_map_1134_; lean_object* v_subst_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1173_; 
v___x_1133_ = lean_st_ref_take(v_a_1112_);
v_map_1134_ = lean_ctor_get(v___x_1133_, 0);
v_subst_1135_ = lean_ctor_get(v___x_1133_, 1);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1137_ = v___x_1133_;
v_isShared_1138_ = v_isSharedCheck_1173_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_subst_1135_);
lean_inc(v_map_1134_);
lean_dec(v___x_1133_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1173_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
lean_inc(v_fvarId_1124_);
v___x_1139_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_map_1134_, v___x_1131_, v_fvarId_1124_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1139_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_subst_1135_);
v___x_1141_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_st_ref_set(v_a_1112_, v___x_1141_);
lean_inc_ref(v_k_1119_);
v___x_1143_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1110_, v_k_1119_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1171_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1171_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1171_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
uint8_t v___y_1149_; size_t v___x_1165_; size_t v___x_1166_; uint8_t v___x_1167_; 
v___x_1165_ = lean_ptr_addr(v_k_1119_);
v___x_1166_ = lean_ptr_addr(v_a_1144_);
v___x_1167_ = lean_usize_dec_eq(v___x_1165_, v___x_1166_);
if (v___x_1167_ == 0)
{
v___y_1149_ = v___x_1167_;
goto v___jp_1148_;
}
else
{
size_t v___x_1168_; size_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1168_ = lean_ptr_addr(v_decl_1118_);
v___x_1169_ = lean_ptr_addr(v_a_1123_);
v___x_1170_ = lean_usize_dec_eq(v___x_1168_, v___x_1169_);
v___y_1149_ = v___x_1170_;
goto v___jp_1148_;
}
v___jp_1148_:
{
if (v___y_1149_ == 0)
{
lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1159_; 
v_isSharedCheck_1159_ = !lean_is_exclusive(v_code_1111_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; lean_object* v_unused_1161_; 
v_unused_1160_ = lean_ctor_get(v_code_1111_, 1);
lean_dec(v_unused_1160_);
v_unused_1161_ = lean_ctor_get(v_code_1111_, 0);
lean_dec(v_unused_1161_);
v___x_1151_ = v_code_1111_;
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
else
{
lean_dec(v_code_1111_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v_a_1144_);
lean_ctor_set(v___x_1151_, 0, v_a_1123_);
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1123_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_a_1144_);
v___x_1154_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1156_; 
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1154_);
v___x_1156_ = v___x_1146_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
else
{
lean_object* v___x_1163_; 
lean_dec(v_a_1144_);
lean_dec(v_a_1123_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v_code_1111_);
v___x_1163_ = v___x_1146_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_code_1111_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
else
{
lean_dec(v_a_1123_);
lean_dec_ref_known(v_code_1111_, 2);
return v___x_1143_;
}
}
}
}
else
{
lean_object* v_val_1174_; lean_object* v___x_1175_; 
lean_inc_ref(v_k_1119_);
lean_dec_ref(v___x_1131_);
lean_dec_ref_known(v_code_1111_, 2);
v_val_1174_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_val_1174_);
lean_dec_ref_known(v___x_1132_, 1);
v___x_1175_ = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(v_a_1123_, v_val_1174_, v_a_1112_, v_a_1114_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_dec_ref_known(v___x_1175_, 1);
v_code_1111_ = v_k_1119_;
goto _start;
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec_ref(v_k_1119_);
v_a_1177_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1175_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1175_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
else
{
lean_object* v___x_1185_; 
lean_inc_ref(v_k_1119_);
v___x_1185_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1110_, v_k_1119_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1213_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1213_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1213_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
uint8_t v___y_1191_; size_t v___x_1207_; size_t v___x_1208_; uint8_t v___x_1209_; 
v___x_1207_ = lean_ptr_addr(v_k_1119_);
v___x_1208_ = lean_ptr_addr(v_a_1186_);
v___x_1209_ = lean_usize_dec_eq(v___x_1207_, v___x_1208_);
if (v___x_1209_ == 0)
{
v___y_1191_ = v___x_1209_;
goto v___jp_1190_;
}
else
{
size_t v___x_1210_; size_t v___x_1211_; uint8_t v___x_1212_; 
v___x_1210_ = lean_ptr_addr(v_decl_1118_);
v___x_1211_ = lean_ptr_addr(v_a_1123_);
v___x_1212_ = lean_usize_dec_eq(v___x_1210_, v___x_1211_);
v___y_1191_ = v___x_1212_;
goto v___jp_1190_;
}
v___jp_1190_:
{
if (v___y_1191_ == 0)
{
lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1201_; 
v_isSharedCheck_1201_ = !lean_is_exclusive(v_code_1111_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; lean_object* v_unused_1203_; 
v_unused_1202_ = lean_ctor_get(v_code_1111_, 1);
lean_dec(v_unused_1202_);
v_unused_1203_ = lean_ctor_get(v_code_1111_, 0);
lean_dec(v_unused_1203_);
v___x_1193_ = v_code_1111_;
v_isShared_1194_ = v_isSharedCheck_1201_;
goto v_resetjp_1192_;
}
else
{
lean_dec(v_code_1111_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1201_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v_a_1186_);
lean_ctor_set(v___x_1193_, 0, v_a_1123_);
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1123_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_a_1186_);
v___x_1196_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1196_);
v___x_1198_ = v___x_1188_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v___x_1205_; 
lean_dec(v_a_1186_);
lean_dec(v_a_1123_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v_code_1111_);
v___x_1205_ = v___x_1188_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_code_1111_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
else
{
lean_dec(v_a_1123_);
lean_dec_ref_known(v_code_1111_, 2);
return v___x_1185_;
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec(v_a_1123_);
lean_dec_ref_known(v_code_1111_, 2);
v_a_1214_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1126_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1126_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec_ref_known(v_code_1111_, 2);
v_a_1222_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1122_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1122_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
case 1:
{
lean_object* v_decl_1230_; lean_object* v_k_1231_; lean_object* v___x_1232_; 
v_decl_1230_ = lean_ctor_get(v_code_1111_, 0);
v_k_1231_ = lean_ctor_get(v_code_1111_, 1);
lean_inc_ref(v_decl_1230_);
v___x_1232_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_1110_, v_decl_1230_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1232_) == 0)
{
if (v_shouldElimFunDecls_1110_ == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1234_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
lean_inc_ref(v_k_1231_);
v___x_1234_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1110_, v_k_1231_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1262_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1262_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1262_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
uint8_t v___y_1240_; size_t v___x_1256_; size_t v___x_1257_; uint8_t v___x_1258_; 
v___x_1256_ = lean_ptr_addr(v_k_1231_);
v___x_1257_ = lean_ptr_addr(v_a_1235_);
v___x_1258_ = lean_usize_dec_eq(v___x_1256_, v___x_1257_);
if (v___x_1258_ == 0)
{
v___y_1240_ = v___x_1258_;
goto v___jp_1239_;
}
else
{
size_t v___x_1259_; size_t v___x_1260_; uint8_t v___x_1261_; 
v___x_1259_ = lean_ptr_addr(v_decl_1230_);
v___x_1260_ = lean_ptr_addr(v_a_1233_);
v___x_1261_ = lean_usize_dec_eq(v___x_1259_, v___x_1260_);
v___y_1240_ = v___x_1261_;
goto v___jp_1239_;
}
v___jp_1239_:
{
if (v___y_1240_ == 0)
{
lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1250_; 
v_isSharedCheck_1250_ = !lean_is_exclusive(v_code_1111_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; lean_object* v_unused_1252_; 
v_unused_1251_ = lean_ctor_get(v_code_1111_, 1);
lean_dec(v_unused_1251_);
v_unused_1252_ = lean_ctor_get(v_code_1111_, 0);
lean_dec(v_unused_1252_);
v___x_1242_ = v_code_1111_;
v_isShared_1243_ = v_isSharedCheck_1250_;
goto v_resetjp_1241_;
}
else
{
lean_dec(v_code_1111_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1250_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v_a_1235_);
lean_ctor_set(v___x_1242_, 0, v_a_1233_);
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1233_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_a_1235_);
v___x_1245_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1247_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1245_);
v___x_1247_ = v___x_1237_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
else
{
lean_object* v___x_1254_; 
lean_dec(v_a_1235_);
lean_dec(v_a_1233_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v_code_1111_);
v___x_1254_ = v___x_1237_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_code_1111_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
else
{
lean_dec(v_a_1233_);
lean_dec_ref_known(v_code_1111_, 2);
return v___x_1234_;
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1264_; lean_object* v_map_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_a_1263_ = lean_ctor_get(v___x_1232_, 0);
lean_inc_n(v_a_1263_, 2);
lean_dec_ref_known(v___x_1232_, 1);
v___x_1264_ = lean_st_ref_get(v_a_1112_);
v_map_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc_ref(v_map_1265_);
lean_dec(v___x_1264_);
v___x_1266_ = 0;
v___x_1267_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___closed__0));
v___x_1268_ = l_Lean_Compiler_LCNF_FunDecl_toExpr(v___x_1266_, v_a_1263_, v___x_1267_);
v___x_1269_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_map_1265_, v___x_1268_);
lean_dec_ref(v_map_1265_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_fvarId_1270_; lean_object* v___x_1271_; lean_object* v_map_1272_; lean_object* v_subst_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1311_; 
v_fvarId_1270_ = lean_ctor_get(v_a_1263_, 0);
v___x_1271_ = lean_st_ref_take(v_a_1112_);
v_map_1272_ = lean_ctor_get(v___x_1271_, 0);
v_subst_1273_ = lean_ctor_get(v___x_1271_, 1);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1275_ = v___x_1271_;
v_isShared_1276_ = v_isSharedCheck_1311_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_subst_1273_);
lean_inc(v_map_1272_);
lean_dec(v___x_1271_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1311_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
lean_inc(v_fvarId_1270_);
v___x_1277_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_map_1272_, v___x_1268_, v_fvarId_1270_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1277_);
v___x_1279_ = v___x_1275_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_subst_1273_);
v___x_1279_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_st_ref_set(v_a_1112_, v___x_1279_);
lean_inc_ref(v_k_1231_);
v___x_1281_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1110_, v_k_1231_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1309_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1309_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1309_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
uint8_t v___y_1287_; size_t v___x_1303_; size_t v___x_1304_; uint8_t v___x_1305_; 
v___x_1303_ = lean_ptr_addr(v_k_1231_);
v___x_1304_ = lean_ptr_addr(v_a_1282_);
v___x_1305_ = lean_usize_dec_eq(v___x_1303_, v___x_1304_);
if (v___x_1305_ == 0)
{
v___y_1287_ = v___x_1305_;
goto v___jp_1286_;
}
else
{
size_t v___x_1306_; size_t v___x_1307_; uint8_t v___x_1308_; 
v___x_1306_ = lean_ptr_addr(v_decl_1230_);
v___x_1307_ = lean_ptr_addr(v_a_1263_);
v___x_1308_ = lean_usize_dec_eq(v___x_1306_, v___x_1307_);
v___y_1287_ = v___x_1308_;
goto v___jp_1286_;
}
v___jp_1286_:
{
if (v___y_1287_ == 0)
{
lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1297_; 
v_isSharedCheck_1297_ = !lean_is_exclusive(v_code_1111_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; lean_object* v_unused_1299_; 
v_unused_1298_ = lean_ctor_get(v_code_1111_, 1);
lean_dec(v_unused_1298_);
v_unused_1299_ = lean_ctor_get(v_code_1111_, 0);
lean_dec(v_unused_1299_);
v___x_1289_ = v_code_1111_;
v_isShared_1290_ = v_isSharedCheck_1297_;
goto v_resetjp_1288_;
}
else
{
lean_dec(v_code_1111_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1297_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 1, v_a_1282_);
lean_ctor_set(v___x_1289_, 0, v_a_1263_);
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1263_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_a_1282_);
v___x_1292_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1294_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1292_);
v___x_1294_ = v___x_1284_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
else
{
lean_object* v___x_1301_; 
lean_dec(v_a_1282_);
lean_dec(v_a_1263_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v_code_1111_);
v___x_1301_ = v___x_1284_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_code_1111_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
else
{
lean_dec(v_a_1263_);
lean_dec_ref_known(v_code_1111_, 2);
return v___x_1281_;
}
}
}
}
else
{
lean_object* v_val_1312_; lean_object* v___x_1313_; 
lean_inc_ref(v_k_1231_);
lean_dec_ref(v___x_1268_);
lean_dec_ref_known(v_code_1111_, 2);
v_val_1312_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_val_1312_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1313_ = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(v_a_1263_, v_val_1312_, v_a_1112_, v_a_1114_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_dec_ref_known(v___x_1313_, 1);
v_code_1111_ = v_k_1231_;
goto _start;
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec_ref(v_k_1231_);
v_a_1315_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1313_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1313_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_dec_ref_known(v_code_1111_, 2);
v_a_1323_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1232_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1232_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
case 2:
{
lean_object* v_decl_1331_; lean_object* v_k_1332_; lean_object* v___x_1333_; 
v_decl_1331_ = lean_ctor_get(v_code_1111_, 0);
v_k_1332_ = lean_ctor_get(v_code_1111_, 1);
lean_inc_ref(v_decl_1331_);
v___x_1333_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_1110_, v_decl_1331_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___x_1335_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1333_, 1);
lean_inc_ref(v_k_1332_);
v___x_1335_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1110_, v_k_1332_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1363_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1363_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1363_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
uint8_t v___y_1341_; size_t v___x_1357_; size_t v___x_1358_; uint8_t v___x_1359_; 
v___x_1357_ = lean_ptr_addr(v_k_1332_);
v___x_1358_ = lean_ptr_addr(v_a_1336_);
v___x_1359_ = lean_usize_dec_eq(v___x_1357_, v___x_1358_);
if (v___x_1359_ == 0)
{
v___y_1341_ = v___x_1359_;
goto v___jp_1340_;
}
else
{
size_t v___x_1360_; size_t v___x_1361_; uint8_t v___x_1362_; 
v___x_1360_ = lean_ptr_addr(v_decl_1331_);
v___x_1361_ = lean_ptr_addr(v_a_1334_);
v___x_1362_ = lean_usize_dec_eq(v___x_1360_, v___x_1361_);
v___y_1341_ = v___x_1362_;
goto v___jp_1340_;
}
v___jp_1340_:
{
if (v___y_1341_ == 0)
{
lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1351_; 
v_isSharedCheck_1351_ = !lean_is_exclusive(v_code_1111_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; lean_object* v_unused_1353_; 
v_unused_1352_ = lean_ctor_get(v_code_1111_, 1);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v_code_1111_, 0);
lean_dec(v_unused_1353_);
v___x_1343_ = v_code_1111_;
v_isShared_1344_ = v_isSharedCheck_1351_;
goto v_resetjp_1342_;
}
else
{
lean_dec(v_code_1111_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1351_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 1, v_a_1336_);
lean_ctor_set(v___x_1343_, 0, v_a_1334_);
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1334_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_a_1336_);
v___x_1346_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v___x_1348_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1346_);
v___x_1348_ = v___x_1338_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
lean_object* v___x_1355_; 
lean_dec(v_a_1336_);
lean_dec(v_a_1334_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v_code_1111_);
v___x_1355_ = v___x_1338_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_code_1111_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
else
{
lean_dec(v_a_1334_);
lean_dec_ref_known(v_code_1111_, 2);
return v___x_1335_;
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec_ref_known(v_code_1111_, 2);
v_a_1364_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1333_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1333_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_1372_; lean_object* v_args_1373_; lean_object* v___x_1374_; lean_object* v_subst_1375_; uint8_t v___x_1376_; uint8_t v___x_1377_; lean_object* v___x_1378_; 
v_fvarId_1372_ = lean_ctor_get(v_code_1111_, 0);
v_args_1373_ = lean_ctor_get(v_code_1111_, 1);
v___x_1374_ = lean_st_ref_get(v_a_1112_);
v_subst_1375_ = lean_ctor_get(v___x_1374_, 1);
lean_inc_ref(v_subst_1375_);
lean_dec(v___x_1374_);
v___x_1376_ = 0;
v___x_1377_ = 0;
lean_inc(v_fvarId_1372_);
v___x_1378_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1375_, v_fvarId_1372_, v___x_1377_);
lean_dec_ref(v_subst_1375_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_fvarId_1379_; lean_object* v___x_1380_; 
v_fvarId_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_fvarId_1379_);
lean_dec_ref_known(v___x_1378_, 1);
lean_inc_ref(v_args_1373_);
v___x_1380_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v___x_1376_, v___x_1377_, v_args_1373_, v_a_1112_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1406_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1406_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1406_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
uint8_t v___y_1386_; uint8_t v___x_1402_; 
v___x_1402_ = l_Lean_instBEqFVarId_beq(v_fvarId_1372_, v_fvarId_1379_);
if (v___x_1402_ == 0)
{
v___y_1386_ = v___x_1402_;
goto v___jp_1385_;
}
else
{
size_t v___x_1403_; size_t v___x_1404_; uint8_t v___x_1405_; 
v___x_1403_ = lean_ptr_addr(v_args_1373_);
v___x_1404_ = lean_ptr_addr(v_a_1381_);
v___x_1405_ = lean_usize_dec_eq(v___x_1403_, v___x_1404_);
v___y_1386_ = v___x_1405_;
goto v___jp_1385_;
}
v___jp_1385_:
{
if (v___y_1386_ == 0)
{
lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1396_; 
v_isSharedCheck_1396_ = !lean_is_exclusive(v_code_1111_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; lean_object* v_unused_1398_; 
v_unused_1397_ = lean_ctor_get(v_code_1111_, 1);
lean_dec(v_unused_1397_);
v_unused_1398_ = lean_ctor_get(v_code_1111_, 0);
lean_dec(v_unused_1398_);
v___x_1388_ = v_code_1111_;
v_isShared_1389_ = v_isSharedCheck_1396_;
goto v_resetjp_1387_;
}
else
{
lean_dec(v_code_1111_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1396_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 1, v_a_1381_);
lean_ctor_set(v___x_1388_, 0, v_fvarId_1379_);
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_fvarId_1379_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_a_1381_);
v___x_1391_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1393_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1391_);
v___x_1393_ = v___x_1383_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_object* v___x_1400_; 
lean_dec(v_a_1381_);
lean_dec(v_fvarId_1379_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v_code_1111_);
v___x_1400_ = v___x_1383_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_code_1111_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec(v_fvarId_1379_);
lean_dec_ref_known(v_code_1111_, 2);
v_a_1407_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1380_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1380_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
else
{
lean_object* v___x_1415_; 
lean_dec_ref_known(v_code_1111_, 2);
v___x_1415_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1376_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
return v___x_1415_;
}
}
case 4:
{
lean_object* v_cases_1416_; lean_object* v_typeName_1417_; lean_object* v_resultType_1418_; lean_object* v_discr_1419_; lean_object* v_alts_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1473_; 
v_cases_1416_ = lean_ctor_get(v_code_1111_, 0);
lean_inc_ref(v_cases_1416_);
v_typeName_1417_ = lean_ctor_get(v_cases_1416_, 0);
v_resultType_1418_ = lean_ctor_get(v_cases_1416_, 1);
v_discr_1419_ = lean_ctor_get(v_cases_1416_, 2);
v_alts_1420_ = lean_ctor_get(v_cases_1416_, 3);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_cases_1416_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1422_ = v_cases_1416_;
v_isShared_1423_ = v_isSharedCheck_1473_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_alts_1420_);
lean_inc(v_discr_1419_);
lean_inc(v_resultType_1418_);
lean_inc(v_typeName_1417_);
lean_dec(v_cases_1416_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1473_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v_subst_1425_; uint8_t v___x_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; 
v___x_1424_ = lean_st_ref_get(v_a_1112_);
v_subst_1425_ = lean_ctor_get(v___x_1424_, 1);
lean_inc_ref(v_subst_1425_);
lean_dec(v___x_1424_);
v___x_1426_ = 0;
v___x_1427_ = 0;
lean_inc(v_discr_1419_);
v___x_1428_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1425_, v_discr_1419_, v___x_1427_);
lean_dec_ref(v_subst_1425_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_fvarId_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1471_; 
v_fvarId_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1471_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_fvarId_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1471_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = lean_st_ref_get(v_a_1112_);
v___x_1434_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1420_);
v___x_1435_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(v_shouldElimFunDecls_1110_, v___x_1434_, v_alts_1420_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1462_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1462_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1462_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v_subst_1440_; lean_object* v___x_1441_; uint8_t v___y_1453_; size_t v___x_1456_; size_t v___x_1457_; uint8_t v___x_1458_; 
v_subst_1440_ = lean_ctor_get(v___x_1433_, 1);
lean_inc_ref(v_subst_1440_);
lean_dec(v___x_1433_);
lean_inc_ref(v_resultType_1418_);
v___x_1441_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_1426_, v_subst_1440_, v___x_1427_, v_resultType_1418_);
lean_dec_ref(v_subst_1440_);
v___x_1456_ = lean_ptr_addr(v_alts_1420_);
lean_dec_ref(v_alts_1420_);
v___x_1457_ = lean_ptr_addr(v_a_1436_);
v___x_1458_ = lean_usize_dec_eq(v___x_1456_, v___x_1457_);
if (v___x_1458_ == 0)
{
lean_dec_ref(v_resultType_1418_);
v___y_1453_ = v___x_1458_;
goto v___jp_1452_;
}
else
{
size_t v___x_1459_; size_t v___x_1460_; uint8_t v___x_1461_; 
v___x_1459_ = lean_ptr_addr(v_resultType_1418_);
lean_dec_ref(v_resultType_1418_);
v___x_1460_ = lean_ptr_addr(v___x_1441_);
v___x_1461_ = lean_usize_dec_eq(v___x_1459_, v___x_1460_);
v___y_1453_ = v___x_1461_;
goto v___jp_1452_;
}
v___jp_1442_:
{
lean_object* v___x_1444_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 3, v_a_1436_);
lean_ctor_set(v___x_1422_, 2, v_fvarId_1429_);
lean_ctor_set(v___x_1422_, 1, v___x_1441_);
v___x_1444_ = v___x_1422_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_typeName_1417_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1451_, 2, v_fvarId_1429_);
lean_ctor_set(v_reuseFailAlloc_1451_, 3, v_a_1436_);
v___x_1444_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1446_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set_tag(v___x_1431_, 4);
lean_ctor_set(v___x_1431_, 0, v___x_1444_);
v___x_1446_ = v___x_1431_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1448_; 
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1446_);
v___x_1448_ = v___x_1438_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1446_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
v___jp_1452_:
{
if (v___y_1453_ == 0)
{
lean_dec(v_discr_1419_);
lean_dec_ref_known(v_code_1111_, 1);
goto v___jp_1442_;
}
else
{
uint8_t v___x_1454_; 
v___x_1454_ = l_Lean_instBEqFVarId_beq(v_discr_1419_, v_fvarId_1429_);
lean_dec(v_discr_1419_);
if (v___x_1454_ == 0)
{
lean_dec_ref_known(v_code_1111_, 1);
goto v___jp_1442_;
}
else
{
lean_object* v___x_1455_; 
lean_dec_ref(v___x_1441_);
lean_del_object(v___x_1438_);
lean_dec(v_a_1436_);
lean_del_object(v___x_1431_);
lean_dec(v_fvarId_1429_);
lean_del_object(v___x_1422_);
lean_dec(v_typeName_1417_);
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v_code_1111_);
return v___x_1455_;
}
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec(v___x_1433_);
lean_del_object(v___x_1431_);
lean_dec(v_fvarId_1429_);
lean_del_object(v___x_1422_);
lean_dec_ref(v_alts_1420_);
lean_dec(v_discr_1419_);
lean_dec_ref(v_resultType_1418_);
lean_dec(v_typeName_1417_);
lean_dec_ref_known(v_code_1111_, 1);
v_a_1463_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1435_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1435_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
else
{
lean_object* v___x_1472_; 
lean_del_object(v___x_1422_);
lean_dec_ref(v_alts_1420_);
lean_dec(v_discr_1419_);
lean_dec_ref(v_resultType_1418_);
lean_dec(v_typeName_1417_);
lean_dec_ref_known(v_code_1111_, 1);
v___x_1472_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1426_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
return v___x_1472_;
}
}
}
case 5:
{
lean_object* v_fvarId_1474_; lean_object* v___x_1475_; lean_object* v_subst_1476_; uint8_t v___x_1477_; lean_object* v___x_1478_; 
v_fvarId_1474_ = lean_ctor_get(v_code_1111_, 0);
v___x_1475_ = lean_st_ref_get(v_a_1112_);
v_subst_1476_ = lean_ctor_get(v___x_1475_, 1);
lean_inc_ref(v_subst_1476_);
lean_dec(v___x_1475_);
v___x_1477_ = 0;
lean_inc(v_fvarId_1474_);
v___x_1478_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1476_, v_fvarId_1474_, v___x_1477_);
lean_dec_ref(v_subst_1476_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_fvarId_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1498_; 
v_fvarId_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1498_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_fvarId_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1498_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
uint8_t v___x_1483_; 
v___x_1483_ = l_Lean_instBEqFVarId_beq(v_fvarId_1474_, v_fvarId_1479_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1493_; 
v_isSharedCheck_1493_ = !lean_is_exclusive(v_code_1111_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v_code_1111_, 0);
lean_dec(v_unused_1494_);
v___x_1485_ = v_code_1111_;
v_isShared_1486_ = v_isSharedCheck_1493_;
goto v_resetjp_1484_;
}
else
{
lean_dec(v_code_1111_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1493_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v_fvarId_1479_);
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_fvarId_1479_);
v___x_1488_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1490_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1488_);
v___x_1490_ = v___x_1481_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
else
{
lean_object* v___x_1496_; 
lean_dec(v_fvarId_1479_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v_code_1111_);
v___x_1496_ = v___x_1481_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_code_1111_);
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
uint8_t v___x_1499_; lean_object* v___x_1500_; 
lean_dec_ref_known(v_code_1111_, 1);
v___x_1499_ = 0;
v___x_1500_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1499_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
return v___x_1500_;
}
}
default: 
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v_code_1111_);
return v___x_1501_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(uint8_t v_shouldElimFunDecls_1502_, lean_object* v_decl_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v_params_1510_; lean_object* v_type_1511_; lean_object* v_value_1512_; lean_object* v___x_1513_; lean_object* v_subst_1514_; uint8_t v___x_1515_; uint8_t v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v_params_1510_ = lean_ctor_get(v_decl_1503_, 2);
v_type_1511_ = lean_ctor_get(v_decl_1503_, 3);
v_value_1512_ = lean_ctor_get(v_decl_1503_, 4);
v___x_1513_ = lean_st_ref_get(v_a_1504_);
v_subst_1514_ = lean_ctor_get(v___x_1513_, 1);
lean_inc_ref(v_subst_1514_);
lean_dec(v___x_1513_);
v___x_1515_ = 0;
v___x_1516_ = 0;
lean_inc_ref(v_type_1511_);
v___x_1517_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_1515_, v_subst_1514_, v___x_1516_, v_type_1511_);
lean_dec_ref(v_subst_1514_);
lean_inc_ref(v_params_1510_);
v___x_1518_ = l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(v___x_1515_, v___x_1516_, v_params_1510_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1520_; lean_object* v_map_1521_; lean_object* v_r_1522_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v___x_1520_ = lean_st_ref_get(v_a_1504_);
v_map_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc_ref(v_map_1521_);
lean_dec(v___x_1520_);
lean_inc_ref(v_value_1512_);
v_r_1522_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1502_, v_value_1512_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
if (lean_obj_tag(v_r_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1540_; 
v_a_1523_ = lean_ctor_get(v_r_1522_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v_r_1522_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1525_ = v_r_1522_;
v_isShared_1526_ = v_isSharedCheck_1540_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v_r_1522_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1540_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
lean_inc(v_a_1523_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set_tag(v___x_1525_, 1);
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1529_; 
v___x_1529_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(v_a_1504_, v_map_1521_, v___x_1528_);
lean_dec_ref(v___x_1528_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v___x_1530_; 
lean_dec_ref_known(v___x_1529_, 1);
v___x_1530_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1515_, v_decl_1503_, v___x_1517_, v_a_1519_, v_a_1523_, v_a_1506_);
return v___x_1530_;
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_a_1523_);
lean_dec(v_a_1519_);
lean_dec_ref(v___x_1517_);
lean_dec_ref(v_decl_1503_);
v_a_1531_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1529_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1529_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_dec(v_a_1519_);
lean_dec_ref(v___x_1517_);
lean_dec_ref(v_decl_1503_);
v_a_1541_ = lean_ctor_get(v_r_1522_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v_r_1522_, 1);
v___x_1542_ = lean_box(0);
v___x_1543_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(v_a_1504_, v_map_1521_, v___x_1542_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v___x_1543_, 0);
lean_dec(v_unused_1551_);
v___x_1545_ = v___x_1543_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_dec(v___x_1543_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set_tag(v___x_1545_, 1);
lean_ctor_set(v___x_1545_, 0, v_a_1541_);
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1541_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec(v_a_1541_);
v_a_1552_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1543_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1543_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec_ref(v___x_1517_);
lean_dec_ref(v_decl_1503_);
v_a_1560_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1518_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1518_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___boxed(lean_object* v_shouldElimFunDecls_1568_, lean_object* v_decl_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1576_; lean_object* v_res_1577_; 
v_shouldElimFunDecls_boxed_1576_ = lean_unbox(v_shouldElimFunDecls_1568_);
v_res_1577_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_boxed_1576_, v_decl_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
lean_dec(v_a_1570_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___boxed(lean_object* v_shouldElimFunDecls_1578_, lean_object* v_i_1579_, lean_object* v_as_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1587_; lean_object* v_res_1588_; 
v_shouldElimFunDecls_boxed_1587_ = lean_unbox(v_shouldElimFunDecls_1578_);
v_res_1588_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(v_shouldElimFunDecls_boxed_1587_, v_i_1579_, v_as_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___boxed(lean_object* v_shouldElimFunDecls_1589_, lean_object* v_code_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1597_; lean_object* v_res_1598_; 
v_shouldElimFunDecls_boxed_1597_ = lean_unbox(v_shouldElimFunDecls_1589_);
v_res_1598_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_boxed_1597_, v_code_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
lean_dec(v_a_1591_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2(uint8_t v_pu_1599_, uint8_t v_t_1600_, lean_object* v_decl_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v_pu_1599_, v_t_1600_, v_decl_1601_, v___y_1602_, v___y_1604_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___boxed(lean_object* v_pu_1609_, lean_object* v_t_1610_, lean_object* v_decl_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
uint8_t v_pu_boxed_1618_; uint8_t v_t_boxed_1619_; lean_object* v_res_1620_; 
v_pu_boxed_1618_ = lean_unbox(v_pu_1609_);
v_t_boxed_1619_ = lean_unbox(v_t_1610_);
v_res_1620_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2(v_pu_boxed_1618_, v_t_boxed_1619_, v_decl_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5(uint8_t v_pu_1621_, uint8_t v_t_1622_, lean_object* v_args_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v_pu_1621_, v_t_1622_, v_args_1623_, v___y_1624_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___boxed(lean_object* v_pu_1631_, lean_object* v_t_1632_, lean_object* v_args_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
uint8_t v_pu_boxed_1640_; uint8_t v_t_boxed_1641_; lean_object* v_res_1642_; 
v_pu_boxed_1640_ = lean_unbox(v_pu_1631_);
v_t_boxed_1641_ = lean_unbox(v_t_1632_);
v_res_1642_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5(v_pu_boxed_1640_, v_t_boxed_1641_, v_args_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3(lean_object* v_00_u03b2_1643_, lean_object* v_x_1644_, lean_object* v_x_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_x_1644_, v_x_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___boxed(lean_object* v_00_u03b2_1647_, lean_object* v_x_1648_, lean_object* v_x_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3(v_00_u03b2_1647_, v_x_1648_, v_x_1649_);
lean_dec_ref(v_x_1649_);
lean_dec_ref(v_x_1648_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4(lean_object* v_00_u03b2_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_, lean_object* v_x_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_x_1652_, v_x_1653_, v_x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(uint8_t v_pu_1656_, uint8_t v_t_1657_, lean_object* v_i_1658_, lean_object* v_as_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(v_pu_1656_, v_t_1657_, v_i_1658_, v_as_1659_, v___y_1660_, v___y_1662_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___boxed(lean_object* v_pu_1667_, lean_object* v_t_1668_, lean_object* v_i_1669_, lean_object* v_as_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
uint8_t v_pu_boxed_1677_; uint8_t v_t_boxed_1678_; lean_object* v_res_1679_; 
v_pu_boxed_1677_ = lean_unbox(v_pu_1667_);
v_t_boxed_1678_ = lean_unbox(v_t_1668_);
v_res_1679_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(v_pu_boxed_1677_, v_t_boxed_1678_, v_i_1669_, v_as_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4(lean_object* v_00_u03b2_1680_, lean_object* v_x_1681_, size_t v_x_1682_, lean_object* v_x_1683_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_1681_, v_x_1682_, v_x_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1685_, lean_object* v_x_1686_, lean_object* v_x_1687_, lean_object* v_x_1688_){
_start:
{
size_t v_x_17261__boxed_1689_; lean_object* v_res_1690_; 
v_x_17261__boxed_1689_ = lean_unbox_usize(v_x_1687_);
lean_dec(v_x_1687_);
v_res_1690_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4(v_00_u03b2_1685_, v_x_1686_, v_x_17261__boxed_1689_, v_x_1688_);
lean_dec_ref(v_x_1688_);
lean_dec_ref(v_x_1686_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6(lean_object* v_00_u03b2_1691_, lean_object* v_x_1692_, size_t v_x_1693_, size_t v_x_1694_, lean_object* v_x_1695_, lean_object* v_x_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_1692_, v_x_1693_, v_x_1694_, v_x_1695_, v_x_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_, lean_object* v_x_1701_, lean_object* v_x_1702_, lean_object* v_x_1703_){
_start:
{
size_t v_x_17272__boxed_1704_; size_t v_x_17273__boxed_1705_; lean_object* v_res_1706_; 
v_x_17272__boxed_1704_ = lean_unbox_usize(v_x_1700_);
lean_dec(v_x_1700_);
v_x_17273__boxed_1705_ = lean_unbox_usize(v_x_1701_);
lean_dec(v_x_1701_);
v_res_1706_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6(v_00_u03b2_1698_, v_x_1699_, v_x_17272__boxed_1704_, v_x_17273__boxed_1705_, v_x_1702_, v_x_1703_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1707_, lean_object* v_keys_1708_, lean_object* v_vals_1709_, lean_object* v_heq_1710_, lean_object* v_i_1711_, lean_object* v_k_1712_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(v_keys_1708_, v_vals_1709_, v_i_1711_, v_k_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1714_, lean_object* v_keys_1715_, lean_object* v_vals_1716_, lean_object* v_heq_1717_, lean_object* v_i_1718_, lean_object* v_k_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6(v_00_u03b2_1714_, v_keys_1715_, v_vals_1716_, v_heq_1717_, v_i_1718_, v_k_1719_);
lean_dec_ref(v_k_1719_);
lean_dec_ref(v_vals_1716_);
lean_dec_ref(v_keys_1715_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_1721_, lean_object* v_n_1722_, lean_object* v_k_1723_, lean_object* v_v_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(v_n_1722_, v_k_1723_, v_v_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_1726_, size_t v_depth_1727_, lean_object* v_keys_1728_, lean_object* v_vals_1729_, lean_object* v_heq_1730_, lean_object* v_i_1731_, lean_object* v_entries_1732_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_depth_1727_, v_keys_1728_, v_vals_1729_, v_i_1731_, v_entries_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1734_, lean_object* v_depth_1735_, lean_object* v_keys_1736_, lean_object* v_vals_1737_, lean_object* v_heq_1738_, lean_object* v_i_1739_, lean_object* v_entries_1740_){
_start:
{
size_t v_depth_boxed_1741_; lean_object* v_res_1742_; 
v_depth_boxed_1741_ = lean_unbox_usize(v_depth_1735_);
lean_dec(v_depth_1735_);
v_res_1742_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10(v_00_u03b2_1734_, v_depth_boxed_1741_, v_keys_1736_, v_vals_1737_, v_heq_1738_, v_i_1739_, v_entries_1740_);
lean_dec_ref(v_vals_1737_);
lean_dec_ref(v_keys_1736_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_1743_, lean_object* v_x_1744_, lean_object* v_x_1745_, lean_object* v_x_1746_, lean_object* v_x_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(v_x_1744_, v_x_1745_, v_x_1746_, v_x_1747_);
return v___x_1748_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__0(void){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1749_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__1(void){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__0, &l_Lean_Compiler_LCNF_Code_cse___closed__0_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__0);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__2(void){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = lean_box(0);
v___x_1753_ = lean_unsigned_to_nat(16u);
v___x_1754_ = lean_mk_array(v___x_1753_, v___x_1752_);
return v___x_1754_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__3(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__2, &l_Lean_Compiler_LCNF_Code_cse___closed__2_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__2);
v___x_1756_ = lean_unsigned_to_nat(0u);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v___x_1755_);
return v___x_1757_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__4(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__3, &l_Lean_Compiler_LCNF_Code_cse___closed__3_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__3);
v___x_1759_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__1, &l_Lean_Compiler_LCNF_Code_cse___closed__1_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__1);
v___x_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
lean_ctor_set(v___x_1760_, 1, v___x_1758_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse(uint8_t v_shouldElimFunDecls_1761_, lean_object* v_code_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__4, &l_Lean_Compiler_LCNF_Code_cse___closed__4_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__4);
v___x_1769_ = lean_st_mk_ref(v___x_1768_);
v___x_1770_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1761_, v_code_1762_, v___x_1769_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1779_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1779_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1779_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1775_ = lean_st_ref_get(v___x_1769_);
lean_dec(v___x_1769_);
lean_dec(v___x_1775_);
if (v_isShared_1774_ == 0)
{
v___x_1777_ = v___x_1773_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1771_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
else
{
lean_dec(v___x_1769_);
return v___x_1770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse___boxed(lean_object* v_shouldElimFunDecls_1780_, lean_object* v_code_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1787_; lean_object* v_res_1788_; 
v_shouldElimFunDecls_boxed_1787_ = lean_unbox(v_shouldElimFunDecls_1780_);
v_res_1788_ = l_Lean_Compiler_LCNF_Code_cse(v_shouldElimFunDecls_boxed_1787_, v_code_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(lean_object* v_f_1789_, lean_object* v_v_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
if (lean_obj_tag(v_v_1790_) == 0)
{
lean_object* v_code_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1820_; 
v_code_1796_ = lean_ctor_get(v_v_1790_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_v_1790_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1798_ = v_v_1790_;
v_isShared_1799_ = v_isSharedCheck_1820_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_code_1796_);
lean_dec(v_v_1790_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1820_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; 
lean_inc(v___y_1794_);
lean_inc_ref(v___y_1793_);
lean_inc(v___y_1792_);
lean_inc_ref(v___y_1791_);
v___x_1800_ = lean_apply_6(v_f_1789_, v_code_1796_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, lean_box(0));
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1811_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1811_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1811_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v_a_1801_);
v___x_1806_ = v___x_1798_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1808_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1806_);
v___x_1808_ = v___x_1803_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_del_object(v___x_1798_);
v_a_1812_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1800_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1800_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
else
{
lean_object* v___x_1821_; 
lean_dec_ref(v_f_1789_);
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v_v_1790_);
return v___x_1821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg___boxed(lean_object* v_f_1822_, lean_object* v_v_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v_f_1822_, v_v_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0(uint8_t v_pu_1830_, lean_object* v_f_1831_, lean_object* v_v_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v_f_1831_, v_v_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___boxed(lean_object* v_pu_1839_, lean_object* v_f_1840_, lean_object* v_v_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
uint8_t v_pu_boxed_1847_; lean_object* v_res_1848_; 
v_pu_boxed_1847_ = lean_unbox(v_pu_1839_);
v_res_1848_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0(v_pu_boxed_1847_, v_f_1840_, v_v_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0(uint8_t v_shouldElimFunDecls_1849_, lean_object* v_x_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_Compiler_LCNF_Code_cse(v_shouldElimFunDecls_1849_, v_x_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed(lean_object* v_shouldElimFunDecls_1857_, lean_object* v_x_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1864_; lean_object* v_res_1865_; 
v_shouldElimFunDecls_boxed_1864_ = lean_unbox(v_shouldElimFunDecls_1857_);
v_res_1865_ = l_Lean_Compiler_LCNF_Decl_cse___lam__0(v_shouldElimFunDecls_boxed_1864_, v_x_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse(uint8_t v_shouldElimFunDecls_1866_, lean_object* v_decl_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v_toSignature_1873_; lean_object* v_value_1874_; uint8_t v_recursive_1875_; lean_object* v_inlineAttr_x3f_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1902_; 
v_toSignature_1873_ = lean_ctor_get(v_decl_1867_, 0);
v_value_1874_ = lean_ctor_get(v_decl_1867_, 1);
v_recursive_1875_ = lean_ctor_get_uint8(v_decl_1867_, sizeof(void*)*3);
v_inlineAttr_x3f_1876_ = lean_ctor_get(v_decl_1867_, 2);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_decl_1867_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1878_ = v_decl_1867_;
v_isShared_1879_ = v_isSharedCheck_1902_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_inlineAttr_x3f_1876_);
lean_inc(v_value_1874_);
lean_inc(v_toSignature_1873_);
lean_dec(v_decl_1867_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1902_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v___f_1881_; lean_object* v___x_1882_; 
v___x_1880_ = lean_box(v_shouldElimFunDecls_1866_);
v___f_1881_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1881_, 0, v___x_1880_);
v___x_1882_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v___f_1881_, v_value_1874_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1893_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1893_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1893_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v_a_1883_);
v___x_1888_ = v___x_1878_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_toSignature_1873_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_a_1883_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_inlineAttr_x3f_1876_);
lean_ctor_set_uint8(v_reuseFailAlloc_1892_, sizeof(void*)*3, v_recursive_1875_);
v___x_1888_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1888_);
v___x_1890_ = v___x_1885_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_del_object(v___x_1878_);
lean_dec(v_inlineAttr_x3f_1876_);
lean_dec_ref(v_toSignature_1873_);
v_a_1894_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1882_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1882_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___boxed(lean_object* v_shouldElimFunDecls_1903_, lean_object* v_decl_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1910_; lean_object* v_res_1911_; 
v_shouldElimFunDecls_boxed_1910_ = lean_unbox(v_shouldElimFunDecls_1903_);
v_res_1911_ = l_Lean_Compiler_LCNF_Decl_cse(v_shouldElimFunDecls_boxed_1910_, v_decl_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
lean_dec(v_a_1908_);
lean_dec_ref(v_a_1907_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___lam__0(uint8_t v_shouldElimFunDecls_1915_, uint8_t v_phase_1916_, lean_object* v_occurrence_1917_, lean_object* v_h_1918_){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1919_ = ((lean_object*)(l_Lean_Compiler_LCNF_cse___lam__0___closed__1));
v___x_1920_ = lean_box(v_shouldElimFunDecls_1915_);
v___x_1921_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_cse___boxed), 7, 1);
lean_closure_set(v___x_1921_, 0, v___x_1920_);
v___x_1922_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1919_, v_phase_1916_, v___x_1921_, v_occurrence_1917_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___lam__0___boxed(lean_object* v_shouldElimFunDecls_1923_, lean_object* v_phase_1924_, lean_object* v_occurrence_1925_, lean_object* v_h_1926_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1927_; uint8_t v_phase_boxed_1928_; lean_object* v_res_1929_; 
v_shouldElimFunDecls_boxed_1927_ = lean_unbox(v_shouldElimFunDecls_1923_);
v_phase_boxed_1928_ = lean_unbox(v_phase_1924_);
v_res_1929_ = l_Lean_Compiler_LCNF_cse___lam__0(v_shouldElimFunDecls_boxed_1927_, v_phase_boxed_1928_, v_occurrence_1925_, v_h_1926_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse(uint8_t v_phase_1930_, uint8_t v_shouldElimFunDecls_1931_, lean_object* v_occurrence_1932_){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___f_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; lean_object* v___x_1938_; 
v___x_1933_ = lean_box(v_shouldElimFunDecls_1931_);
v___x_1934_ = lean_box(v_phase_1930_);
v___f_1935_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_cse___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1935_, 0, v___x_1933_);
lean_closure_set(v___f_1935_, 1, v___x_1934_);
lean_closure_set(v___f_1935_, 2, v_occurrence_1932_);
v___x_1936_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_1937_ = 0;
v___x_1938_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_1936_, v_phase_1930_, v___x_1937_, v___f_1935_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___boxed(lean_object* v_phase_1939_, lean_object* v_shouldElimFunDecls_1940_, lean_object* v_occurrence_1941_){
_start:
{
uint8_t v_phase_boxed_1942_; uint8_t v_shouldElimFunDecls_boxed_1943_; lean_object* v_res_1944_; 
v_phase_boxed_1942_ = lean_unbox(v_phase_1939_);
v_shouldElimFunDecls_boxed_1943_ = lean_unbox(v_shouldElimFunDecls_1940_);
v_res_1944_ = l_Lean_Compiler_LCNF_cse(v_phase_boxed_1942_, v_shouldElimFunDecls_boxed_1943_, v_occurrence_1941_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2015_; uint8_t v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2015_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_));
v___x_2016_ = 1;
v___x_2017_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_));
v___x_2018_ = l_Lean_registerTraceClass(v___x_2015_, v___x_2016_, v___x_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2____boxed(lean_object* v_a_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_();
return v_res_2020_;
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
