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
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedPass;
lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftBaseIOEIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__7_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__8_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_liftIOCore___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__9_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__10_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__11_value;
static const lean_closure_object l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___lam__0(lean_object* v_____do__lift_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v_res_10_;
v_res_10_ = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___lam__0(v_____do__lift_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___lam__0___boxed(lean_object* v_____do__lift_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___lam__0(v_____do__lift_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
lean_dec(v___y_12_);
lean_dec_ref(v_____do__lift_11_);
return v_res_18_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__0(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_instMonadEIO___redArg();
return v___x_19_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_obj_once(&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__0, &l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__0_once, _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__0);
v___x_21_ = l_StateRefT_x27_instMonad___redArg(v___x_20_);
return v___x_21_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse(void){
_start:
{
lean_object* v___x_50_; lean_object* v_toApplicative_51_; lean_object* v_toFunctor_52_; lean_object* v_toSeq_53_; lean_object* v_toSeqLeft_54_; lean_object* v_toSeqRight_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___f_59_; lean_object* v___x_60_; lean_object* v___f_61_; lean_object* v___f_62_; lean_object* v___f_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v_toApplicative_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_97_; 
v___x_50_ = lean_obj_once(&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1, &l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1_once, _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1);
v_toApplicative_51_ = lean_ctor_get(v___x_50_, 0);
v_toFunctor_52_ = lean_ctor_get(v_toApplicative_51_, 0);
v_toSeq_53_ = lean_ctor_get(v_toApplicative_51_, 2);
v_toSeqLeft_54_ = lean_ctor_get(v_toApplicative_51_, 3);
v_toSeqRight_55_ = lean_ctor_get(v_toApplicative_51_, 4);
v___f_56_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__2));
v___f_57_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__3));
lean_inc_ref_n(v_toFunctor_52_, 2);
v___f_58_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_58_, 0, v_toFunctor_52_);
v___f_59_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_59_, 0, v_toFunctor_52_);
v___x_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_60_, 0, v___f_58_);
lean_ctor_set(v___x_60_, 1, v___f_59_);
lean_inc(v_toSeqRight_55_);
v___f_61_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_61_, 0, v_toSeqRight_55_);
lean_inc(v_toSeqLeft_54_);
v___f_62_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_62_, 0, v_toSeqLeft_54_);
lean_inc(v_toSeq_53_);
v___f_63_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_63_, 0, v_toSeq_53_);
v___x_64_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_64_, 0, v___x_60_);
lean_ctor_set(v___x_64_, 1, v___f_56_);
lean_ctor_set(v___x_64_, 2, v___f_63_);
lean_ctor_set(v___x_64_, 3, v___f_62_);
lean_ctor_set(v___x_64_, 4, v___f_61_);
v___x_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___f_57_);
v___x_66_ = l_StateRefT_x27_instMonad___redArg(v___x_65_);
v_toApplicative_67_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_97_ == 0)
{
lean_object* v_unused_98_; 
v_unused_98_ = lean_ctor_get(v___x_66_, 1);
lean_dec(v_unused_98_);
v___x_69_ = v___x_66_;
v_isShared_70_ = v_isSharedCheck_97_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_toApplicative_67_);
lean_dec(v___x_66_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_97_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v_toFunctor_71_; lean_object* v_toSeq_72_; lean_object* v_toSeqLeft_73_; lean_object* v_toSeqRight_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_95_; 
v_toFunctor_71_ = lean_ctor_get(v_toApplicative_67_, 0);
v_toSeq_72_ = lean_ctor_get(v_toApplicative_67_, 2);
v_toSeqLeft_73_ = lean_ctor_get(v_toApplicative_67_, 3);
v_toSeqRight_74_ = lean_ctor_get(v_toApplicative_67_, 4);
v_isSharedCheck_95_ = !lean_is_exclusive(v_toApplicative_67_);
if (v_isSharedCheck_95_ == 0)
{
lean_object* v_unused_96_; 
v_unused_96_ = lean_ctor_get(v_toApplicative_67_, 1);
lean_dec(v_unused_96_);
v___x_76_ = v_toApplicative_67_;
v_isShared_77_ = v_isSharedCheck_95_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_toSeqRight_74_);
lean_inc(v_toSeqLeft_73_);
lean_inc(v_toSeq_72_);
lean_inc(v_toFunctor_71_);
lean_dec(v_toApplicative_67_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_95_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___f_78_; lean_object* v___f_79_; lean_object* v___f_80_; lean_object* v___f_81_; lean_object* v___f_82_; lean_object* v___x_83_; lean_object* v___f_84_; lean_object* v___f_85_; lean_object* v___f_86_; lean_object* v___x_88_; 
v___f_78_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__4));
v___f_79_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__5));
v___f_80_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__6));
lean_inc_ref(v_toFunctor_71_);
v___f_81_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_81_, 0, v_toFunctor_71_);
v___f_82_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_82_, 0, v_toFunctor_71_);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v___f_81_);
lean_ctor_set(v___x_83_, 1, v___f_82_);
v___f_84_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_84_, 0, v_toSeqRight_74_);
v___f_85_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_85_, 0, v_toSeqLeft_73_);
v___f_86_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_86_, 0, v_toSeq_72_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 4, v___f_84_);
lean_ctor_set(v___x_76_, 3, v___f_85_);
lean_ctor_set(v___x_76_, 2, v___f_86_);
lean_ctor_set(v___x_76_, 1, v___f_79_);
lean_ctor_set(v___x_76_, 0, v___x_83_);
v___x_88_ = v___x_76_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_83_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v___f_79_);
lean_ctor_set(v_reuseFailAlloc_94_, 2, v___f_86_);
lean_ctor_set(v_reuseFailAlloc_94_, 3, v___f_85_);
lean_ctor_set(v_reuseFailAlloc_94_, 4, v___f_84_);
v___x_88_ = v_reuseFailAlloc_94_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_90_; 
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 1, v___f_80_);
lean_ctor_set(v___x_69_, 0, v___x_88_);
v___x_90_ = v___x_69_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_88_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v___f_80_);
v___x_90_ = v_reuseFailAlloc_93_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__18));
v___x_92_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_92_, 0, lean_box(0));
lean_closure_set(v___x_92_, 1, lean_box(0));
lean_closure_set(v___x_92_, 2, v___x_90_);
lean_closure_set(v___x_92_, 3, lean_box(0));
lean_closure_set(v___x_92_, 4, lean_box(0));
lean_closure_set(v___x_92_, 5, v___x_91_);
lean_closure_set(v___x_92_, 6, v___f_78_);
return v___x_92_;
}
}
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0(lean_object* v_f_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___x_106_; lean_object* v_map_107_; lean_object* v_subst_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_119_; 
v___x_106_ = lean_st_ref_take(v___y_100_);
v_map_107_ = lean_ctor_get(v___x_106_, 0);
v_subst_108_ = lean_ctor_get(v___x_106_, 1);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_119_ == 0)
{
v___x_110_ = v___x_106_;
v_isShared_111_ = v_isSharedCheck_119_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_subst_108_);
lean_inc(v_map_107_);
lean_dec(v___x_106_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_119_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_112_ = lean_box(0);
v___x_113_ = lean_apply_1(v_f_99_, v_subst_108_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 1, v___x_113_);
v___x_115_ = v___x_110_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_map_107_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v___x_113_);
v___x_115_ = v_reuseFailAlloc_118_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_st_ref_put(v___y_100_, v___x_115_);
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_112_);
return v___x_117_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_99_ = stack[0].m_obj;
lean_object* v___y_100_ = stack[1].m_obj;
lean_object* v___y_101_ = stack[2].m_obj;
lean_object* v___y_102_ = stack[3].m_obj;
lean_object* v___y_103_ = stack[4].m_obj;
lean_object* v___y_104_ = stack[5].m_obj;
lean_object* v_res_120_;
v_res_120_ = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0(v_f_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
stack->m_obj
 = v_res_120_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0___boxed(lean_object* v_f_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0(v_f_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
return v_res_128_;
}
}
lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___redArg(lean_object* v_a_131_){
_start:
{
lean_object* v___x_133_; lean_object* v_subst_134_; lean_object* v___x_135_; 
v___x_133_ = lean_st_ref_get(v_a_131_);
v_subst_134_ = lean_ctor_get(v___x_133_, 1);
lean_inc_ref(v_subst_134_);
lean_dec(v___x_133_);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v_subst_134_);
return v___x_135_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CSE_getSubst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_131_ = stack[0].m_obj;
lean_object* v_res_136_;
v_res_136_ = l_Lean_Compiler_LCNF_CSE_getSubst___redArg(v_a_131_);
stack->m_obj
 = v_res_136_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___redArg___boxed(lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Compiler_LCNF_CSE_getSubst___redArg(v_a_137_);
lean_dec(v_a_137_);
return v_res_139_;
}
}
lean_object* l_Lean_Compiler_LCNF_CSE_getSubst(lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v___x_146_; lean_object* v_subst_147_; lean_object* v___x_148_; 
v___x_146_ = lean_st_ref_get(v_a_140_);
v_subst_147_ = lean_ctor_get(v___x_146_, 1);
lean_inc_ref(v_subst_147_);
lean_dec(v___x_146_);
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v_subst_147_);
return v___x_148_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CSE_getSubst_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_140_ = stack[0].m_obj;
lean_object* v_a_141_ = stack[1].m_obj;
lean_object* v_a_142_ = stack[2].m_obj;
lean_object* v_a_143_ = stack[3].m_obj;
lean_object* v_a_144_ = stack[4].m_obj;
lean_object* v_res_149_;
v_res_149_ = l_Lean_Compiler_LCNF_CSE_getSubst(v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
stack->m_obj
 = v_res_149_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___boxed(lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Compiler_LCNF_CSE_getSubst(v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
return v_res_156_;
}
}
lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg(lean_object* v_value_159_, lean_object* v_fvarId_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_map_166_; lean_object* v_subst_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_178_; 
v___x_163_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0));
v___x_164_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1));
v___x_165_ = lean_st_ref_take(v_a_161_);
v_map_166_ = lean_ctor_get(v___x_165_, 0);
v_subst_167_ = lean_ctor_get(v___x_165_, 1);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_178_ == 0)
{
v___x_169_ = v___x_165_;
v_isShared_170_ = v_isSharedCheck_178_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_subst_167_);
lean_inc(v_map_166_);
lean_dec(v___x_165_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_178_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_171_ = lean_box(0);
v___x_172_ = l_Lean_PersistentHashMap_insert___redArg(v___x_163_, v___x_164_, v_map_166_, v_value_159_, v_fvarId_160_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_172_);
v___x_174_ = v___x_169_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_subst_167_);
v___x_174_ = v_reuseFailAlloc_177_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_st_ref_put(v_a_161_, v___x_174_);
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_171_);
return v___x_176_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CSE_addEntry___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_159_ = stack[0].m_obj;
lean_object* v_fvarId_160_ = stack[1].m_obj;
lean_object* v_a_161_ = stack[2].m_obj;
lean_object* v_res_179_;
v_res_179_ = l_Lean_Compiler_LCNF_CSE_addEntry___redArg(v_value_159_, v_fvarId_160_, v_a_161_);
stack->m_obj
 = v_res_179_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg___boxed(lean_object* v_value_180_, lean_object* v_fvarId_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Compiler_LCNF_CSE_addEntry___redArg(v_value_180_, v_fvarId_181_, v_a_182_);
lean_dec(v_a_182_);
return v_res_184_;
}
}
lean_object* l_Lean_Compiler_LCNF_CSE_addEntry(lean_object* v_value_185_, lean_object* v_fvarId_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v_map_196_; lean_object* v_subst_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_208_; 
v___x_193_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0));
v___x_194_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1));
v___x_195_ = lean_st_ref_take(v_a_187_);
v_map_196_ = lean_ctor_get(v___x_195_, 0);
v_subst_197_ = lean_ctor_get(v___x_195_, 1);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_208_ == 0)
{
v___x_199_ = v___x_195_;
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_subst_197_);
lean_inc(v_map_196_);
lean_dec(v___x_195_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_201_ = lean_box(0);
v___x_202_ = l_Lean_PersistentHashMap_insert___redArg(v___x_193_, v___x_194_, v_map_196_, v_value_185_, v_fvarId_186_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_202_);
v___x_204_ = v___x_199_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_subst_197_);
v___x_204_ = v_reuseFailAlloc_207_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_st_ref_put(v_a_187_, v___x_204_);
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_201_);
return v___x_206_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CSE_addEntry_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_185_ = stack[0].m_obj;
lean_object* v_fvarId_186_ = stack[1].m_obj;
lean_object* v_a_187_ = stack[2].m_obj;
lean_object* v_a_188_ = stack[3].m_obj;
lean_object* v_a_189_ = stack[4].m_obj;
lean_object* v_a_190_ = stack[5].m_obj;
lean_object* v_a_191_ = stack[6].m_obj;
lean_object* v_res_209_;
v_res_209_ = l_Lean_Compiler_LCNF_CSE_addEntry(v_value_185_, v_fvarId_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
stack->m_obj
 = v_res_209_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___boxed(lean_object* v_value_210_, lean_object* v_fvarId_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Compiler_LCNF_CSE_addEntry(v_value_210_, v_fvarId_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
return v_res_218_;
}
}
lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(lean_object* v_a_219_, lean_object* v_map_220_, lean_object* v_a_x3f_221_){
_start:
{
lean_object* v___x_223_; lean_object* v_subst_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_234_; 
v___x_223_ = lean_st_ref_take(v_a_219_);
v_subst_224_ = lean_ctor_get(v___x_223_, 1);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_234_ == 0)
{
lean_object* v_unused_235_; 
v_unused_235_ = lean_ctor_get(v___x_223_, 0);
lean_dec(v_unused_235_);
v___x_226_ = v___x_223_;
v_isShared_227_ = v_isSharedCheck_234_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_subst_224_);
lean_dec(v___x_223_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_234_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = lean_box(0);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v_map_220_);
v___x_230_ = v___x_226_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_map_220_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_subst_224_);
v___x_230_ = v_reuseFailAlloc_233_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_st_ref_put(v_a_219_, v___x_230_);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_228_);
return v___x_232_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_219_ = stack[0].m_obj;
lean_object* v_map_220_ = stack[1].m_obj;
lean_object* v_a_x3f_221_ = stack[2].m_obj;
lean_object* v_res_236_;
v_res_236_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(v_a_219_, v_map_220_, v_a_x3f_221_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0___boxed(lean_object* v_a_237_, lean_object* v_map_238_, lean_object* v_a_x3f_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(v_a_237_, v_map_238_, v_a_x3f_239_);
lean_dec(v_a_x3f_239_);
lean_dec(v_a_237_);
return v_res_241_;
}
}
lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg(lean_object* v_x_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v___x_249_; lean_object* v_map_250_; lean_object* v_r_251_; 
v___x_249_ = lean_st_ref_get(v_a_243_);
v_map_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc_ref(v_map_250_);
lean_dec(v___x_249_);
lean_inc(v_a_247_);
lean_inc_ref(v_a_246_);
lean_inc(v_a_245_);
lean_inc_ref(v_a_244_);
lean_inc(v_a_243_);
v_r_251_ = lean_apply_6(v_x_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, lean_box(0));
if (lean_obj_tag(v_r_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_268_; 
v_a_252_ = lean_ctor_get(v_r_251_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v_r_251_);
if (v_isSharedCheck_268_ == 0)
{
v___x_254_ = v_r_251_;
v_isShared_255_ = v_isSharedCheck_268_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v_r_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_268_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
lean_inc(v_a_252_);
if (v_isShared_255_ == 0)
{
lean_ctor_set_tag(v___x_254_, 1);
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_267_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
v___x_258_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(v_a_243_, v_map_250_, v___x_257_);
lean_dec_ref(v___x_257_);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; 
v_unused_266_ = lean_ctor_get(v___x_258_, 0);
lean_dec(v_unused_266_);
v___x_260_ = v___x_258_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_dec(v___x_258_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v_a_252_);
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_252_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
v_a_269_ = lean_ctor_get(v_r_251_, 0);
lean_inc(v_a_269_);
lean_dec_ref_known(v_r_251_, 1);
v___x_270_ = lean_box(0);
v___x_271_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(v_a_243_, v_map_250_, v___x_270_);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v___x_271_, 0);
lean_dec(v_unused_279_);
v___x_273_ = v___x_271_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_dec(v___x_271_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set_tag(v___x_273_, 1);
lean_ctor_set(v___x_273_, 0, v_a_269_);
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_269_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CSE_withNewScope___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_242_ = stack[0].m_obj;
lean_object* v_a_243_ = stack[1].m_obj;
lean_object* v_a_244_ = stack[2].m_obj;
lean_object* v_a_245_ = stack[3].m_obj;
lean_object* v_a_246_ = stack[4].m_obj;
lean_object* v_a_247_ = stack[5].m_obj;
lean_object* v_res_280_;
v_res_280_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg(v_x_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
stack->m_obj
 = v_res_280_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___boxed(lean_object* v_x_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg(v_x_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
return v_res_288_;
}
}
lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope(lean_object* v_00_u03b1_289_, lean_object* v_x_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_297_; lean_object* v_map_298_; lean_object* v_r_299_; 
v___x_297_ = lean_st_ref_get(v_a_291_);
v_map_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc_ref(v_map_298_);
lean_dec(v___x_297_);
lean_inc(v_a_295_);
lean_inc_ref(v_a_294_);
lean_inc(v_a_293_);
lean_inc_ref(v_a_292_);
lean_inc(v_a_291_);
v_r_299_ = lean_apply_6(v_x_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, lean_box(0));
if (lean_obj_tag(v_r_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_316_; 
v_a_300_ = lean_ctor_get(v_r_299_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v_r_299_);
if (v_isSharedCheck_316_ == 0)
{
v___x_302_ = v_r_299_;
v_isShared_303_ = v_isSharedCheck_316_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v_r_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_316_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
lean_inc(v_a_300_);
if (v_isShared_303_ == 0)
{
lean_ctor_set_tag(v___x_302_, 1);
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_315_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
v___x_306_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(v_a_291_, v_map_298_, v___x_305_);
lean_dec_ref(v___x_305_);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; 
v_unused_314_ = lean_ctor_get(v___x_306_, 0);
lean_dec(v_unused_314_);
v___x_308_ = v___x_306_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_dec(v___x_306_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v_a_300_);
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_300_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
v_a_317_ = lean_ctor_get(v_r_299_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v_r_299_, 1);
v___x_318_ = lean_box(0);
v___x_319_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(v_a_291_, v_map_298_, v___x_318_);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_326_ == 0)
{
lean_object* v_unused_327_; 
v_unused_327_ = lean_ctor_get(v___x_319_, 0);
lean_dec(v_unused_327_);
v___x_321_ = v___x_319_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_dec(v___x_319_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 1);
lean_ctor_set(v___x_321_, 0, v_a_317_);
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_317_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CSE_withNewScope_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_290_ = stack[1].m_obj;
lean_object* v_a_291_ = stack[2].m_obj;
lean_object* v_a_292_ = stack[3].m_obj;
lean_object* v_a_293_ = stack[4].m_obj;
lean_object* v_a_294_ = stack[5].m_obj;
lean_object* v_a_295_ = stack[6].m_obj;
lean_object* v_res_328_;
v_res_328_ = l_Lean_Compiler_LCNF_CSE_withNewScope(lean_box(0), v_x_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
stack->m_obj
 = v_res_328_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___boxed(lean_object* v_00_u03b1_329_, lean_object* v_x_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Compiler_LCNF_CSE_withNewScope(v_00_u03b1_329_, v_x_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
if (lean_obj_tag(v_x_339_) == 0)
{
return v_x_338_;
}
else
{
lean_object* v_key_340_; lean_object* v_value_341_; lean_object* v_tail_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_365_; 
v_key_340_ = lean_ctor_get(v_x_339_, 0);
v_value_341_ = lean_ctor_get(v_x_339_, 1);
v_tail_342_ = lean_ctor_get(v_x_339_, 2);
v_isSharedCheck_365_ = !lean_is_exclusive(v_x_339_);
if (v_isSharedCheck_365_ == 0)
{
v___x_344_ = v_x_339_;
v_isShared_345_ = v_isSharedCheck_365_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_tail_342_);
lean_inc(v_value_341_);
lean_inc(v_key_340_);
lean_dec(v_x_339_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_365_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; uint64_t v___x_347_; uint64_t v___x_348_; uint64_t v___x_349_; uint64_t v_fold_350_; uint64_t v___x_351_; uint64_t v___x_352_; uint64_t v___x_353_; size_t v___x_354_; size_t v___x_355_; size_t v___x_356_; size_t v___x_357_; size_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_346_ = lean_array_get_size(v_x_338_);
v___x_347_ = l_Lean_instHashableFVarId_hash(v_key_340_);
v___x_348_ = 32ULL;
v___x_349_ = lean_uint64_shift_right(v___x_347_, v___x_348_);
v_fold_350_ = lean_uint64_xor(v___x_347_, v___x_349_);
v___x_351_ = 16ULL;
v___x_352_ = lean_uint64_shift_right(v_fold_350_, v___x_351_);
v___x_353_ = lean_uint64_xor(v_fold_350_, v___x_352_);
v___x_354_ = lean_uint64_to_usize(v___x_353_);
v___x_355_ = lean_usize_of_nat(v___x_346_);
v___x_356_ = ((size_t)1ULL);
v___x_357_ = lean_usize_sub(v___x_355_, v___x_356_);
v___x_358_ = lean_usize_land(v___x_354_, v___x_357_);
v___x_359_ = lean_array_uget_borrowed(v_x_338_, v___x_358_);
lean_inc(v___x_359_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 2, v___x_359_);
v___x_361_ = v___x_344_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_key_340_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_value_341_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v___x_359_);
v___x_361_ = v_reuseFailAlloc_364_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; 
v___x_362_ = lean_array_uset(v_x_338_, v___x_358_, v___x_361_);
v_x_338_ = v___x_362_;
v_x_339_ = v_tail_342_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2___redArg(lean_object* v_i_366_, lean_object* v_source_367_, lean_object* v_target_368_){
_start:
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = lean_array_get_size(v_source_367_);
v___x_370_ = lean_nat_dec_lt(v_i_366_, v___x_369_);
if (v___x_370_ == 0)
{
lean_dec_ref(v_source_367_);
lean_dec(v_i_366_);
return v_target_368_;
}
else
{
lean_object* v_es_371_; lean_object* v___x_372_; lean_object* v_source_373_; lean_object* v_target_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_es_371_ = lean_array_fget(v_source_367_, v_i_366_);
v___x_372_ = lean_box(0);
v_source_373_ = lean_array_fset(v_source_367_, v_i_366_, v___x_372_);
v_target_374_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3___redArg(v_target_368_, v_es_371_);
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_nat_add(v_i_366_, v___x_375_);
lean_dec(v_i_366_);
v_i_366_ = v___x_376_;
v_source_367_ = v_source_373_;
v_target_368_ = v_target_374_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1___redArg(lean_object* v_data_378_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_nbuckets_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_379_ = lean_array_get_size(v_data_378_);
v___x_380_ = lean_unsigned_to_nat(2u);
v_nbuckets_381_ = lean_nat_mul(v___x_379_, v___x_380_);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = lean_box(0);
v___x_384_ = lean_mk_array(v_nbuckets_381_, v___x_383_);
v___x_385_ = lean_array_propagate_mark(v_data_378_, v___x_384_);
v___x_386_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2___redArg(v___x_382_, v_data_378_, v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(lean_object* v_a_387_, lean_object* v_b_388_, lean_object* v_x_389_){
_start:
{
if (lean_obj_tag(v_x_389_) == 0)
{
lean_dec(v_b_388_);
lean_dec(v_a_387_);
return v_x_389_;
}
else
{
lean_object* v_key_390_; lean_object* v_value_391_; lean_object* v_tail_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_404_; 
v_key_390_ = lean_ctor_get(v_x_389_, 0);
v_value_391_ = lean_ctor_get(v_x_389_, 1);
v_tail_392_ = lean_ctor_get(v_x_389_, 2);
v_isSharedCheck_404_ = !lean_is_exclusive(v_x_389_);
if (v_isSharedCheck_404_ == 0)
{
v___x_394_ = v_x_389_;
v_isShared_395_ = v_isSharedCheck_404_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_tail_392_);
lean_inc(v_value_391_);
lean_inc(v_key_390_);
lean_dec(v_x_389_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_404_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
uint8_t v___x_396_; 
v___x_396_ = l_Lean_instBEqFVarId_beq(v_key_390_, v_a_387_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(v_a_387_, v_b_388_, v_tail_392_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 2, v___x_397_);
v___x_399_ = v___x_394_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_key_390_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_value_391_);
lean_ctor_set(v_reuseFailAlloc_400_, 2, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
else
{
lean_object* v___x_402_; 
lean_dec(v_value_391_);
lean_dec(v_key_390_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 1, v_b_388_);
lean_ctor_set(v___x_394_, 0, v_a_387_);
v___x_402_ = v___x_394_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_387_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_b_388_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v_tail_392_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(lean_object* v_a_405_, lean_object* v_x_406_){
_start:
{
if (lean_obj_tag(v_x_406_) == 0)
{
uint8_t v___x_407_; 
v___x_407_ = 0;
return v___x_407_;
}
else
{
lean_object* v_key_408_; lean_object* v_tail_409_; uint8_t v___x_410_; 
v_key_408_ = lean_ctor_get(v_x_406_, 0);
v_tail_409_ = lean_ctor_get(v_x_406_, 2);
v___x_410_ = l_Lean_instBEqFVarId_beq(v_key_408_, v_a_405_);
if (v___x_410_ == 0)
{
v_x_406_ = v_tail_409_;
goto _start;
}
else
{
return v___x_410_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_405_ = stack[0].m_obj;
lean_object* v_x_406_ = stack[1].m_obj;
uint8_t v_res_412_;
v_res_412_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(v_a_405_, v_x_406_);
stack->m_num = v_res_412_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg___boxed(lean_object* v_a_413_, lean_object* v_x_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(v_a_413_, v_x_414_);
lean_dec(v_x_414_);
lean_dec(v_a_413_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(lean_object* v_m_417_, lean_object* v_a_418_, lean_object* v_b_419_){
_start:
{
lean_object* v_size_420_; lean_object* v_buckets_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_464_; 
v_size_420_ = lean_ctor_get(v_m_417_, 0);
v_buckets_421_ = lean_ctor_get(v_m_417_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v_m_417_);
if (v_isSharedCheck_464_ == 0)
{
v___x_423_ = v_m_417_;
v_isShared_424_ = v_isSharedCheck_464_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_buckets_421_);
lean_inc(v_size_420_);
lean_dec(v_m_417_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_464_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; uint64_t v___x_426_; uint64_t v___x_427_; uint64_t v___x_428_; uint64_t v_fold_429_; uint64_t v___x_430_; uint64_t v___x_431_; uint64_t v___x_432_; size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; size_t v___x_436_; size_t v___x_437_; lean_object* v_bkt_438_; uint8_t v___x_439_; 
v___x_425_ = lean_array_get_size(v_buckets_421_);
v___x_426_ = l_Lean_instHashableFVarId_hash(v_a_418_);
v___x_427_ = 32ULL;
v___x_428_ = lean_uint64_shift_right(v___x_426_, v___x_427_);
v_fold_429_ = lean_uint64_xor(v___x_426_, v___x_428_);
v___x_430_ = 16ULL;
v___x_431_ = lean_uint64_shift_right(v_fold_429_, v___x_430_);
v___x_432_ = lean_uint64_xor(v_fold_429_, v___x_431_);
v___x_433_ = lean_uint64_to_usize(v___x_432_);
v___x_434_ = lean_usize_of_nat(v___x_425_);
v___x_435_ = ((size_t)1ULL);
v___x_436_ = lean_usize_sub(v___x_434_, v___x_435_);
v___x_437_ = lean_usize_land(v___x_433_, v___x_436_);
v_bkt_438_ = lean_array_uget_borrowed(v_buckets_421_, v___x_437_);
v___x_439_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(v_a_418_, v_bkt_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v_size_x27_441_; lean_object* v___x_442_; lean_object* v_buckets_x27_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_440_ = lean_unsigned_to_nat(1u);
v_size_x27_441_ = lean_nat_add(v_size_420_, v___x_440_);
lean_dec(v_size_420_);
lean_inc(v_bkt_438_);
v___x_442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_442_, 0, v_a_418_);
lean_ctor_set(v___x_442_, 1, v_b_419_);
lean_ctor_set(v___x_442_, 2, v_bkt_438_);
v_buckets_x27_443_ = lean_array_uset(v_buckets_421_, v___x_437_, v___x_442_);
v___x_444_ = lean_unsigned_to_nat(4u);
v___x_445_ = lean_nat_mul(v_size_x27_441_, v___x_444_);
v___x_446_ = lean_unsigned_to_nat(3u);
v___x_447_ = lean_nat_div(v___x_445_, v___x_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_array_get_size(v_buckets_x27_443_);
v___x_449_ = lean_nat_dec_le(v___x_447_, v___x_448_);
lean_dec(v___x_447_);
if (v___x_449_ == 0)
{
lean_object* v_val_450_; lean_object* v___x_452_; 
v_val_450_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1___redArg(v_buckets_x27_443_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v_val_450_);
lean_ctor_set(v___x_423_, 0, v_size_x27_441_);
v___x_452_ = v___x_423_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_size_x27_441_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_val_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
else
{
lean_object* v___x_455_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v_buckets_x27_443_);
lean_ctor_set(v___x_423_, 0, v_size_x27_441_);
v___x_455_ = v___x_423_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_size_x27_441_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_buckets_x27_443_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
else
{
lean_object* v___x_457_; lean_object* v_buckets_x27_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
lean_inc(v_bkt_438_);
v___x_457_ = lean_box(0);
v_buckets_x27_458_ = lean_array_uset(v_buckets_421_, v___x_437_, v___x_457_);
v___x_459_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(v_a_418_, v_b_419_, v_bkt_438_);
v___x_460_ = lean_array_uset(v_buckets_x27_458_, v___x_437_, v___x_459_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v___x_460_);
v___x_462_ = v___x_423_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_size_420_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(lean_object* v_decl_465_, lean_object* v_fvarId_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
uint8_t v___x_470_; lean_object* v___x_471_; 
v___x_470_ = 0;
v___x_471_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_470_, v_decl_465_, v_a_468_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_493_; 
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; 
v_unused_494_ = lean_ctor_get(v___x_471_, 0);
lean_dec(v_unused_494_);
v___x_473_ = v___x_471_;
v_isShared_474_ = v_isSharedCheck_493_;
goto v_resetjp_472_;
}
else
{
lean_dec(v___x_471_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_493_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v_fvarId_475_; lean_object* v___x_476_; lean_object* v_map_477_; lean_object* v_subst_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_492_; 
v_fvarId_475_ = lean_ctor_get(v_decl_465_, 0);
lean_inc(v_fvarId_475_);
lean_dec_ref(v_decl_465_);
v___x_476_ = lean_st_ref_take(v_a_467_);
v_map_477_ = lean_ctor_get(v___x_476_, 0);
v_subst_478_ = lean_ctor_get(v___x_476_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_492_ == 0)
{
v___x_480_ = v___x_476_;
v_isShared_481_ = v_isSharedCheck_492_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_subst_478_);
lean_inc(v_map_477_);
lean_dec(v___x_476_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_492_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_482_ = lean_box(0);
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v_fvarId_466_);
v___x_484_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(v_subst_478_, v_fvarId_475_, v___x_483_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 1, v___x_484_);
v___x_486_ = v___x_480_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_map_477_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_491_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_487_ = lean_st_ref_put(v_a_467_, v___x_486_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_482_);
v___x_489_ = v___x_473_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_482_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_466_);
lean_dec_ref(v_decl_465_);
return v___x_471_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CSE_replaceLet___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_465_ = stack[0].m_obj;
lean_object* v_fvarId_466_ = stack[1].m_obj;
lean_object* v_a_467_ = stack[2].m_obj;
lean_object* v_a_468_ = stack[3].m_obj;
lean_object* v_res_495_;
v_res_495_ = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(v_decl_465_, v_fvarId_466_, v_a_467_, v_a_468_);
stack->m_obj
 = v_res_495_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg___boxed(lean_object* v_decl_496_, lean_object* v_fvarId_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(v_decl_496_, v_fvarId_497_, v_a_498_, v_a_499_);
lean_dec(v_a_499_);
lean_dec(v_a_498_);
return v_res_501_;
}
}
lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet(lean_object* v_decl_502_, lean_object* v_fvarId_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(v_decl_502_, v_fvarId_503_, v_a_504_, v_a_506_);
return v___x_510_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CSE_replaceLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_502_ = stack[0].m_obj;
lean_object* v_fvarId_503_ = stack[1].m_obj;
lean_object* v_a_504_ = stack[2].m_obj;
lean_object* v_a_505_ = stack[3].m_obj;
lean_object* v_a_506_ = stack[4].m_obj;
lean_object* v_a_507_ = stack[5].m_obj;
lean_object* v_a_508_ = stack[6].m_obj;
lean_object* v_res_511_;
v_res_511_ = l_Lean_Compiler_LCNF_CSE_replaceLet(v_decl_502_, v_fvarId_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
stack->m_obj
 = v_res_511_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___boxed(lean_object* v_decl_512_, lean_object* v_fvarId_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Compiler_LCNF_CSE_replaceLet(v_decl_512_, v_fvarId_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0(lean_object* v_00_u03b2_521_, lean_object* v_m_522_, lean_object* v_a_523_, lean_object* v_b_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(v_m_522_, v_a_523_, v_b_524_);
return v___x_525_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0(lean_object* v_00_u03b2_526_, lean_object* v_a_527_, lean_object* v_x_528_){
_start:
{
uint8_t v___x_529_; 
v___x_529_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(v_a_527_, v_x_528_);
return v___x_529_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_527_ = stack[1].m_obj;
lean_object* v_x_528_ = stack[2].m_obj;
uint8_t v_res_530_;
v_res_530_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0(lean_box(0), v_a_527_, v_x_528_);
stack->m_num = v_res_530_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___boxed(lean_object* v_00_u03b2_531_, lean_object* v_a_532_, lean_object* v_x_533_){
_start:
{
uint8_t v_res_534_; lean_object* v_r_535_; 
v_res_534_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0(v_00_u03b2_531_, v_a_532_, v_x_533_);
lean_dec(v_x_533_);
lean_dec(v_a_532_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1(lean_object* v_00_u03b2_536_, lean_object* v_data_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1___redArg(v_data_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2(lean_object* v_00_u03b2_539_, lean_object* v_a_540_, lean_object* v_b_541_, lean_object* v_x_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(v_a_540_, v_b_541_, v_x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_544_, lean_object* v_i_545_, lean_object* v_source_546_, lean_object* v_target_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2___redArg(v_i_545_, v_source_546_, v_target_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_549_, lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3___redArg(v_x_550_, v_x_551_);
return v___x_552_;
}
}
lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(lean_object* v_decl_553_, lean_object* v_fvarId_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
uint8_t v___x_558_; uint8_t v___x_559_; lean_object* v___x_560_; 
v___x_558_ = 0;
v___x_559_ = 1;
v___x_560_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_558_, v_decl_553_, v___x_559_, v_a_556_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_582_; 
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; 
v_unused_583_ = lean_ctor_get(v___x_560_, 0);
lean_dec(v_unused_583_);
v___x_562_ = v___x_560_;
v_isShared_563_ = v_isSharedCheck_582_;
goto v_resetjp_561_;
}
else
{
lean_dec(v___x_560_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_582_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v_fvarId_564_; lean_object* v___x_565_; lean_object* v_map_566_; lean_object* v_subst_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_581_; 
v_fvarId_564_ = lean_ctor_get(v_decl_553_, 0);
lean_inc(v_fvarId_564_);
lean_dec_ref(v_decl_553_);
v___x_565_ = lean_st_ref_take(v_a_555_);
v_map_566_ = lean_ctor_get(v___x_565_, 0);
v_subst_567_ = lean_ctor_get(v___x_565_, 1);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_581_ == 0)
{
v___x_569_ = v___x_565_;
v_isShared_570_ = v_isSharedCheck_581_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_subst_567_);
lean_inc(v_map_566_);
lean_dec(v___x_565_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_581_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_571_ = lean_box(0);
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v_fvarId_554_);
v___x_573_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(v_subst_567_, v_fvarId_564_, v___x_572_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 1, v___x_573_);
v___x_575_ = v___x_569_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_map_566_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___x_573_);
v___x_575_ = v_reuseFailAlloc_580_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_576_ = lean_st_ref_put(v_a_555_, v___x_575_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_571_);
v___x_578_ = v___x_562_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_571_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_554_);
lean_dec_ref(v_decl_553_);
return v___x_560_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CSE_replaceFun___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_553_ = stack[0].m_obj;
lean_object* v_fvarId_554_ = stack[1].m_obj;
lean_object* v_a_555_ = stack[2].m_obj;
lean_object* v_a_556_ = stack[3].m_obj;
lean_object* v_res_584_;
v_res_584_ = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(v_decl_553_, v_fvarId_554_, v_a_555_, v_a_556_);
stack->m_obj
 = v_res_584_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg___boxed(lean_object* v_decl_585_, lean_object* v_fvarId_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(v_decl_585_, v_fvarId_586_, v_a_587_, v_a_588_);
lean_dec(v_a_588_);
lean_dec(v_a_587_);
return v_res_590_;
}
}
lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun(lean_object* v_decl_591_, lean_object* v_fvarId_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(v_decl_591_, v_fvarId_592_, v_a_593_, v_a_595_);
return v___x_599_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CSE_replaceFun_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_591_ = stack[0].m_obj;
lean_object* v_fvarId_592_ = stack[1].m_obj;
lean_object* v_a_593_ = stack[2].m_obj;
lean_object* v_a_594_ = stack[3].m_obj;
lean_object* v_a_595_ = stack[4].m_obj;
lean_object* v_a_596_ = stack[5].m_obj;
lean_object* v_a_597_ = stack[6].m_obj;
lean_object* v_res_600_;
v_res_600_ = l_Lean_Compiler_LCNF_CSE_replaceFun(v_decl_591_, v_fvarId_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
stack->m_obj
 = v_res_600_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___boxed(lean_object* v_decl_601_, lean_object* v_fvarId_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_Compiler_LCNF_CSE_replaceFun(v_decl_601_, v_fvarId_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
return v_res_609_;
}
}
lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(lean_object* v_v_610_, lean_object* v_a_611_){
_start:
{
if (lean_obj_tag(v_v_610_) == 3)
{
lean_object* v_declName_613_; lean_object* v___x_614_; lean_object* v_env_615_; uint8_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_declName_613_ = lean_ctor_get(v_v_610_, 0);
lean_inc(v_declName_613_);
lean_dec_ref_known(v_v_610_, 3);
v___x_614_ = lean_st_ref_get(v_a_611_);
v_env_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc_ref(v_env_615_);
lean_dec(v___x_614_);
v___x_616_ = l_Lean_hasNeverExtractAttribute(v_env_615_, v_declName_613_);
v___x_617_ = lean_box(v___x_616_);
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
return v___x_618_;
}
else
{
uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v_v_610_);
v___x_619_ = 0;
v___x_620_ = lean_box(v___x_619_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_610_ = stack[0].m_obj;
lean_object* v_a_611_ = stack[1].m_obj;
lean_object* v_res_622_;
v_res_622_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(v_v_610_, v_a_611_);
stack->m_obj
 = v_res_622_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg___boxed(lean_object* v_v_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(v_v_623_, v_a_624_);
lean_dec(v_a_624_);
return v_res_626_;
}
}
lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract(lean_object* v_v_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(v_v_627_, v_a_631_);
return v___x_633_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CSE_hasNeverExtract_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_627_ = stack[0].m_obj;
lean_object* v_a_628_ = stack[1].m_obj;
lean_object* v_a_629_ = stack[2].m_obj;
lean_object* v_a_630_ = stack[3].m_obj;
lean_object* v_a_631_ = stack[4].m_obj;
lean_object* v_res_634_;
v_res_634_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract(v_v_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
stack->m_obj
 = v_res_634_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___boxed(lean_object* v_v_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract(v_v_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
return v_res_641_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(lean_object* v_a_642_, lean_object* v_map_643_, lean_object* v_a_x3f_644_){
_start:
{
lean_object* v___x_646_; lean_object* v_subst_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_657_; 
v___x_646_ = lean_st_ref_take(v_a_642_);
v_subst_647_ = lean_ctor_get(v___x_646_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v___x_646_, 0);
lean_dec(v_unused_658_);
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_657_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_subst_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_657_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_651_ = lean_box(0);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v_map_643_);
v___x_653_ = v___x_649_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_map_643_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_subst_647_);
v___x_653_ = v_reuseFailAlloc_656_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_st_ref_put(v_a_642_, v___x_653_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_651_);
return v___x_655_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_642_ = stack[0].m_obj;
lean_object* v_map_643_ = stack[1].m_obj;
lean_object* v_a_x3f_644_ = stack[2].m_obj;
lean_object* v_res_659_;
v_res_659_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(v_a_642_, v_map_643_, v_a_x3f_644_);
stack->m_obj
 = v_res_659_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0___boxed(lean_object* v_a_660_, lean_object* v_map_661_, lean_object* v_a_x3f_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(v_a_660_, v_map_661_, v_a_x3f_662_);
lean_dec(v_a_x3f_662_);
lean_dec(v_a_660_);
return v_res_664_;
}
}
lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(uint8_t v_pu_665_, uint8_t v_t_666_, lean_object* v_args_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; lean_object* v_subst_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_670_ = lean_st_ref_get(v___y_668_);
v_subst_671_ = lean_ctor_get(v___x_670_, 1);
lean_inc_ref(v_subst_671_);
lean_dec(v___x_670_);
v___x_672_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_665_, v_subst_671_, v_args_667_, v_t_666_);
lean_dec_ref(v_subst_671_);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_665_ = stack[0].m_num;
uint8_t v_t_666_ = stack[1].m_num;
lean_object* v_args_667_ = stack[2].m_obj;
lean_object* v___y_668_ = stack[3].m_obj;
lean_object* v_res_674_;
v_res_674_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v_pu_665_, v_t_666_, v_args_667_, v___y_668_);
stack->m_obj
 = v_res_674_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg___boxed(lean_object* v_pu_675_, lean_object* v_t_676_, lean_object* v_args_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
uint8_t v_pu_boxed_680_; uint8_t v_t_boxed_681_; lean_object* v_res_682_; 
v_pu_boxed_680_ = lean_unbox(v_pu_675_);
v_t_boxed_681_ = lean_unbox(v_t_676_);
v_res_682_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v_pu_boxed_680_, v_t_boxed_681_, v_args_677_, v___y_678_);
lean_dec(v___y_678_);
return v_res_682_;
}
}
lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(uint8_t v_pu_683_, uint8_t v_t_684_, lean_object* v_decl_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_type_689_; lean_object* v_value_690_; lean_object* v___x_691_; lean_object* v_subst_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v_subst_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_type_689_ = lean_ctor_get(v_decl_685_, 2);
v_value_690_ = lean_ctor_get(v_decl_685_, 3);
v___x_691_ = lean_st_ref_get(v___y_686_);
v_subst_692_ = lean_ctor_get(v___x_691_, 1);
lean_inc_ref(v_subst_692_);
lean_dec(v___x_691_);
lean_inc_ref(v_type_689_);
v___x_693_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_683_, v_subst_692_, v_t_684_, v_type_689_);
lean_dec_ref(v_subst_692_);
v___x_694_ = lean_st_ref_get(v___y_686_);
v_subst_695_ = lean_ctor_get(v___x_694_, 1);
lean_inc_ref(v_subst_695_);
lean_dec(v___x_694_);
lean_inc(v_value_690_);
v___x_696_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_683_, v_subst_695_, v_value_690_, v_t_684_);
lean_dec_ref(v_subst_695_);
v___x_697_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_683_, v_decl_685_, v___x_693_, v___x_696_, v___y_687_);
return v___x_697_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_683_ = stack[0].m_num;
uint8_t v_t_684_ = stack[1].m_num;
lean_object* v_decl_685_ = stack[2].m_obj;
lean_object* v___y_686_ = stack[3].m_obj;
lean_object* v___y_687_ = stack[4].m_obj;
lean_object* v_res_698_;
v_res_698_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v_pu_683_, v_t_684_, v_decl_685_, v___y_686_, v___y_687_);
stack->m_obj
 = v_res_698_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg___boxed(lean_object* v_pu_699_, lean_object* v_t_700_, lean_object* v_decl_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
uint8_t v_pu_boxed_705_; uint8_t v_t_boxed_706_; lean_object* v_res_707_; 
v_pu_boxed_705_ = lean_unbox(v_pu_699_);
v_t_boxed_706_ = lean_unbox(v_t_700_);
v_res_707_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v_pu_boxed_705_, v_t_boxed_706_, v_decl_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec(v___y_702_);
return v_res_707_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(lean_object* v___y_708_, lean_object* v_map_709_, lean_object* v_a_x3f_710_){
_start:
{
lean_object* v___x_712_; lean_object* v_subst_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_723_; 
v___x_712_ = lean_st_ref_take(v___y_708_);
v_subst_713_ = lean_ctor_get(v___x_712_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; 
v_unused_724_ = lean_ctor_get(v___x_712_, 0);
lean_dec(v_unused_724_);
v___x_715_ = v___x_712_;
v_isShared_716_ = v_isSharedCheck_723_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_subst_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_723_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = lean_box(0);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v_map_709_);
v___x_719_ = v___x_715_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_map_709_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_subst_713_);
v___x_719_ = v_reuseFailAlloc_722_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_st_ref_put(v___y_708_, v___x_719_);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_717_);
return v___x_721_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_708_ = stack[0].m_obj;
lean_object* v_map_709_ = stack[1].m_obj;
lean_object* v_a_x3f_710_ = stack[2].m_obj;
lean_object* v_res_725_;
v_res_725_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_708_, v_map_709_, v_a_x3f_710_);
stack->m_obj
 = v_res_725_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0___boxed(lean_object* v___y_726_, lean_object* v_map_727_, lean_object* v_a_x3f_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_726_, v_map_727_, v_a_x3f_728_);
lean_dec(v_a_x3f_728_);
lean_dec(v___y_726_);
return v_res_730_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(uint8_t v_pu_731_, uint8_t v_t_732_, lean_object* v_i_733_, lean_object* v_as_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = lean_array_get_size(v_as_734_);
v___x_739_ = lean_nat_dec_lt(v_i_733_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec(v_i_733_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v_as_734_);
return v___x_740_;
}
else
{
lean_object* v_a_741_; lean_object* v_type_742_; lean_object* v___x_743_; lean_object* v_subst_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_a_741_ = lean_array_fget_borrowed(v_as_734_, v_i_733_);
v_type_742_ = lean_ctor_get(v_a_741_, 2);
v___x_743_ = lean_st_ref_get(v___y_735_);
v_subst_744_ = lean_ctor_get(v___x_743_, 1);
lean_inc_ref(v_subst_744_);
lean_dec(v___x_743_);
lean_inc_ref(v_type_742_);
v___x_745_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_731_, v_subst_744_, v_t_732_, v_type_742_);
lean_dec_ref(v_subst_744_);
lean_inc(v_a_741_);
v___x_746_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_731_, v_a_741_, v___x_745_, v___y_736_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; size_t v___x_748_; size_t v___x_749_; uint8_t v___x_750_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = lean_ptr_addr(v_a_741_);
v___x_749_ = lean_ptr_addr(v_a_747_);
v___x_750_ = lean_usize_dec_eq(v___x_748_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_751_ = lean_unsigned_to_nat(1u);
v___x_752_ = lean_nat_add(v_i_733_, v___x_751_);
v___x_753_ = lean_array_fset(v_as_734_, v_i_733_, v_a_747_);
lean_dec(v_i_733_);
v_i_733_ = v___x_752_;
v_as_734_ = v___x_753_;
goto _start;
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; 
lean_dec(v_a_747_);
v___x_755_ = lean_unsigned_to_nat(1u);
v___x_756_ = lean_nat_add(v_i_733_, v___x_755_);
lean_dec(v_i_733_);
v_i_733_ = v___x_756_;
goto _start;
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v_as_734_);
lean_dec(v_i_733_);
v_a_758_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_746_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_746_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_731_ = stack[0].m_num;
uint8_t v_t_732_ = stack[1].m_num;
lean_object* v_i_733_ = stack[2].m_obj;
lean_object* v_as_734_ = stack[3].m_obj;
lean_object* v___y_735_ = stack[4].m_obj;
lean_object* v___y_736_ = stack[5].m_obj;
lean_object* v_res_766_;
v_res_766_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(v_pu_731_, v_t_732_, v_i_733_, v_as_734_, v___y_735_, v___y_736_);
stack->m_obj
 = v_res_766_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg___boxed(lean_object* v_pu_767_, lean_object* v_t_768_, lean_object* v_i_769_, lean_object* v_as_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
uint8_t v_pu_boxed_774_; uint8_t v_t_boxed_775_; lean_object* v_res_776_; 
v_pu_boxed_774_ = lean_unbox(v_pu_767_);
v_t_boxed_775_ = lean_unbox(v_t_768_);
v_res_776_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(v_pu_boxed_774_, v_t_boxed_775_, v_i_769_, v_as_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec(v___y_771_);
return v_res_776_;
}
}
lean_object* l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(uint8_t v_pu_777_, uint8_t v_t_778_, lean_object* v_ps_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(v_pu_777_, v_t_778_, v___x_786_, v_ps_779_, v___y_780_, v___y_782_);
return v___x_787_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_777_ = stack[0].m_num;
uint8_t v_t_778_ = stack[1].m_num;
lean_object* v_ps_779_ = stack[2].m_obj;
lean_object* v___y_780_ = stack[3].m_obj;
lean_object* v___y_781_ = stack[4].m_obj;
lean_object* v___y_782_ = stack[5].m_obj;
lean_object* v___y_783_ = stack[6].m_obj;
lean_object* v___y_784_ = stack[7].m_obj;
lean_object* v_res_788_;
v_res_788_ = l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(v_pu_777_, v_t_778_, v_ps_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
stack->m_obj
 = v_res_788_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___boxed(lean_object* v_pu_789_, lean_object* v_t_790_, lean_object* v_ps_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
uint8_t v_pu_boxed_798_; uint8_t v_t_boxed_799_; lean_object* v_res_800_; 
v_pu_boxed_798_ = lean_unbox(v_pu_789_);
v_t_boxed_799_ = lean_unbox(v_t_790_);
v_res_800_ = l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(v_pu_boxed_798_, v_t_boxed_799_, v_ps_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(lean_object* v_keys_801_, lean_object* v_vals_802_, lean_object* v_i_803_, lean_object* v_k_804_){
_start:
{
lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_805_ = lean_array_get_size(v_keys_801_);
v___x_806_ = lean_nat_dec_lt(v_i_803_, v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; 
lean_dec(v_i_803_);
v___x_807_ = lean_box(0);
return v___x_807_;
}
else
{
lean_object* v_k_x27_808_; uint8_t v___x_809_; 
v_k_x27_808_ = lean_array_fget_borrowed(v_keys_801_, v_i_803_);
v___x_809_ = lean_expr_eqv(v_k_804_, v_k_x27_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_unsigned_to_nat(1u);
v___x_811_ = lean_nat_add(v_i_803_, v___x_810_);
lean_dec(v_i_803_);
v_i_803_ = v___x_811_;
goto _start;
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_array_fget_borrowed(v_vals_802_, v_i_803_);
lean_dec(v_i_803_);
lean_inc(v___x_813_);
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_keys_815_, lean_object* v_vals_816_, lean_object* v_i_817_, lean_object* v_k_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(v_keys_815_, v_vals_816_, v_i_817_, v_k_818_);
lean_dec_ref(v_k_818_);
lean_dec_ref(v_vals_816_);
lean_dec_ref(v_keys_815_);
return v_res_819_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(lean_object* v_x_820_, size_t v_x_821_, lean_object* v_x_822_){
_start:
{
if (lean_obj_tag(v_x_820_) == 0)
{
lean_object* v_es_823_; lean_object* v___x_824_; size_t v___x_825_; size_t v___x_826_; lean_object* v_j_827_; lean_object* v___x_828_; 
v_es_823_ = lean_ctor_get(v_x_820_, 0);
v___x_824_ = lean_box(2);
v___x_825_ = ((size_t)31ULL);
v___x_826_ = lean_usize_land(v_x_821_, v___x_825_);
v_j_827_ = lean_usize_to_nat(v___x_826_);
v___x_828_ = lean_array_get_borrowed(v___x_824_, v_es_823_, v_j_827_);
lean_dec(v_j_827_);
switch(lean_obj_tag(v___x_828_))
{
case 0:
{
lean_object* v_key_829_; lean_object* v_val_830_; uint8_t v___x_831_; 
v_key_829_ = lean_ctor_get(v___x_828_, 0);
v_val_830_ = lean_ctor_get(v___x_828_, 1);
v___x_831_ = lean_expr_eqv(v_x_822_, v_key_829_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
v___x_832_ = lean_box(0);
return v___x_832_;
}
else
{
lean_object* v___x_833_; 
lean_inc(v_val_830_);
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v_val_830_);
return v___x_833_;
}
}
case 1:
{
lean_object* v_node_834_; size_t v___x_835_; size_t v___x_836_; 
v_node_834_ = lean_ctor_get(v___x_828_, 0);
v___x_835_ = ((size_t)5ULL);
v___x_836_ = lean_usize_shift_right(v_x_821_, v___x_835_);
v_x_820_ = v_node_834_;
v_x_821_ = v___x_836_;
goto _start;
}
default: 
{
lean_object* v___x_838_; 
v___x_838_ = lean_box(0);
return v___x_838_;
}
}
}
else
{
lean_object* v_ks_839_; lean_object* v_vs_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_ks_839_ = lean_ctor_get(v_x_820_, 0);
v_vs_840_ = lean_ctor_get(v_x_820_, 1);
v___x_841_ = lean_unsigned_to_nat(0u);
v___x_842_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(v_ks_839_, v_vs_840_, v___x_841_, v_x_822_);
return v___x_842_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_820_ = stack[0].m_obj;
size_t v_x_821_ = stack[1].m_num;
lean_object* v_x_822_ = stack[2].m_obj;
lean_object* v_res_843_;
v_res_843_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_820_, v_x_821_, v_x_822_);
stack->m_obj
 = v_res_843_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___boxed(lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
size_t v_x_15386__boxed_847_; lean_object* v_res_848_; 
v_x_15386__boxed_847_ = lean_unbox_usize(v_x_845_);
lean_dec(v_x_845_);
v_res_848_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_844_, v_x_15386__boxed_847_, v_x_846_);
lean_dec_ref(v_x_846_);
lean_dec_ref(v_x_844_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
uint64_t v___x_851_; size_t v___x_852_; lean_object* v___x_853_; 
v___x_851_ = l_Lean_Expr_hash(v_x_850_);
v___x_852_ = lean_uint64_to_usize(v___x_851_);
v___x_853_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_849_, v___x_852_, v_x_850_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg___boxed(lean_object* v_x_854_, lean_object* v_x_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_x_854_, v_x_855_);
lean_dec_ref(v_x_855_);
lean_dec_ref(v_x_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(lean_object* v_x_857_, lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
lean_object* v_ks_861_; lean_object* v_vs_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_886_; 
v_ks_861_ = lean_ctor_get(v_x_857_, 0);
v_vs_862_ = lean_ctor_get(v_x_857_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v_x_857_);
if (v_isSharedCheck_886_ == 0)
{
v___x_864_ = v_x_857_;
v_isShared_865_ = v_isSharedCheck_886_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_vs_862_);
lean_inc(v_ks_861_);
lean_dec(v_x_857_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_886_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_866_ = lean_array_get_size(v_ks_861_);
v___x_867_ = lean_nat_dec_lt(v_x_858_, v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
lean_dec(v_x_858_);
v___x_868_ = lean_array_push(v_ks_861_, v_x_859_);
v___x_869_ = lean_array_push(v_vs_862_, v_x_860_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___x_869_);
lean_ctor_set(v___x_864_, 0, v___x_868_);
v___x_871_ = v___x_864_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
else
{
lean_object* v_k_x27_873_; uint8_t v___x_874_; 
v_k_x27_873_ = lean_array_fget_borrowed(v_ks_861_, v_x_858_);
v___x_874_ = lean_expr_eqv(v_x_859_, v_k_x27_873_);
if (v___x_874_ == 0)
{
lean_object* v___x_876_; 
if (v_isShared_865_ == 0)
{
v___x_876_ = v___x_864_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_ks_861_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_vs_862_);
v___x_876_ = v_reuseFailAlloc_880_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_unsigned_to_nat(1u);
v___x_878_ = lean_nat_add(v_x_858_, v___x_877_);
lean_dec(v_x_858_);
v_x_857_ = v___x_876_;
v_x_858_ = v___x_878_;
goto _start;
}
}
else
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_881_ = lean_array_fset(v_ks_861_, v_x_858_, v_x_859_);
v___x_882_ = lean_array_fset(v_vs_862_, v_x_858_, v_x_860_);
lean_dec(v_x_858_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___x_882_);
lean_ctor_set(v___x_864_, 0, v___x_881_);
v___x_884_ = v___x_864_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(lean_object* v_n_887_, lean_object* v_k_888_, lean_object* v_v_889_){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_unsigned_to_nat(0u);
v___x_891_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(v_n_887_, v___x_890_, v_k_888_, v_v_889_);
return v___x_891_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_892_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(lean_object* v_x_893_, size_t v_x_894_, size_t v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
lean_object* v_es_898_; size_t v___x_899_; size_t v___x_900_; lean_object* v_j_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v_es_898_ = lean_ctor_get(v_x_893_, 0);
v___x_899_ = ((size_t)31ULL);
v___x_900_ = lean_usize_land(v_x_894_, v___x_899_);
v_j_901_ = lean_usize_to_nat(v___x_900_);
v___x_902_ = lean_array_get_size(v_es_898_);
v___x_903_ = lean_nat_dec_lt(v_j_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_dec(v_j_901_);
lean_dec(v_x_897_);
lean_dec_ref(v_x_896_);
return v_x_893_;
}
else
{
lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_942_; 
lean_inc_ref(v_es_898_);
v_isSharedCheck_942_ = !lean_is_exclusive(v_x_893_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; 
v_unused_943_ = lean_ctor_get(v_x_893_, 0);
lean_dec(v_unused_943_);
v___x_905_ = v_x_893_;
v_isShared_906_ = v_isSharedCheck_942_;
goto v_resetjp_904_;
}
else
{
lean_dec(v_x_893_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_942_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v_v_907_; lean_object* v___x_908_; lean_object* v_xs_x27_909_; lean_object* v___y_911_; 
v_v_907_ = lean_array_fget(v_es_898_, v_j_901_);
v___x_908_ = lean_box(0);
v_xs_x27_909_ = lean_array_fset(v_es_898_, v_j_901_, v___x_908_);
switch(lean_obj_tag(v_v_907_))
{
case 0:
{
lean_object* v_key_916_; lean_object* v_val_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_927_; 
v_key_916_ = lean_ctor_get(v_v_907_, 0);
v_val_917_ = lean_ctor_get(v_v_907_, 1);
v_isSharedCheck_927_ = !lean_is_exclusive(v_v_907_);
if (v_isSharedCheck_927_ == 0)
{
v___x_919_ = v_v_907_;
v_isShared_920_ = v_isSharedCheck_927_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_val_917_);
lean_inc(v_key_916_);
lean_dec(v_v_907_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_927_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
uint8_t v___x_921_; 
v___x_921_ = lean_expr_eqv(v_x_896_, v_key_916_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; 
lean_del_object(v___x_919_);
v___x_922_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_916_, v_val_917_, v_x_896_, v_x_897_);
v___x_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
v___y_911_ = v___x_923_;
goto v___jp_910_;
}
else
{
lean_object* v___x_925_; 
lean_dec(v_val_917_);
lean_dec(v_key_916_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 1, v_x_897_);
lean_ctor_set(v___x_919_, 0, v_x_896_);
v___x_925_ = v___x_919_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_x_896_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_x_897_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
v___y_911_ = v___x_925_;
goto v___jp_910_;
}
}
}
}
case 1:
{
lean_object* v_node_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_940_; 
v_node_928_ = lean_ctor_get(v_v_907_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v_v_907_);
if (v_isSharedCheck_940_ == 0)
{
v___x_930_ = v_v_907_;
v_isShared_931_ = v_isSharedCheck_940_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_node_928_);
lean_dec(v_v_907_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_940_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
size_t v___x_932_; size_t v___x_933_; size_t v___x_934_; size_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_932_ = ((size_t)5ULL);
v___x_933_ = lean_usize_shift_right(v_x_894_, v___x_932_);
v___x_934_ = ((size_t)1ULL);
v___x_935_ = lean_usize_add(v_x_895_, v___x_934_);
v___x_936_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_node_928_, v___x_933_, v___x_935_, v_x_896_, v_x_897_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_936_);
v___x_938_ = v___x_930_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
v___y_911_ = v___x_938_;
goto v___jp_910_;
}
}
}
default: 
{
lean_object* v___x_941_; 
v___x_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_941_, 0, v_x_896_);
lean_ctor_set(v___x_941_, 1, v_x_897_);
v___y_911_ = v___x_941_;
goto v___jp_910_;
}
}
v___jp_910_:
{
lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_912_ = lean_array_fset(v_xs_x27_909_, v_j_901_, v___y_911_);
lean_dec(v_j_901_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_912_);
v___x_914_ = v___x_905_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
else
{
lean_object* v_ks_944_; lean_object* v_vs_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_963_; 
v_ks_944_ = lean_ctor_get(v_x_893_, 0);
v_vs_945_ = lean_ctor_get(v_x_893_, 1);
v_isSharedCheck_963_ = !lean_is_exclusive(v_x_893_);
if (v_isSharedCheck_963_ == 0)
{
v___x_947_ = v_x_893_;
v_isShared_948_ = v_isSharedCheck_963_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_vs_945_);
lean_inc(v_ks_944_);
lean_dec(v_x_893_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_963_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_ks_944_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_vs_945_);
v___x_950_ = v_reuseFailAlloc_962_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v_newNode_951_; size_t v___x_952_; uint8_t v___x_953_; 
v_newNode_951_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(v___x_950_, v_x_896_, v_x_897_);
v___x_952_ = ((size_t)7ULL);
v___x_953_ = lean_usize_dec_le(v___x_952_, v_x_895_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_954_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_951_);
v___x_955_ = lean_unsigned_to_nat(4u);
v___x_956_ = lean_nat_dec_lt(v___x_954_, v___x_955_);
lean_dec(v___x_954_);
if (v___x_956_ == 0)
{
lean_object* v_ks_957_; lean_object* v_vs_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_ks_957_ = lean_ctor_get(v_newNode_951_, 0);
lean_inc_ref(v_ks_957_);
v_vs_958_ = lean_ctor_get(v_newNode_951_, 1);
lean_inc_ref(v_vs_958_);
lean_dec_ref(v_newNode_951_);
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0);
v___x_961_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_x_895_, v_ks_957_, v_vs_958_, v___x_959_, v___x_960_);
lean_dec_ref(v_vs_958_);
lean_dec_ref(v_ks_957_);
return v___x_961_;
}
else
{
return v_newNode_951_;
}
}
else
{
return v_newNode_951_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_893_ = stack[0].m_obj;
size_t v_x_894_ = stack[1].m_num;
size_t v_x_895_ = stack[2].m_num;
lean_object* v_x_896_ = stack[3].m_obj;
lean_object* v_x_897_ = stack[4].m_obj;
lean_object* v_res_964_;
v_res_964_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_893_, v_x_894_, v_x_895_, v_x_896_, v_x_897_);
stack->m_obj
 = v_res_964_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(size_t v_depth_965_, lean_object* v_keys_966_, lean_object* v_vals_967_, lean_object* v_i_968_, lean_object* v_entries_969_){
_start:
{
lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_970_ = lean_array_get_size(v_keys_966_);
v___x_971_ = lean_nat_dec_lt(v_i_968_, v___x_970_);
if (v___x_971_ == 0)
{
lean_dec(v_i_968_);
return v_entries_969_;
}
else
{
lean_object* v_k_972_; lean_object* v_v_973_; uint64_t v___x_974_; size_t v_h_975_; size_t v___x_976_; lean_object* v___x_977_; size_t v___x_978_; size_t v___x_979_; size_t v___x_980_; size_t v_h_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_k_972_ = lean_array_fget_borrowed(v_keys_966_, v_i_968_);
v_v_973_ = lean_array_fget_borrowed(v_vals_967_, v_i_968_);
v___x_974_ = l_Lean_Expr_hash(v_k_972_);
v_h_975_ = lean_uint64_to_usize(v___x_974_);
v___x_976_ = ((size_t)5ULL);
v___x_977_ = lean_unsigned_to_nat(1u);
v___x_978_ = ((size_t)1ULL);
v___x_979_ = lean_usize_sub(v_depth_965_, v___x_978_);
v___x_980_ = lean_usize_mul(v___x_976_, v___x_979_);
v_h_981_ = lean_usize_shift_right(v_h_975_, v___x_980_);
v___x_982_ = lean_nat_add(v_i_968_, v___x_977_);
lean_dec(v_i_968_);
lean_inc(v_v_973_);
lean_inc(v_k_972_);
v___x_983_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_entries_969_, v_h_981_, v_depth_965_, v_k_972_, v_v_973_);
v_i_968_ = v___x_982_;
v_entries_969_ = v___x_983_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_965_ = stack[0].m_num;
lean_object* v_keys_966_ = stack[1].m_obj;
lean_object* v_vals_967_ = stack[2].m_obj;
lean_object* v_i_968_ = stack[3].m_obj;
lean_object* v_entries_969_ = stack[4].m_obj;
lean_object* v_res_985_;
v_res_985_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_depth_965_, v_keys_966_, v_vals_967_, v_i_968_, v_entries_969_);
stack->m_obj
 = v_res_985_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_depth_986_, lean_object* v_keys_987_, lean_object* v_vals_988_, lean_object* v_i_989_, lean_object* v_entries_990_){
_start:
{
size_t v_depth_boxed_991_; lean_object* v_res_992_; 
v_depth_boxed_991_ = lean_unbox_usize(v_depth_986_);
lean_dec(v_depth_986_);
v_res_992_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_depth_boxed_991_, v_keys_987_, v_vals_988_, v_i_989_, v_entries_990_);
lean_dec_ref(v_vals_988_);
lean_dec_ref(v_keys_987_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___boxed(lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v_x_996_, lean_object* v_x_997_){
_start:
{
size_t v_x_15584__boxed_998_; size_t v_x_15585__boxed_999_; lean_object* v_res_1000_; 
v_x_15584__boxed_998_ = lean_unbox_usize(v_x_994_);
lean_dec(v_x_994_);
v_x_15585__boxed_999_ = lean_unbox_usize(v_x_995_);
lean_dec(v_x_995_);
v_res_1000_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_993_, v_x_15584__boxed_998_, v_x_15585__boxed_999_, v_x_996_, v_x_997_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
uint64_t v___x_1004_; size_t v___x_1005_; size_t v___x_1006_; lean_object* v___x_1007_; 
v___x_1004_ = l_Lean_Expr_hash(v_x_1002_);
v___x_1005_ = lean_uint64_to_usize(v___x_1004_);
v___x_1006_ = ((size_t)1ULL);
v___x_1007_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_1001_, v___x_1005_, v___x_1006_, v_x_1002_, v_x_1003_);
return v___x_1007_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(uint8_t v_shouldElimFunDecls_1010_, lean_object* v_i_1011_, lean_object* v_as_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1019_ = lean_array_get_size(v_as_1012_);
v___x_1020_ = lean_nat_dec_lt(v_i_1011_, v___x_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; 
lean_dec(v_i_1011_);
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v_as_1012_);
return v___x_1021_;
}
else
{
lean_object* v_a_1022_; lean_object* v_a_1024_; 
v_a_1022_ = lean_array_fget_borrowed(v_as_1012_, v_i_1011_);
if (lean_obj_tag(v_a_1022_) == 0)
{
lean_object* v_params_1035_; lean_object* v_code_1036_; uint8_t v___x_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v_map_1040_; lean_object* v_a_1042_; lean_object* v___x_1061_; 
v_params_1035_ = lean_ctor_get(v_a_1022_, 1);
v_code_1036_ = lean_ctor_get(v_a_1022_, 2);
v___x_1037_ = 0;
v___x_1038_ = 0;
v___x_1039_ = lean_st_ref_get(v___y_1013_);
v_map_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc_ref(v_map_1040_);
lean_dec(v___x_1039_);
lean_inc_ref(v_params_1035_);
v___x_1061_ = l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(v___x_1037_, v___x_1038_, v_params_1035_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1063_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1062_);
lean_dec_ref_known(v___x_1061_, 1);
lean_inc_ref(v_code_1036_);
v___x_1063_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1010_, v_code_1036_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1081_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1081_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1081_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
lean_inc_ref(v_a_1022_);
v___x_1068_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v___x_1037_, v_a_1022_, v_a_1062_, v_a_1064_);
lean_inc_ref(v___x_1068_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 1);
lean_ctor_set(v___x_1066_, 0, v___x_1068_);
v___x_1070_ = v___x_1066_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1071_; 
v___x_1071_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_1013_, v_map_1040_, v___x_1070_);
lean_dec_ref(v___x_1070_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_dec_ref_known(v___x_1071_, 1);
v_a_1024_ = v___x_1068_;
goto v___jp_1023_;
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec_ref(v___x_1068_);
lean_dec_ref(v_as_1012_);
lean_dec(v_i_1011_);
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
}
else
{
lean_object* v_a_1082_; 
lean_dec(v_a_1062_);
lean_dec_ref(v_as_1012_);
lean_dec(v_i_1011_);
v_a_1082_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1063_, 1);
v_a_1042_ = v_a_1082_;
goto v___jp_1041_;
}
}
else
{
lean_object* v_a_1083_; 
lean_dec_ref(v_as_1012_);
lean_dec(v_i_1011_);
v_a_1083_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v___x_1061_, 1);
v_a_1042_ = v_a_1083_;
goto v___jp_1041_;
}
v___jp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_box(0);
v___x_1044_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_1013_, v_map_1040_, v___x_1043_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; 
v_unused_1052_ = lean_ctor_get(v___x_1044_, 0);
lean_dec(v_unused_1052_);
v___x_1046_ = v___x_1044_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_dec(v___x_1044_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 1);
lean_ctor_set(v___x_1046_, 0, v_a_1042_);
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1042_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec_ref(v_a_1042_);
v_a_1053_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1044_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1044_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
else
{
lean_object* v_code_1084_; lean_object* v___x_1085_; lean_object* v_map_1086_; lean_object* v___x_1087_; 
v_code_1084_ = lean_ctor_get(v_a_1022_, 0);
v___x_1085_ = lean_st_ref_get(v___y_1013_);
v_map_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc_ref(v_map_1086_);
lean_dec(v___x_1085_);
lean_inc_ref(v_code_1084_);
v___x_1087_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1010_, v_code_1084_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1105_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1105_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1105_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
lean_inc_ref(v_a_1022_);
v___x_1092_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1022_, v_a_1088_);
lean_inc_ref(v___x_1092_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set_tag(v___x_1090_, 1);
lean_ctor_set(v___x_1090_, 0, v___x_1092_);
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; 
v___x_1095_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_1013_, v_map_1086_, v___x_1094_);
lean_dec_ref(v___x_1094_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_dec_ref_known(v___x_1095_, 1);
v_a_1024_ = v___x_1092_;
goto v___jp_1023_;
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref(v___x_1092_);
lean_dec_ref(v_as_1012_);
lean_dec(v_i_1011_);
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1095_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1095_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec_ref(v_as_1012_);
lean_dec(v_i_1011_);
v_a_1106_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1107_ = lean_box(0);
v___x_1108_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_1013_, v_map_1086_, v___x_1107_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; 
v_unused_1116_ = lean_ctor_get(v___x_1108_, 0);
lean_dec(v_unused_1116_);
v___x_1110_ = v___x_1108_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_dec(v___x_1108_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
lean_ctor_set_tag(v___x_1110_, 1);
lean_ctor_set(v___x_1110_, 0, v_a_1106_);
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1106_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec(v_a_1106_);
v_a_1117_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1108_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1108_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
v___jp_1023_:
{
size_t v___x_1025_; size_t v___x_1026_; uint8_t v___x_1027_; 
v___x_1025_ = lean_ptr_addr(v_a_1022_);
v___x_1026_ = lean_ptr_addr(v_a_1024_);
v___x_1027_ = lean_usize_dec_eq(v___x_1025_, v___x_1026_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = lean_unsigned_to_nat(1u);
v___x_1029_ = lean_nat_add(v_i_1011_, v___x_1028_);
v___x_1030_ = lean_array_fset(v_as_1012_, v_i_1011_, v_a_1024_);
lean_dec(v_i_1011_);
v_i_1011_ = v___x_1029_;
v_as_1012_ = v___x_1030_;
goto _start;
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec_ref(v_a_1024_);
v___x_1032_ = lean_unsigned_to_nat(1u);
v___x_1033_ = lean_nat_add(v_i_1011_, v___x_1032_);
lean_dec(v_i_1011_);
v_i_1011_ = v___x_1033_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6_0interp(lean_interpreter_value* stack)
{
uint8_t v_shouldElimFunDecls_1010_ = stack[0].m_num;
lean_object* v_i_1011_ = stack[1].m_obj;
lean_object* v_as_1012_ = stack[2].m_obj;
lean_object* v___y_1013_ = stack[3].m_obj;
lean_object* v___y_1014_ = stack[4].m_obj;
lean_object* v___y_1015_ = stack[5].m_obj;
lean_object* v___y_1016_ = stack[6].m_obj;
lean_object* v___y_1017_ = stack[7].m_obj;
lean_object* v_res_1125_;
v_res_1125_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(v_shouldElimFunDecls_1010_, v_i_1011_, v_as_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
stack->m_obj
 = v_res_1125_;
}
lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(uint8_t v_shouldElimFunDecls_1126_, lean_object* v_code_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
switch(lean_obj_tag(v_code_1127_))
{
case 0:
{
lean_object* v_decl_1134_; lean_object* v_k_1135_; uint8_t v___x_1136_; uint8_t v___x_1137_; lean_object* v___x_1138_; 
v_decl_1134_ = lean_ctor_get(v_code_1127_, 0);
v_k_1135_ = lean_ctor_get(v_code_1127_, 1);
v___x_1136_ = 0;
v___x_1137_ = 0;
lean_inc_ref(v_decl_1134_);
v___x_1138_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v___x_1136_, v___x_1137_, v_decl_1134_, v_a_1128_, v_a_1130_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v_fvarId_1140_; lean_object* v_value_1141_; lean_object* v___x_1142_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref_known(v___x_1138_, 1);
v_fvarId_1140_ = lean_ctor_get(v_a_1139_, 0);
v_value_1141_ = lean_ctor_get(v_a_1139_, 3);
lean_inc(v_value_1141_);
v___x_1142_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(v_value_1141_, v_a_1132_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; uint8_t v___x_1144_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
v___x_1144_ = lean_unbox(v_a_1143_);
lean_dec(v_a_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v_map_1147_; lean_object* v___x_1148_; 
lean_inc(v_value_1141_);
v___x_1145_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v___x_1136_, v_value_1141_);
v___x_1146_ = lean_st_ref_get(v_a_1128_);
v_map_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc_ref(v_map_1147_);
lean_dec(v___x_1146_);
v___x_1148_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_map_1147_, v___x_1145_);
lean_dec_ref(v_map_1147_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v___x_1149_; lean_object* v_map_1150_; lean_object* v_subst_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1199_; 
v___x_1149_ = lean_st_ref_take(v_a_1128_);
v_map_1150_ = lean_ctor_get(v___x_1149_, 0);
v_subst_1151_ = lean_ctor_get(v___x_1149_, 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1153_ = v___x_1149_;
v_isShared_1154_ = v_isSharedCheck_1199_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_subst_1151_);
lean_inc(v_map_1150_);
lean_dec(v___x_1149_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1199_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
lean_inc(v_fvarId_1140_);
v___x_1155_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_map_1150_, v___x_1145_, v_fvarId_1140_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1155_);
v___x_1157_ = v___x_1153_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_subst_1151_);
v___x_1157_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_st_ref_put(v_a_1128_, v___x_1157_);
lean_inc_ref(v_k_1135_);
v___x_1159_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1126_, v_k_1135_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1197_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1162_ = v___x_1159_;
v_isShared_1163_ = v_isSharedCheck_1197_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1159_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1197_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
size_t v___x_1164_; size_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1164_ = lean_ptr_addr(v_k_1135_);
v___x_1165_ = lean_ptr_addr(v_a_1160_);
v___x_1166_ = lean_usize_dec_eq(v___x_1164_, v___x_1165_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1176_; 
v_isSharedCheck_1176_ = !lean_is_exclusive(v_code_1127_);
if (v_isSharedCheck_1176_ == 0)
{
lean_object* v_unused_1177_; lean_object* v_unused_1178_; 
v_unused_1177_ = lean_ctor_get(v_code_1127_, 1);
lean_dec(v_unused_1177_);
v_unused_1178_ = lean_ctor_get(v_code_1127_, 0);
lean_dec(v_unused_1178_);
v___x_1168_ = v_code_1127_;
v_isShared_1169_ = v_isSharedCheck_1176_;
goto v_resetjp_1167_;
}
else
{
lean_dec(v_code_1127_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1176_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v_a_1160_);
lean_ctor_set(v___x_1168_, 0, v_a_1139_);
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1139_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_a_1160_);
v___x_1171_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1173_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1171_);
v___x_1173_ = v___x_1162_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
else
{
size_t v___x_1179_; size_t v___x_1180_; uint8_t v___x_1181_; 
v___x_1179_ = lean_ptr_addr(v_decl_1134_);
v___x_1180_ = lean_ptr_addr(v_a_1139_);
v___x_1181_ = lean_usize_dec_eq(v___x_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1191_; 
v_isSharedCheck_1191_ = !lean_is_exclusive(v_code_1127_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; lean_object* v_unused_1193_; 
v_unused_1192_ = lean_ctor_get(v_code_1127_, 1);
lean_dec(v_unused_1192_);
v_unused_1193_ = lean_ctor_get(v_code_1127_, 0);
lean_dec(v_unused_1193_);
v___x_1183_ = v_code_1127_;
v_isShared_1184_ = v_isSharedCheck_1191_;
goto v_resetjp_1182_;
}
else
{
lean_dec(v_code_1127_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1191_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v_a_1160_);
lean_ctor_set(v___x_1183_, 0, v_a_1139_);
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1139_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_a_1160_);
v___x_1186_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1188_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1186_);
v___x_1188_ = v___x_1162_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1186_);
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
else
{
lean_object* v___x_1195_; 
lean_dec(v_a_1160_);
lean_dec(v_a_1139_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v_code_1127_);
v___x_1195_ = v___x_1162_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_code_1127_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
else
{
lean_dec(v_a_1139_);
lean_dec_ref_known(v_code_1127_, 2);
return v___x_1159_;
}
}
}
}
else
{
lean_object* v_val_1200_; lean_object* v___x_1201_; 
lean_inc_ref(v_k_1135_);
lean_dec_ref(v___x_1145_);
lean_dec_ref_known(v_code_1127_, 2);
v_val_1200_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_val_1200_);
lean_dec_ref_known(v___x_1148_, 1);
v___x_1201_ = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(v_a_1139_, v_val_1200_, v_a_1128_, v_a_1130_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_dec_ref_known(v___x_1201_, 1);
v_code_1127_ = v_k_1135_;
goto _start;
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v_k_1135_);
v_a_1203_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1201_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1201_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
else
{
lean_object* v___x_1211_; 
lean_inc_ref(v_k_1135_);
v___x_1211_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1126_, v_k_1135_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1249_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1249_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1249_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
size_t v___x_1216_; size_t v___x_1217_; uint8_t v___x_1218_; 
v___x_1216_ = lean_ptr_addr(v_k_1135_);
v___x_1217_ = lean_ptr_addr(v_a_1212_);
v___x_1218_ = lean_usize_dec_eq(v___x_1216_, v___x_1217_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1228_; 
v_isSharedCheck_1228_ = !lean_is_exclusive(v_code_1127_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; lean_object* v_unused_1230_; 
v_unused_1229_ = lean_ctor_get(v_code_1127_, 1);
lean_dec(v_unused_1229_);
v_unused_1230_ = lean_ctor_get(v_code_1127_, 0);
lean_dec(v_unused_1230_);
v___x_1220_ = v_code_1127_;
v_isShared_1221_ = v_isSharedCheck_1228_;
goto v_resetjp_1219_;
}
else
{
lean_dec(v_code_1127_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1228_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 1, v_a_1212_);
lean_ctor_set(v___x_1220_, 0, v_a_1139_);
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1139_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_a_1212_);
v___x_1223_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1225_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1223_);
v___x_1225_ = v___x_1214_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
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
size_t v___x_1231_; size_t v___x_1232_; uint8_t v___x_1233_; 
v___x_1231_ = lean_ptr_addr(v_decl_1134_);
v___x_1232_ = lean_ptr_addr(v_a_1139_);
v___x_1233_ = lean_usize_dec_eq(v___x_1231_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1243_; 
v_isSharedCheck_1243_ = !lean_is_exclusive(v_code_1127_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; lean_object* v_unused_1245_; 
v_unused_1244_ = lean_ctor_get(v_code_1127_, 1);
lean_dec(v_unused_1244_);
v_unused_1245_ = lean_ctor_get(v_code_1127_, 0);
lean_dec(v_unused_1245_);
v___x_1235_ = v_code_1127_;
v_isShared_1236_ = v_isSharedCheck_1243_;
goto v_resetjp_1234_;
}
else
{
lean_dec(v_code_1127_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1243_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v_a_1212_);
lean_ctor_set(v___x_1235_, 0, v_a_1139_);
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1139_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_a_1212_);
v___x_1238_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1240_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1238_);
v___x_1240_ = v___x_1214_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
else
{
lean_object* v___x_1247_; 
lean_dec(v_a_1212_);
lean_dec(v_a_1139_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v_code_1127_);
v___x_1247_ = v___x_1214_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_code_1127_);
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
}
else
{
lean_dec(v_a_1139_);
lean_dec_ref_known(v_code_1127_, 2);
return v___x_1211_;
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v_a_1139_);
lean_dec_ref_known(v_code_1127_, 2);
v_a_1250_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1142_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1142_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec_ref_known(v_code_1127_, 2);
v_a_1258_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1138_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1138_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
case 1:
{
lean_object* v_decl_1266_; lean_object* v_k_1267_; lean_object* v___x_1268_; 
v_decl_1266_ = lean_ctor_get(v_code_1127_, 0);
v_k_1267_ = lean_ctor_get(v_code_1127_, 1);
lean_inc_ref(v_decl_1266_);
v___x_1268_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_1126_, v_decl_1266_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1268_) == 0)
{
if (v_shouldElimFunDecls_1126_ == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1270_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1268_, 1);
lean_inc_ref(v_k_1267_);
v___x_1270_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1126_, v_k_1267_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1308_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1308_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1308_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
size_t v___x_1275_; size_t v___x_1276_; uint8_t v___x_1277_; 
v___x_1275_ = lean_ptr_addr(v_k_1267_);
v___x_1276_ = lean_ptr_addr(v_a_1271_);
v___x_1277_ = lean_usize_dec_eq(v___x_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1287_; 
v_isSharedCheck_1287_ = !lean_is_exclusive(v_code_1127_);
if (v_isSharedCheck_1287_ == 0)
{
lean_object* v_unused_1288_; lean_object* v_unused_1289_; 
v_unused_1288_ = lean_ctor_get(v_code_1127_, 1);
lean_dec(v_unused_1288_);
v_unused_1289_ = lean_ctor_get(v_code_1127_, 0);
lean_dec(v_unused_1289_);
v___x_1279_ = v_code_1127_;
v_isShared_1280_ = v_isSharedCheck_1287_;
goto v_resetjp_1278_;
}
else
{
lean_dec(v_code_1127_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1287_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v_a_1271_);
lean_ctor_set(v___x_1279_, 0, v_a_1269_);
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1269_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_a_1271_);
v___x_1282_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v___x_1284_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___x_1282_);
v___x_1284_ = v___x_1273_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
else
{
size_t v___x_1290_; size_t v___x_1291_; uint8_t v___x_1292_; 
v___x_1290_ = lean_ptr_addr(v_decl_1266_);
v___x_1291_ = lean_ptr_addr(v_a_1269_);
v___x_1292_ = lean_usize_dec_eq(v___x_1290_, v___x_1291_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1302_; 
v_isSharedCheck_1302_ = !lean_is_exclusive(v_code_1127_);
if (v_isSharedCheck_1302_ == 0)
{
lean_object* v_unused_1303_; lean_object* v_unused_1304_; 
v_unused_1303_ = lean_ctor_get(v_code_1127_, 1);
lean_dec(v_unused_1303_);
v_unused_1304_ = lean_ctor_get(v_code_1127_, 0);
lean_dec(v_unused_1304_);
v___x_1294_ = v_code_1127_;
v_isShared_1295_ = v_isSharedCheck_1302_;
goto v_resetjp_1293_;
}
else
{
lean_dec(v_code_1127_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1302_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 1, v_a_1271_);
lean_ctor_set(v___x_1294_, 0, v_a_1269_);
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1269_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_a_1271_);
v___x_1297_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
lean_object* v___x_1299_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___x_1297_);
v___x_1299_ = v___x_1273_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
else
{
lean_object* v___x_1306_; 
lean_dec(v_a_1271_);
lean_dec(v_a_1269_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v_code_1127_);
v___x_1306_ = v___x_1273_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_code_1127_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
else
{
lean_dec(v_a_1269_);
lean_dec_ref_known(v_code_1127_, 2);
return v___x_1270_;
}
}
else
{
lean_object* v_a_1309_; uint8_t v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v_map_1314_; lean_object* v___x_1315_; 
v_a_1309_ = lean_ctor_get(v___x_1268_, 0);
lean_inc_n(v_a_1309_, 2);
lean_dec_ref_known(v___x_1268_, 1);
v___x_1310_ = 0;
v___x_1311_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___closed__0));
v___x_1312_ = l_Lean_Compiler_LCNF_FunDecl_toExpr(v___x_1310_, v_a_1309_, v___x_1311_);
v___x_1313_ = lean_st_ref_get(v_a_1128_);
v_map_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc_ref(v_map_1314_);
lean_dec(v___x_1313_);
v___x_1315_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_map_1314_, v___x_1312_);
lean_dec_ref(v_map_1314_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_fvarId_1316_; lean_object* v___x_1317_; lean_object* v_map_1318_; lean_object* v_subst_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1367_; 
v_fvarId_1316_ = lean_ctor_get(v_a_1309_, 0);
v___x_1317_ = lean_st_ref_take(v_a_1128_);
v_map_1318_ = lean_ctor_get(v___x_1317_, 0);
v_subst_1319_ = lean_ctor_get(v___x_1317_, 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1321_ = v___x_1317_;
v_isShared_1322_ = v_isSharedCheck_1367_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_subst_1319_);
lean_inc(v_map_1318_);
lean_dec(v___x_1317_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1367_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
lean_inc(v_fvarId_1316_);
v___x_1323_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_map_1318_, v___x_1312_, v_fvarId_1316_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1323_);
v___x_1325_ = v___x_1321_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_subst_1319_);
v___x_1325_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_st_ref_put(v_a_1128_, v___x_1325_);
lean_inc_ref(v_k_1267_);
v___x_1327_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1126_, v_k_1267_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1365_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1365_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1365_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
size_t v___x_1332_; size_t v___x_1333_; uint8_t v___x_1334_; 
v___x_1332_ = lean_ptr_addr(v_k_1267_);
v___x_1333_ = lean_ptr_addr(v_a_1328_);
v___x_1334_ = lean_usize_dec_eq(v___x_1332_, v___x_1333_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1344_; 
v_isSharedCheck_1344_ = !lean_is_exclusive(v_code_1127_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; lean_object* v_unused_1346_; 
v_unused_1345_ = lean_ctor_get(v_code_1127_, 1);
lean_dec(v_unused_1345_);
v_unused_1346_ = lean_ctor_get(v_code_1127_, 0);
lean_dec(v_unused_1346_);
v___x_1336_ = v_code_1127_;
v_isShared_1337_ = v_isSharedCheck_1344_;
goto v_resetjp_1335_;
}
else
{
lean_dec(v_code_1127_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1344_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 1, v_a_1328_);
lean_ctor_set(v___x_1336_, 0, v_a_1309_);
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1309_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_a_1328_);
v___x_1339_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1341_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1339_);
v___x_1341_ = v___x_1330_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
else
{
size_t v___x_1347_; size_t v___x_1348_; uint8_t v___x_1349_; 
v___x_1347_ = lean_ptr_addr(v_decl_1266_);
v___x_1348_ = lean_ptr_addr(v_a_1309_);
v___x_1349_ = lean_usize_dec_eq(v___x_1347_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1359_; 
v_isSharedCheck_1359_ = !lean_is_exclusive(v_code_1127_);
if (v_isSharedCheck_1359_ == 0)
{
lean_object* v_unused_1360_; lean_object* v_unused_1361_; 
v_unused_1360_ = lean_ctor_get(v_code_1127_, 1);
lean_dec(v_unused_1360_);
v_unused_1361_ = lean_ctor_get(v_code_1127_, 0);
lean_dec(v_unused_1361_);
v___x_1351_ = v_code_1127_;
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
else
{
lean_dec(v_code_1127_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 1, v_a_1328_);
lean_ctor_set(v___x_1351_, 0, v_a_1309_);
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1309_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_a_1328_);
v___x_1354_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1356_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1354_);
v___x_1356_ = v___x_1330_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v___x_1363_; 
lean_dec(v_a_1328_);
lean_dec(v_a_1309_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v_code_1127_);
v___x_1363_ = v___x_1330_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_code_1127_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
else
{
lean_dec(v_a_1309_);
lean_dec_ref_known(v_code_1127_, 2);
return v___x_1327_;
}
}
}
}
else
{
lean_object* v_val_1368_; lean_object* v___x_1369_; 
lean_inc_ref(v_k_1267_);
lean_dec_ref(v___x_1312_);
lean_dec_ref_known(v_code_1127_, 2);
v_val_1368_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_val_1368_);
lean_dec_ref_known(v___x_1315_, 1);
v___x_1369_ = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(v_a_1309_, v_val_1368_, v_a_1128_, v_a_1130_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_dec_ref_known(v___x_1369_, 1);
v_code_1127_ = v_k_1267_;
goto _start;
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec_ref(v_k_1267_);
v_a_1371_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1369_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1369_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec_ref_known(v_code_1127_, 2);
v_a_1379_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1268_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1268_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
case 2:
{
lean_object* v_decl_1387_; lean_object* v_k_1388_; lean_object* v___x_1389_; 
v_decl_1387_ = lean_ctor_get(v_code_1127_, 0);
v_k_1388_ = lean_ctor_get(v_code_1127_, 1);
lean_inc_ref(v_decl_1387_);
v___x_1389_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_1126_, v_decl_1387_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1391_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
lean_inc_ref(v_k_1388_);
v___x_1391_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1126_, v_k_1388_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1429_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1394_ = v___x_1391_;
v_isShared_1395_ = v_isSharedCheck_1429_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1391_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1429_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
size_t v___x_1396_; size_t v___x_1397_; uint8_t v___x_1398_; 
v___x_1396_ = lean_ptr_addr(v_k_1388_);
v___x_1397_ = lean_ptr_addr(v_a_1392_);
v___x_1398_ = lean_usize_dec_eq(v___x_1396_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1408_; 
v_isSharedCheck_1408_ = !lean_is_exclusive(v_code_1127_);
if (v_isSharedCheck_1408_ == 0)
{
lean_object* v_unused_1409_; lean_object* v_unused_1410_; 
v_unused_1409_ = lean_ctor_get(v_code_1127_, 1);
lean_dec(v_unused_1409_);
v_unused_1410_ = lean_ctor_get(v_code_1127_, 0);
lean_dec(v_unused_1410_);
v___x_1400_ = v_code_1127_;
v_isShared_1401_ = v_isSharedCheck_1408_;
goto v_resetjp_1399_;
}
else
{
lean_dec(v_code_1127_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1408_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 1, v_a_1392_);
lean_ctor_set(v___x_1400_, 0, v_a_1390_);
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1390_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_a_1392_);
v___x_1403_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1405_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1403_);
v___x_1405_ = v___x_1394_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
size_t v___x_1411_; size_t v___x_1412_; uint8_t v___x_1413_; 
v___x_1411_ = lean_ptr_addr(v_decl_1387_);
v___x_1412_ = lean_ptr_addr(v_a_1390_);
v___x_1413_ = lean_usize_dec_eq(v___x_1411_, v___x_1412_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1423_; 
v_isSharedCheck_1423_ = !lean_is_exclusive(v_code_1127_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; lean_object* v_unused_1425_; 
v_unused_1424_ = lean_ctor_get(v_code_1127_, 1);
lean_dec(v_unused_1424_);
v_unused_1425_ = lean_ctor_get(v_code_1127_, 0);
lean_dec(v_unused_1425_);
v___x_1415_ = v_code_1127_;
v_isShared_1416_ = v_isSharedCheck_1423_;
goto v_resetjp_1414_;
}
else
{
lean_dec(v_code_1127_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1423_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 1, v_a_1392_);
lean_ctor_set(v___x_1415_, 0, v_a_1390_);
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1390_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_a_1392_);
v___x_1418_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1420_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1418_);
v___x_1420_ = v___x_1394_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
else
{
lean_object* v___x_1427_; 
lean_dec(v_a_1392_);
lean_dec(v_a_1390_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v_code_1127_);
v___x_1427_ = v___x_1394_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_code_1127_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
}
else
{
lean_dec(v_a_1390_);
lean_dec_ref_known(v_code_1127_, 2);
return v___x_1391_;
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec_ref_known(v_code_1127_, 2);
v_a_1430_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1389_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1389_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_1438_; lean_object* v_args_1439_; uint8_t v___x_1440_; uint8_t v___x_1441_; lean_object* v___x_1442_; lean_object* v_subst_1443_; lean_object* v___x_1444_; 
v_fvarId_1438_ = lean_ctor_get(v_code_1127_, 0);
v_args_1439_ = lean_ctor_get(v_code_1127_, 1);
v___x_1440_ = 0;
v___x_1441_ = 0;
v___x_1442_ = lean_st_ref_get(v_a_1128_);
v_subst_1443_ = lean_ctor_get(v___x_1442_, 1);
lean_inc_ref(v_subst_1443_);
lean_dec(v___x_1442_);
lean_inc(v_fvarId_1438_);
v___x_1444_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1443_, v_fvarId_1438_, v___x_1441_);
lean_dec_ref(v_subst_1443_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_fvarId_1445_; lean_object* v___x_1446_; 
v_fvarId_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_fvarId_1445_);
lean_dec_ref_known(v___x_1444_, 1);
lean_inc_ref(v_args_1439_);
v___x_1446_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v___x_1440_, v___x_1441_, v_args_1439_, v_a_1128_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1472_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1449_ = v___x_1446_;
v_isShared_1450_ = v_isSharedCheck_1472_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1446_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1472_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
uint8_t v___y_1452_; uint8_t v___x_1468_; 
v___x_1468_ = l_Lean_instBEqFVarId_beq(v_fvarId_1438_, v_fvarId_1445_);
if (v___x_1468_ == 0)
{
v___y_1452_ = v___x_1468_;
goto v___jp_1451_;
}
else
{
size_t v___x_1469_; size_t v___x_1470_; uint8_t v___x_1471_; 
v___x_1469_ = lean_ptr_addr(v_args_1439_);
v___x_1470_ = lean_ptr_addr(v_a_1447_);
v___x_1471_ = lean_usize_dec_eq(v___x_1469_, v___x_1470_);
v___y_1452_ = v___x_1471_;
goto v___jp_1451_;
}
v___jp_1451_:
{
if (v___y_1452_ == 0)
{
lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1462_; 
v_isSharedCheck_1462_ = !lean_is_exclusive(v_code_1127_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; lean_object* v_unused_1464_; 
v_unused_1463_ = lean_ctor_get(v_code_1127_, 1);
lean_dec(v_unused_1463_);
v_unused_1464_ = lean_ctor_get(v_code_1127_, 0);
lean_dec(v_unused_1464_);
v___x_1454_ = v_code_1127_;
v_isShared_1455_ = v_isSharedCheck_1462_;
goto v_resetjp_1453_;
}
else
{
lean_dec(v_code_1127_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1462_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 1, v_a_1447_);
lean_ctor_set(v___x_1454_, 0, v_fvarId_1445_);
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_fvarId_1445_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_a_1447_);
v___x_1457_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1459_; 
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1457_);
v___x_1459_ = v___x_1449_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1457_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
else
{
lean_object* v___x_1466_; 
lean_dec(v_a_1447_);
lean_dec(v_fvarId_1445_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v_code_1127_);
v___x_1466_ = v___x_1449_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_code_1127_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_fvarId_1445_);
lean_dec_ref_known(v_code_1127_, 2);
v_a_1473_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1446_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1446_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v___x_1481_; 
lean_dec_ref_known(v_code_1127_, 2);
v___x_1481_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1440_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
return v___x_1481_;
}
}
case 4:
{
lean_object* v_cases_1482_; lean_object* v_typeName_1483_; lean_object* v_resultType_1484_; lean_object* v_discr_1485_; lean_object* v_alts_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1537_; 
v_cases_1482_ = lean_ctor_get(v_code_1127_, 0);
lean_inc_ref(v_cases_1482_);
v_typeName_1483_ = lean_ctor_get(v_cases_1482_, 0);
v_resultType_1484_ = lean_ctor_get(v_cases_1482_, 1);
v_discr_1485_ = lean_ctor_get(v_cases_1482_, 2);
v_alts_1486_ = lean_ctor_get(v_cases_1482_, 3);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_cases_1482_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1488_ = v_cases_1482_;
v_isShared_1489_ = v_isSharedCheck_1537_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_alts_1486_);
lean_inc(v_discr_1485_);
lean_inc(v_resultType_1484_);
lean_inc(v_typeName_1483_);
lean_dec(v_cases_1482_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1537_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
uint8_t v___x_1490_; uint8_t v___x_1491_; lean_object* v___x_1492_; lean_object* v_subst_1493_; lean_object* v___x_1494_; 
v___x_1490_ = 0;
v___x_1491_ = 0;
v___x_1492_ = lean_st_ref_get(v_a_1128_);
v_subst_1493_ = lean_ctor_get(v___x_1492_, 1);
lean_inc_ref(v_subst_1493_);
lean_dec(v___x_1492_);
lean_inc(v_discr_1485_);
v___x_1494_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1493_, v_discr_1485_, v___x_1491_);
lean_dec_ref(v_subst_1493_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_fvarId_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1535_; 
v_fvarId_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1535_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_fvarId_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1535_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v_subst_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1499_ = lean_st_ref_get(v_a_1128_);
v_subst_1500_ = lean_ctor_get(v___x_1499_, 1);
lean_inc_ref(v_subst_1500_);
lean_dec(v___x_1499_);
lean_inc_ref(v_resultType_1484_);
v___x_1501_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_1490_, v_subst_1500_, v___x_1491_, v_resultType_1484_);
lean_dec_ref(v_subst_1500_);
v___x_1502_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1486_);
v___x_1503_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(v_shouldElimFunDecls_1126_, v___x_1502_, v_alts_1486_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1526_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1526_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1526_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
size_t v___x_1518_; size_t v___x_1519_; uint8_t v___x_1520_; 
v___x_1518_ = lean_ptr_addr(v_alts_1486_);
lean_dec_ref(v_alts_1486_);
v___x_1519_ = lean_ptr_addr(v_a_1504_);
v___x_1520_ = lean_usize_dec_eq(v___x_1518_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_dec(v_discr_1485_);
lean_dec_ref(v_resultType_1484_);
lean_dec_ref_known(v_code_1127_, 1);
goto v___jp_1508_;
}
else
{
size_t v___x_1521_; size_t v___x_1522_; uint8_t v___x_1523_; 
v___x_1521_ = lean_ptr_addr(v_resultType_1484_);
lean_dec_ref(v_resultType_1484_);
v___x_1522_ = lean_ptr_addr(v___x_1501_);
v___x_1523_ = lean_usize_dec_eq(v___x_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_dec(v_discr_1485_);
lean_dec_ref_known(v_code_1127_, 1);
goto v___jp_1508_;
}
else
{
uint8_t v___x_1524_; 
v___x_1524_ = l_Lean_instBEqFVarId_beq(v_discr_1485_, v_fvarId_1495_);
lean_dec(v_discr_1485_);
if (v___x_1524_ == 0)
{
lean_dec_ref_known(v_code_1127_, 1);
goto v___jp_1508_;
}
else
{
lean_object* v___x_1525_; 
lean_del_object(v___x_1506_);
lean_dec(v_a_1504_);
lean_dec_ref(v___x_1501_);
lean_del_object(v___x_1497_);
lean_dec(v_fvarId_1495_);
lean_del_object(v___x_1488_);
lean_dec(v_typeName_1483_);
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_code_1127_);
return v___x_1525_;
}
}
}
v___jp_1508_:
{
lean_object* v___x_1510_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 3, v_a_1504_);
lean_ctor_set(v___x_1488_, 2, v_fvarId_1495_);
lean_ctor_set(v___x_1488_, 1, v___x_1501_);
v___x_1510_ = v___x_1488_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_typeName_1483_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_fvarId_1495_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_a_1504_);
v___x_1510_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1512_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set_tag(v___x_1497_, 4);
lean_ctor_set(v___x_1497_, 0, v___x_1510_);
v___x_1512_ = v___x_1497_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1512_);
v___x_1514_ = v___x_1506_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec_ref(v___x_1501_);
lean_del_object(v___x_1497_);
lean_dec(v_fvarId_1495_);
lean_del_object(v___x_1488_);
lean_dec_ref(v_alts_1486_);
lean_dec(v_discr_1485_);
lean_dec_ref(v_resultType_1484_);
lean_dec(v_typeName_1483_);
lean_dec_ref_known(v_code_1127_, 1);
v_a_1527_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1503_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1503_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
}
else
{
lean_object* v___x_1536_; 
lean_del_object(v___x_1488_);
lean_dec_ref(v_alts_1486_);
lean_dec(v_discr_1485_);
lean_dec_ref(v_resultType_1484_);
lean_dec(v_typeName_1483_);
lean_dec_ref_known(v_code_1127_, 1);
v___x_1536_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1490_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
return v___x_1536_;
}
}
}
case 5:
{
lean_object* v_fvarId_1538_; uint8_t v___x_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v_subst_1542_; lean_object* v___x_1543_; 
v_fvarId_1538_ = lean_ctor_get(v_code_1127_, 0);
v___x_1539_ = 0;
v___x_1540_ = 0;
v___x_1541_ = lean_st_ref_get(v_a_1128_);
v_subst_1542_ = lean_ctor_get(v___x_1541_, 1);
lean_inc_ref(v_subst_1542_);
lean_dec(v___x_1541_);
lean_inc(v_fvarId_1538_);
v___x_1543_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1542_, v_fvarId_1538_, v___x_1540_);
lean_dec_ref(v_subst_1542_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_fvarId_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1563_; 
v_fvarId_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1563_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_fvarId_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1563_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
uint8_t v___x_1548_; 
v___x_1548_ = l_Lean_instBEqFVarId_beq(v_fvarId_1538_, v_fvarId_1544_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1558_; 
v_isSharedCheck_1558_ = !lean_is_exclusive(v_code_1127_);
if (v_isSharedCheck_1558_ == 0)
{
lean_object* v_unused_1559_; 
v_unused_1559_ = lean_ctor_get(v_code_1127_, 0);
lean_dec(v_unused_1559_);
v___x_1550_ = v_code_1127_;
v_isShared_1551_ = v_isSharedCheck_1558_;
goto v_resetjp_1549_;
}
else
{
lean_dec(v_code_1127_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1558_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v_fvarId_1544_);
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_fvarId_1544_);
v___x_1553_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1555_; 
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1553_);
v___x_1555_ = v___x_1546_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
else
{
lean_object* v___x_1561_; 
lean_dec(v_fvarId_1544_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v_code_1127_);
v___x_1561_ = v___x_1546_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_code_1127_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_object* v___x_1564_; 
lean_dec_ref_known(v_code_1127_, 1);
v___x_1564_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1539_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
return v___x_1564_;
}
}
default: 
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v_code_1127_);
return v___x_1565_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_shouldElimFunDecls_1126_ = stack[0].m_num;
lean_object* v_code_1127_ = stack[1].m_obj;
lean_object* v_a_1128_ = stack[2].m_obj;
lean_object* v_a_1129_ = stack[3].m_obj;
lean_object* v_a_1130_ = stack[4].m_obj;
lean_object* v_a_1131_ = stack[5].m_obj;
lean_object* v_a_1132_ = stack[6].m_obj;
lean_object* v_res_1566_;
v_res_1566_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1126_, v_code_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
stack->m_obj
 = v_res_1566_;
}
lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(uint8_t v_shouldElimFunDecls_1567_, lean_object* v_decl_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v_params_1575_; lean_object* v_type_1576_; lean_object* v_value_1577_; uint8_t v___x_1578_; uint8_t v___x_1579_; lean_object* v___x_1580_; lean_object* v_subst_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v_params_1575_ = lean_ctor_get(v_decl_1568_, 2);
v_type_1576_ = lean_ctor_get(v_decl_1568_, 3);
v_value_1577_ = lean_ctor_get(v_decl_1568_, 4);
v___x_1578_ = 0;
v___x_1579_ = 0;
v___x_1580_ = lean_st_ref_get(v_a_1569_);
v_subst_1581_ = lean_ctor_get(v___x_1580_, 1);
lean_inc_ref(v_subst_1581_);
lean_dec(v___x_1580_);
lean_inc_ref(v_type_1576_);
v___x_1582_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_1578_, v_subst_1581_, v___x_1579_, v_type_1576_);
lean_dec_ref(v_subst_1581_);
lean_inc_ref(v_params_1575_);
v___x_1583_ = l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(v___x_1578_, v___x_1579_, v_params_1575_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1585_; lean_object* v_map_1586_; lean_object* v_r_1587_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
v___x_1585_ = lean_st_ref_get(v_a_1569_);
v_map_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc_ref(v_map_1586_);
lean_dec(v___x_1585_);
lean_inc_ref(v_value_1577_);
v_r_1587_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1567_, v_value_1577_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_);
if (lean_obj_tag(v_r_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1605_; 
v_a_1588_ = lean_ctor_get(v_r_1587_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_r_1587_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1590_ = v_r_1587_;
v_isShared_1591_ = v_isSharedCheck_1605_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v_r_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1605_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
lean_inc(v_a_1588_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set_tag(v___x_1590_, 1);
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1594_; 
v___x_1594_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(v_a_1569_, v_map_1586_, v___x_1593_);
lean_dec_ref(v___x_1593_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v___x_1595_; 
lean_dec_ref_known(v___x_1594_, 1);
v___x_1595_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1578_, v_decl_1568_, v___x_1582_, v_a_1584_, v_a_1588_, v_a_1571_);
return v___x_1595_;
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v_a_1588_);
lean_dec(v_a_1584_);
lean_dec_ref(v___x_1582_);
lean_dec_ref(v_decl_1568_);
v_a_1596_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1594_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1594_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_dec(v_a_1584_);
lean_dec_ref(v___x_1582_);
lean_dec_ref(v_decl_1568_);
v_a_1606_ = lean_ctor_get(v_r_1587_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v_r_1587_, 1);
v___x_1607_ = lean_box(0);
v___x_1608_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(v_a_1569_, v_map_1586_, v___x_1607_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; 
v_unused_1616_ = lean_ctor_get(v___x_1608_, 0);
lean_dec(v_unused_1616_);
v___x_1610_ = v___x_1608_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_dec(v___x_1608_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
lean_ctor_set_tag(v___x_1610_, 1);
lean_ctor_set(v___x_1610_, 0, v_a_1606_);
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1606_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec(v_a_1606_);
v_a_1617_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1608_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1608_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec_ref(v___x_1582_);
lean_dec_ref(v_decl_1568_);
v_a_1625_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1583_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1583_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_shouldElimFunDecls_1567_ = stack[0].m_num;
lean_object* v_decl_1568_ = stack[1].m_obj;
lean_object* v_a_1569_ = stack[2].m_obj;
lean_object* v_a_1570_ = stack[3].m_obj;
lean_object* v_a_1571_ = stack[4].m_obj;
lean_object* v_a_1572_ = stack[5].m_obj;
lean_object* v_a_1573_ = stack[6].m_obj;
lean_object* v_res_1633_;
v_res_1633_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_1567_, v_decl_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_);
stack->m_obj
 = v_res_1633_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___boxed(lean_object* v_shouldElimFunDecls_1634_, lean_object* v_decl_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1642_; lean_object* v_res_1643_; 
v_shouldElimFunDecls_boxed_1642_ = lean_unbox(v_shouldElimFunDecls_1634_);
v_res_1643_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_boxed_1642_, v_decl_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___boxed(lean_object* v_shouldElimFunDecls_1644_, lean_object* v_i_1645_, lean_object* v_as_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1653_; lean_object* v_res_1654_; 
v_shouldElimFunDecls_boxed_1653_ = lean_unbox(v_shouldElimFunDecls_1644_);
v_res_1654_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(v_shouldElimFunDecls_boxed_1653_, v_i_1645_, v_as_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___boxed(lean_object* v_shouldElimFunDecls_1655_, lean_object* v_code_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1663_; lean_object* v_res_1664_; 
v_shouldElimFunDecls_boxed_1663_ = lean_unbox(v_shouldElimFunDecls_1655_);
v_res_1664_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_boxed_1663_, v_code_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec(v_a_1657_);
return v_res_1664_;
}
}
lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2(uint8_t v_pu_1665_, uint8_t v_t_1666_, lean_object* v_decl_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v_pu_1665_, v_t_1666_, v_decl_1667_, v___y_1668_, v___y_1670_);
return v___x_1674_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1665_ = stack[0].m_num;
uint8_t v_t_1666_ = stack[1].m_num;
lean_object* v_decl_1667_ = stack[2].m_obj;
lean_object* v___y_1668_ = stack[3].m_obj;
lean_object* v___y_1669_ = stack[4].m_obj;
lean_object* v___y_1670_ = stack[5].m_obj;
lean_object* v___y_1671_ = stack[6].m_obj;
lean_object* v___y_1672_ = stack[7].m_obj;
lean_object* v_res_1675_;
v_res_1675_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2(v_pu_1665_, v_t_1666_, v_decl_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
stack->m_obj
 = v_res_1675_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___boxed(lean_object* v_pu_1676_, lean_object* v_t_1677_, lean_object* v_decl_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v_pu_boxed_1685_; uint8_t v_t_boxed_1686_; lean_object* v_res_1687_; 
v_pu_boxed_1685_ = lean_unbox(v_pu_1676_);
v_t_boxed_1686_ = lean_unbox(v_t_1677_);
v_res_1687_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2(v_pu_boxed_1685_, v_t_boxed_1686_, v_decl_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
return v_res_1687_;
}
}
lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5(uint8_t v_pu_1688_, uint8_t v_t_1689_, lean_object* v_args_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v_pu_1688_, v_t_1689_, v_args_1690_, v___y_1691_);
return v___x_1697_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1688_ = stack[0].m_num;
uint8_t v_t_1689_ = stack[1].m_num;
lean_object* v_args_1690_ = stack[2].m_obj;
lean_object* v___y_1691_ = stack[3].m_obj;
lean_object* v___y_1692_ = stack[4].m_obj;
lean_object* v___y_1693_ = stack[5].m_obj;
lean_object* v___y_1694_ = stack[6].m_obj;
lean_object* v___y_1695_ = stack[7].m_obj;
lean_object* v_res_1698_;
v_res_1698_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5(v_pu_1688_, v_t_1689_, v_args_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
stack->m_obj
 = v_res_1698_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___boxed(lean_object* v_pu_1699_, lean_object* v_t_1700_, lean_object* v_args_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
uint8_t v_pu_boxed_1708_; uint8_t v_t_boxed_1709_; lean_object* v_res_1710_; 
v_pu_boxed_1708_ = lean_unbox(v_pu_1699_);
v_t_boxed_1709_ = lean_unbox(v_t_1700_);
v_res_1710_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5(v_pu_boxed_1708_, v_t_boxed_1709_, v_args_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3(lean_object* v_00_u03b2_1711_, lean_object* v_x_1712_, lean_object* v_x_1713_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_x_1712_, v_x_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___boxed(lean_object* v_00_u03b2_1715_, lean_object* v_x_1716_, lean_object* v_x_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3(v_00_u03b2_1715_, v_x_1716_, v_x_1717_);
lean_dec_ref(v_x_1717_);
lean_dec_ref(v_x_1716_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4(lean_object* v_00_u03b2_1719_, lean_object* v_x_1720_, lean_object* v_x_1721_, lean_object* v_x_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_x_1720_, v_x_1721_, v_x_1722_);
return v___x_1723_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(uint8_t v_pu_1724_, uint8_t v_t_1725_, lean_object* v_i_1726_, lean_object* v_as_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(v_pu_1724_, v_t_1725_, v_i_1726_, v_as_1727_, v___y_1728_, v___y_1730_);
return v___x_1734_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1724_ = stack[0].m_num;
uint8_t v_t_1725_ = stack[1].m_num;
lean_object* v_i_1726_ = stack[2].m_obj;
lean_object* v_as_1727_ = stack[3].m_obj;
lean_object* v___y_1728_ = stack[4].m_obj;
lean_object* v___y_1729_ = stack[5].m_obj;
lean_object* v___y_1730_ = stack[6].m_obj;
lean_object* v___y_1731_ = stack[7].m_obj;
lean_object* v___y_1732_ = stack[8].m_obj;
lean_object* v_res_1735_;
v_res_1735_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(v_pu_1724_, v_t_1725_, v_i_1726_, v_as_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
stack->m_obj
 = v_res_1735_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___boxed(lean_object* v_pu_1736_, lean_object* v_t_1737_, lean_object* v_i_1738_, lean_object* v_as_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
uint8_t v_pu_boxed_1746_; uint8_t v_t_boxed_1747_; lean_object* v_res_1748_; 
v_pu_boxed_1746_ = lean_unbox(v_pu_1736_);
v_t_boxed_1747_ = lean_unbox(v_t_1737_);
v_res_1748_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(v_pu_boxed_1746_, v_t_boxed_1747_, v_i_1738_, v_as_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
return v_res_1748_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4(lean_object* v_00_u03b2_1749_, lean_object* v_x_1750_, size_t v_x_1751_, lean_object* v_x_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_1750_, v_x_1751_, v_x_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1750_ = stack[1].m_obj;
size_t v_x_1751_ = stack[2].m_num;
lean_object* v_x_1752_ = stack[3].m_obj;
lean_object* v_res_1754_;
v_res_1754_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4(lean_box(0), v_x_1750_, v_x_1751_, v_x_1752_);
stack->m_obj
 = v_res_1754_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1755_, lean_object* v_x_1756_, lean_object* v_x_1757_, lean_object* v_x_1758_){
_start:
{
size_t v_x_17770__boxed_1759_; lean_object* v_res_1760_; 
v_x_17770__boxed_1759_ = lean_unbox_usize(v_x_1757_);
lean_dec(v_x_1757_);
v_res_1760_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4(v_00_u03b2_1755_, v_x_1756_, v_x_17770__boxed_1759_, v_x_1758_);
lean_dec_ref(v_x_1758_);
lean_dec_ref(v_x_1756_);
return v_res_1760_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6(lean_object* v_00_u03b2_1761_, lean_object* v_x_1762_, size_t v_x_1763_, size_t v_x_1764_, lean_object* v_x_1765_, lean_object* v_x_1766_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_1762_, v_x_1763_, v_x_1764_, v_x_1765_, v_x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1762_ = stack[1].m_obj;
size_t v_x_1763_ = stack[2].m_num;
size_t v_x_1764_ = stack[3].m_num;
lean_object* v_x_1765_ = stack[4].m_obj;
lean_object* v_x_1766_ = stack[5].m_obj;
lean_object* v_res_1768_;
v_res_1768_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6(lean_box(0), v_x_1762_, v_x_1763_, v_x_1764_, v_x_1765_, v_x_1766_);
stack->m_obj
 = v_res_1768_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1769_, lean_object* v_x_1770_, lean_object* v_x_1771_, lean_object* v_x_1772_, lean_object* v_x_1773_, lean_object* v_x_1774_){
_start:
{
size_t v_x_17788__boxed_1775_; size_t v_x_17789__boxed_1776_; lean_object* v_res_1777_; 
v_x_17788__boxed_1775_ = lean_unbox_usize(v_x_1771_);
lean_dec(v_x_1771_);
v_x_17789__boxed_1776_ = lean_unbox_usize(v_x_1772_);
lean_dec(v_x_1772_);
v_res_1777_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6(v_00_u03b2_1769_, v_x_1770_, v_x_17788__boxed_1775_, v_x_17789__boxed_1776_, v_x_1773_, v_x_1774_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1778_, lean_object* v_keys_1779_, lean_object* v_vals_1780_, lean_object* v_heq_1781_, lean_object* v_i_1782_, lean_object* v_k_1783_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(v_keys_1779_, v_vals_1780_, v_i_1782_, v_k_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1785_, lean_object* v_keys_1786_, lean_object* v_vals_1787_, lean_object* v_heq_1788_, lean_object* v_i_1789_, lean_object* v_k_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6(v_00_u03b2_1785_, v_keys_1786_, v_vals_1787_, v_heq_1788_, v_i_1789_, v_k_1790_);
lean_dec_ref(v_k_1790_);
lean_dec_ref(v_vals_1787_);
lean_dec_ref(v_keys_1786_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_1792_, lean_object* v_n_1793_, lean_object* v_k_1794_, lean_object* v_v_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(v_n_1793_, v_k_1794_, v_v_1795_);
return v___x_1796_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_1797_, size_t v_depth_1798_, lean_object* v_keys_1799_, lean_object* v_vals_1800_, lean_object* v_heq_1801_, lean_object* v_i_1802_, lean_object* v_entries_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_depth_1798_, v_keys_1799_, v_vals_1800_, v_i_1802_, v_entries_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1798_ = stack[1].m_num;
lean_object* v_keys_1799_ = stack[2].m_obj;
lean_object* v_vals_1800_ = stack[3].m_obj;
lean_object* v_i_1802_ = stack[5].m_obj;
lean_object* v_entries_1803_ = stack[6].m_obj;
lean_object* v_res_1805_;
v_res_1805_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10(lean_box(0), v_depth_1798_, v_keys_1799_, v_vals_1800_, lean_box(0), v_i_1802_, v_entries_1803_);
stack->m_obj
 = v_res_1805_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1806_, lean_object* v_depth_1807_, lean_object* v_keys_1808_, lean_object* v_vals_1809_, lean_object* v_heq_1810_, lean_object* v_i_1811_, lean_object* v_entries_1812_){
_start:
{
size_t v_depth_boxed_1813_; lean_object* v_res_1814_; 
v_depth_boxed_1813_ = lean_unbox_usize(v_depth_1807_);
lean_dec(v_depth_1807_);
v_res_1814_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10(v_00_u03b2_1806_, v_depth_boxed_1813_, v_keys_1808_, v_vals_1809_, v_heq_1810_, v_i_1811_, v_entries_1812_);
lean_dec_ref(v_vals_1809_);
lean_dec_ref(v_keys_1808_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_1815_, lean_object* v_x_1816_, lean_object* v_x_1817_, lean_object* v_x_1818_, lean_object* v_x_1819_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(v_x_1816_, v_x_1817_, v_x_1818_, v_x_1819_);
return v___x_1820_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__0(void){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1821_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__1(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__0, &l_Lean_Compiler_LCNF_Code_cse___closed__0_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__0);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
return v___x_1823_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__2(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = lean_box(0);
v___x_1825_ = lean_unsigned_to_nat(16u);
v___x_1826_ = lean_mk_array(v___x_1825_, v___x_1824_);
return v___x_1826_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__3(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__2, &l_Lean_Compiler_LCNF_Code_cse___closed__2_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__2);
v___x_1828_ = lean_unsigned_to_nat(0u);
v___x_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
lean_ctor_set(v___x_1829_, 1, v___x_1827_);
return v___x_1829_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__4(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1830_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__3, &l_Lean_Compiler_LCNF_Code_cse___closed__3_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__3);
v___x_1831_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__1, &l_Lean_Compiler_LCNF_Code_cse___closed__1_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__1);
v___x_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
lean_ctor_set(v___x_1832_, 1, v___x_1830_);
return v___x_1832_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_cse(uint8_t v_shouldElimFunDecls_1833_, lean_object* v_code_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__4, &l_Lean_Compiler_LCNF_Code_cse___closed__4_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__4);
v___x_1841_ = lean_st_mk_ref(v___x_1840_);
v___x_1842_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1833_, v_code_1834_, v___x_1841_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1851_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1847_ = lean_st_ref_get(v___x_1841_);
lean_dec(v___x_1841_);
lean_dec(v___x_1847_);
if (v_isShared_1846_ == 0)
{
v___x_1849_ = v___x_1845_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1843_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
else
{
lean_dec(v___x_1841_);
return v___x_1842_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_cse_0interp(lean_interpreter_value* stack)
{
uint8_t v_shouldElimFunDecls_1833_ = stack[0].m_num;
lean_object* v_code_1834_ = stack[1].m_obj;
lean_object* v_a_1835_ = stack[2].m_obj;
lean_object* v_a_1836_ = stack[3].m_obj;
lean_object* v_a_1837_ = stack[4].m_obj;
lean_object* v_a_1838_ = stack[5].m_obj;
lean_object* v_res_1852_;
v_res_1852_ = l_Lean_Compiler_LCNF_Code_cse(v_shouldElimFunDecls_1833_, v_code_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
stack->m_obj
 = v_res_1852_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse___boxed(lean_object* v_shouldElimFunDecls_1853_, lean_object* v_code_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1860_; lean_object* v_res_1861_; 
v_shouldElimFunDecls_boxed_1860_ = lean_unbox(v_shouldElimFunDecls_1853_);
v_res_1861_ = l_Lean_Compiler_LCNF_Code_cse(v_shouldElimFunDecls_boxed_1860_, v_code_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1855_);
return v_res_1861_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(lean_object* v_f_1862_, lean_object* v_v_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
if (lean_obj_tag(v_v_1863_) == 0)
{
lean_object* v_code_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1893_; 
v_code_1869_ = lean_ctor_get(v_v_1863_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_v_1863_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1871_ = v_v_1863_;
v_isShared_1872_ = v_isSharedCheck_1893_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_code_1869_);
lean_dec(v_v_1863_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1893_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; 
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
v___x_1873_ = lean_apply_6(v_f_1862_, v_code_1869_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, lean_box(0));
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1884_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1884_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1884_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v_a_1874_);
v___x_1879_ = v___x_1871_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1881_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1879_);
v___x_1881_ = v___x_1876_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_del_object(v___x_1871_);
v_a_1885_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1873_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1873_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
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
}
else
{
lean_object* v___x_1894_; 
lean_dec_ref(v_f_1862_);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v_v_1863_);
return v___x_1894_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1862_ = stack[0].m_obj;
lean_object* v_v_1863_ = stack[1].m_obj;
lean_object* v___y_1864_ = stack[2].m_obj;
lean_object* v___y_1865_ = stack[3].m_obj;
lean_object* v___y_1866_ = stack[4].m_obj;
lean_object* v___y_1867_ = stack[5].m_obj;
lean_object* v_res_1895_;
v_res_1895_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v_f_1862_, v_v_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
stack->m_obj
 = v_res_1895_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg___boxed(lean_object* v_f_1896_, lean_object* v_v_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v_f_1896_, v_v_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
return v_res_1903_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0(uint8_t v_pu_1904_, lean_object* v_f_1905_, lean_object* v_v_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v_f_1905_, v_v_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
return v___x_1912_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1904_ = stack[0].m_num;
lean_object* v_f_1905_ = stack[1].m_obj;
lean_object* v_v_1906_ = stack[2].m_obj;
lean_object* v___y_1907_ = stack[3].m_obj;
lean_object* v___y_1908_ = stack[4].m_obj;
lean_object* v___y_1909_ = stack[5].m_obj;
lean_object* v___y_1910_ = stack[6].m_obj;
lean_object* v_res_1913_;
v_res_1913_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0(v_pu_1904_, v_f_1905_, v_v_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
stack->m_obj
 = v_res_1913_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___boxed(lean_object* v_pu_1914_, lean_object* v_f_1915_, lean_object* v_v_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
uint8_t v_pu_boxed_1922_; lean_object* v_res_1923_; 
v_pu_boxed_1922_ = lean_unbox(v_pu_1914_);
v_res_1923_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0(v_pu_boxed_1922_, v_f_1915_, v_v_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
return v_res_1923_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0(uint8_t v_shouldElimFunDecls_1924_, lean_object* v_x_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_Compiler_LCNF_Code_cse(v_shouldElimFunDecls_1924_, v_x_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
return v___x_1931_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_cse___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_shouldElimFunDecls_1924_ = stack[0].m_num;
lean_object* v_x_1925_ = stack[1].m_obj;
lean_object* v___y_1926_ = stack[2].m_obj;
lean_object* v___y_1927_ = stack[3].m_obj;
lean_object* v___y_1928_ = stack[4].m_obj;
lean_object* v___y_1929_ = stack[5].m_obj;
lean_object* v_res_1932_;
v_res_1932_ = l_Lean_Compiler_LCNF_Decl_cse___lam__0(v_shouldElimFunDecls_1924_, v_x_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
stack->m_obj
 = v_res_1932_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed(lean_object* v_shouldElimFunDecls_1933_, lean_object* v_x_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1940_; lean_object* v_res_1941_; 
v_shouldElimFunDecls_boxed_1940_ = lean_unbox(v_shouldElimFunDecls_1933_);
v_res_1941_ = l_Lean_Compiler_LCNF_Decl_cse___lam__0(v_shouldElimFunDecls_boxed_1940_, v_x_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
return v_res_1941_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_cse(uint8_t v_shouldElimFunDecls_1942_, lean_object* v_decl_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v_toSignature_1949_; lean_object* v_value_1950_; uint8_t v_recursive_1951_; lean_object* v_inlineAttr_x3f_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1978_; 
v_toSignature_1949_ = lean_ctor_get(v_decl_1943_, 0);
v_value_1950_ = lean_ctor_get(v_decl_1943_, 1);
v_recursive_1951_ = lean_ctor_get_uint8(v_decl_1943_, sizeof(void*)*3);
v_inlineAttr_x3f_1952_ = lean_ctor_get(v_decl_1943_, 2);
v_isSharedCheck_1978_ = !lean_is_exclusive(v_decl_1943_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1954_ = v_decl_1943_;
v_isShared_1955_ = v_isSharedCheck_1978_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_inlineAttr_x3f_1952_);
lean_inc(v_value_1950_);
lean_inc(v_toSignature_1949_);
lean_dec(v_decl_1943_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1978_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___f_1957_; lean_object* v___x_1958_; 
v___x_1956_ = lean_box(v_shouldElimFunDecls_1942_);
v___f_1957_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1957_, 0, v___x_1956_);
v___x_1958_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v___f_1957_, v_value_1950_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1969_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1969_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1969_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 1, v_a_1959_);
v___x_1964_ = v___x_1954_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_toSignature_1949_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_a_1959_);
lean_ctor_set(v_reuseFailAlloc_1968_, 2, v_inlineAttr_x3f_1952_);
lean_ctor_set_uint8(v_reuseFailAlloc_1968_, sizeof(void*)*3, v_recursive_1951_);
v___x_1964_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1966_; 
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1964_);
v___x_1966_ = v___x_1961_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_del_object(v___x_1954_);
lean_dec(v_inlineAttr_x3f_1952_);
lean_dec_ref(v_toSignature_1949_);
v_a_1970_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1958_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1958_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_cse_0interp(lean_interpreter_value* stack)
{
uint8_t v_shouldElimFunDecls_1942_ = stack[0].m_num;
lean_object* v_decl_1943_ = stack[1].m_obj;
lean_object* v_a_1944_ = stack[2].m_obj;
lean_object* v_a_1945_ = stack[3].m_obj;
lean_object* v_a_1946_ = stack[4].m_obj;
lean_object* v_a_1947_ = stack[5].m_obj;
lean_object* v_res_1979_;
v_res_1979_ = l_Lean_Compiler_LCNF_Decl_cse(v_shouldElimFunDecls_1942_, v_decl_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_);
stack->m_obj
 = v_res_1979_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___boxed(lean_object* v_shouldElimFunDecls_1980_, lean_object* v_decl_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1987_; lean_object* v_res_1988_; 
v_shouldElimFunDecls_boxed_1987_ = lean_unbox(v_shouldElimFunDecls_1980_);
v_res_1988_ = l_Lean_Compiler_LCNF_Decl_cse(v_shouldElimFunDecls_boxed_1987_, v_decl_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
return v_res_1988_;
}
}
lean_object* l_Lean_Compiler_LCNF_cse___lam__0(uint8_t v_shouldElimFunDecls_1992_, uint8_t v_phase_1993_, lean_object* v_occurrence_1994_, lean_object* v_h_1995_){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1996_ = ((lean_object*)(l_Lean_Compiler_LCNF_cse___lam__0___closed__1));
v___x_1997_ = lean_box(v_shouldElimFunDecls_1992_);
v___x_1998_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_cse___boxed), 7, 1);
lean_closure_set(v___x_1998_, 0, v___x_1997_);
v___x_1999_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1996_, v_phase_1993_, v___x_1998_, v_occurrence_1994_);
return v___x_1999_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_cse___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_shouldElimFunDecls_1992_ = stack[0].m_num;
uint8_t v_phase_1993_ = stack[1].m_num;
lean_object* v_occurrence_1994_ = stack[2].m_obj;
lean_object* v_res_2000_;
v_res_2000_ = l_Lean_Compiler_LCNF_cse___lam__0(v_shouldElimFunDecls_1992_, v_phase_1993_, v_occurrence_1994_, lean_box(0));
stack->m_obj
 = v_res_2000_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___lam__0___boxed(lean_object* v_shouldElimFunDecls_2001_, lean_object* v_phase_2002_, lean_object* v_occurrence_2003_, lean_object* v_h_2004_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_2005_; uint8_t v_phase_boxed_2006_; lean_object* v_res_2007_; 
v_shouldElimFunDecls_boxed_2005_ = lean_unbox(v_shouldElimFunDecls_2001_);
v_phase_boxed_2006_ = lean_unbox(v_phase_2002_);
v_res_2007_ = l_Lean_Compiler_LCNF_cse___lam__0(v_shouldElimFunDecls_boxed_2005_, v_phase_boxed_2006_, v_occurrence_2003_, v_h_2004_);
return v_res_2007_;
}
}
lean_object* l_Lean_Compiler_LCNF_cse(uint8_t v_phase_2008_, uint8_t v_shouldElimFunDecls_2009_, lean_object* v_occurrence_2010_){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___f_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; lean_object* v___x_2016_; 
v___x_2011_ = lean_box(v_shouldElimFunDecls_2009_);
v___x_2012_ = lean_box(v_phase_2008_);
v___f_2013_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_cse___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2013_, 0, v___x_2011_);
lean_closure_set(v___f_2013_, 1, v___x_2012_);
lean_closure_set(v___f_2013_, 2, v_occurrence_2010_);
v___x_2014_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_2015_ = 0;
v___x_2016_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_2014_, v_phase_2008_, v___x_2015_, v___f_2013_);
return v___x_2016_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_cse_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_2008_ = stack[0].m_num;
uint8_t v_shouldElimFunDecls_2009_ = stack[1].m_num;
lean_object* v_occurrence_2010_ = stack[2].m_obj;
lean_object* v_res_2017_;
v_res_2017_ = l_Lean_Compiler_LCNF_cse(v_phase_2008_, v_shouldElimFunDecls_2009_, v_occurrence_2010_);
stack->m_obj
 = v_res_2017_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___boxed(lean_object* v_phase_2018_, lean_object* v_shouldElimFunDecls_2019_, lean_object* v_occurrence_2020_){
_start:
{
uint8_t v_phase_boxed_2021_; uint8_t v_shouldElimFunDecls_boxed_2022_; lean_object* v_res_2023_; 
v_phase_boxed_2021_ = lean_unbox(v_phase_2018_);
v_shouldElimFunDecls_boxed_2022_ = lean_unbox(v_shouldElimFunDecls_2019_);
v_res_2023_ = l_Lean_Compiler_LCNF_cse(v_phase_boxed_2021_, v_shouldElimFunDecls_boxed_2022_, v_occurrence_2020_);
return v_res_2023_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2094_; uint8_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2094_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_));
v___x_2095_ = 1;
v___x_2096_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_));
v___x_2097_ = l_Lean_registerTraceClass(v___x_2094_, v___x_2095_, v___x_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2098_;
v_res_2098_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2098_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2____boxed(lean_object* v_a_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_();
return v_res_2100_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_NeverExtractAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_CSE(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
