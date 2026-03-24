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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_49_; lean_object* v_toApplicative_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_110_; 
v___x_49_ = lean_obj_once(&l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1, &l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1_once, _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1);
v_toApplicative_50_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_110_ == 0)
{
lean_object* v_unused_111_; 
v_unused_111_ = lean_ctor_get(v___x_49_, 1);
lean_dec(v_unused_111_);
v___x_52_ = v___x_49_;
v_isShared_53_ = v_isSharedCheck_110_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_toApplicative_50_);
lean_dec(v___x_49_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_110_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v_toFunctor_54_; lean_object* v_toSeq_55_; lean_object* v_toSeqLeft_56_; lean_object* v_toSeqRight_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_108_; 
v_toFunctor_54_ = lean_ctor_get(v_toApplicative_50_, 0);
v_toSeq_55_ = lean_ctor_get(v_toApplicative_50_, 2);
v_toSeqLeft_56_ = lean_ctor_get(v_toApplicative_50_, 3);
v_toSeqRight_57_ = lean_ctor_get(v_toApplicative_50_, 4);
v_isSharedCheck_108_ = !lean_is_exclusive(v_toApplicative_50_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; 
v_unused_109_ = lean_ctor_get(v_toApplicative_50_, 1);
lean_dec(v_unused_109_);
v___x_59_ = v_toApplicative_50_;
v_isShared_60_ = v_isSharedCheck_108_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_toSeqRight_57_);
lean_inc(v_toSeqLeft_56_);
lean_inc(v_toSeq_55_);
lean_inc(v_toFunctor_54_);
lean_dec(v_toApplicative_50_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_108_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___f_61_; lean_object* v___f_62_; lean_object* v___f_63_; lean_object* v___f_64_; lean_object* v___x_65_; lean_object* v___f_66_; lean_object* v___f_67_; lean_object* v___f_68_; lean_object* v___x_70_; 
v___f_61_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__2));
v___f_62_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__3));
lean_inc_ref(v_toFunctor_54_);
v___f_63_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_63_, 0, v_toFunctor_54_);
v___f_64_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_64_, 0, v_toFunctor_54_);
v___x_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_65_, 0, v___f_63_);
lean_ctor_set(v___x_65_, 1, v___f_64_);
v___f_66_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_66_, 0, v_toSeqRight_57_);
v___f_67_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_67_, 0, v_toSeqLeft_56_);
v___f_68_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_68_, 0, v_toSeq_55_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 4, v___f_66_);
lean_ctor_set(v___x_59_, 3, v___f_67_);
lean_ctor_set(v___x_59_, 2, v___f_68_);
lean_ctor_set(v___x_59_, 1, v___f_61_);
lean_ctor_set(v___x_59_, 0, v___x_65_);
v___x_70_ = v___x_59_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_65_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v___f_61_);
lean_ctor_set(v_reuseFailAlloc_107_, 2, v___f_68_);
lean_ctor_set(v_reuseFailAlloc_107_, 3, v___f_67_);
lean_ctor_set(v_reuseFailAlloc_107_, 4, v___f_66_);
v___x_70_ = v_reuseFailAlloc_107_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_72_; 
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 1, v___f_62_);
lean_ctor_set(v___x_52_, 0, v___x_70_);
v___x_72_ = v___x_52_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_70_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___f_62_);
v___x_72_ = v_reuseFailAlloc_106_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; lean_object* v_toApplicative_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_104_; 
v___x_73_ = l_StateRefT_x27_instMonad___redArg(v___x_72_);
v_toApplicative_74_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v___x_73_, 1);
lean_dec(v_unused_105_);
v___x_76_ = v___x_73_;
v_isShared_77_ = v_isSharedCheck_104_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_toApplicative_74_);
lean_dec(v___x_73_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_104_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v_toFunctor_78_; lean_object* v_toSeq_79_; lean_object* v_toSeqLeft_80_; lean_object* v_toSeqRight_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_102_; 
v_toFunctor_78_ = lean_ctor_get(v_toApplicative_74_, 0);
v_toSeq_79_ = lean_ctor_get(v_toApplicative_74_, 2);
v_toSeqLeft_80_ = lean_ctor_get(v_toApplicative_74_, 3);
v_toSeqRight_81_ = lean_ctor_get(v_toApplicative_74_, 4);
v_isSharedCheck_102_ = !lean_is_exclusive(v_toApplicative_74_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; 
v_unused_103_ = lean_ctor_get(v_toApplicative_74_, 1);
lean_dec(v_unused_103_);
v___x_83_ = v_toApplicative_74_;
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_toSeqRight_81_);
lean_inc(v_toSeqLeft_80_);
lean_inc(v_toSeq_79_);
lean_inc(v_toFunctor_78_);
lean_dec(v_toApplicative_74_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___f_85_; lean_object* v___f_86_; lean_object* v___f_87_; lean_object* v___f_88_; lean_object* v___f_89_; lean_object* v___x_90_; lean_object* v___f_91_; lean_object* v___f_92_; lean_object* v___f_93_; lean_object* v___x_95_; 
v___f_85_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__4));
v___f_86_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__5));
v___f_87_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__6));
lean_inc_ref(v_toFunctor_78_);
v___f_88_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_88_, 0, v_toFunctor_78_);
v___f_89_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_89_, 0, v_toFunctor_78_);
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v___f_88_);
lean_ctor_set(v___x_90_, 1, v___f_89_);
v___f_91_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_91_, 0, v_toSeqRight_81_);
v___f_92_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_92_, 0, v_toSeqLeft_80_);
v___f_93_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_93_, 0, v_toSeq_79_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 4, v___f_91_);
lean_ctor_set(v___x_83_, 3, v___f_92_);
lean_ctor_set(v___x_83_, 2, v___f_93_);
lean_ctor_set(v___x_83_, 1, v___f_86_);
lean_ctor_set(v___x_83_, 0, v___x_90_);
v___x_95_ = v___x_83_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_90_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v___f_86_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v___f_93_);
lean_ctor_set(v_reuseFailAlloc_101_, 3, v___f_92_);
lean_ctor_set(v_reuseFailAlloc_101_, 4, v___f_91_);
v___x_95_ = v_reuseFailAlloc_101_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_97_; 
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 1, v___f_87_);
lean_ctor_set(v___x_76_, 0, v___x_95_);
v___x_97_ = v___x_76_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_95_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v___f_87_);
v___x_97_ = v_reuseFailAlloc_100_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__18));
v___x_99_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_99_, 0, lean_box(0));
lean_closure_set(v___x_99_, 1, lean_box(0));
lean_closure_set(v___x_99_, 2, lean_box(0));
lean_closure_set(v___x_99_, 3, v___x_97_);
lean_closure_set(v___x_99_, 4, lean_box(0));
lean_closure_set(v___x_99_, 5, lean_box(0));
lean_closure_set(v___x_99_, 6, v___x_98_);
lean_closure_set(v___x_99_, 7, v___f_85_);
return v___x_99_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0(lean_object* v_f_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v___x_119_; lean_object* v_map_120_; lean_object* v_subst_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_132_; 
v___x_119_ = lean_st_ref_take(v___y_113_);
v_map_120_ = lean_ctor_get(v___x_119_, 0);
v_subst_121_ = lean_ctor_get(v___x_119_, 1);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_132_ == 0)
{
v___x_123_ = v___x_119_;
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_subst_121_);
lean_inc(v_map_120_);
lean_dec(v___x_119_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = lean_apply_1(v_f_112_, v_subst_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_map_120_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v___x_125_);
v___x_127_ = v_reuseFailAlloc_131_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_st_ref_set(v___y_113_, v___x_127_);
v___x_129_ = lean_box(0);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0___boxed(lean_object* v_f_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0(v_f_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___redArg(lean_object* v_a_143_){
_start:
{
lean_object* v___x_145_; lean_object* v_subst_146_; lean_object* v___x_147_; 
v___x_145_ = lean_st_ref_get(v_a_143_);
v_subst_146_ = lean_ctor_get(v___x_145_, 1);
lean_inc_ref(v_subst_146_);
lean_dec(v___x_145_);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v_subst_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___redArg___boxed(lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Compiler_LCNF_CSE_getSubst___redArg(v_a_148_);
lean_dec(v_a_148_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst(lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___x_157_; lean_object* v_subst_158_; lean_object* v___x_159_; 
v___x_157_ = lean_st_ref_get(v_a_151_);
v_subst_158_ = lean_ctor_get(v___x_157_, 1);
lean_inc_ref(v_subst_158_);
lean_dec(v___x_157_);
v___x_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_159_, 0, v_subst_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___boxed(lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Compiler_LCNF_CSE_getSubst(v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec(v_a_160_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg(lean_object* v_value_169_, lean_object* v_fvarId_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_173_; lean_object* v_map_174_; lean_object* v_subst_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_188_; 
v___x_173_ = lean_st_ref_take(v_a_171_);
v_map_174_ = lean_ctor_get(v___x_173_, 0);
v_subst_175_ = lean_ctor_get(v___x_173_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_188_ == 0)
{
v___x_177_ = v___x_173_;
v_isShared_178_ = v_isSharedCheck_188_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_subst_175_);
lean_inc(v_map_174_);
lean_dec(v___x_173_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_188_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_179_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0));
v___x_180_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1));
v___x_181_ = l_Lean_PersistentHashMap_insert___redArg(v___x_179_, v___x_180_, v_map_174_, v_value_169_, v_fvarId_170_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_181_);
v___x_183_ = v___x_177_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_subst_175_);
v___x_183_ = v_reuseFailAlloc_187_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_st_ref_set(v_a_171_, v___x_183_);
v___x_185_ = lean_box(0);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___redArg___boxed(lean_object* v_value_189_, lean_object* v_fvarId_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Compiler_LCNF_CSE_addEntry___redArg(v_value_189_, v_fvarId_190_, v_a_191_);
lean_dec(v_a_191_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry(lean_object* v_value_194_, lean_object* v_fvarId_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_202_; lean_object* v_map_203_; lean_object* v_subst_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_217_; 
v___x_202_ = lean_st_ref_take(v_a_196_);
v_map_203_ = lean_ctor_get(v___x_202_, 0);
v_subst_204_ = lean_ctor_get(v___x_202_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_217_ == 0)
{
v___x_206_ = v___x_202_;
v_isShared_207_ = v_isSharedCheck_217_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_subst_204_);
lean_inc(v_map_203_);
lean_dec(v___x_202_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_217_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_208_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0));
v___x_209_ = ((lean_object*)(l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1));
v___x_210_ = l_Lean_PersistentHashMap_insert___redArg(v___x_208_, v___x_209_, v_map_203_, v_value_194_, v_fvarId_195_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_210_);
v___x_212_ = v___x_206_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_subst_204_);
v___x_212_ = v_reuseFailAlloc_216_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = lean_st_ref_set(v_a_196_, v___x_212_);
v___x_214_ = lean_box(0);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___boxed(lean_object* v_value_218_, lean_object* v_fvarId_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Compiler_LCNF_CSE_addEntry(v_value_218_, v_fvarId_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_a_220_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(lean_object* v_a_227_, lean_object* v_map_228_, lean_object* v_a_x3f_229_){
_start:
{
lean_object* v___x_231_; lean_object* v_subst_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_242_; 
v___x_231_ = lean_st_ref_take(v_a_227_);
v_subst_232_ = lean_ctor_get(v___x_231_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_242_ == 0)
{
lean_object* v_unused_243_; 
v_unused_243_ = lean_ctor_get(v___x_231_, 0);
lean_dec(v_unused_243_);
v___x_234_ = v___x_231_;
v_isShared_235_ = v_isSharedCheck_242_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_subst_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_242_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v_map_228_);
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_map_228_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_subst_232_);
v___x_237_ = v_reuseFailAlloc_241_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_st_ref_set(v_a_227_, v___x_237_);
v___x_239_ = lean_box(0);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0___boxed(lean_object* v_a_244_, lean_object* v_map_245_, lean_object* v_a_x3f_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(v_a_244_, v_map_245_, v_a_x3f_246_);
lean_dec(v_a_x3f_246_);
lean_dec(v_a_244_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg(lean_object* v_x_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v___x_256_; lean_object* v_map_257_; lean_object* v_r_258_; 
v___x_256_ = lean_st_ref_get(v_a_250_);
v_map_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc_ref(v_map_257_);
lean_dec(v___x_256_);
lean_inc(v_a_254_);
lean_inc_ref(v_a_253_);
lean_inc(v_a_252_);
lean_inc_ref(v_a_251_);
lean_inc(v_a_250_);
v_r_258_ = lean_apply_6(v_x_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, lean_box(0));
if (lean_obj_tag(v_r_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_275_; 
v_a_259_ = lean_ctor_get(v_r_258_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v_r_258_);
if (v_isSharedCheck_275_ == 0)
{
v___x_261_ = v_r_258_;
v_isShared_262_ = v_isSharedCheck_275_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v_r_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_275_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
lean_inc(v_a_259_);
if (v_isShared_262_ == 0)
{
lean_ctor_set_tag(v___x_261_, 1);
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_274_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
v___x_265_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(v_a_250_, v_map_257_, v___x_264_);
lean_dec_ref(v___x_264_);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; 
v_unused_273_ = lean_ctor_get(v___x_265_, 0);
lean_dec(v_unused_273_);
v___x_267_ = v___x_265_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_dec(v___x_265_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v_a_259_);
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_259_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
v_a_276_ = lean_ctor_get(v_r_258_, 0);
lean_inc(v_a_276_);
lean_dec_ref(v_r_258_);
v___x_277_ = lean_box(0);
v___x_278_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(v_a_250_, v_map_257_, v___x_277_);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; 
v_unused_286_ = lean_ctor_get(v___x_278_, 0);
lean_dec(v_unused_286_);
v___x_280_ = v___x_278_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_dec(v___x_278_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set_tag(v___x_280_, 1);
lean_ctor_set(v___x_280_, 0, v_a_276_);
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_276_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___boxed(lean_object* v_x_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg(v_x_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope(lean_object* v_00_u03b1_295_, lean_object* v_x_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_303_; lean_object* v_map_304_; lean_object* v_r_305_; 
v___x_303_ = lean_st_ref_get(v_a_297_);
v_map_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc_ref(v_map_304_);
lean_dec(v___x_303_);
lean_inc(v_a_301_);
lean_inc_ref(v_a_300_);
lean_inc(v_a_299_);
lean_inc_ref(v_a_298_);
lean_inc(v_a_297_);
v_r_305_ = lean_apply_6(v_x_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, lean_box(0));
if (lean_obj_tag(v_r_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_322_; 
v_a_306_ = lean_ctor_get(v_r_305_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v_r_305_);
if (v_isSharedCheck_322_ == 0)
{
v___x_308_ = v_r_305_;
v_isShared_309_ = v_isSharedCheck_322_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v_r_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_322_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
lean_inc(v_a_306_);
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 1);
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_321_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
v___x_312_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(v_a_297_, v_map_304_, v___x_311_);
lean_dec_ref(v___x_311_);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; 
v_unused_320_ = lean_ctor_get(v___x_312_, 0);
lean_dec(v_unused_320_);
v___x_314_ = v___x_312_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_dec(v___x_312_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v_a_306_);
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_306_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
v_a_323_ = lean_ctor_get(v_r_305_, 0);
lean_inc(v_a_323_);
lean_dec_ref(v_r_305_);
v___x_324_ = lean_box(0);
v___x_325_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(v_a_297_, v_map_304_, v___x_324_);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; 
v_unused_333_ = lean_ctor_get(v___x_325_, 0);
lean_dec(v_unused_333_);
v___x_327_ = v___x_325_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_dec(v___x_325_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 1);
lean_ctor_set(v___x_327_, 0, v_a_323_);
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_323_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___boxed(lean_object* v_00_u03b1_334_, lean_object* v_x_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Compiler_LCNF_CSE_withNewScope(v_00_u03b1_334_, v_x_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
if (lean_obj_tag(v_x_344_) == 0)
{
return v_x_343_;
}
else
{
lean_object* v_key_345_; lean_object* v_value_346_; lean_object* v_tail_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_370_; 
v_key_345_ = lean_ctor_get(v_x_344_, 0);
v_value_346_ = lean_ctor_get(v_x_344_, 1);
v_tail_347_ = lean_ctor_get(v_x_344_, 2);
v_isSharedCheck_370_ = !lean_is_exclusive(v_x_344_);
if (v_isSharedCheck_370_ == 0)
{
v___x_349_ = v_x_344_;
v_isShared_350_ = v_isSharedCheck_370_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_tail_347_);
lean_inc(v_value_346_);
lean_inc(v_key_345_);
lean_dec(v_x_344_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_370_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; uint64_t v___x_352_; uint64_t v___x_353_; uint64_t v___x_354_; uint64_t v_fold_355_; uint64_t v___x_356_; uint64_t v___x_357_; uint64_t v___x_358_; size_t v___x_359_; size_t v___x_360_; size_t v___x_361_; size_t v___x_362_; size_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_351_ = lean_array_get_size(v_x_343_);
v___x_352_ = l_Lean_instHashableFVarId_hash(v_key_345_);
v___x_353_ = 32ULL;
v___x_354_ = lean_uint64_shift_right(v___x_352_, v___x_353_);
v_fold_355_ = lean_uint64_xor(v___x_352_, v___x_354_);
v___x_356_ = 16ULL;
v___x_357_ = lean_uint64_shift_right(v_fold_355_, v___x_356_);
v___x_358_ = lean_uint64_xor(v_fold_355_, v___x_357_);
v___x_359_ = lean_uint64_to_usize(v___x_358_);
v___x_360_ = lean_usize_of_nat(v___x_351_);
v___x_361_ = ((size_t)1ULL);
v___x_362_ = lean_usize_sub(v___x_360_, v___x_361_);
v___x_363_ = lean_usize_land(v___x_359_, v___x_362_);
v___x_364_ = lean_array_uget_borrowed(v_x_343_, v___x_363_);
lean_inc(v___x_364_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 2, v___x_364_);
v___x_366_ = v___x_349_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_key_345_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_value_346_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v___x_364_);
v___x_366_ = v_reuseFailAlloc_369_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; 
v___x_367_ = lean_array_uset(v_x_343_, v___x_363_, v___x_366_);
v_x_343_ = v___x_367_;
v_x_344_ = v_tail_347_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2___redArg(lean_object* v_i_371_, lean_object* v_source_372_, lean_object* v_target_373_){
_start:
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = lean_array_get_size(v_source_372_);
v___x_375_ = lean_nat_dec_lt(v_i_371_, v___x_374_);
if (v___x_375_ == 0)
{
lean_dec_ref(v_source_372_);
lean_dec(v_i_371_);
return v_target_373_;
}
else
{
lean_object* v_es_376_; lean_object* v___x_377_; lean_object* v_source_378_; lean_object* v_target_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_es_376_ = lean_array_fget(v_source_372_, v_i_371_);
v___x_377_ = lean_box(0);
v_source_378_ = lean_array_fset(v_source_372_, v_i_371_, v___x_377_);
v_target_379_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3___redArg(v_target_373_, v_es_376_);
v___x_380_ = lean_unsigned_to_nat(1u);
v___x_381_ = lean_nat_add(v_i_371_, v___x_380_);
lean_dec(v_i_371_);
v_i_371_ = v___x_381_;
v_source_372_ = v_source_378_;
v_target_373_ = v_target_379_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1___redArg(lean_object* v_data_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v_nbuckets_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_384_ = lean_array_get_size(v_data_383_);
v___x_385_ = lean_unsigned_to_nat(2u);
v_nbuckets_386_ = lean_nat_mul(v___x_384_, v___x_385_);
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = lean_box(0);
v___x_389_ = lean_mk_array(v_nbuckets_386_, v___x_388_);
v___x_390_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2___redArg(v___x_387_, v_data_383_, v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(lean_object* v_a_391_, lean_object* v_b_392_, lean_object* v_x_393_){
_start:
{
if (lean_obj_tag(v_x_393_) == 0)
{
lean_dec(v_b_392_);
lean_dec(v_a_391_);
return v_x_393_;
}
else
{
lean_object* v_key_394_; lean_object* v_value_395_; lean_object* v_tail_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_408_; 
v_key_394_ = lean_ctor_get(v_x_393_, 0);
v_value_395_ = lean_ctor_get(v_x_393_, 1);
v_tail_396_ = lean_ctor_get(v_x_393_, 2);
v_isSharedCheck_408_ = !lean_is_exclusive(v_x_393_);
if (v_isSharedCheck_408_ == 0)
{
v___x_398_ = v_x_393_;
v_isShared_399_ = v_isSharedCheck_408_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_tail_396_);
lean_inc(v_value_395_);
lean_inc(v_key_394_);
lean_dec(v_x_393_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_408_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
uint8_t v___x_400_; 
v___x_400_ = l_Lean_instBEqFVarId_beq(v_key_394_, v_a_391_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(v_a_391_, v_b_392_, v_tail_396_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 2, v___x_401_);
v___x_403_ = v___x_398_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_key_394_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_value_395_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
else
{
lean_object* v___x_406_; 
lean_dec(v_value_395_);
lean_dec(v_key_394_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 1, v_b_392_);
lean_ctor_set(v___x_398_, 0, v_a_391_);
v___x_406_ = v___x_398_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_391_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_b_392_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_tail_396_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(lean_object* v_a_409_, lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
uint8_t v___x_411_; 
v___x_411_ = 0;
return v___x_411_;
}
else
{
lean_object* v_key_412_; lean_object* v_tail_413_; uint8_t v___x_414_; 
v_key_412_ = lean_ctor_get(v_x_410_, 0);
v_tail_413_ = lean_ctor_get(v_x_410_, 2);
v___x_414_ = l_Lean_instBEqFVarId_beq(v_key_412_, v_a_409_);
if (v___x_414_ == 0)
{
v_x_410_ = v_tail_413_;
goto _start;
}
else
{
return v___x_414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg___boxed(lean_object* v_a_416_, lean_object* v_x_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(v_a_416_, v_x_417_);
lean_dec(v_x_417_);
lean_dec(v_a_416_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(lean_object* v_m_420_, lean_object* v_a_421_, lean_object* v_b_422_){
_start:
{
lean_object* v_size_423_; lean_object* v_buckets_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_467_; 
v_size_423_ = lean_ctor_get(v_m_420_, 0);
v_buckets_424_ = lean_ctor_get(v_m_420_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_m_420_);
if (v_isSharedCheck_467_ == 0)
{
v___x_426_ = v_m_420_;
v_isShared_427_ = v_isSharedCheck_467_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_buckets_424_);
lean_inc(v_size_423_);
lean_dec(v_m_420_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_467_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; uint64_t v___x_431_; uint64_t v_fold_432_; uint64_t v___x_433_; uint64_t v___x_434_; uint64_t v___x_435_; size_t v___x_436_; size_t v___x_437_; size_t v___x_438_; size_t v___x_439_; size_t v___x_440_; lean_object* v_bkt_441_; uint8_t v___x_442_; 
v___x_428_ = lean_array_get_size(v_buckets_424_);
v___x_429_ = l_Lean_instHashableFVarId_hash(v_a_421_);
v___x_430_ = 32ULL;
v___x_431_ = lean_uint64_shift_right(v___x_429_, v___x_430_);
v_fold_432_ = lean_uint64_xor(v___x_429_, v___x_431_);
v___x_433_ = 16ULL;
v___x_434_ = lean_uint64_shift_right(v_fold_432_, v___x_433_);
v___x_435_ = lean_uint64_xor(v_fold_432_, v___x_434_);
v___x_436_ = lean_uint64_to_usize(v___x_435_);
v___x_437_ = lean_usize_of_nat(v___x_428_);
v___x_438_ = ((size_t)1ULL);
v___x_439_ = lean_usize_sub(v___x_437_, v___x_438_);
v___x_440_ = lean_usize_land(v___x_436_, v___x_439_);
v_bkt_441_ = lean_array_uget_borrowed(v_buckets_424_, v___x_440_);
v___x_442_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(v_a_421_, v_bkt_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v_size_x27_444_; lean_object* v___x_445_; lean_object* v_buckets_x27_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_443_ = lean_unsigned_to_nat(1u);
v_size_x27_444_ = lean_nat_add(v_size_423_, v___x_443_);
lean_dec(v_size_423_);
lean_inc(v_bkt_441_);
v___x_445_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_445_, 0, v_a_421_);
lean_ctor_set(v___x_445_, 1, v_b_422_);
lean_ctor_set(v___x_445_, 2, v_bkt_441_);
v_buckets_x27_446_ = lean_array_uset(v_buckets_424_, v___x_440_, v___x_445_);
v___x_447_ = lean_unsigned_to_nat(4u);
v___x_448_ = lean_nat_mul(v_size_x27_444_, v___x_447_);
v___x_449_ = lean_unsigned_to_nat(3u);
v___x_450_ = lean_nat_div(v___x_448_, v___x_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_array_get_size(v_buckets_x27_446_);
v___x_452_ = lean_nat_dec_le(v___x_450_, v___x_451_);
lean_dec(v___x_450_);
if (v___x_452_ == 0)
{
lean_object* v_val_453_; lean_object* v___x_455_; 
v_val_453_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1___redArg(v_buckets_x27_446_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v_val_453_);
lean_ctor_set(v___x_426_, 0, v_size_x27_444_);
v___x_455_ = v___x_426_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_size_x27_444_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_val_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
else
{
lean_object* v___x_458_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v_buckets_x27_446_);
lean_ctor_set(v___x_426_, 0, v_size_x27_444_);
v___x_458_ = v___x_426_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_size_x27_444_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_buckets_x27_446_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
else
{
lean_object* v___x_460_; lean_object* v_buckets_x27_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
lean_inc(v_bkt_441_);
v___x_460_ = lean_box(0);
v_buckets_x27_461_ = lean_array_uset(v_buckets_424_, v___x_440_, v___x_460_);
v___x_462_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(v_a_421_, v_b_422_, v_bkt_441_);
v___x_463_ = lean_array_uset(v_buckets_x27_461_, v___x_440_, v___x_462_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v___x_463_);
v___x_465_ = v___x_426_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_size_423_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(lean_object* v_decl_468_, lean_object* v_fvarId_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
uint8_t v___x_473_; lean_object* v___x_474_; 
v___x_473_ = 0;
v___x_474_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_473_, v_decl_468_, v_a_471_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_496_; 
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; 
v_unused_497_ = lean_ctor_get(v___x_474_, 0);
lean_dec(v_unused_497_);
v___x_476_ = v___x_474_;
v_isShared_477_ = v_isSharedCheck_496_;
goto v_resetjp_475_;
}
else
{
lean_dec(v___x_474_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_496_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v_fvarId_479_; lean_object* v_map_480_; lean_object* v_subst_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_495_; 
v___x_478_ = lean_st_ref_take(v_a_470_);
v_fvarId_479_ = lean_ctor_get(v_decl_468_, 0);
lean_inc(v_fvarId_479_);
lean_dec_ref(v_decl_468_);
v_map_480_ = lean_ctor_get(v___x_478_, 0);
v_subst_481_ = lean_ctor_get(v___x_478_, 1);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_495_ == 0)
{
v___x_483_ = v___x_478_;
v_isShared_484_ = v_isSharedCheck_495_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_subst_481_);
lean_inc(v_map_480_);
lean_dec(v___x_478_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_495_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_485_, 0, v_fvarId_469_);
v___x_486_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(v_subst_481_, v_fvarId_479_, v___x_485_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v___x_486_);
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_map_480_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_486_);
v___x_488_ = v_reuseFailAlloc_494_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_489_ = lean_st_ref_set(v_a_470_, v___x_488_);
v___x_490_ = lean_box(0);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_490_);
v___x_492_ = v___x_476_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_469_);
lean_dec_ref(v_decl_468_);
return v___x_474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg___boxed(lean_object* v_decl_498_, lean_object* v_fvarId_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(v_decl_498_, v_fvarId_499_, v_a_500_, v_a_501_);
lean_dec(v_a_501_);
lean_dec(v_a_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet(lean_object* v_decl_504_, lean_object* v_fvarId_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(v_decl_504_, v_fvarId_505_, v_a_506_, v_a_508_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___boxed(lean_object* v_decl_513_, lean_object* v_fvarId_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Compiler_LCNF_CSE_replaceLet(v_decl_513_, v_fvarId_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0(lean_object* v_00_u03b2_522_, lean_object* v_m_523_, lean_object* v_a_524_, lean_object* v_b_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(v_m_523_, v_a_524_, v_b_525_);
return v___x_526_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0(lean_object* v_00_u03b2_527_, lean_object* v_a_528_, lean_object* v_x_529_){
_start:
{
uint8_t v___x_530_; 
v___x_530_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(v_a_528_, v_x_529_);
return v___x_530_;
}
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(lean_object* v_decl_553_, lean_object* v_fvarId_554_, lean_object* v_a_555_, lean_object* v_a_556_){
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
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_571_, 0, v_fvarId_554_);
v___x_572_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(v_subst_567_, v_fvarId_564_, v___x_571_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 1, v___x_572_);
v___x_574_ = v___x_569_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_map_566_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___x_572_);
v___x_574_ = v_reuseFailAlloc_580_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_575_ = lean_st_ref_set(v_a_555_, v___x_574_);
v___x_576_ = lean_box(0);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_576_);
v___x_578_ = v___x_562_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg___boxed(lean_object* v_decl_584_, lean_object* v_fvarId_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(v_decl_584_, v_fvarId_585_, v_a_586_, v_a_587_);
lean_dec(v_a_587_);
lean_dec(v_a_586_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun(lean_object* v_decl_590_, lean_object* v_fvarId_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(v_decl_590_, v_fvarId_591_, v_a_592_, v_a_594_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___boxed(lean_object* v_decl_599_, lean_object* v_fvarId_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_Compiler_LCNF_CSE_replaceFun(v_decl_599_, v_fvarId_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(lean_object* v_v_608_, lean_object* v_a_609_){
_start:
{
switch(lean_obj_tag(v_v_608_))
{
case 0:
{
lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_619_; 
v_isSharedCheck_619_ = !lean_is_exclusive(v_v_608_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v_v_608_, 0);
lean_dec(v_unused_620_);
v___x_612_ = v_v_608_;
v_isShared_613_ = v_isSharedCheck_619_;
goto v_resetjp_611_;
}
else
{
lean_dec(v_v_608_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_619_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
uint8_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_614_ = 0;
v___x_615_ = lean_box(v___x_614_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_615_);
v___x_617_ = v___x_612_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
case 3:
{
lean_object* v_declName_621_; lean_object* v___x_622_; lean_object* v_env_623_; uint8_t v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_declName_621_ = lean_ctor_get(v_v_608_, 0);
lean_inc(v_declName_621_);
lean_dec_ref(v_v_608_);
v___x_622_ = lean_st_ref_get(v_a_609_);
v_env_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc_ref(v_env_623_);
lean_dec(v___x_622_);
v___x_624_ = l_Lean_hasNeverExtractAttribute(v_env_623_, v_declName_621_);
v___x_625_ = lean_box(v___x_624_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
default: 
{
uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec(v_v_608_);
v___x_627_ = 0;
v___x_628_ = lean_box(v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg___boxed(lean_object* v_v_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(v_v_630_, v_a_631_);
lean_dec(v_a_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract(lean_object* v_v_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(v_v_634_, v_a_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___boxed(lean_object* v_v_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract(v_v_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(lean_object* v_a_648_, lean_object* v_map_649_, lean_object* v_a_x3f_650_){
_start:
{
lean_object* v___x_652_; lean_object* v_subst_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_663_; 
v___x_652_ = lean_st_ref_take(v_a_648_);
v_subst_653_ = lean_ctor_get(v___x_652_, 1);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v___x_652_, 0);
lean_dec(v_unused_664_);
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_663_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_subst_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_663_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v_map_649_);
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_map_649_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_subst_653_);
v___x_658_ = v_reuseFailAlloc_662_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = lean_st_ref_set(v_a_648_, v___x_658_);
v___x_660_ = lean_box(0);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0___boxed(lean_object* v_a_665_, lean_object* v_map_666_, lean_object* v_a_x3f_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(v_a_665_, v_map_666_, v_a_x3f_667_);
lean_dec(v_a_x3f_667_);
lean_dec(v_a_665_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(uint8_t v_pu_670_, uint8_t v_t_671_, lean_object* v_args_672_, lean_object* v___y_673_){
_start:
{
lean_object* v___x_675_; lean_object* v_subst_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_675_ = lean_st_ref_get(v___y_673_);
v_subst_676_ = lean_ctor_get(v___x_675_, 1);
lean_inc_ref(v_subst_676_);
lean_dec(v___x_675_);
v___x_677_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_670_, v_subst_676_, v_args_672_, v_t_671_);
lean_dec_ref(v_subst_676_);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg___boxed(lean_object* v_pu_679_, lean_object* v_t_680_, lean_object* v_args_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
uint8_t v_pu_boxed_684_; uint8_t v_t_boxed_685_; lean_object* v_res_686_; 
v_pu_boxed_684_ = lean_unbox(v_pu_679_);
v_t_boxed_685_ = lean_unbox(v_t_680_);
v_res_686_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v_pu_boxed_684_, v_t_boxed_685_, v_args_681_, v___y_682_);
lean_dec(v___y_682_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(uint8_t v_pu_687_, uint8_t v_t_688_, lean_object* v_decl_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v_type_693_; lean_object* v_value_694_; lean_object* v___x_695_; lean_object* v_subst_696_; lean_object* v___x_697_; lean_object* v_subst_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v_type_693_ = lean_ctor_get(v_decl_689_, 2);
v_value_694_ = lean_ctor_get(v_decl_689_, 3);
v___x_695_ = lean_st_ref_get(v___y_690_);
v_subst_696_ = lean_ctor_get(v___x_695_, 1);
lean_inc_ref(v_subst_696_);
lean_dec(v___x_695_);
v___x_697_ = lean_st_ref_get(v___y_690_);
v_subst_698_ = lean_ctor_get(v___x_697_, 1);
lean_inc_ref(v_subst_698_);
lean_dec(v___x_697_);
lean_inc_ref(v_type_693_);
v___x_699_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_687_, v_subst_696_, v_t_688_, v_type_693_);
lean_dec_ref(v_subst_696_);
lean_inc(v_value_694_);
v___x_700_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_687_, v_subst_698_, v_value_694_, v_t_688_);
lean_dec_ref(v_subst_698_);
v___x_701_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_687_, v_decl_689_, v___x_699_, v___x_700_, v___y_691_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg___boxed(lean_object* v_pu_702_, lean_object* v_t_703_, lean_object* v_decl_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
uint8_t v_pu_boxed_708_; uint8_t v_t_boxed_709_; lean_object* v_res_710_; 
v_pu_boxed_708_ = lean_unbox(v_pu_702_);
v_t_boxed_709_ = lean_unbox(v_t_703_);
v_res_710_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v_pu_boxed_708_, v_t_boxed_709_, v_decl_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec(v___y_705_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(lean_object* v___y_711_, lean_object* v_map_712_, lean_object* v_a_x3f_713_){
_start:
{
lean_object* v___x_715_; lean_object* v_subst_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_726_; 
v___x_715_ = lean_st_ref_take(v___y_711_);
v_subst_716_ = lean_ctor_get(v___x_715_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v___x_715_, 0);
lean_dec(v_unused_727_);
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_726_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_subst_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_726_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v_map_712_);
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_map_712_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_subst_716_);
v___x_721_ = v_reuseFailAlloc_725_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_722_ = lean_st_ref_set(v___y_711_, v___x_721_);
v___x_723_ = lean_box(0);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0___boxed(lean_object* v___y_728_, lean_object* v_map_729_, lean_object* v_a_x3f_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_728_, v_map_729_, v_a_x3f_730_);
lean_dec(v_a_x3f_730_);
lean_dec(v___y_728_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(uint8_t v_pu_733_, uint8_t v_t_734_, lean_object* v_i_735_, lean_object* v_as_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = lean_array_get_size(v_as_736_);
v___x_741_ = lean_nat_dec_lt(v_i_735_, v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; 
lean_dec(v_i_735_);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v_as_736_);
return v___x_742_;
}
else
{
lean_object* v_a_743_; lean_object* v_type_744_; lean_object* v___x_745_; lean_object* v_subst_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_a_743_ = lean_array_fget_borrowed(v_as_736_, v_i_735_);
v_type_744_ = lean_ctor_get(v_a_743_, 2);
v___x_745_ = lean_st_ref_get(v___y_737_);
v_subst_746_ = lean_ctor_get(v___x_745_, 1);
lean_inc_ref(v_subst_746_);
lean_dec(v___x_745_);
lean_inc_ref(v_type_744_);
v___x_747_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_733_, v_subst_746_, v_t_734_, v_type_744_);
lean_dec_ref(v_subst_746_);
lean_inc(v_a_743_);
v___x_748_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_733_, v_a_743_, v___x_747_, v___y_738_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; size_t v___x_750_; size_t v___x_751_; uint8_t v___x_752_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref(v___x_748_);
v___x_750_ = lean_ptr_addr(v_a_743_);
v___x_751_ = lean_ptr_addr(v_a_749_);
v___x_752_ = lean_usize_dec_eq(v___x_750_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = lean_unsigned_to_nat(1u);
v___x_754_ = lean_nat_add(v_i_735_, v___x_753_);
v___x_755_ = lean_array_fset(v_as_736_, v_i_735_, v_a_749_);
lean_dec(v_i_735_);
v_i_735_ = v___x_754_;
v_as_736_ = v___x_755_;
goto _start;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; 
lean_dec(v_a_749_);
v___x_757_ = lean_unsigned_to_nat(1u);
v___x_758_ = lean_nat_add(v_i_735_, v___x_757_);
lean_dec(v_i_735_);
v_i_735_ = v___x_758_;
goto _start;
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec_ref(v_as_736_);
lean_dec(v_i_735_);
v_a_760_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_748_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_748_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg___boxed(lean_object* v_pu_768_, lean_object* v_t_769_, lean_object* v_i_770_, lean_object* v_as_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
uint8_t v_pu_boxed_775_; uint8_t v_t_boxed_776_; lean_object* v_res_777_; 
v_pu_boxed_775_ = lean_unbox(v_pu_768_);
v_t_boxed_776_ = lean_unbox(v_t_769_);
v_res_777_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(v_pu_boxed_775_, v_t_boxed_776_, v_i_770_, v_as_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec(v___y_772_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(uint8_t v_pu_778_, uint8_t v_t_779_, lean_object* v_ps_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(v_pu_778_, v_t_779_, v___x_787_, v_ps_780_, v___y_781_, v___y_783_);
return v___x_788_;
}
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
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_820_; size_t v___x_821_; size_t v___x_822_; 
v___x_820_ = ((size_t)5ULL);
v___x_821_ = ((size_t)1ULL);
v___x_822_ = lean_usize_shift_left(v___x_821_, v___x_820_);
return v___x_822_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_823_; size_t v___x_824_; size_t v___x_825_; 
v___x_823_ = ((size_t)1ULL);
v___x_824_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__0);
v___x_825_ = lean_usize_sub(v___x_824_, v___x_823_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(lean_object* v_x_826_, size_t v_x_827_, lean_object* v_x_828_){
_start:
{
if (lean_obj_tag(v_x_826_) == 0)
{
lean_object* v_es_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_850_; 
v_es_829_ = lean_ctor_get(v_x_826_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v_x_826_);
if (v_isSharedCheck_850_ == 0)
{
v___x_831_ = v_x_826_;
v_isShared_832_ = v_isSharedCheck_850_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_es_829_);
lean_dec(v_x_826_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_850_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; size_t v___x_834_; size_t v___x_835_; size_t v___x_836_; lean_object* v_j_837_; lean_object* v___x_838_; 
v___x_833_ = lean_box(2);
v___x_834_ = ((size_t)5ULL);
v___x_835_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1);
v___x_836_ = lean_usize_land(v_x_827_, v___x_835_);
v_j_837_ = lean_usize_to_nat(v___x_836_);
v___x_838_ = lean_array_get(v___x_833_, v_es_829_, v_j_837_);
lean_dec(v_j_837_);
lean_dec_ref(v_es_829_);
switch(lean_obj_tag(v___x_838_))
{
case 0:
{
lean_object* v_key_839_; lean_object* v_val_840_; uint8_t v___x_841_; 
v_key_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_key_839_);
v_val_840_ = lean_ctor_get(v___x_838_, 1);
lean_inc(v_val_840_);
lean_dec_ref(v___x_838_);
v___x_841_ = lean_expr_eqv(v_x_828_, v_key_839_);
lean_dec(v_key_839_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; 
lean_dec(v_val_840_);
lean_del_object(v___x_831_);
v___x_842_ = lean_box(0);
return v___x_842_;
}
else
{
lean_object* v___x_844_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set_tag(v___x_831_, 1);
lean_ctor_set(v___x_831_, 0, v_val_840_);
v___x_844_ = v___x_831_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_val_840_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
case 1:
{
lean_object* v_node_846_; size_t v___x_847_; 
lean_del_object(v___x_831_);
v_node_846_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_node_846_);
lean_dec_ref(v___x_838_);
v___x_847_ = lean_usize_shift_right(v_x_827_, v___x_834_);
v_x_826_ = v_node_846_;
v_x_827_ = v___x_847_;
goto _start;
}
default: 
{
lean_object* v___x_849_; 
lean_del_object(v___x_831_);
v___x_849_ = lean_box(0);
return v___x_849_;
}
}
}
}
else
{
lean_object* v_ks_851_; lean_object* v_vs_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_ks_851_ = lean_ctor_get(v_x_826_, 0);
lean_inc_ref(v_ks_851_);
v_vs_852_ = lean_ctor_get(v_x_826_, 1);
lean_inc_ref(v_vs_852_);
lean_dec_ref(v_x_826_);
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(v_ks_851_, v_vs_852_, v___x_853_, v_x_828_);
lean_dec_ref(v_vs_852_);
lean_dec_ref(v_ks_851_);
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___boxed(lean_object* v_x_855_, lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
size_t v_x_15783__boxed_858_; lean_object* v_res_859_; 
v_x_15783__boxed_858_ = lean_unbox_usize(v_x_856_);
lean_dec(v_x_856_);
v_res_859_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_855_, v_x_15783__boxed_858_, v_x_857_);
lean_dec_ref(v_x_857_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
uint64_t v___x_862_; size_t v___x_863_; lean_object* v___x_864_; 
v___x_862_ = l_Lean_Expr_hash(v_x_861_);
v___x_863_ = lean_uint64_to_usize(v___x_862_);
v___x_864_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_860_, v___x_863_, v_x_861_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg___boxed(lean_object* v_x_865_, lean_object* v_x_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_x_865_, v_x_866_);
lean_dec_ref(v_x_866_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
lean_object* v_ks_872_; lean_object* v_vs_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_897_; 
v_ks_872_ = lean_ctor_get(v_x_868_, 0);
v_vs_873_ = lean_ctor_get(v_x_868_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v_x_868_);
if (v_isSharedCheck_897_ == 0)
{
v___x_875_ = v_x_868_;
v_isShared_876_ = v_isSharedCheck_897_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_vs_873_);
lean_inc(v_ks_872_);
lean_dec(v_x_868_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_897_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_877_ = lean_array_get_size(v_ks_872_);
v___x_878_ = lean_nat_dec_lt(v_x_869_, v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
lean_dec(v_x_869_);
v___x_879_ = lean_array_push(v_ks_872_, v_x_870_);
v___x_880_ = lean_array_push(v_vs_873_, v_x_871_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 1, v___x_880_);
lean_ctor_set(v___x_875_, 0, v___x_879_);
v___x_882_ = v___x_875_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
else
{
lean_object* v_k_x27_884_; uint8_t v___x_885_; 
v_k_x27_884_ = lean_array_fget_borrowed(v_ks_872_, v_x_869_);
v___x_885_ = lean_expr_eqv(v_x_870_, v_k_x27_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_887_; 
if (v_isShared_876_ == 0)
{
v___x_887_ = v___x_875_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_ks_872_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_vs_873_);
v___x_887_ = v_reuseFailAlloc_891_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_unsigned_to_nat(1u);
v___x_889_ = lean_nat_add(v_x_869_, v___x_888_);
lean_dec(v_x_869_);
v_x_868_ = v___x_887_;
v_x_869_ = v___x_889_;
goto _start;
}
}
else
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_892_ = lean_array_fset(v_ks_872_, v_x_869_, v_x_870_);
v___x_893_ = lean_array_fset(v_vs_873_, v_x_869_, v_x_871_);
lean_dec(v_x_869_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 1, v___x_893_);
lean_ctor_set(v___x_875_, 0, v___x_892_);
v___x_895_ = v___x_875_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(lean_object* v_n_898_, lean_object* v_k_899_, lean_object* v_v_900_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(v_n_898_, v___x_901_, v_k_899_, v_v_900_);
return v___x_902_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(lean_object* v_x_904_, size_t v_x_905_, size_t v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
if (lean_obj_tag(v_x_904_) == 0)
{
lean_object* v_es_909_; size_t v___x_910_; size_t v___x_911_; size_t v___x_912_; size_t v___x_913_; lean_object* v_j_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_es_909_ = lean_ctor_get(v_x_904_, 0);
v___x_910_ = ((size_t)5ULL);
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1);
v___x_913_ = lean_usize_land(v_x_905_, v___x_912_);
v_j_914_ = lean_usize_to_nat(v___x_913_);
v___x_915_ = lean_array_get_size(v_es_909_);
v___x_916_ = lean_nat_dec_lt(v_j_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_dec(v_j_914_);
lean_dec(v_x_908_);
lean_dec_ref(v_x_907_);
return v_x_904_;
}
else
{
lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_953_; 
lean_inc_ref(v_es_909_);
v_isSharedCheck_953_ = !lean_is_exclusive(v_x_904_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; 
v_unused_954_ = lean_ctor_get(v_x_904_, 0);
lean_dec(v_unused_954_);
v___x_918_ = v_x_904_;
v_isShared_919_ = v_isSharedCheck_953_;
goto v_resetjp_917_;
}
else
{
lean_dec(v_x_904_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_953_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v_v_920_; lean_object* v___x_921_; lean_object* v_xs_x27_922_; lean_object* v___y_924_; 
v_v_920_ = lean_array_fget(v_es_909_, v_j_914_);
v___x_921_ = lean_box(0);
v_xs_x27_922_ = lean_array_fset(v_es_909_, v_j_914_, v___x_921_);
switch(lean_obj_tag(v_v_920_))
{
case 0:
{
lean_object* v_key_929_; lean_object* v_val_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_940_; 
v_key_929_ = lean_ctor_get(v_v_920_, 0);
v_val_930_ = lean_ctor_get(v_v_920_, 1);
v_isSharedCheck_940_ = !lean_is_exclusive(v_v_920_);
if (v_isSharedCheck_940_ == 0)
{
v___x_932_ = v_v_920_;
v_isShared_933_ = v_isSharedCheck_940_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_val_930_);
lean_inc(v_key_929_);
lean_dec(v_v_920_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_940_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
uint8_t v___x_934_; 
v___x_934_ = lean_expr_eqv(v_x_907_, v_key_929_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; 
lean_del_object(v___x_932_);
v___x_935_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_929_, v_val_930_, v_x_907_, v_x_908_);
v___x_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
v___y_924_ = v___x_936_;
goto v___jp_923_;
}
else
{
lean_object* v___x_938_; 
lean_dec(v_val_930_);
lean_dec(v_key_929_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v_x_908_);
lean_ctor_set(v___x_932_, 0, v_x_907_);
v___x_938_ = v___x_932_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_x_907_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_x_908_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
v___y_924_ = v___x_938_;
goto v___jp_923_;
}
}
}
}
case 1:
{
lean_object* v_node_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_951_; 
v_node_941_ = lean_ctor_get(v_v_920_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v_v_920_);
if (v_isSharedCheck_951_ == 0)
{
v___x_943_ = v_v_920_;
v_isShared_944_ = v_isSharedCheck_951_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_node_941_);
lean_dec(v_v_920_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_951_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
size_t v___x_945_; size_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_945_ = lean_usize_shift_right(v_x_905_, v___x_910_);
v___x_946_ = lean_usize_add(v_x_906_, v___x_911_);
v___x_947_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_node_941_, v___x_945_, v___x_946_, v_x_907_, v_x_908_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_947_);
v___x_949_ = v___x_943_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
v___y_924_ = v___x_949_;
goto v___jp_923_;
}
}
}
default: 
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v_x_907_);
lean_ctor_set(v___x_952_, 1, v_x_908_);
v___y_924_ = v___x_952_;
goto v___jp_923_;
}
}
v___jp_923_:
{
lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_925_ = lean_array_fset(v_xs_x27_922_, v_j_914_, v___y_924_);
lean_dec(v_j_914_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_925_);
v___x_927_ = v___x_918_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
}
else
{
lean_object* v_ks_955_; lean_object* v_vs_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_976_; 
v_ks_955_ = lean_ctor_get(v_x_904_, 0);
v_vs_956_ = lean_ctor_get(v_x_904_, 1);
v_isSharedCheck_976_ = !lean_is_exclusive(v_x_904_);
if (v_isSharedCheck_976_ == 0)
{
v___x_958_ = v_x_904_;
v_isShared_959_ = v_isSharedCheck_976_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_vs_956_);
lean_inc(v_ks_955_);
lean_dec(v_x_904_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_976_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_ks_955_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_vs_956_);
v___x_961_ = v_reuseFailAlloc_975_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v_newNode_962_; uint8_t v___y_964_; size_t v___x_970_; uint8_t v___x_971_; 
v_newNode_962_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(v___x_961_, v_x_907_, v_x_908_);
v___x_970_ = ((size_t)7ULL);
v___x_971_ = lean_usize_dec_le(v___x_970_, v_x_906_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_972_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_962_);
v___x_973_ = lean_unsigned_to_nat(4u);
v___x_974_ = lean_nat_dec_lt(v___x_972_, v___x_973_);
lean_dec(v___x_972_);
v___y_964_ = v___x_974_;
goto v___jp_963_;
}
else
{
v___y_964_ = v___x_971_;
goto v___jp_963_;
}
v___jp_963_:
{
if (v___y_964_ == 0)
{
lean_object* v_ks_965_; lean_object* v_vs_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_ks_965_ = lean_ctor_get(v_newNode_962_, 0);
lean_inc_ref(v_ks_965_);
v_vs_966_ = lean_ctor_get(v_newNode_962_, 1);
lean_inc_ref(v_vs_966_);
lean_dec_ref(v_newNode_962_);
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0);
v___x_969_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_x_906_, v_ks_965_, v_vs_966_, v___x_967_, v___x_968_);
lean_dec_ref(v_vs_966_);
lean_dec_ref(v_ks_965_);
return v___x_969_;
}
else
{
return v_newNode_962_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(size_t v_depth_977_, lean_object* v_keys_978_, lean_object* v_vals_979_, lean_object* v_i_980_, lean_object* v_entries_981_){
_start:
{
lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_982_ = lean_array_get_size(v_keys_978_);
v___x_983_ = lean_nat_dec_lt(v_i_980_, v___x_982_);
if (v___x_983_ == 0)
{
lean_dec(v_i_980_);
return v_entries_981_;
}
else
{
lean_object* v_k_984_; lean_object* v_v_985_; uint64_t v___x_986_; size_t v_h_987_; size_t v___x_988_; lean_object* v___x_989_; size_t v___x_990_; size_t v___x_991_; size_t v___x_992_; size_t v_h_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_k_984_ = lean_array_fget_borrowed(v_keys_978_, v_i_980_);
v_v_985_ = lean_array_fget_borrowed(v_vals_979_, v_i_980_);
v___x_986_ = l_Lean_Expr_hash(v_k_984_);
v_h_987_ = lean_uint64_to_usize(v___x_986_);
v___x_988_ = ((size_t)5ULL);
v___x_989_ = lean_unsigned_to_nat(1u);
v___x_990_ = ((size_t)1ULL);
v___x_991_ = lean_usize_sub(v_depth_977_, v___x_990_);
v___x_992_ = lean_usize_mul(v___x_988_, v___x_991_);
v_h_993_ = lean_usize_shift_right(v_h_987_, v___x_992_);
v___x_994_ = lean_nat_add(v_i_980_, v___x_989_);
lean_dec(v_i_980_);
lean_inc(v_v_985_);
lean_inc(v_k_984_);
v___x_995_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_entries_981_, v_h_993_, v_depth_977_, v_k_984_, v_v_985_);
v_i_980_ = v___x_994_;
v_entries_981_ = v___x_995_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_depth_997_, lean_object* v_keys_998_, lean_object* v_vals_999_, lean_object* v_i_1000_, lean_object* v_entries_1001_){
_start:
{
size_t v_depth_boxed_1002_; lean_object* v_res_1003_; 
v_depth_boxed_1002_ = lean_unbox_usize(v_depth_997_);
lean_dec(v_depth_997_);
v_res_1003_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_depth_boxed_1002_, v_keys_998_, v_vals_999_, v_i_1000_, v_entries_1001_);
lean_dec_ref(v_vals_999_);
lean_dec_ref(v_keys_998_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___boxed(lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_){
_start:
{
size_t v_x_15942__boxed_1009_; size_t v_x_15943__boxed_1010_; lean_object* v_res_1011_; 
v_x_15942__boxed_1009_ = lean_unbox_usize(v_x_1005_);
lean_dec(v_x_1005_);
v_x_15943__boxed_1010_ = lean_unbox_usize(v_x_1006_);
lean_dec(v_x_1006_);
v_res_1011_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_1004_, v_x_15942__boxed_1009_, v_x_15943__boxed_1010_, v_x_1007_, v_x_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(lean_object* v_x_1012_, lean_object* v_x_1013_, lean_object* v_x_1014_){
_start:
{
uint64_t v___x_1015_; size_t v___x_1016_; size_t v___x_1017_; lean_object* v___x_1018_; 
v___x_1015_ = l_Lean_Expr_hash(v_x_1013_);
v___x_1016_ = lean_uint64_to_usize(v___x_1015_);
v___x_1017_ = ((size_t)1ULL);
v___x_1018_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_1012_, v___x_1016_, v___x_1017_, v_x_1013_, v_x_1014_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(uint8_t v_shouldElimFunDecls_1021_, lean_object* v_i_1022_, lean_object* v_as_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = lean_array_get_size(v_as_1023_);
v___x_1031_ = lean_nat_dec_lt(v_i_1022_, v___x_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; 
lean_dec(v_i_1022_);
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v_as_1023_);
return v___x_1032_;
}
else
{
lean_object* v_a_1033_; lean_object* v_a_1035_; 
v_a_1033_ = lean_array_fget_borrowed(v_as_1023_, v_i_1022_);
if (lean_obj_tag(v_a_1033_) == 0)
{
lean_object* v_params_1046_; lean_object* v_code_1047_; lean_object* v___x_1048_; lean_object* v_map_1049_; uint8_t v___x_1050_; uint8_t v___x_1051_; lean_object* v_a_1053_; lean_object* v___x_1072_; 
v_params_1046_ = lean_ctor_get(v_a_1033_, 1);
v_code_1047_ = lean_ctor_get(v_a_1033_, 2);
v___x_1048_ = lean_st_ref_get(v___y_1024_);
v_map_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc_ref(v_map_1049_);
lean_dec(v___x_1048_);
v___x_1050_ = 0;
v___x_1051_ = 0;
lean_inc_ref(v_params_1046_);
v___x_1072_ = l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(v___x_1050_, v___x_1051_, v_params_1046_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1074_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref(v___x_1072_);
lean_inc_ref(v_code_1047_);
v___x_1074_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1021_, v_code_1047_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1092_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1092_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1092_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
lean_inc_ref(v_a_1033_);
v___x_1079_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v___x_1050_, v_a_1033_, v_a_1073_, v_a_1075_);
lean_inc_ref(v___x_1079_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set_tag(v___x_1077_, 1);
lean_ctor_set(v___x_1077_, 0, v___x_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1082_; 
v___x_1082_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_1024_, v_map_1049_, v___x_1081_);
lean_dec_ref(v___x_1081_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_dec_ref(v___x_1082_);
v_a_1035_ = v___x_1079_;
goto v___jp_1034_;
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec_ref(v___x_1079_);
lean_dec_ref(v_as_1023_);
lean_dec(v_i_1022_);
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
}
else
{
lean_object* v_a_1093_; 
lean_dec(v_a_1073_);
lean_dec_ref(v_as_1023_);
lean_dec(v_i_1022_);
v_a_1093_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1093_);
lean_dec_ref(v___x_1074_);
v_a_1053_ = v_a_1093_;
goto v___jp_1052_;
}
}
else
{
lean_object* v_a_1094_; 
lean_dec_ref(v_as_1023_);
lean_dec(v_i_1022_);
v_a_1094_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1094_);
lean_dec_ref(v___x_1072_);
v_a_1053_ = v_a_1094_;
goto v___jp_1052_;
}
v___jp_1052_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = lean_box(0);
v___x_1055_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_1024_, v_map_1049_, v___x_1054_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1062_ == 0)
{
lean_object* v_unused_1063_; 
v_unused_1063_ = lean_ctor_get(v___x_1055_, 0);
lean_dec(v_unused_1063_);
v___x_1057_ = v___x_1055_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_dec(v___x_1055_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set_tag(v___x_1057_, 1);
lean_ctor_set(v___x_1057_, 0, v_a_1053_);
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1053_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec_ref(v_a_1053_);
v_a_1064_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1055_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1055_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
else
{
lean_object* v_code_1095_; lean_object* v___x_1096_; lean_object* v_map_1097_; lean_object* v___x_1098_; 
v_code_1095_ = lean_ctor_get(v_a_1033_, 0);
v___x_1096_ = lean_st_ref_get(v___y_1024_);
v_map_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc_ref(v_map_1097_);
lean_dec(v___x_1096_);
lean_inc_ref(v_code_1095_);
v___x_1098_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1021_, v_code_1095_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1116_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1116_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1116_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1105_; 
lean_inc_ref(v_a_1033_);
v___x_1103_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1033_, v_a_1099_);
lean_inc_ref(v___x_1103_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set_tag(v___x_1101_, 1);
lean_ctor_set(v___x_1101_, 0, v___x_1103_);
v___x_1105_ = v___x_1101_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; 
v___x_1106_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_1024_, v_map_1097_, v___x_1105_);
lean_dec_ref(v___x_1105_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_dec_ref(v___x_1106_);
v_a_1035_ = v___x_1103_;
goto v___jp_1034_;
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec_ref(v___x_1103_);
lean_dec_ref(v_as_1023_);
lean_dec(v_i_1022_);
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec_ref(v_as_1023_);
lean_dec(v_i_1022_);
v_a_1117_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1117_);
lean_dec_ref(v___x_1098_);
v___x_1118_ = lean_box(0);
v___x_1119_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_1024_, v_map_1097_, v___x_1118_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v___x_1119_, 0);
lean_dec(v_unused_1127_);
v___x_1121_ = v___x_1119_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_dec(v___x_1119_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set_tag(v___x_1121_, 1);
lean_ctor_set(v___x_1121_, 0, v_a_1117_);
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1117_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec(v_a_1117_);
v_a_1128_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1119_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1119_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
v___jp_1034_:
{
size_t v___x_1036_; size_t v___x_1037_; uint8_t v___x_1038_; 
v___x_1036_ = lean_ptr_addr(v_a_1033_);
v___x_1037_ = lean_ptr_addr(v_a_1035_);
v___x_1038_ = lean_usize_dec_eq(v___x_1036_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = lean_unsigned_to_nat(1u);
v___x_1040_ = lean_nat_add(v_i_1022_, v___x_1039_);
v___x_1041_ = lean_array_fset(v_as_1023_, v_i_1022_, v_a_1035_);
lean_dec(v_i_1022_);
v_i_1022_ = v___x_1040_;
v_as_1023_ = v___x_1041_;
goto _start;
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec_ref(v_a_1035_);
v___x_1043_ = lean_unsigned_to_nat(1u);
v___x_1044_ = lean_nat_add(v_i_1022_, v___x_1043_);
lean_dec(v_i_1022_);
v_i_1022_ = v___x_1044_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(uint8_t v_shouldElimFunDecls_1136_, lean_object* v_code_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
switch(lean_obj_tag(v_code_1137_))
{
case 0:
{
lean_object* v_decl_1144_; lean_object* v_k_1145_; uint8_t v___x_1146_; uint8_t v___x_1147_; lean_object* v___x_1148_; 
v_decl_1144_ = lean_ctor_get(v_code_1137_, 0);
v_k_1145_ = lean_ctor_get(v_code_1137_, 1);
v___x_1146_ = 0;
v___x_1147_ = 0;
lean_inc_ref(v_decl_1144_);
v___x_1148_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v___x_1146_, v___x_1147_, v_decl_1144_, v_a_1138_, v_a_1140_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v_fvarId_1150_; lean_object* v_value_1151_; lean_object* v___x_1152_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref(v___x_1148_);
v_fvarId_1150_ = lean_ctor_get(v_a_1149_, 0);
v_value_1151_ = lean_ctor_get(v_a_1149_, 3);
lean_inc(v_value_1151_);
v___x_1152_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(v_value_1151_, v_a_1142_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; uint8_t v___x_1154_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref(v___x_1152_);
v___x_1154_ = lean_unbox(v_a_1153_);
lean_dec(v_a_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v_map_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1155_ = lean_st_ref_get(v_a_1138_);
v_map_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc_ref(v_map_1156_);
lean_dec(v___x_1155_);
lean_inc(v_value_1151_);
v___x_1157_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v___x_1146_, v_value_1151_);
v___x_1158_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_map_1156_, v___x_1157_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v___x_1159_; lean_object* v_map_1160_; lean_object* v_subst_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1199_; 
v___x_1159_ = lean_st_ref_take(v_a_1138_);
v_map_1160_ = lean_ctor_get(v___x_1159_, 0);
v_subst_1161_ = lean_ctor_get(v___x_1159_, 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1163_ = v___x_1159_;
v_isShared_1164_ = v_isSharedCheck_1199_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_subst_1161_);
lean_inc(v_map_1160_);
lean_dec(v___x_1159_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1199_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
lean_inc(v_fvarId_1150_);
v___x_1165_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_map_1160_, v___x_1157_, v_fvarId_1150_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1165_);
v___x_1167_ = v___x_1163_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_subst_1161_);
v___x_1167_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_st_ref_set(v_a_1138_, v___x_1167_);
lean_inc_ref(v_k_1145_);
v___x_1169_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1136_, v_k_1145_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1197_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1172_ = v___x_1169_;
v_isShared_1173_ = v_isSharedCheck_1197_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1169_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1197_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
uint8_t v___y_1175_; size_t v___x_1191_; size_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1191_ = lean_ptr_addr(v_k_1145_);
v___x_1192_ = lean_ptr_addr(v_a_1170_);
v___x_1193_ = lean_usize_dec_eq(v___x_1191_, v___x_1192_);
if (v___x_1193_ == 0)
{
v___y_1175_ = v___x_1193_;
goto v___jp_1174_;
}
else
{
size_t v___x_1194_; size_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1194_ = lean_ptr_addr(v_decl_1144_);
v___x_1195_ = lean_ptr_addr(v_a_1149_);
v___x_1196_ = lean_usize_dec_eq(v___x_1194_, v___x_1195_);
v___y_1175_ = v___x_1196_;
goto v___jp_1174_;
}
v___jp_1174_:
{
if (v___y_1175_ == 0)
{
lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1185_; 
v_isSharedCheck_1185_ = !lean_is_exclusive(v_code_1137_);
if (v_isSharedCheck_1185_ == 0)
{
lean_object* v_unused_1186_; lean_object* v_unused_1187_; 
v_unused_1186_ = lean_ctor_get(v_code_1137_, 1);
lean_dec(v_unused_1186_);
v_unused_1187_ = lean_ctor_get(v_code_1137_, 0);
lean_dec(v_unused_1187_);
v___x_1177_ = v_code_1137_;
v_isShared_1178_ = v_isSharedCheck_1185_;
goto v_resetjp_1176_;
}
else
{
lean_dec(v_code_1137_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1185_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v_a_1170_);
lean_ctor_set(v___x_1177_, 0, v_a_1149_);
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1149_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_a_1170_);
v___x_1180_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1182_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v___x_1180_);
v___x_1182_ = v___x_1172_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1180_);
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
else
{
lean_object* v___x_1189_; 
lean_dec(v_a_1170_);
lean_dec(v_a_1149_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v_code_1137_);
v___x_1189_ = v___x_1172_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_code_1137_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
else
{
lean_dec(v_a_1149_);
lean_dec_ref(v_code_1137_);
return v___x_1169_;
}
}
}
}
else
{
lean_object* v_val_1200_; lean_object* v___x_1201_; 
lean_inc_ref(v_k_1145_);
lean_dec_ref(v___x_1157_);
lean_dec_ref(v_code_1137_);
v_val_1200_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_val_1200_);
lean_dec_ref(v___x_1158_);
v___x_1201_ = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(v_a_1149_, v_val_1200_, v_a_1138_, v_a_1140_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_dec_ref(v___x_1201_);
v_code_1137_ = v_k_1145_;
goto _start;
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v_k_1145_);
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
lean_inc_ref(v_k_1145_);
v___x_1211_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1136_, v_k_1145_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1239_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1239_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1239_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
uint8_t v___y_1217_; size_t v___x_1233_; size_t v___x_1234_; uint8_t v___x_1235_; 
v___x_1233_ = lean_ptr_addr(v_k_1145_);
v___x_1234_ = lean_ptr_addr(v_a_1212_);
v___x_1235_ = lean_usize_dec_eq(v___x_1233_, v___x_1234_);
if (v___x_1235_ == 0)
{
v___y_1217_ = v___x_1235_;
goto v___jp_1216_;
}
else
{
size_t v___x_1236_; size_t v___x_1237_; uint8_t v___x_1238_; 
v___x_1236_ = lean_ptr_addr(v_decl_1144_);
v___x_1237_ = lean_ptr_addr(v_a_1149_);
v___x_1238_ = lean_usize_dec_eq(v___x_1236_, v___x_1237_);
v___y_1217_ = v___x_1238_;
goto v___jp_1216_;
}
v___jp_1216_:
{
if (v___y_1217_ == 0)
{
lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1227_; 
v_isSharedCheck_1227_ = !lean_is_exclusive(v_code_1137_);
if (v_isSharedCheck_1227_ == 0)
{
lean_object* v_unused_1228_; lean_object* v_unused_1229_; 
v_unused_1228_ = lean_ctor_get(v_code_1137_, 1);
lean_dec(v_unused_1228_);
v_unused_1229_ = lean_ctor_get(v_code_1137_, 0);
lean_dec(v_unused_1229_);
v___x_1219_ = v_code_1137_;
v_isShared_1220_ = v_isSharedCheck_1227_;
goto v_resetjp_1218_;
}
else
{
lean_dec(v_code_1137_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1227_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 1, v_a_1212_);
lean_ctor_set(v___x_1219_, 0, v_a_1149_);
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1149_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_a_1212_);
v___x_1222_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1224_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1222_);
v___x_1224_ = v___x_1214_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
else
{
lean_object* v___x_1231_; 
lean_dec(v_a_1212_);
lean_dec(v_a_1149_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v_code_1137_);
v___x_1231_ = v___x_1214_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_code_1137_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
else
{
lean_dec(v_a_1149_);
lean_dec_ref(v_code_1137_);
return v___x_1211_;
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v_a_1149_);
lean_dec_ref(v_code_1137_);
v_a_1240_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1152_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1152_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec_ref(v_code_1137_);
v_a_1248_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1148_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1148_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
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
case 1:
{
lean_object* v_decl_1256_; lean_object* v_k_1257_; lean_object* v___x_1258_; 
v_decl_1256_ = lean_ctor_get(v_code_1137_, 0);
v_k_1257_ = lean_ctor_get(v_code_1137_, 1);
lean_inc_ref(v_decl_1256_);
v___x_1258_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_1136_, v_decl_1256_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1258_) == 0)
{
if (v_shouldElimFunDecls_1136_ == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1260_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref(v___x_1258_);
lean_inc_ref(v_k_1257_);
v___x_1260_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1136_, v_k_1257_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1288_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1288_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1288_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
uint8_t v___y_1266_; size_t v___x_1282_; size_t v___x_1283_; uint8_t v___x_1284_; 
v___x_1282_ = lean_ptr_addr(v_k_1257_);
v___x_1283_ = lean_ptr_addr(v_a_1261_);
v___x_1284_ = lean_usize_dec_eq(v___x_1282_, v___x_1283_);
if (v___x_1284_ == 0)
{
v___y_1266_ = v___x_1284_;
goto v___jp_1265_;
}
else
{
size_t v___x_1285_; size_t v___x_1286_; uint8_t v___x_1287_; 
v___x_1285_ = lean_ptr_addr(v_decl_1256_);
v___x_1286_ = lean_ptr_addr(v_a_1259_);
v___x_1287_ = lean_usize_dec_eq(v___x_1285_, v___x_1286_);
v___y_1266_ = v___x_1287_;
goto v___jp_1265_;
}
v___jp_1265_:
{
if (v___y_1266_ == 0)
{
lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1276_; 
v_isSharedCheck_1276_ = !lean_is_exclusive(v_code_1137_);
if (v_isSharedCheck_1276_ == 0)
{
lean_object* v_unused_1277_; lean_object* v_unused_1278_; 
v_unused_1277_ = lean_ctor_get(v_code_1137_, 1);
lean_dec(v_unused_1277_);
v_unused_1278_ = lean_ctor_get(v_code_1137_, 0);
lean_dec(v_unused_1278_);
v___x_1268_ = v_code_1137_;
v_isShared_1269_ = v_isSharedCheck_1276_;
goto v_resetjp_1267_;
}
else
{
lean_dec(v_code_1137_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1276_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v_a_1261_);
lean_ctor_set(v___x_1268_, 0, v_a_1259_);
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1259_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_a_1261_);
v___x_1271_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1273_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1271_);
v___x_1273_ = v___x_1263_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
else
{
lean_object* v___x_1280_; 
lean_dec(v_a_1261_);
lean_dec(v_a_1259_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v_code_1137_);
v___x_1280_ = v___x_1263_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_code_1137_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
else
{
lean_dec(v_a_1259_);
lean_dec_ref(v_code_1137_);
return v___x_1260_;
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1290_; lean_object* v_map_1291_; uint8_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v_a_1289_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1289_);
lean_dec_ref(v___x_1258_);
v___x_1290_ = lean_st_ref_get(v_a_1138_);
v_map_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc_ref(v_map_1291_);
lean_dec(v___x_1290_);
v___x_1292_ = 0;
v___x_1293_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___closed__0));
lean_inc(v_a_1289_);
v___x_1294_ = l_Lean_Compiler_LCNF_FunDecl_toExpr(v___x_1292_, v_a_1289_, v___x_1293_);
v___x_1295_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_map_1291_, v___x_1294_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_fvarId_1296_; lean_object* v___x_1297_; lean_object* v_map_1298_; lean_object* v_subst_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1337_; 
v_fvarId_1296_ = lean_ctor_get(v_a_1289_, 0);
v___x_1297_ = lean_st_ref_take(v_a_1138_);
v_map_1298_ = lean_ctor_get(v___x_1297_, 0);
v_subst_1299_ = lean_ctor_get(v___x_1297_, 1);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1301_ = v___x_1297_;
v_isShared_1302_ = v_isSharedCheck_1337_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_subst_1299_);
lean_inc(v_map_1298_);
lean_dec(v___x_1297_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1337_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
lean_inc(v_fvarId_1296_);
v___x_1303_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_map_1298_, v___x_1294_, v_fvarId_1296_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1303_);
v___x_1305_ = v___x_1301_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_subst_1299_);
v___x_1305_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_st_ref_set(v_a_1138_, v___x_1305_);
lean_inc_ref(v_k_1257_);
v___x_1307_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1136_, v_k_1257_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1335_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1335_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1335_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
uint8_t v___y_1313_; size_t v___x_1329_; size_t v___x_1330_; uint8_t v___x_1331_; 
v___x_1329_ = lean_ptr_addr(v_k_1257_);
v___x_1330_ = lean_ptr_addr(v_a_1308_);
v___x_1331_ = lean_usize_dec_eq(v___x_1329_, v___x_1330_);
if (v___x_1331_ == 0)
{
v___y_1313_ = v___x_1331_;
goto v___jp_1312_;
}
else
{
size_t v___x_1332_; size_t v___x_1333_; uint8_t v___x_1334_; 
v___x_1332_ = lean_ptr_addr(v_decl_1256_);
v___x_1333_ = lean_ptr_addr(v_a_1289_);
v___x_1334_ = lean_usize_dec_eq(v___x_1332_, v___x_1333_);
v___y_1313_ = v___x_1334_;
goto v___jp_1312_;
}
v___jp_1312_:
{
if (v___y_1313_ == 0)
{
lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1323_; 
v_isSharedCheck_1323_ = !lean_is_exclusive(v_code_1137_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; lean_object* v_unused_1325_; 
v_unused_1324_ = lean_ctor_get(v_code_1137_, 1);
lean_dec(v_unused_1324_);
v_unused_1325_ = lean_ctor_get(v_code_1137_, 0);
lean_dec(v_unused_1325_);
v___x_1315_ = v_code_1137_;
v_isShared_1316_ = v_isSharedCheck_1323_;
goto v_resetjp_1314_;
}
else
{
lean_dec(v_code_1137_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1323_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 1, v_a_1308_);
lean_ctor_set(v___x_1315_, 0, v_a_1289_);
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1289_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_a_1308_);
v___x_1318_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1320_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1318_);
v___x_1320_ = v___x_1310_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1318_);
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
else
{
lean_object* v___x_1327_; 
lean_dec(v_a_1308_);
lean_dec(v_a_1289_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v_code_1137_);
v___x_1327_ = v___x_1310_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_code_1137_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
else
{
lean_dec(v_a_1289_);
lean_dec_ref(v_code_1137_);
return v___x_1307_;
}
}
}
}
else
{
lean_object* v_val_1338_; lean_object* v___x_1339_; 
lean_inc_ref(v_k_1257_);
lean_dec_ref(v___x_1294_);
lean_dec_ref(v_code_1137_);
v_val_1338_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_val_1338_);
lean_dec_ref(v___x_1295_);
v___x_1339_ = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(v_a_1289_, v_val_1338_, v_a_1138_, v_a_1140_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_dec_ref(v___x_1339_);
v_code_1137_ = v_k_1257_;
goto _start;
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v_k_1257_);
v_a_1341_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1339_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1339_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec_ref(v_code_1137_);
v_a_1349_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1258_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1258_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
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
case 2:
{
lean_object* v_decl_1357_; lean_object* v_k_1358_; lean_object* v___x_1359_; 
v_decl_1357_ = lean_ctor_get(v_code_1137_, 0);
v_k_1358_ = lean_ctor_get(v_code_1137_, 1);
lean_inc_ref(v_decl_1357_);
v___x_1359_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_1136_, v_decl_1357_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1361_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref(v___x_1359_);
lean_inc_ref(v_k_1358_);
v___x_1361_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1136_, v_k_1358_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1389_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1389_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1389_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
uint8_t v___y_1367_; size_t v___x_1383_; size_t v___x_1384_; uint8_t v___x_1385_; 
v___x_1383_ = lean_ptr_addr(v_k_1358_);
v___x_1384_ = lean_ptr_addr(v_a_1362_);
v___x_1385_ = lean_usize_dec_eq(v___x_1383_, v___x_1384_);
if (v___x_1385_ == 0)
{
v___y_1367_ = v___x_1385_;
goto v___jp_1366_;
}
else
{
size_t v___x_1386_; size_t v___x_1387_; uint8_t v___x_1388_; 
v___x_1386_ = lean_ptr_addr(v_decl_1357_);
v___x_1387_ = lean_ptr_addr(v_a_1360_);
v___x_1388_ = lean_usize_dec_eq(v___x_1386_, v___x_1387_);
v___y_1367_ = v___x_1388_;
goto v___jp_1366_;
}
v___jp_1366_:
{
if (v___y_1367_ == 0)
{
lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1377_; 
v_isSharedCheck_1377_ = !lean_is_exclusive(v_code_1137_);
if (v_isSharedCheck_1377_ == 0)
{
lean_object* v_unused_1378_; lean_object* v_unused_1379_; 
v_unused_1378_ = lean_ctor_get(v_code_1137_, 1);
lean_dec(v_unused_1378_);
v_unused_1379_ = lean_ctor_get(v_code_1137_, 0);
lean_dec(v_unused_1379_);
v___x_1369_ = v_code_1137_;
v_isShared_1370_ = v_isSharedCheck_1377_;
goto v_resetjp_1368_;
}
else
{
lean_dec(v_code_1137_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1377_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v_a_1362_);
lean_ctor_set(v___x_1369_, 0, v_a_1360_);
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1360_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_a_1362_);
v___x_1372_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1374_; 
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1372_);
v___x_1374_ = v___x_1364_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
else
{
lean_object* v___x_1381_; 
lean_dec(v_a_1362_);
lean_dec(v_a_1360_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v_code_1137_);
v___x_1381_ = v___x_1364_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_code_1137_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
else
{
lean_dec(v_a_1360_);
lean_dec_ref(v_code_1137_);
return v___x_1361_;
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec_ref(v_code_1137_);
v_a_1390_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1359_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1359_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_1398_; lean_object* v_args_1399_; lean_object* v___x_1400_; lean_object* v_subst_1401_; uint8_t v___x_1402_; uint8_t v___x_1403_; lean_object* v___x_1404_; 
v_fvarId_1398_ = lean_ctor_get(v_code_1137_, 0);
v_args_1399_ = lean_ctor_get(v_code_1137_, 1);
v___x_1400_ = lean_st_ref_get(v_a_1138_);
v_subst_1401_ = lean_ctor_get(v___x_1400_, 1);
lean_inc_ref(v_subst_1401_);
lean_dec(v___x_1400_);
v___x_1402_ = 0;
v___x_1403_ = 0;
lean_inc(v_fvarId_1398_);
v___x_1404_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1401_, v_fvarId_1398_, v___x_1403_);
lean_dec_ref(v_subst_1401_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_fvarId_1405_; lean_object* v___x_1406_; 
v_fvarId_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_fvarId_1405_);
lean_dec_ref(v___x_1404_);
lean_inc_ref(v_args_1399_);
v___x_1406_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v___x_1402_, v___x_1403_, v_args_1399_, v_a_1138_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1432_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1432_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1432_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
uint8_t v___y_1412_; uint8_t v___x_1428_; 
v___x_1428_ = l_Lean_instBEqFVarId_beq(v_fvarId_1398_, v_fvarId_1405_);
if (v___x_1428_ == 0)
{
v___y_1412_ = v___x_1428_;
goto v___jp_1411_;
}
else
{
size_t v___x_1429_; size_t v___x_1430_; uint8_t v___x_1431_; 
v___x_1429_ = lean_ptr_addr(v_args_1399_);
v___x_1430_ = lean_ptr_addr(v_a_1407_);
v___x_1431_ = lean_usize_dec_eq(v___x_1429_, v___x_1430_);
v___y_1412_ = v___x_1431_;
goto v___jp_1411_;
}
v___jp_1411_:
{
if (v___y_1412_ == 0)
{
lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1422_; 
v_isSharedCheck_1422_ = !lean_is_exclusive(v_code_1137_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; lean_object* v_unused_1424_; 
v_unused_1423_ = lean_ctor_get(v_code_1137_, 1);
lean_dec(v_unused_1423_);
v_unused_1424_ = lean_ctor_get(v_code_1137_, 0);
lean_dec(v_unused_1424_);
v___x_1414_ = v_code_1137_;
v_isShared_1415_ = v_isSharedCheck_1422_;
goto v_resetjp_1413_;
}
else
{
lean_dec(v_code_1137_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1422_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 1, v_a_1407_);
lean_ctor_set(v___x_1414_, 0, v_fvarId_1405_);
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_fvarId_1405_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_a_1407_);
v___x_1417_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1419_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1417_);
v___x_1419_ = v___x_1409_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
else
{
lean_object* v___x_1426_; 
lean_dec(v_a_1407_);
lean_dec(v_fvarId_1405_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v_code_1137_);
v___x_1426_ = v___x_1409_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_code_1137_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec(v_fvarId_1405_);
lean_dec_ref(v_code_1137_);
v_a_1433_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1406_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1406_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
else
{
lean_object* v___x_1441_; 
lean_dec_ref(v_code_1137_);
v___x_1441_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1402_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
return v___x_1441_;
}
}
case 4:
{
lean_object* v_cases_1442_; lean_object* v_typeName_1443_; lean_object* v_resultType_1444_; lean_object* v_discr_1445_; lean_object* v_alts_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1499_; 
v_cases_1442_ = lean_ctor_get(v_code_1137_, 0);
lean_inc_ref(v_cases_1442_);
v_typeName_1443_ = lean_ctor_get(v_cases_1442_, 0);
v_resultType_1444_ = lean_ctor_get(v_cases_1442_, 1);
v_discr_1445_ = lean_ctor_get(v_cases_1442_, 2);
v_alts_1446_ = lean_ctor_get(v_cases_1442_, 3);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_cases_1442_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1448_ = v_cases_1442_;
v_isShared_1449_ = v_isSharedCheck_1499_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_alts_1446_);
lean_inc(v_discr_1445_);
lean_inc(v_resultType_1444_);
lean_inc(v_typeName_1443_);
lean_dec(v_cases_1442_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1499_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1450_; lean_object* v_subst_1451_; uint8_t v___x_1452_; uint8_t v___x_1453_; lean_object* v___x_1454_; 
v___x_1450_ = lean_st_ref_get(v_a_1138_);
v_subst_1451_ = lean_ctor_get(v___x_1450_, 1);
lean_inc_ref(v_subst_1451_);
lean_dec(v___x_1450_);
v___x_1452_ = 0;
v___x_1453_ = 0;
lean_inc(v_discr_1445_);
v___x_1454_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1451_, v_discr_1445_, v___x_1453_);
lean_dec_ref(v_subst_1451_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_fvarId_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1497_; 
v_fvarId_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1497_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_fvarId_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1497_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1459_ = lean_st_ref_get(v_a_1138_);
v___x_1460_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1446_);
v___x_1461_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(v_shouldElimFunDecls_1136_, v___x_1460_, v_alts_1446_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1488_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1488_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1461_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1488_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v_subst_1466_; lean_object* v___x_1467_; uint8_t v___y_1479_; size_t v___x_1482_; size_t v___x_1483_; uint8_t v___x_1484_; 
v_subst_1466_ = lean_ctor_get(v___x_1459_, 1);
lean_inc_ref(v_subst_1466_);
lean_dec(v___x_1459_);
lean_inc_ref(v_resultType_1444_);
v___x_1467_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_1452_, v_subst_1466_, v___x_1453_, v_resultType_1444_);
lean_dec_ref(v_subst_1466_);
v___x_1482_ = lean_ptr_addr(v_alts_1446_);
lean_dec_ref(v_alts_1446_);
v___x_1483_ = lean_ptr_addr(v_a_1462_);
v___x_1484_ = lean_usize_dec_eq(v___x_1482_, v___x_1483_);
if (v___x_1484_ == 0)
{
lean_dec_ref(v_resultType_1444_);
v___y_1479_ = v___x_1484_;
goto v___jp_1478_;
}
else
{
size_t v___x_1485_; size_t v___x_1486_; uint8_t v___x_1487_; 
v___x_1485_ = lean_ptr_addr(v_resultType_1444_);
lean_dec_ref(v_resultType_1444_);
v___x_1486_ = lean_ptr_addr(v___x_1467_);
v___x_1487_ = lean_usize_dec_eq(v___x_1485_, v___x_1486_);
v___y_1479_ = v___x_1487_;
goto v___jp_1478_;
}
v___jp_1468_:
{
lean_object* v___x_1470_; 
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 3, v_a_1462_);
lean_ctor_set(v___x_1448_, 2, v_fvarId_1455_);
lean_ctor_set(v___x_1448_, 1, v___x_1467_);
v___x_1470_ = v___x_1448_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_typeName_1443_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_fvarId_1455_);
lean_ctor_set(v_reuseFailAlloc_1477_, 3, v_a_1462_);
v___x_1470_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1472_; 
if (v_isShared_1458_ == 0)
{
lean_ctor_set_tag(v___x_1457_, 4);
lean_ctor_set(v___x_1457_, 0, v___x_1470_);
v___x_1472_ = v___x_1457_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1474_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v___x_1472_);
v___x_1474_ = v___x_1464_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
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
v___jp_1478_:
{
if (v___y_1479_ == 0)
{
lean_dec(v_discr_1445_);
lean_dec_ref(v_code_1137_);
goto v___jp_1468_;
}
else
{
uint8_t v___x_1480_; 
v___x_1480_ = l_Lean_instBEqFVarId_beq(v_discr_1445_, v_fvarId_1455_);
lean_dec(v_discr_1445_);
if (v___x_1480_ == 0)
{
lean_dec_ref(v_code_1137_);
goto v___jp_1468_;
}
else
{
lean_object* v___x_1481_; 
lean_dec_ref(v___x_1467_);
lean_del_object(v___x_1464_);
lean_dec(v_a_1462_);
lean_del_object(v___x_1457_);
lean_dec(v_fvarId_1455_);
lean_del_object(v___x_1448_);
lean_dec(v_typeName_1443_);
v___x_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1481_, 0, v_code_1137_);
return v___x_1481_;
}
}
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec(v___x_1459_);
lean_del_object(v___x_1457_);
lean_dec(v_fvarId_1455_);
lean_del_object(v___x_1448_);
lean_dec_ref(v_alts_1446_);
lean_dec(v_discr_1445_);
lean_dec_ref(v_resultType_1444_);
lean_dec(v_typeName_1443_);
lean_dec_ref(v_code_1137_);
v_a_1489_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1461_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1461_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
else
{
lean_object* v___x_1498_; 
lean_del_object(v___x_1448_);
lean_dec_ref(v_alts_1446_);
lean_dec(v_discr_1445_);
lean_dec_ref(v_resultType_1444_);
lean_dec(v_typeName_1443_);
lean_dec_ref(v_code_1137_);
v___x_1498_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1452_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
return v___x_1498_;
}
}
}
case 5:
{
lean_object* v_fvarId_1500_; lean_object* v___x_1501_; lean_object* v_subst_1502_; uint8_t v___x_1503_; lean_object* v___x_1504_; 
v_fvarId_1500_ = lean_ctor_get(v_code_1137_, 0);
v___x_1501_ = lean_st_ref_get(v_a_1138_);
v_subst_1502_ = lean_ctor_get(v___x_1501_, 1);
lean_inc_ref(v_subst_1502_);
lean_dec(v___x_1501_);
v___x_1503_ = 0;
lean_inc(v_fvarId_1500_);
v___x_1504_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1502_, v_fvarId_1500_, v___x_1503_);
lean_dec_ref(v_subst_1502_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_fvarId_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1524_; 
v_fvarId_1505_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1507_ = v___x_1504_;
v_isShared_1508_ = v_isSharedCheck_1524_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_fvarId_1505_);
lean_dec(v___x_1504_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1524_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
uint8_t v___x_1509_; 
v___x_1509_ = l_Lean_instBEqFVarId_beq(v_fvarId_1500_, v_fvarId_1505_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1519_; 
v_isSharedCheck_1519_ = !lean_is_exclusive(v_code_1137_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v_code_1137_, 0);
lean_dec(v_unused_1520_);
v___x_1511_ = v_code_1137_;
v_isShared_1512_ = v_isSharedCheck_1519_;
goto v_resetjp_1510_;
}
else
{
lean_dec(v_code_1137_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1519_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v_fvarId_1505_);
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_fvarId_1505_);
v___x_1514_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1516_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1514_);
v___x_1516_ = v___x_1507_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
else
{
lean_object* v___x_1522_; 
lean_dec(v_fvarId_1505_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v_code_1137_);
v___x_1522_ = v___x_1507_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_code_1137_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
else
{
uint8_t v___x_1525_; lean_object* v___x_1526_; 
lean_dec_ref(v_code_1137_);
v___x_1525_ = 0;
v___x_1526_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1525_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
return v___x_1526_;
}
}
default: 
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v_code_1137_);
return v___x_1527_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(uint8_t v_shouldElimFunDecls_1528_, lean_object* v_decl_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_params_1536_; lean_object* v_type_1537_; lean_object* v_value_1538_; lean_object* v___x_1539_; lean_object* v_subst_1540_; uint8_t v___x_1541_; uint8_t v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_params_1536_ = lean_ctor_get(v_decl_1529_, 2);
v_type_1537_ = lean_ctor_get(v_decl_1529_, 3);
v_value_1538_ = lean_ctor_get(v_decl_1529_, 4);
v___x_1539_ = lean_st_ref_get(v_a_1530_);
v_subst_1540_ = lean_ctor_get(v___x_1539_, 1);
lean_inc_ref(v_subst_1540_);
lean_dec(v___x_1539_);
v___x_1541_ = 0;
v___x_1542_ = 0;
lean_inc_ref(v_type_1537_);
v___x_1543_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_1541_, v_subst_1540_, v___x_1542_, v_type_1537_);
lean_dec_ref(v_subst_1540_);
lean_inc_ref(v_params_1536_);
v___x_1544_ = l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(v___x_1541_, v___x_1542_, v_params_1536_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1546_; lean_object* v_map_1547_; lean_object* v_r_1548_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref(v___x_1544_);
v___x_1546_ = lean_st_ref_get(v_a_1530_);
v_map_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc_ref(v_map_1547_);
lean_dec(v___x_1546_);
lean_inc_ref(v_value_1538_);
v_r_1548_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1528_, v_value_1538_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
if (lean_obj_tag(v_r_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1566_; 
v_a_1549_ = lean_ctor_get(v_r_1548_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_r_1548_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1551_ = v_r_1548_;
v_isShared_1552_ = v_isSharedCheck_1566_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v_r_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1566_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
lean_inc(v_a_1549_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 1);
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1555_; 
v___x_1555_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(v_a_1530_, v_map_1547_, v___x_1554_);
lean_dec_ref(v___x_1554_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v___x_1556_; 
lean_dec_ref(v___x_1555_);
v___x_1556_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1541_, v_decl_1529_, v___x_1543_, v_a_1545_, v_a_1549_, v_a_1532_);
return v___x_1556_;
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v_a_1549_);
lean_dec(v_a_1545_);
lean_dec_ref(v___x_1543_);
lean_dec_ref(v_decl_1529_);
v_a_1557_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1555_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1555_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
lean_dec(v_a_1545_);
lean_dec_ref(v___x_1543_);
lean_dec_ref(v_decl_1529_);
v_a_1567_ = lean_ctor_get(v_r_1548_, 0);
lean_inc(v_a_1567_);
lean_dec_ref(v_r_1548_);
v___x_1568_ = lean_box(0);
v___x_1569_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(v_a_1530_, v_map_1547_, v___x_1568_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1576_ == 0)
{
lean_object* v_unused_1577_; 
v_unused_1577_ = lean_ctor_get(v___x_1569_, 0);
lean_dec(v_unused_1577_);
v___x_1571_ = v___x_1569_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_dec(v___x_1569_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 1);
lean_ctor_set(v___x_1571_, 0, v_a_1567_);
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1567_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec(v_a_1567_);
v_a_1578_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1569_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1569_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v___x_1543_);
lean_dec_ref(v_decl_1529_);
v_a_1586_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1544_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1544_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___boxed(lean_object* v_shouldElimFunDecls_1594_, lean_object* v_decl_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1602_; lean_object* v_res_1603_; 
v_shouldElimFunDecls_boxed_1602_ = lean_unbox(v_shouldElimFunDecls_1594_);
v_res_1603_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_boxed_1602_, v_decl_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec_ref(v_a_1597_);
lean_dec(v_a_1596_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___boxed(lean_object* v_shouldElimFunDecls_1604_, lean_object* v_i_1605_, lean_object* v_as_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1613_; lean_object* v_res_1614_; 
v_shouldElimFunDecls_boxed_1613_ = lean_unbox(v_shouldElimFunDecls_1604_);
v_res_1614_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(v_shouldElimFunDecls_boxed_1613_, v_i_1605_, v_as_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___boxed(lean_object* v_shouldElimFunDecls_1615_, lean_object* v_code_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1623_; lean_object* v_res_1624_; 
v_shouldElimFunDecls_boxed_1623_ = lean_unbox(v_shouldElimFunDecls_1615_);
v_res_1624_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_boxed_1623_, v_code_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec(v_a_1617_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2(uint8_t v_pu_1625_, uint8_t v_t_1626_, lean_object* v_decl_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v_pu_1625_, v_t_1626_, v_decl_1627_, v___y_1628_, v___y_1630_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___boxed(lean_object* v_pu_1635_, lean_object* v_t_1636_, lean_object* v_decl_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
uint8_t v_pu_boxed_1644_; uint8_t v_t_boxed_1645_; lean_object* v_res_1646_; 
v_pu_boxed_1644_ = lean_unbox(v_pu_1635_);
v_t_boxed_1645_ = lean_unbox(v_t_1636_);
v_res_1646_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2(v_pu_boxed_1644_, v_t_boxed_1645_, v_decl_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5(uint8_t v_pu_1647_, uint8_t v_t_1648_, lean_object* v_args_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v_pu_1647_, v_t_1648_, v_args_1649_, v___y_1650_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___boxed(lean_object* v_pu_1657_, lean_object* v_t_1658_, lean_object* v_args_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
uint8_t v_pu_boxed_1666_; uint8_t v_t_boxed_1667_; lean_object* v_res_1668_; 
v_pu_boxed_1666_ = lean_unbox(v_pu_1657_);
v_t_boxed_1667_ = lean_unbox(v_t_1658_);
v_res_1668_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5(v_pu_boxed_1666_, v_t_boxed_1667_, v_args_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3(lean_object* v_00_u03b2_1669_, lean_object* v_x_1670_, lean_object* v_x_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_x_1670_, v_x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___boxed(lean_object* v_00_u03b2_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3(v_00_u03b2_1673_, v_x_1674_, v_x_1675_);
lean_dec_ref(v_x_1675_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4(lean_object* v_00_u03b2_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_, lean_object* v_x_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_x_1678_, v_x_1679_, v_x_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(uint8_t v_pu_1682_, uint8_t v_t_1683_, lean_object* v_i_1684_, lean_object* v_as_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(v_pu_1682_, v_t_1683_, v_i_1684_, v_as_1685_, v___y_1686_, v___y_1688_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___boxed(lean_object* v_pu_1693_, lean_object* v_t_1694_, lean_object* v_i_1695_, lean_object* v_as_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
uint8_t v_pu_boxed_1703_; uint8_t v_t_boxed_1704_; lean_object* v_res_1705_; 
v_pu_boxed_1703_ = lean_unbox(v_pu_1693_);
v_t_boxed_1704_ = lean_unbox(v_t_1694_);
v_res_1705_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(v_pu_boxed_1703_, v_t_boxed_1704_, v_i_1695_, v_as_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4(lean_object* v_00_u03b2_1706_, lean_object* v_x_1707_, size_t v_x_1708_, lean_object* v_x_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_1707_, v_x_1708_, v_x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1711_, lean_object* v_x_1712_, lean_object* v_x_1713_, lean_object* v_x_1714_){
_start:
{
size_t v_x_17301__boxed_1715_; lean_object* v_res_1716_; 
v_x_17301__boxed_1715_ = lean_unbox_usize(v_x_1713_);
lean_dec(v_x_1713_);
v_res_1716_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4(v_00_u03b2_1711_, v_x_1712_, v_x_17301__boxed_1715_, v_x_1714_);
lean_dec_ref(v_x_1714_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6(lean_object* v_00_u03b2_1717_, lean_object* v_x_1718_, size_t v_x_1719_, size_t v_x_1720_, lean_object* v_x_1721_, lean_object* v_x_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_1718_, v_x_1719_, v_x_1720_, v_x_1721_, v_x_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1724_, lean_object* v_x_1725_, lean_object* v_x_1726_, lean_object* v_x_1727_, lean_object* v_x_1728_, lean_object* v_x_1729_){
_start:
{
size_t v_x_17312__boxed_1730_; size_t v_x_17313__boxed_1731_; lean_object* v_res_1732_; 
v_x_17312__boxed_1730_ = lean_unbox_usize(v_x_1726_);
lean_dec(v_x_1726_);
v_x_17313__boxed_1731_ = lean_unbox_usize(v_x_1727_);
lean_dec(v_x_1727_);
v_res_1732_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6(v_00_u03b2_1724_, v_x_1725_, v_x_17312__boxed_1730_, v_x_17313__boxed_1731_, v_x_1728_, v_x_1729_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1733_, lean_object* v_keys_1734_, lean_object* v_vals_1735_, lean_object* v_heq_1736_, lean_object* v_i_1737_, lean_object* v_k_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(v_keys_1734_, v_vals_1735_, v_i_1737_, v_k_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1740_, lean_object* v_keys_1741_, lean_object* v_vals_1742_, lean_object* v_heq_1743_, lean_object* v_i_1744_, lean_object* v_k_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6(v_00_u03b2_1740_, v_keys_1741_, v_vals_1742_, v_heq_1743_, v_i_1744_, v_k_1745_);
lean_dec_ref(v_k_1745_);
lean_dec_ref(v_vals_1742_);
lean_dec_ref(v_keys_1741_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_1747_, lean_object* v_n_1748_, lean_object* v_k_1749_, lean_object* v_v_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(v_n_1748_, v_k_1749_, v_v_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_1752_, size_t v_depth_1753_, lean_object* v_keys_1754_, lean_object* v_vals_1755_, lean_object* v_heq_1756_, lean_object* v_i_1757_, lean_object* v_entries_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_depth_1753_, v_keys_1754_, v_vals_1755_, v_i_1757_, v_entries_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1760_, lean_object* v_depth_1761_, lean_object* v_keys_1762_, lean_object* v_vals_1763_, lean_object* v_heq_1764_, lean_object* v_i_1765_, lean_object* v_entries_1766_){
_start:
{
size_t v_depth_boxed_1767_; lean_object* v_res_1768_; 
v_depth_boxed_1767_ = lean_unbox_usize(v_depth_1761_);
lean_dec(v_depth_1761_);
v_res_1768_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10(v_00_u03b2_1760_, v_depth_boxed_1767_, v_keys_1762_, v_vals_1763_, v_heq_1764_, v_i_1765_, v_entries_1766_);
lean_dec_ref(v_vals_1763_);
lean_dec_ref(v_keys_1762_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_1769_, lean_object* v_x_1770_, lean_object* v_x_1771_, lean_object* v_x_1772_, lean_object* v_x_1773_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(v_x_1770_, v_x_1771_, v_x_1772_, v_x_1773_);
return v___x_1774_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__0(void){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__1(void){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__0, &l_Lean_Compiler_LCNF_Code_cse___closed__0_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__0);
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
return v___x_1777_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__2(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = lean_box(0);
v___x_1779_ = lean_unsigned_to_nat(16u);
v___x_1780_ = lean_mk_array(v___x_1779_, v___x_1778_);
return v___x_1780_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__3(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__2, &l_Lean_Compiler_LCNF_Code_cse___closed__2_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__2);
v___x_1782_ = lean_unsigned_to_nat(0u);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v___x_1781_);
return v___x_1783_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__4(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__3, &l_Lean_Compiler_LCNF_Code_cse___closed__3_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__3);
v___x_1785_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__1, &l_Lean_Compiler_LCNF_Code_cse___closed__1_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__1);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
lean_ctor_set(v___x_1786_, 1, v___x_1784_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse(uint8_t v_shouldElimFunDecls_1787_, lean_object* v_code_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__4, &l_Lean_Compiler_LCNF_Code_cse___closed__4_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__4);
v___x_1795_ = lean_st_mk_ref(v___x_1794_);
v___x_1796_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1787_, v_code_1788_, v___x_1795_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1805_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1805_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1805_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1801_ = lean_st_ref_get(v___x_1795_);
lean_dec(v___x_1795_);
lean_dec(v___x_1801_);
if (v_isShared_1800_ == 0)
{
v___x_1803_ = v___x_1799_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1797_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
else
{
lean_dec(v___x_1795_);
return v___x_1796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse___boxed(lean_object* v_shouldElimFunDecls_1806_, lean_object* v_code_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1813_; lean_object* v_res_1814_; 
v_shouldElimFunDecls_boxed_1813_ = lean_unbox(v_shouldElimFunDecls_1806_);
v_res_1814_ = l_Lean_Compiler_LCNF_Code_cse(v_shouldElimFunDecls_boxed_1813_, v_code_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(lean_object* v_f_1815_, lean_object* v_v_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
if (lean_obj_tag(v_v_1816_) == 0)
{
lean_object* v_code_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1846_; 
v_code_1822_ = lean_ctor_get(v_v_1816_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_v_1816_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1824_ = v_v_1816_;
v_isShared_1825_ = v_isSharedCheck_1846_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_code_1822_);
lean_dec(v_v_1816_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1846_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; 
lean_inc(v___y_1820_);
lean_inc_ref(v___y_1819_);
lean_inc(v___y_1818_);
lean_inc_ref(v___y_1817_);
v___x_1826_ = lean_apply_6(v_f_1815_, v_code_1822_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, lean_box(0));
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1837_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1829_ = v___x_1826_;
v_isShared_1830_ = v_isSharedCheck_1837_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1826_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1837_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v_a_1827_);
v___x_1832_ = v___x_1824_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1834_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1832_);
v___x_1834_ = v___x_1829_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_del_object(v___x_1824_);
v_a_1838_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1826_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1826_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
else
{
lean_object* v___x_1847_; 
lean_dec_ref(v_f_1815_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_v_1816_);
return v___x_1847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg___boxed(lean_object* v_f_1848_, lean_object* v_v_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v_f_1848_, v_v_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0(uint8_t v_pu_1856_, lean_object* v_f_1857_, lean_object* v_v_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v_f_1857_, v_v_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___boxed(lean_object* v_pu_1865_, lean_object* v_f_1866_, lean_object* v_v_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
uint8_t v_pu_boxed_1873_; lean_object* v_res_1874_; 
v_pu_boxed_1873_ = lean_unbox(v_pu_1865_);
v_res_1874_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0(v_pu_boxed_1873_, v_f_1866_, v_v_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0(uint8_t v_shouldElimFunDecls_1875_, lean_object* v_x_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_Compiler_LCNF_Code_cse(v_shouldElimFunDecls_1875_, v_x_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed(lean_object* v_shouldElimFunDecls_1883_, lean_object* v_x_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1890_; lean_object* v_res_1891_; 
v_shouldElimFunDecls_boxed_1890_ = lean_unbox(v_shouldElimFunDecls_1883_);
v_res_1891_ = l_Lean_Compiler_LCNF_Decl_cse___lam__0(v_shouldElimFunDecls_boxed_1890_, v_x_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse(uint8_t v_shouldElimFunDecls_1892_, lean_object* v_decl_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v_toSignature_1899_; lean_object* v_value_1900_; uint8_t v_recursive_1901_; lean_object* v_inlineAttr_x3f_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1928_; 
v_toSignature_1899_ = lean_ctor_get(v_decl_1893_, 0);
v_value_1900_ = lean_ctor_get(v_decl_1893_, 1);
v_recursive_1901_ = lean_ctor_get_uint8(v_decl_1893_, sizeof(void*)*3);
v_inlineAttr_x3f_1902_ = lean_ctor_get(v_decl_1893_, 2);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_decl_1893_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1904_ = v_decl_1893_;
v_isShared_1905_ = v_isSharedCheck_1928_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_inlineAttr_x3f_1902_);
lean_inc(v_value_1900_);
lean_inc(v_toSignature_1899_);
lean_dec(v_decl_1893_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1928_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; lean_object* v___f_1907_; lean_object* v___x_1908_; 
v___x_1906_ = lean_box(v_shouldElimFunDecls_1892_);
v___f_1907_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1907_, 0, v___x_1906_);
v___x_1908_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v___f_1907_, v_value_1900_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1919_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1919_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1919_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 1, v_a_1909_);
v___x_1914_ = v___x_1904_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_toSignature_1899_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_a_1909_);
lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_inlineAttr_x3f_1902_);
lean_ctor_set_uint8(v_reuseFailAlloc_1918_, sizeof(void*)*3, v_recursive_1901_);
v___x_1914_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1916_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1914_);
v___x_1916_ = v___x_1911_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_del_object(v___x_1904_);
lean_dec(v_inlineAttr_x3f_1902_);
lean_dec_ref(v_toSignature_1899_);
v_a_1920_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1908_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1908_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___boxed(lean_object* v_shouldElimFunDecls_1929_, lean_object* v_decl_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1936_; lean_object* v_res_1937_; 
v_shouldElimFunDecls_boxed_1936_ = lean_unbox(v_shouldElimFunDecls_1929_);
v_res_1937_ = l_Lean_Compiler_LCNF_Decl_cse(v_shouldElimFunDecls_boxed_1936_, v_decl_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___lam__0(uint8_t v_shouldElimFunDecls_1941_, uint8_t v_phase_1942_, lean_object* v_occurrence_1943_, lean_object* v_h_1944_){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1945_ = ((lean_object*)(l_Lean_Compiler_LCNF_cse___lam__0___closed__1));
v___x_1946_ = lean_box(v_shouldElimFunDecls_1941_);
v___x_1947_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_cse___boxed), 7, 1);
lean_closure_set(v___x_1947_, 0, v___x_1946_);
v___x_1948_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1945_, v_phase_1942_, v___x_1947_, v_occurrence_1943_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___lam__0___boxed(lean_object* v_shouldElimFunDecls_1949_, lean_object* v_phase_1950_, lean_object* v_occurrence_1951_, lean_object* v_h_1952_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1953_; uint8_t v_phase_boxed_1954_; lean_object* v_res_1955_; 
v_shouldElimFunDecls_boxed_1953_ = lean_unbox(v_shouldElimFunDecls_1949_);
v_phase_boxed_1954_ = lean_unbox(v_phase_1950_);
v_res_1955_ = l_Lean_Compiler_LCNF_cse___lam__0(v_shouldElimFunDecls_boxed_1953_, v_phase_boxed_1954_, v_occurrence_1951_, v_h_1952_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse(uint8_t v_phase_1956_, uint8_t v_shouldElimFunDecls_1957_, lean_object* v_occurrence_1958_){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___f_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; lean_object* v___x_1964_; 
v___x_1959_ = lean_box(v_shouldElimFunDecls_1957_);
v___x_1960_ = lean_box(v_phase_1956_);
v___f_1961_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_cse___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1961_, 0, v___x_1959_);
lean_closure_set(v___f_1961_, 1, v___x_1960_);
lean_closure_set(v___f_1961_, 2, v_occurrence_1958_);
v___x_1962_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_1963_ = 0;
v___x_1964_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_1962_, v_phase_1956_, v___x_1963_, v___f_1961_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___boxed(lean_object* v_phase_1965_, lean_object* v_shouldElimFunDecls_1966_, lean_object* v_occurrence_1967_){
_start:
{
uint8_t v_phase_boxed_1968_; uint8_t v_shouldElimFunDecls_boxed_1969_; lean_object* v_res_1970_; 
v_phase_boxed_1968_ = lean_unbox(v_phase_1965_);
v_shouldElimFunDecls_boxed_1969_ = lean_unbox(v_shouldElimFunDecls_1966_);
v_res_1970_ = l_Lean_Compiler_LCNF_cse(v_phase_boxed_1968_, v_shouldElimFunDecls_boxed_1969_, v_occurrence_1967_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2041_; uint8_t v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2041_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_));
v___x_2042_ = 1;
v___x_2043_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_));
v___x_2044_ = l_Lean_registerTraceClass(v___x_2041_, v___x_2042_, v___x_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2____boxed(lean_object* v_a_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_();
return v_res_2046_;
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
