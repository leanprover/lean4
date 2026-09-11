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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
v___x_91_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_91_, 0, lean_box(0));
lean_closure_set(v___x_91_, 1, lean_box(0));
lean_closure_set(v___x_91_, 2, v___x_89_);
lean_closure_set(v___x_91_, 3, lean_box(0));
lean_closure_set(v___x_91_, 4, lean_box(0));
lean_closure_set(v___x_91_, 5, v___x_90_);
lean_closure_set(v___x_91_, 6, v___f_77_);
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
v___x_114_ = lean_st_ref_put(v___y_99_, v___x_113_);
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
v___x_170_ = lean_st_ref_put(v_a_157_, v___x_169_);
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
v___x_199_ = lean_st_ref_put(v_a_182_, v___x_198_);
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
v___x_224_ = lean_st_ref_put(v_a_213_, v___x_223_);
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
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v_nbuckets_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_370_ = lean_array_get_size(v_data_369_);
v___x_371_ = lean_unsigned_to_nat(2u);
v_nbuckets_372_ = lean_nat_mul(v___x_370_, v___x_371_);
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_box(0);
v___x_375_ = lean_mk_array(v_nbuckets_372_, v___x_374_);
v___x_376_ = lean_array_propagate_mark(v_data_369_, v___x_375_);
v___x_377_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2___redArg(v___x_373_, v_data_369_, v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(lean_object* v_a_378_, lean_object* v_b_379_, lean_object* v_x_380_){
_start:
{
if (lean_obj_tag(v_x_380_) == 0)
{
lean_dec(v_b_379_);
lean_dec(v_a_378_);
return v_x_380_;
}
else
{
lean_object* v_key_381_; lean_object* v_value_382_; lean_object* v_tail_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_395_; 
v_key_381_ = lean_ctor_get(v_x_380_, 0);
v_value_382_ = lean_ctor_get(v_x_380_, 1);
v_tail_383_ = lean_ctor_get(v_x_380_, 2);
v_isSharedCheck_395_ = !lean_is_exclusive(v_x_380_);
if (v_isSharedCheck_395_ == 0)
{
v___x_385_ = v_x_380_;
v_isShared_386_ = v_isSharedCheck_395_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_tail_383_);
lean_inc(v_value_382_);
lean_inc(v_key_381_);
lean_dec(v_x_380_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_395_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
uint8_t v___x_387_; 
v___x_387_ = l_Lean_instBEqFVarId_beq(v_key_381_, v_a_378_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(v_a_378_, v_b_379_, v_tail_383_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 2, v___x_388_);
v___x_390_ = v___x_385_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_key_381_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_value_382_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
else
{
lean_object* v___x_393_; 
lean_dec(v_value_382_);
lean_dec(v_key_381_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 1, v_b_379_);
lean_ctor_set(v___x_385_, 0, v_a_378_);
v___x_393_ = v___x_385_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_378_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_b_379_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v_tail_383_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(lean_object* v_a_396_, lean_object* v_x_397_){
_start:
{
if (lean_obj_tag(v_x_397_) == 0)
{
uint8_t v___x_398_; 
v___x_398_ = 0;
return v___x_398_;
}
else
{
lean_object* v_key_399_; lean_object* v_tail_400_; uint8_t v___x_401_; 
v_key_399_ = lean_ctor_get(v_x_397_, 0);
v_tail_400_ = lean_ctor_get(v_x_397_, 2);
v___x_401_ = l_Lean_instBEqFVarId_beq(v_key_399_, v_a_396_);
if (v___x_401_ == 0)
{
v_x_397_ = v_tail_400_;
goto _start;
}
else
{
return v___x_401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg___boxed(lean_object* v_a_403_, lean_object* v_x_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(v_a_403_, v_x_404_);
lean_dec(v_x_404_);
lean_dec(v_a_403_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(lean_object* v_m_407_, lean_object* v_a_408_, lean_object* v_b_409_){
_start:
{
lean_object* v_size_410_; lean_object* v_buckets_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_454_; 
v_size_410_ = lean_ctor_get(v_m_407_, 0);
v_buckets_411_ = lean_ctor_get(v_m_407_, 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v_m_407_);
if (v_isSharedCheck_454_ == 0)
{
v___x_413_ = v_m_407_;
v_isShared_414_ = v_isSharedCheck_454_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_buckets_411_);
lean_inc(v_size_410_);
lean_dec(v_m_407_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_454_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; uint64_t v___x_416_; uint64_t v___x_417_; uint64_t v___x_418_; uint64_t v_fold_419_; uint64_t v___x_420_; uint64_t v___x_421_; uint64_t v___x_422_; size_t v___x_423_; size_t v___x_424_; size_t v___x_425_; size_t v___x_426_; size_t v___x_427_; lean_object* v_bkt_428_; uint8_t v___x_429_; 
v___x_415_ = lean_array_get_size(v_buckets_411_);
v___x_416_ = l_Lean_instHashableFVarId_hash(v_a_408_);
v___x_417_ = 32ULL;
v___x_418_ = lean_uint64_shift_right(v___x_416_, v___x_417_);
v_fold_419_ = lean_uint64_xor(v___x_416_, v___x_418_);
v___x_420_ = 16ULL;
v___x_421_ = lean_uint64_shift_right(v_fold_419_, v___x_420_);
v___x_422_ = lean_uint64_xor(v_fold_419_, v___x_421_);
v___x_423_ = lean_uint64_to_usize(v___x_422_);
v___x_424_ = lean_usize_of_nat(v___x_415_);
v___x_425_ = ((size_t)1ULL);
v___x_426_ = lean_usize_sub(v___x_424_, v___x_425_);
v___x_427_ = lean_usize_land(v___x_423_, v___x_426_);
v_bkt_428_ = lean_array_uget_borrowed(v_buckets_411_, v___x_427_);
v___x_429_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(v_a_408_, v_bkt_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v_size_x27_431_; lean_object* v___x_432_; lean_object* v_buckets_x27_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_430_ = lean_unsigned_to_nat(1u);
v_size_x27_431_ = lean_nat_add(v_size_410_, v___x_430_);
lean_dec(v_size_410_);
lean_inc(v_bkt_428_);
v___x_432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_432_, 0, v_a_408_);
lean_ctor_set(v___x_432_, 1, v_b_409_);
lean_ctor_set(v___x_432_, 2, v_bkt_428_);
v_buckets_x27_433_ = lean_array_uset(v_buckets_411_, v___x_427_, v___x_432_);
v___x_434_ = lean_unsigned_to_nat(4u);
v___x_435_ = lean_nat_mul(v_size_x27_431_, v___x_434_);
v___x_436_ = lean_unsigned_to_nat(3u);
v___x_437_ = lean_nat_div(v___x_435_, v___x_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_array_get_size(v_buckets_x27_433_);
v___x_439_ = lean_nat_dec_le(v___x_437_, v___x_438_);
lean_dec(v___x_437_);
if (v___x_439_ == 0)
{
lean_object* v_val_440_; lean_object* v___x_442_; 
v_val_440_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1___redArg(v_buckets_x27_433_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v_val_440_);
lean_ctor_set(v___x_413_, 0, v_size_x27_431_);
v___x_442_ = v___x_413_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_size_x27_431_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_val_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
else
{
lean_object* v___x_445_; 
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v_buckets_x27_433_);
lean_ctor_set(v___x_413_, 0, v_size_x27_431_);
v___x_445_ = v___x_413_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_size_x27_431_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_buckets_x27_433_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
else
{
lean_object* v___x_447_; lean_object* v_buckets_x27_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
lean_inc(v_bkt_428_);
v___x_447_ = lean_box(0);
v_buckets_x27_448_ = lean_array_uset(v_buckets_411_, v___x_427_, v___x_447_);
v___x_449_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(v_a_408_, v_b_409_, v_bkt_428_);
v___x_450_ = lean_array_uset(v_buckets_x27_448_, v___x_427_, v___x_449_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v___x_450_);
v___x_452_ = v___x_413_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_size_410_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(lean_object* v_decl_455_, lean_object* v_fvarId_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
uint8_t v___x_460_; lean_object* v___x_461_; 
v___x_460_ = 0;
v___x_461_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_460_, v_decl_455_, v_a_458_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_483_; 
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v___x_461_, 0);
lean_dec(v_unused_484_);
v___x_463_ = v___x_461_;
v_isShared_464_ = v_isSharedCheck_483_;
goto v_resetjp_462_;
}
else
{
lean_dec(v___x_461_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_483_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v_fvarId_466_; lean_object* v_map_467_; lean_object* v_subst_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_482_; 
v___x_465_ = lean_st_ref_take(v_a_457_);
v_fvarId_466_ = lean_ctor_get(v_decl_455_, 0);
lean_inc(v_fvarId_466_);
lean_dec_ref(v_decl_455_);
v_map_467_ = lean_ctor_get(v___x_465_, 0);
v_subst_468_ = lean_ctor_get(v___x_465_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_482_ == 0)
{
v___x_470_ = v___x_465_;
v_isShared_471_ = v_isSharedCheck_482_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_subst_468_);
lean_inc(v_map_467_);
lean_dec(v___x_465_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_482_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v_fvarId_456_);
v___x_473_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(v_subst_468_, v_fvarId_466_, v___x_472_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 1, v___x_473_);
v___x_475_ = v___x_470_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_map_467_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v___x_473_);
v___x_475_ = v_reuseFailAlloc_481_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_476_ = lean_st_ref_put(v_a_457_, v___x_475_);
v___x_477_ = lean_box(0);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_477_);
v___x_479_ = v___x_463_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_456_);
lean_dec_ref(v_decl_455_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___redArg___boxed(lean_object* v_decl_485_, lean_object* v_fvarId_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(v_decl_485_, v_fvarId_486_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec(v_a_487_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet(lean_object* v_decl_491_, lean_object* v_fvarId_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(v_decl_491_, v_fvarId_492_, v_a_493_, v_a_495_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___boxed(lean_object* v_decl_500_, lean_object* v_fvarId_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Compiler_LCNF_CSE_replaceLet(v_decl_500_, v_fvarId_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0(lean_object* v_00_u03b2_509_, lean_object* v_m_510_, lean_object* v_a_511_, lean_object* v_b_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(v_m_510_, v_a_511_, v_b_512_);
return v___x_513_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0(lean_object* v_00_u03b2_514_, lean_object* v_a_515_, lean_object* v_x_516_){
_start:
{
uint8_t v___x_517_; 
v___x_517_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(v_a_515_, v_x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___boxed(lean_object* v_00_u03b2_518_, lean_object* v_a_519_, lean_object* v_x_520_){
_start:
{
uint8_t v_res_521_; lean_object* v_r_522_; 
v_res_521_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0(v_00_u03b2_518_, v_a_519_, v_x_520_);
lean_dec(v_x_520_);
lean_dec(v_a_519_);
v_r_522_ = lean_box(v_res_521_);
return v_r_522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1(lean_object* v_00_u03b2_523_, lean_object* v_data_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1___redArg(v_data_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2(lean_object* v_00_u03b2_526_, lean_object* v_a_527_, lean_object* v_b_528_, lean_object* v_x_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(v_a_527_, v_b_528_, v_x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_531_, lean_object* v_i_532_, lean_object* v_source_533_, lean_object* v_target_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2___redArg(v_i_532_, v_source_533_, v_target_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_536_, lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3___redArg(v_x_537_, v_x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(lean_object* v_decl_540_, lean_object* v_fvarId_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
uint8_t v___x_545_; uint8_t v___x_546_; lean_object* v___x_547_; 
v___x_545_ = 0;
v___x_546_ = 1;
v___x_547_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_545_, v_decl_540_, v___x_546_, v_a_543_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_569_; 
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; 
v_unused_570_ = lean_ctor_get(v___x_547_, 0);
lean_dec(v_unused_570_);
v___x_549_ = v___x_547_;
v_isShared_550_ = v_isSharedCheck_569_;
goto v_resetjp_548_;
}
else
{
lean_dec(v___x_547_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_569_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v_fvarId_551_; lean_object* v___x_552_; lean_object* v_map_553_; lean_object* v_subst_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_568_; 
v_fvarId_551_ = lean_ctor_get(v_decl_540_, 0);
lean_inc(v_fvarId_551_);
lean_dec_ref(v_decl_540_);
v___x_552_ = lean_st_ref_take(v_a_542_);
v_map_553_ = lean_ctor_get(v___x_552_, 0);
v_subst_554_ = lean_ctor_get(v___x_552_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_568_ == 0)
{
v___x_556_ = v___x_552_;
v_isShared_557_ = v_isSharedCheck_568_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_subst_554_);
lean_inc(v_map_553_);
lean_dec(v___x_552_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_568_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v_fvarId_541_);
v___x_559_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(v_subst_554_, v_fvarId_551_, v___x_558_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 1, v___x_559_);
v___x_561_ = v___x_556_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_map_553_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v___x_559_);
v___x_561_ = v_reuseFailAlloc_567_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_562_ = lean_st_ref_put(v_a_542_, v___x_561_);
v___x_563_ = lean_box(0);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_563_);
v___x_565_ = v___x_549_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_541_);
lean_dec_ref(v_decl_540_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___redArg___boxed(lean_object* v_decl_571_, lean_object* v_fvarId_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(v_decl_571_, v_fvarId_572_, v_a_573_, v_a_574_);
lean_dec(v_a_574_);
lean_dec(v_a_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun(lean_object* v_decl_577_, lean_object* v_fvarId_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(v_decl_577_, v_fvarId_578_, v_a_579_, v_a_581_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___boxed(lean_object* v_decl_586_, lean_object* v_fvarId_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_Compiler_LCNF_CSE_replaceFun(v_decl_586_, v_fvarId_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec(v_a_588_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(lean_object* v_v_595_, lean_object* v_a_596_){
_start:
{
switch(lean_obj_tag(v_v_595_))
{
case 0:
{
lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_606_; 
v_isSharedCheck_606_ = !lean_is_exclusive(v_v_595_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v_v_595_, 0);
lean_dec(v_unused_607_);
v___x_599_ = v_v_595_;
v_isShared_600_ = v_isSharedCheck_606_;
goto v_resetjp_598_;
}
else
{
lean_dec(v_v_595_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_606_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
uint8_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_601_ = 0;
v___x_602_ = lean_box(v___x_601_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_602_);
v___x_604_ = v___x_599_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
case 3:
{
lean_object* v_declName_608_; lean_object* v___x_609_; lean_object* v_env_610_; uint8_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_declName_608_ = lean_ctor_get(v_v_595_, 0);
lean_inc(v_declName_608_);
lean_dec_ref_known(v_v_595_, 3);
v___x_609_ = lean_st_ref_get(v_a_596_);
v_env_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc_ref(v_env_610_);
lean_dec(v___x_609_);
v___x_611_ = l_Lean_hasNeverExtractAttribute(v_env_610_, v_declName_608_);
v___x_612_ = lean_box(v___x_611_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
default: 
{
uint8_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
lean_dec(v_v_595_);
v___x_614_ = 0;
v___x_615_ = lean_box(v___x_614_);
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
return v___x_616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg___boxed(lean_object* v_v_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(v_v_617_, v_a_618_);
lean_dec(v_a_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract(lean_object* v_v_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(v_v_621_, v_a_625_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_hasNeverExtract___boxed(lean_object* v_v_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract(v_v_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(lean_object* v_a_635_, lean_object* v_map_636_, lean_object* v_a_x3f_637_){
_start:
{
lean_object* v___x_639_; lean_object* v_subst_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_650_; 
v___x_639_ = lean_st_ref_take(v_a_635_);
v_subst_640_ = lean_ctor_get(v___x_639_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v___x_639_, 0);
lean_dec(v_unused_651_);
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_650_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_subst_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_650_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v_map_636_);
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_map_636_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_subst_640_);
v___x_645_ = v_reuseFailAlloc_649_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = lean_st_ref_put(v_a_635_, v___x_645_);
v___x_647_ = lean_box(0);
v___x_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
return v___x_648_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0___boxed(lean_object* v_a_652_, lean_object* v_map_653_, lean_object* v_a_x3f_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(v_a_652_, v_map_653_, v_a_x3f_654_);
lean_dec(v_a_x3f_654_);
lean_dec(v_a_652_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(uint8_t v_pu_657_, uint8_t v_t_658_, lean_object* v_args_659_, lean_object* v___y_660_){
_start:
{
lean_object* v___x_662_; lean_object* v_subst_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_662_ = lean_st_ref_get(v___y_660_);
v_subst_663_ = lean_ctor_get(v___x_662_, 1);
lean_inc_ref(v_subst_663_);
lean_dec(v___x_662_);
v___x_664_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_657_, v_subst_663_, v_args_659_, v_t_658_);
lean_dec_ref(v_subst_663_);
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg___boxed(lean_object* v_pu_666_, lean_object* v_t_667_, lean_object* v_args_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
uint8_t v_pu_boxed_671_; uint8_t v_t_boxed_672_; lean_object* v_res_673_; 
v_pu_boxed_671_ = lean_unbox(v_pu_666_);
v_t_boxed_672_ = lean_unbox(v_t_667_);
v_res_673_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v_pu_boxed_671_, v_t_boxed_672_, v_args_668_, v___y_669_);
lean_dec(v___y_669_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(uint8_t v_pu_674_, uint8_t v_t_675_, lean_object* v_decl_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_type_680_; lean_object* v_value_681_; lean_object* v___x_682_; lean_object* v_subst_683_; lean_object* v___x_684_; lean_object* v_subst_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_type_680_ = lean_ctor_get(v_decl_676_, 2);
v_value_681_ = lean_ctor_get(v_decl_676_, 3);
v___x_682_ = lean_st_ref_get(v___y_677_);
v_subst_683_ = lean_ctor_get(v___x_682_, 1);
lean_inc_ref(v_subst_683_);
lean_dec(v___x_682_);
v___x_684_ = lean_st_ref_get(v___y_677_);
v_subst_685_ = lean_ctor_get(v___x_684_, 1);
lean_inc_ref(v_subst_685_);
lean_dec(v___x_684_);
lean_inc_ref(v_type_680_);
v___x_686_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_674_, v_subst_683_, v_t_675_, v_type_680_);
lean_dec_ref(v_subst_683_);
lean_inc(v_value_681_);
v___x_687_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_674_, v_subst_685_, v_value_681_, v_t_675_);
lean_dec_ref(v_subst_685_);
v___x_688_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_674_, v_decl_676_, v___x_686_, v___x_687_, v___y_678_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg___boxed(lean_object* v_pu_689_, lean_object* v_t_690_, lean_object* v_decl_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
uint8_t v_pu_boxed_695_; uint8_t v_t_boxed_696_; lean_object* v_res_697_; 
v_pu_boxed_695_ = lean_unbox(v_pu_689_);
v_t_boxed_696_ = lean_unbox(v_t_690_);
v_res_697_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v_pu_boxed_695_, v_t_boxed_696_, v_decl_691_, v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec(v___y_692_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(lean_object* v___y_698_, lean_object* v_map_699_, lean_object* v_a_x3f_700_){
_start:
{
lean_object* v___x_702_; lean_object* v_subst_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_713_; 
v___x_702_ = lean_st_ref_take(v___y_698_);
v_subst_703_ = lean_ctor_get(v___x_702_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; 
v_unused_714_ = lean_ctor_get(v___x_702_, 0);
lean_dec(v_unused_714_);
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_713_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_subst_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_713_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v_map_699_);
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_map_699_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_subst_703_);
v___x_708_ = v_reuseFailAlloc_712_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_709_ = lean_st_ref_put(v___y_698_, v___x_708_);
v___x_710_ = lean_box(0);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0___boxed(lean_object* v___y_715_, lean_object* v_map_716_, lean_object* v_a_x3f_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_715_, v_map_716_, v_a_x3f_717_);
lean_dec(v_a_x3f_717_);
lean_dec(v___y_715_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(uint8_t v_pu_720_, uint8_t v_t_721_, lean_object* v_i_722_, lean_object* v_as_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = lean_array_get_size(v_as_723_);
v___x_728_ = lean_nat_dec_lt(v_i_722_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
lean_dec(v_i_722_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v_as_723_);
return v___x_729_;
}
else
{
lean_object* v_a_730_; lean_object* v_type_731_; lean_object* v___x_732_; lean_object* v_subst_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_a_730_ = lean_array_fget_borrowed(v_as_723_, v_i_722_);
v_type_731_ = lean_ctor_get(v_a_730_, 2);
v___x_732_ = lean_st_ref_get(v___y_724_);
v_subst_733_ = lean_ctor_get(v___x_732_, 1);
lean_inc_ref(v_subst_733_);
lean_dec(v___x_732_);
lean_inc_ref(v_type_731_);
v___x_734_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_720_, v_subst_733_, v_t_721_, v_type_731_);
lean_dec_ref(v_subst_733_);
lean_inc(v_a_730_);
v___x_735_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_720_, v_a_730_, v___x_734_, v___y_725_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; size_t v___x_737_; size_t v___x_738_; uint8_t v___x_739_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = lean_ptr_addr(v_a_730_);
v___x_738_ = lean_ptr_addr(v_a_736_);
v___x_739_ = lean_usize_dec_eq(v___x_737_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_add(v_i_722_, v___x_740_);
v___x_742_ = lean_array_fset(v_as_723_, v_i_722_, v_a_736_);
lean_dec(v_i_722_);
v_i_722_ = v___x_741_;
v_as_723_ = v___x_742_;
goto _start;
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; 
lean_dec(v_a_736_);
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = lean_nat_add(v_i_722_, v___x_744_);
lean_dec(v_i_722_);
v_i_722_ = v___x_745_;
goto _start;
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec_ref(v_as_723_);
lean_dec(v_i_722_);
v_a_747_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_735_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_735_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg___boxed(lean_object* v_pu_755_, lean_object* v_t_756_, lean_object* v_i_757_, lean_object* v_as_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
uint8_t v_pu_boxed_762_; uint8_t v_t_boxed_763_; lean_object* v_res_764_; 
v_pu_boxed_762_ = lean_unbox(v_pu_755_);
v_t_boxed_763_ = lean_unbox(v_t_756_);
v_res_764_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(v_pu_boxed_762_, v_t_boxed_763_, v_i_757_, v_as_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec(v___y_759_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(uint8_t v_pu_765_, uint8_t v_t_766_, lean_object* v_ps_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(v_pu_765_, v_t_766_, v___x_774_, v_ps_767_, v___y_768_, v___y_770_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___boxed(lean_object* v_pu_776_, lean_object* v_t_777_, lean_object* v_ps_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
uint8_t v_pu_boxed_785_; uint8_t v_t_boxed_786_; lean_object* v_res_787_; 
v_pu_boxed_785_ = lean_unbox(v_pu_776_);
v_t_boxed_786_ = lean_unbox(v_t_777_);
v_res_787_ = l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(v_pu_boxed_785_, v_t_boxed_786_, v_ps_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(lean_object* v_keys_788_, lean_object* v_vals_789_, lean_object* v_i_790_, lean_object* v_k_791_){
_start:
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = lean_array_get_size(v_keys_788_);
v___x_793_ = lean_nat_dec_lt(v_i_790_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
lean_dec(v_i_790_);
v___x_794_ = lean_box(0);
return v___x_794_;
}
else
{
lean_object* v_k_x27_795_; uint8_t v___x_796_; 
v_k_x27_795_ = lean_array_fget_borrowed(v_keys_788_, v_i_790_);
v___x_796_ = lean_expr_eqv(v_k_791_, v_k_x27_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_unsigned_to_nat(1u);
v___x_798_ = lean_nat_add(v_i_790_, v___x_797_);
lean_dec(v_i_790_);
v_i_790_ = v___x_798_;
goto _start;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_array_fget_borrowed(v_vals_789_, v_i_790_);
lean_dec(v_i_790_);
lean_inc(v___x_800_);
v___x_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_keys_802_, lean_object* v_vals_803_, lean_object* v_i_804_, lean_object* v_k_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(v_keys_802_, v_vals_803_, v_i_804_, v_k_805_);
lean_dec_ref(v_k_805_);
lean_dec_ref(v_vals_803_);
lean_dec_ref(v_keys_802_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(lean_object* v_x_807_, size_t v_x_808_, lean_object* v_x_809_){
_start:
{
if (lean_obj_tag(v_x_807_) == 0)
{
lean_object* v_es_810_; lean_object* v___x_811_; size_t v___x_812_; size_t v___x_813_; lean_object* v_j_814_; lean_object* v___x_815_; 
v_es_810_ = lean_ctor_get(v_x_807_, 0);
v___x_811_ = lean_box(2);
v___x_812_ = ((size_t)31ULL);
v___x_813_ = lean_usize_land(v_x_808_, v___x_812_);
v_j_814_ = lean_usize_to_nat(v___x_813_);
v___x_815_ = lean_array_get_borrowed(v___x_811_, v_es_810_, v_j_814_);
lean_dec(v_j_814_);
switch(lean_obj_tag(v___x_815_))
{
case 0:
{
lean_object* v_key_816_; lean_object* v_val_817_; uint8_t v___x_818_; 
v_key_816_ = lean_ctor_get(v___x_815_, 0);
v_val_817_ = lean_ctor_get(v___x_815_, 1);
v___x_818_ = lean_expr_eqv(v_x_809_, v_key_816_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; 
v___x_819_ = lean_box(0);
return v___x_819_;
}
else
{
lean_object* v___x_820_; 
lean_inc(v_val_817_);
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v_val_817_);
return v___x_820_;
}
}
case 1:
{
lean_object* v_node_821_; size_t v___x_822_; size_t v___x_823_; 
v_node_821_ = lean_ctor_get(v___x_815_, 0);
v___x_822_ = ((size_t)5ULL);
v___x_823_ = lean_usize_shift_right(v_x_808_, v___x_822_);
v_x_807_ = v_node_821_;
v_x_808_ = v___x_823_;
goto _start;
}
default: 
{
lean_object* v___x_825_; 
v___x_825_ = lean_box(0);
return v___x_825_;
}
}
}
else
{
lean_object* v_ks_826_; lean_object* v_vs_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_ks_826_ = lean_ctor_get(v_x_807_, 0);
v_vs_827_ = lean_ctor_get(v_x_807_, 1);
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(v_ks_826_, v_vs_827_, v___x_828_, v_x_809_);
return v___x_829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___boxed(lean_object* v_x_830_, lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
size_t v_x_15480__boxed_833_; lean_object* v_res_834_; 
v_x_15480__boxed_833_ = lean_unbox_usize(v_x_831_);
lean_dec(v_x_831_);
v_res_834_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_830_, v_x_15480__boxed_833_, v_x_832_);
lean_dec_ref(v_x_832_);
lean_dec_ref(v_x_830_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(lean_object* v_x_835_, lean_object* v_x_836_){
_start:
{
uint64_t v___x_837_; size_t v___x_838_; lean_object* v___x_839_; 
v___x_837_ = l_Lean_Expr_hash(v_x_836_);
v___x_838_ = lean_uint64_to_usize(v___x_837_);
v___x_839_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_835_, v___x_838_, v_x_836_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg___boxed(lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_x_840_, v_x_841_);
lean_dec_ref(v_x_841_);
lean_dec_ref(v_x_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
lean_object* v_ks_847_; lean_object* v_vs_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_872_; 
v_ks_847_ = lean_ctor_get(v_x_843_, 0);
v_vs_848_ = lean_ctor_get(v_x_843_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v_x_843_);
if (v_isSharedCheck_872_ == 0)
{
v___x_850_ = v_x_843_;
v_isShared_851_ = v_isSharedCheck_872_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_vs_848_);
lean_inc(v_ks_847_);
lean_dec(v_x_843_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_872_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_852_ = lean_array_get_size(v_ks_847_);
v___x_853_ = lean_nat_dec_lt(v_x_844_, v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
lean_dec(v_x_844_);
v___x_854_ = lean_array_push(v_ks_847_, v_x_845_);
v___x_855_ = lean_array_push(v_vs_848_, v_x_846_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v___x_855_);
lean_ctor_set(v___x_850_, 0, v___x_854_);
v___x_857_ = v___x_850_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
else
{
lean_object* v_k_x27_859_; uint8_t v___x_860_; 
v_k_x27_859_ = lean_array_fget_borrowed(v_ks_847_, v_x_844_);
v___x_860_ = lean_expr_eqv(v_x_845_, v_k_x27_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_862_; 
if (v_isShared_851_ == 0)
{
v___x_862_ = v___x_850_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_ks_847_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_vs_848_);
v___x_862_ = v_reuseFailAlloc_866_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_unsigned_to_nat(1u);
v___x_864_ = lean_nat_add(v_x_844_, v___x_863_);
lean_dec(v_x_844_);
v_x_843_ = v___x_862_;
v_x_844_ = v___x_864_;
goto _start;
}
}
else
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_867_ = lean_array_fset(v_ks_847_, v_x_844_, v_x_845_);
v___x_868_ = lean_array_fset(v_vs_848_, v_x_844_, v_x_846_);
lean_dec(v_x_844_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v___x_868_);
lean_ctor_set(v___x_850_, 0, v___x_867_);
v___x_870_ = v___x_850_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(lean_object* v_n_873_, lean_object* v_k_874_, lean_object* v_v_875_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(v_n_873_, v___x_876_, v_k_874_, v_v_875_);
return v___x_877_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(lean_object* v_x_879_, size_t v_x_880_, size_t v_x_881_, lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
if (lean_obj_tag(v_x_879_) == 0)
{
lean_object* v_es_884_; size_t v___x_885_; size_t v___x_886_; lean_object* v_j_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v_es_884_ = lean_ctor_get(v_x_879_, 0);
v___x_885_ = ((size_t)31ULL);
v___x_886_ = lean_usize_land(v_x_880_, v___x_885_);
v_j_887_ = lean_usize_to_nat(v___x_886_);
v___x_888_ = lean_array_get_size(v_es_884_);
v___x_889_ = lean_nat_dec_lt(v_j_887_, v___x_888_);
if (v___x_889_ == 0)
{
lean_dec(v_j_887_);
lean_dec(v_x_883_);
lean_dec_ref(v_x_882_);
return v_x_879_;
}
else
{
lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_928_; 
lean_inc_ref(v_es_884_);
v_isSharedCheck_928_ = !lean_is_exclusive(v_x_879_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v_x_879_, 0);
lean_dec(v_unused_929_);
v___x_891_ = v_x_879_;
v_isShared_892_ = v_isSharedCheck_928_;
goto v_resetjp_890_;
}
else
{
lean_dec(v_x_879_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_928_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v_v_893_; lean_object* v___x_894_; lean_object* v_xs_x27_895_; lean_object* v___y_897_; 
v_v_893_ = lean_array_fget(v_es_884_, v_j_887_);
v___x_894_ = lean_box(0);
v_xs_x27_895_ = lean_array_fset(v_es_884_, v_j_887_, v___x_894_);
switch(lean_obj_tag(v_v_893_))
{
case 0:
{
lean_object* v_key_902_; lean_object* v_val_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_913_; 
v_key_902_ = lean_ctor_get(v_v_893_, 0);
v_val_903_ = lean_ctor_get(v_v_893_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v_v_893_);
if (v_isSharedCheck_913_ == 0)
{
v___x_905_ = v_v_893_;
v_isShared_906_ = v_isSharedCheck_913_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_val_903_);
lean_inc(v_key_902_);
lean_dec(v_v_893_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_913_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
uint8_t v___x_907_; 
v___x_907_ = lean_expr_eqv(v_x_882_, v_key_902_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; 
lean_del_object(v___x_905_);
v___x_908_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_902_, v_val_903_, v_x_882_, v_x_883_);
v___x_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
v___y_897_ = v___x_909_;
goto v___jp_896_;
}
else
{
lean_object* v___x_911_; 
lean_dec(v_val_903_);
lean_dec(v_key_902_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 1, v_x_883_);
lean_ctor_set(v___x_905_, 0, v_x_882_);
v___x_911_ = v___x_905_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_x_882_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_x_883_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
v___y_897_ = v___x_911_;
goto v___jp_896_;
}
}
}
}
case 1:
{
lean_object* v_node_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_926_; 
v_node_914_ = lean_ctor_get(v_v_893_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v_v_893_);
if (v_isSharedCheck_926_ == 0)
{
v___x_916_ = v_v_893_;
v_isShared_917_ = v_isSharedCheck_926_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_node_914_);
lean_dec(v_v_893_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_926_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
size_t v___x_918_; size_t v___x_919_; size_t v___x_920_; size_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_918_ = ((size_t)5ULL);
v___x_919_ = lean_usize_shift_right(v_x_880_, v___x_918_);
v___x_920_ = ((size_t)1ULL);
v___x_921_ = lean_usize_add(v_x_881_, v___x_920_);
v___x_922_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_node_914_, v___x_919_, v___x_921_, v_x_882_, v_x_883_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_922_);
v___x_924_ = v___x_916_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
v___y_897_ = v___x_924_;
goto v___jp_896_;
}
}
}
default: 
{
lean_object* v___x_927_; 
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v_x_882_);
lean_ctor_set(v___x_927_, 1, v_x_883_);
v___y_897_ = v___x_927_;
goto v___jp_896_;
}
}
v___jp_896_:
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = lean_array_fset(v_xs_x27_895_, v_j_887_, v___y_897_);
lean_dec(v_j_887_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_898_);
v___x_900_ = v___x_891_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
else
{
lean_object* v_ks_930_; lean_object* v_vs_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_949_; 
v_ks_930_ = lean_ctor_get(v_x_879_, 0);
v_vs_931_ = lean_ctor_get(v_x_879_, 1);
v_isSharedCheck_949_ = !lean_is_exclusive(v_x_879_);
if (v_isSharedCheck_949_ == 0)
{
v___x_933_ = v_x_879_;
v_isShared_934_ = v_isSharedCheck_949_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_vs_931_);
lean_inc(v_ks_930_);
lean_dec(v_x_879_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_949_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_ks_930_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_vs_931_);
v___x_936_ = v_reuseFailAlloc_948_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v_newNode_937_; size_t v___x_938_; uint8_t v___x_939_; 
v_newNode_937_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(v___x_936_, v_x_882_, v_x_883_);
v___x_938_ = ((size_t)7ULL);
v___x_939_ = lean_usize_dec_le(v___x_938_, v_x_881_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_940_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_937_);
v___x_941_ = lean_unsigned_to_nat(4u);
v___x_942_ = lean_nat_dec_lt(v___x_940_, v___x_941_);
lean_dec(v___x_940_);
if (v___x_942_ == 0)
{
lean_object* v_ks_943_; lean_object* v_vs_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v_ks_943_ = lean_ctor_get(v_newNode_937_, 0);
lean_inc_ref(v_ks_943_);
v_vs_944_ = lean_ctor_get(v_newNode_937_, 1);
lean_inc_ref(v_vs_944_);
lean_dec_ref(v_newNode_937_);
v___x_945_ = lean_unsigned_to_nat(0u);
v___x_946_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0);
v___x_947_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_x_881_, v_ks_943_, v_vs_944_, v___x_945_, v___x_946_);
lean_dec_ref(v_vs_944_);
lean_dec_ref(v_ks_943_);
return v___x_947_;
}
else
{
return v_newNode_937_;
}
}
else
{
return v_newNode_937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(size_t v_depth_950_, lean_object* v_keys_951_, lean_object* v_vals_952_, lean_object* v_i_953_, lean_object* v_entries_954_){
_start:
{
lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_955_ = lean_array_get_size(v_keys_951_);
v___x_956_ = lean_nat_dec_lt(v_i_953_, v___x_955_);
if (v___x_956_ == 0)
{
lean_dec(v_i_953_);
return v_entries_954_;
}
else
{
lean_object* v_k_957_; lean_object* v_v_958_; uint64_t v___x_959_; size_t v_h_960_; size_t v___x_961_; lean_object* v___x_962_; size_t v___x_963_; size_t v___x_964_; size_t v___x_965_; size_t v_h_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_k_957_ = lean_array_fget_borrowed(v_keys_951_, v_i_953_);
v_v_958_ = lean_array_fget_borrowed(v_vals_952_, v_i_953_);
v___x_959_ = l_Lean_Expr_hash(v_k_957_);
v_h_960_ = lean_uint64_to_usize(v___x_959_);
v___x_961_ = ((size_t)5ULL);
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = ((size_t)1ULL);
v___x_964_ = lean_usize_sub(v_depth_950_, v___x_963_);
v___x_965_ = lean_usize_mul(v___x_961_, v___x_964_);
v_h_966_ = lean_usize_shift_right(v_h_960_, v___x_965_);
v___x_967_ = lean_nat_add(v_i_953_, v___x_962_);
lean_dec(v_i_953_);
lean_inc(v_v_958_);
lean_inc(v_k_957_);
v___x_968_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_entries_954_, v_h_966_, v_depth_950_, v_k_957_, v_v_958_);
v_i_953_ = v___x_967_;
v_entries_954_ = v___x_968_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_depth_970_, lean_object* v_keys_971_, lean_object* v_vals_972_, lean_object* v_i_973_, lean_object* v_entries_974_){
_start:
{
size_t v_depth_boxed_975_; lean_object* v_res_976_; 
v_depth_boxed_975_ = lean_unbox_usize(v_depth_970_);
lean_dec(v_depth_970_);
v_res_976_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_depth_boxed_975_, v_keys_971_, v_vals_972_, v_i_973_, v_entries_974_);
lean_dec_ref(v_vals_972_);
lean_dec_ref(v_keys_971_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___boxed(lean_object* v_x_977_, lean_object* v_x_978_, lean_object* v_x_979_, lean_object* v_x_980_, lean_object* v_x_981_){
_start:
{
size_t v_x_15615__boxed_982_; size_t v_x_15616__boxed_983_; lean_object* v_res_984_; 
v_x_15615__boxed_982_ = lean_unbox_usize(v_x_978_);
lean_dec(v_x_978_);
v_x_15616__boxed_983_ = lean_unbox_usize(v_x_979_);
lean_dec(v_x_979_);
v_res_984_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_977_, v_x_15615__boxed_982_, v_x_15616__boxed_983_, v_x_980_, v_x_981_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
uint64_t v___x_988_; size_t v___x_989_; size_t v___x_990_; lean_object* v___x_991_; 
v___x_988_ = l_Lean_Expr_hash(v_x_986_);
v___x_989_ = lean_uint64_to_usize(v___x_988_);
v___x_990_ = ((size_t)1ULL);
v___x_991_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_985_, v___x_989_, v___x_990_, v_x_986_, v_x_987_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(uint8_t v_shouldElimFunDecls_994_, lean_object* v_i_995_, lean_object* v_as_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = lean_array_get_size(v_as_996_);
v___x_1004_ = lean_nat_dec_lt(v_i_995_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; 
lean_dec(v_i_995_);
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v_as_996_);
return v___x_1005_;
}
else
{
lean_object* v_a_1006_; lean_object* v_a_1008_; 
v_a_1006_ = lean_array_fget_borrowed(v_as_996_, v_i_995_);
if (lean_obj_tag(v_a_1006_) == 0)
{
lean_object* v_params_1019_; lean_object* v_code_1020_; lean_object* v___x_1021_; lean_object* v_map_1022_; uint8_t v___x_1023_; uint8_t v___x_1024_; lean_object* v_a_1026_; lean_object* v___x_1045_; 
v_params_1019_ = lean_ctor_get(v_a_1006_, 1);
v_code_1020_ = lean_ctor_get(v_a_1006_, 2);
v___x_1021_ = lean_st_ref_get(v___y_997_);
v_map_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc_ref(v_map_1022_);
lean_dec(v___x_1021_);
v___x_1023_ = 0;
v___x_1024_ = 0;
lean_inc_ref(v_params_1019_);
v___x_1045_ = l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(v___x_1023_, v___x_1024_, v_params_1019_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1047_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
lean_inc_ref(v_code_1020_);
v___x_1047_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_994_, v_code_1020_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1065_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1050_ = v___x_1047_;
v_isShared_1051_ = v_isSharedCheck_1065_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1047_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1065_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
lean_inc_ref(v_a_1006_);
v___x_1052_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v___x_1023_, v_a_1006_, v_a_1046_, v_a_1048_);
lean_inc_ref(v___x_1052_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set_tag(v___x_1050_, 1);
lean_ctor_set(v___x_1050_, 0, v___x_1052_);
v___x_1054_ = v___x_1050_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; 
v___x_1055_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_997_, v_map_1022_, v___x_1054_);
lean_dec_ref(v___x_1054_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_dec_ref_known(v___x_1055_, 1);
v_a_1008_ = v___x_1052_;
goto v___jp_1007_;
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec_ref(v___x_1052_);
lean_dec_ref(v_as_996_);
lean_dec(v_i_995_);
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
}
else
{
lean_object* v_a_1066_; 
lean_dec(v_a_1046_);
lean_dec_ref(v_as_996_);
lean_dec(v_i_995_);
v_a_1066_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1047_, 1);
v_a_1026_ = v_a_1066_;
goto v___jp_1025_;
}
}
else
{
lean_object* v_a_1067_; 
lean_dec_ref(v_as_996_);
lean_dec(v_i_995_);
v_a_1067_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1045_, 1);
v_a_1026_ = v_a_1067_;
goto v___jp_1025_;
}
v___jp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_box(0);
v___x_1028_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_997_, v_map_1022_, v___x_1027_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1035_ == 0)
{
lean_object* v_unused_1036_; 
v_unused_1036_ = lean_ctor_get(v___x_1028_, 0);
lean_dec(v_unused_1036_);
v___x_1030_ = v___x_1028_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_dec(v___x_1028_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 1);
lean_ctor_set(v___x_1030_, 0, v_a_1026_);
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1026_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref(v_a_1026_);
v_a_1037_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1028_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1028_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
else
{
lean_object* v_code_1068_; lean_object* v___x_1069_; lean_object* v_map_1070_; lean_object* v___x_1071_; 
v_code_1068_ = lean_ctor_get(v_a_1006_, 0);
v___x_1069_ = lean_st_ref_get(v___y_997_);
v_map_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc_ref(v_map_1070_);
lean_dec(v___x_1069_);
lean_inc_ref(v_code_1068_);
v___x_1071_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_994_, v_code_1068_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1089_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1089_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1089_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
lean_inc_ref(v_a_1006_);
v___x_1076_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1006_, v_a_1072_);
lean_inc_ref(v___x_1076_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set_tag(v___x_1074_, 1);
lean_ctor_set(v___x_1074_, 0, v___x_1076_);
v___x_1078_ = v___x_1074_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; 
v___x_1079_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_997_, v_map_1070_, v___x_1078_);
lean_dec_ref(v___x_1078_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_dec_ref_known(v___x_1079_, 1);
v_a_1008_ = v___x_1076_;
goto v___jp_1007_;
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec_ref(v___x_1076_);
lean_dec_ref(v_as_996_);
lean_dec(v_i_995_);
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_dec_ref(v_as_996_);
lean_dec(v_i_995_);
v_a_1090_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1091_ = lean_box(0);
v___x_1092_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_997_, v_map_1070_, v___x_1091_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v___x_1092_, 0);
lean_dec(v_unused_1100_);
v___x_1094_ = v___x_1092_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_dec(v___x_1092_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set_tag(v___x_1094_, 1);
lean_ctor_set(v___x_1094_, 0, v_a_1090_);
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1090_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec(v_a_1090_);
v_a_1101_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1092_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1092_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
v___jp_1007_:
{
size_t v___x_1009_; size_t v___x_1010_; uint8_t v___x_1011_; 
v___x_1009_ = lean_ptr_addr(v_a_1006_);
v___x_1010_ = lean_ptr_addr(v_a_1008_);
v___x_1011_ = lean_usize_dec_eq(v___x_1009_, v___x_1010_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = lean_unsigned_to_nat(1u);
v___x_1013_ = lean_nat_add(v_i_995_, v___x_1012_);
v___x_1014_ = lean_array_fset(v_as_996_, v_i_995_, v_a_1008_);
lean_dec(v_i_995_);
v_i_995_ = v___x_1013_;
v_as_996_ = v___x_1014_;
goto _start;
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec_ref(v_a_1008_);
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = lean_nat_add(v_i_995_, v___x_1016_);
lean_dec(v_i_995_);
v_i_995_ = v___x_1017_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(uint8_t v_shouldElimFunDecls_1109_, lean_object* v_code_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
switch(lean_obj_tag(v_code_1110_))
{
case 0:
{
lean_object* v_decl_1117_; lean_object* v_k_1118_; uint8_t v___x_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; 
v_decl_1117_ = lean_ctor_get(v_code_1110_, 0);
v_k_1118_ = lean_ctor_get(v_code_1110_, 1);
v___x_1119_ = 0;
v___x_1120_ = 0;
lean_inc_ref(v_decl_1117_);
v___x_1121_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v___x_1119_, v___x_1120_, v_decl_1117_, v_a_1111_, v_a_1113_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v_fvarId_1123_; lean_object* v_value_1124_; lean_object* v___x_1125_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v_fvarId_1123_ = lean_ctor_get(v_a_1122_, 0);
v_value_1124_ = lean_ctor_get(v_a_1122_, 3);
lean_inc(v_value_1124_);
v___x_1125_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(v_value_1124_, v_a_1115_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; uint8_t v___x_1127_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1125_, 1);
v___x_1127_ = lean_unbox(v_a_1126_);
lean_dec(v_a_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v_map_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1128_ = lean_st_ref_get(v_a_1111_);
v_map_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc_ref(v_map_1129_);
lean_dec(v___x_1128_);
lean_inc(v_value_1124_);
v___x_1130_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v___x_1119_, v_value_1124_);
v___x_1131_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_map_1129_, v___x_1130_);
lean_dec_ref(v_map_1129_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v___x_1132_; lean_object* v_map_1133_; lean_object* v_subst_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1182_; 
v___x_1132_ = lean_st_ref_take(v_a_1111_);
v_map_1133_ = lean_ctor_get(v___x_1132_, 0);
v_subst_1134_ = lean_ctor_get(v___x_1132_, 1);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1136_ = v___x_1132_;
v_isShared_1137_ = v_isSharedCheck_1182_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_subst_1134_);
lean_inc(v_map_1133_);
lean_dec(v___x_1132_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1182_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
lean_inc(v_fvarId_1123_);
v___x_1138_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_map_1133_, v___x_1130_, v_fvarId_1123_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1138_);
v___x_1140_ = v___x_1136_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_subst_1134_);
v___x_1140_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_st_ref_put(v_a_1111_, v___x_1140_);
lean_inc_ref(v_k_1118_);
v___x_1142_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1109_, v_k_1118_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1180_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1180_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1180_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
size_t v___x_1147_; size_t v___x_1148_; uint8_t v___x_1149_; 
v___x_1147_ = lean_ptr_addr(v_k_1118_);
v___x_1148_ = lean_ptr_addr(v_a_1143_);
v___x_1149_ = lean_usize_dec_eq(v___x_1147_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1159_; 
v_isSharedCheck_1159_ = !lean_is_exclusive(v_code_1110_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; lean_object* v_unused_1161_; 
v_unused_1160_ = lean_ctor_get(v_code_1110_, 1);
lean_dec(v_unused_1160_);
v_unused_1161_ = lean_ctor_get(v_code_1110_, 0);
lean_dec(v_unused_1161_);
v___x_1151_ = v_code_1110_;
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
else
{
lean_dec(v_code_1110_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v_a_1143_);
lean_ctor_set(v___x_1151_, 0, v_a_1122_);
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1122_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_a_1143_);
v___x_1154_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1156_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1154_);
v___x_1156_ = v___x_1145_;
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
size_t v___x_1162_; size_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1162_ = lean_ptr_addr(v_decl_1117_);
v___x_1163_ = lean_ptr_addr(v_a_1122_);
v___x_1164_ = lean_usize_dec_eq(v___x_1162_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1174_; 
v_isSharedCheck_1174_ = !lean_is_exclusive(v_code_1110_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; lean_object* v_unused_1176_; 
v_unused_1175_ = lean_ctor_get(v_code_1110_, 1);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_code_1110_, 0);
lean_dec(v_unused_1176_);
v___x_1166_ = v_code_1110_;
v_isShared_1167_ = v_isSharedCheck_1174_;
goto v_resetjp_1165_;
}
else
{
lean_dec(v_code_1110_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1174_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v_a_1143_);
lean_ctor_set(v___x_1166_, 0, v_a_1122_);
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1122_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_a_1143_);
v___x_1169_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1171_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1169_);
v___x_1171_ = v___x_1145_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
else
{
lean_object* v___x_1178_; 
lean_dec(v_a_1143_);
lean_dec(v_a_1122_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v_code_1110_);
v___x_1178_ = v___x_1145_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_code_1110_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
else
{
lean_dec(v_a_1122_);
lean_dec_ref_known(v_code_1110_, 2);
return v___x_1142_;
}
}
}
}
else
{
lean_object* v_val_1183_; lean_object* v___x_1184_; 
lean_inc_ref(v_k_1118_);
lean_dec_ref(v___x_1130_);
lean_dec_ref_known(v_code_1110_, 2);
v_val_1183_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_val_1183_);
lean_dec_ref_known(v___x_1131_, 1);
v___x_1184_ = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(v_a_1122_, v_val_1183_, v_a_1111_, v_a_1113_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_dec_ref_known(v___x_1184_, 1);
v_code_1110_ = v_k_1118_;
goto _start;
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec_ref(v_k_1118_);
v_a_1186_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1184_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1184_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
else
{
lean_object* v___x_1194_; 
lean_inc_ref(v_k_1118_);
v___x_1194_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1109_, v_k_1118_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1232_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1232_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1232_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
size_t v___x_1199_; size_t v___x_1200_; uint8_t v___x_1201_; 
v___x_1199_ = lean_ptr_addr(v_k_1118_);
v___x_1200_ = lean_ptr_addr(v_a_1195_);
v___x_1201_ = lean_usize_dec_eq(v___x_1199_, v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1211_; 
v_isSharedCheck_1211_ = !lean_is_exclusive(v_code_1110_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; lean_object* v_unused_1213_; 
v_unused_1212_ = lean_ctor_get(v_code_1110_, 1);
lean_dec(v_unused_1212_);
v_unused_1213_ = lean_ctor_get(v_code_1110_, 0);
lean_dec(v_unused_1213_);
v___x_1203_ = v_code_1110_;
v_isShared_1204_ = v_isSharedCheck_1211_;
goto v_resetjp_1202_;
}
else
{
lean_dec(v_code_1110_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1211_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v_a_1195_);
lean_ctor_set(v___x_1203_, 0, v_a_1122_);
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1122_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_a_1195_);
v___x_1206_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1208_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1206_);
v___x_1208_ = v___x_1197_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
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
else
{
size_t v___x_1214_; size_t v___x_1215_; uint8_t v___x_1216_; 
v___x_1214_ = lean_ptr_addr(v_decl_1117_);
v___x_1215_ = lean_ptr_addr(v_a_1122_);
v___x_1216_ = lean_usize_dec_eq(v___x_1214_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1226_; 
v_isSharedCheck_1226_ = !lean_is_exclusive(v_code_1110_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; lean_object* v_unused_1228_; 
v_unused_1227_ = lean_ctor_get(v_code_1110_, 1);
lean_dec(v_unused_1227_);
v_unused_1228_ = lean_ctor_get(v_code_1110_, 0);
lean_dec(v_unused_1228_);
v___x_1218_ = v_code_1110_;
v_isShared_1219_ = v_isSharedCheck_1226_;
goto v_resetjp_1217_;
}
else
{
lean_dec(v_code_1110_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1226_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 1, v_a_1195_);
lean_ctor_set(v___x_1218_, 0, v_a_1122_);
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1122_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_a_1195_);
v___x_1221_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1223_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1221_);
v___x_1223_ = v___x_1197_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v___x_1230_; 
lean_dec(v_a_1195_);
lean_dec(v_a_1122_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v_code_1110_);
v___x_1230_ = v___x_1197_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_code_1110_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
}
else
{
lean_dec(v_a_1122_);
lean_dec_ref_known(v_code_1110_, 2);
return v___x_1194_;
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v_a_1122_);
lean_dec_ref_known(v_code_1110_, 2);
v_a_1233_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1125_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1125_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec_ref_known(v_code_1110_, 2);
v_a_1241_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1121_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1121_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
case 1:
{
lean_object* v_decl_1249_; lean_object* v_k_1250_; lean_object* v___x_1251_; 
v_decl_1249_ = lean_ctor_get(v_code_1110_, 0);
v_k_1250_ = lean_ctor_get(v_code_1110_, 1);
lean_inc_ref(v_decl_1249_);
v___x_1251_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_1109_, v_decl_1249_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1251_) == 0)
{
if (v_shouldElimFunDecls_1109_ == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1253_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1251_, 1);
lean_inc_ref(v_k_1250_);
v___x_1253_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1109_, v_k_1250_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1291_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1291_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1291_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
size_t v___x_1258_; size_t v___x_1259_; uint8_t v___x_1260_; 
v___x_1258_ = lean_ptr_addr(v_k_1250_);
v___x_1259_ = lean_ptr_addr(v_a_1254_);
v___x_1260_ = lean_usize_dec_eq(v___x_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1270_; 
v_isSharedCheck_1270_ = !lean_is_exclusive(v_code_1110_);
if (v_isSharedCheck_1270_ == 0)
{
lean_object* v_unused_1271_; lean_object* v_unused_1272_; 
v_unused_1271_ = lean_ctor_get(v_code_1110_, 1);
lean_dec(v_unused_1271_);
v_unused_1272_ = lean_ctor_get(v_code_1110_, 0);
lean_dec(v_unused_1272_);
v___x_1262_ = v_code_1110_;
v_isShared_1263_ = v_isSharedCheck_1270_;
goto v_resetjp_1261_;
}
else
{
lean_dec(v_code_1110_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1270_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v_a_1254_);
lean_ctor_set(v___x_1262_, 0, v_a_1252_);
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1252_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_a_1254_);
v___x_1265_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1267_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1265_);
v___x_1267_ = v___x_1256_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
else
{
size_t v___x_1273_; size_t v___x_1274_; uint8_t v___x_1275_; 
v___x_1273_ = lean_ptr_addr(v_decl_1249_);
v___x_1274_ = lean_ptr_addr(v_a_1252_);
v___x_1275_ = lean_usize_dec_eq(v___x_1273_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1285_; 
v_isSharedCheck_1285_ = !lean_is_exclusive(v_code_1110_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; lean_object* v_unused_1287_; 
v_unused_1286_ = lean_ctor_get(v_code_1110_, 1);
lean_dec(v_unused_1286_);
v_unused_1287_ = lean_ctor_get(v_code_1110_, 0);
lean_dec(v_unused_1287_);
v___x_1277_ = v_code_1110_;
v_isShared_1278_ = v_isSharedCheck_1285_;
goto v_resetjp_1276_;
}
else
{
lean_dec(v_code_1110_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1285_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v_a_1254_);
lean_ctor_set(v___x_1277_, 0, v_a_1252_);
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1252_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_a_1254_);
v___x_1280_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1282_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1280_);
v___x_1282_ = v___x_1256_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
else
{
lean_object* v___x_1289_; 
lean_dec(v_a_1254_);
lean_dec(v_a_1252_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v_code_1110_);
v___x_1289_ = v___x_1256_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_code_1110_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
else
{
lean_dec(v_a_1252_);
lean_dec_ref_known(v_code_1110_, 2);
return v___x_1253_;
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1293_; lean_object* v_map_1294_; uint8_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v_a_1292_ = lean_ctor_get(v___x_1251_, 0);
lean_inc_n(v_a_1292_, 2);
lean_dec_ref_known(v___x_1251_, 1);
v___x_1293_ = lean_st_ref_get(v_a_1111_);
v_map_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc_ref(v_map_1294_);
lean_dec(v___x_1293_);
v___x_1295_ = 0;
v___x_1296_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___closed__0));
v___x_1297_ = l_Lean_Compiler_LCNF_FunDecl_toExpr(v___x_1295_, v_a_1292_, v___x_1296_);
v___x_1298_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_map_1294_, v___x_1297_);
lean_dec_ref(v_map_1294_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_fvarId_1299_; lean_object* v___x_1300_; lean_object* v_map_1301_; lean_object* v_subst_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1350_; 
v_fvarId_1299_ = lean_ctor_get(v_a_1292_, 0);
v___x_1300_ = lean_st_ref_take(v_a_1111_);
v_map_1301_ = lean_ctor_get(v___x_1300_, 0);
v_subst_1302_ = lean_ctor_get(v___x_1300_, 1);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1304_ = v___x_1300_;
v_isShared_1305_ = v_isSharedCheck_1350_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_subst_1302_);
lean_inc(v_map_1301_);
lean_dec(v___x_1300_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1350_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
lean_inc(v_fvarId_1299_);
v___x_1306_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_map_1301_, v___x_1297_, v_fvarId_1299_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1306_);
v___x_1308_ = v___x_1304_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_subst_1302_);
v___x_1308_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_st_ref_put(v_a_1111_, v___x_1308_);
lean_inc_ref(v_k_1250_);
v___x_1310_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1109_, v_k_1250_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1348_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1348_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1348_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
size_t v___x_1315_; size_t v___x_1316_; uint8_t v___x_1317_; 
v___x_1315_ = lean_ptr_addr(v_k_1250_);
v___x_1316_ = lean_ptr_addr(v_a_1311_);
v___x_1317_ = lean_usize_dec_eq(v___x_1315_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1327_; 
v_isSharedCheck_1327_ = !lean_is_exclusive(v_code_1110_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; lean_object* v_unused_1329_; 
v_unused_1328_ = lean_ctor_get(v_code_1110_, 1);
lean_dec(v_unused_1328_);
v_unused_1329_ = lean_ctor_get(v_code_1110_, 0);
lean_dec(v_unused_1329_);
v___x_1319_ = v_code_1110_;
v_isShared_1320_ = v_isSharedCheck_1327_;
goto v_resetjp_1318_;
}
else
{
lean_dec(v_code_1110_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1327_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 1, v_a_1311_);
lean_ctor_set(v___x_1319_, 0, v_a_1292_);
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1292_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_a_1311_);
v___x_1322_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1324_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1322_);
v___x_1324_ = v___x_1313_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
else
{
size_t v___x_1330_; size_t v___x_1331_; uint8_t v___x_1332_; 
v___x_1330_ = lean_ptr_addr(v_decl_1249_);
v___x_1331_ = lean_ptr_addr(v_a_1292_);
v___x_1332_ = lean_usize_dec_eq(v___x_1330_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1342_; 
v_isSharedCheck_1342_ = !lean_is_exclusive(v_code_1110_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; lean_object* v_unused_1344_; 
v_unused_1343_ = lean_ctor_get(v_code_1110_, 1);
lean_dec(v_unused_1343_);
v_unused_1344_ = lean_ctor_get(v_code_1110_, 0);
lean_dec(v_unused_1344_);
v___x_1334_ = v_code_1110_;
v_isShared_1335_ = v_isSharedCheck_1342_;
goto v_resetjp_1333_;
}
else
{
lean_dec(v_code_1110_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1342_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 1, v_a_1311_);
lean_ctor_set(v___x_1334_, 0, v_a_1292_);
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1292_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_a_1311_);
v___x_1337_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1339_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1337_);
v___x_1339_ = v___x_1313_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v___x_1346_; 
lean_dec(v_a_1311_);
lean_dec(v_a_1292_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v_code_1110_);
v___x_1346_ = v___x_1313_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_code_1110_);
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
else
{
lean_dec(v_a_1292_);
lean_dec_ref_known(v_code_1110_, 2);
return v___x_1310_;
}
}
}
}
else
{
lean_object* v_val_1351_; lean_object* v___x_1352_; 
lean_inc_ref(v_k_1250_);
lean_dec_ref(v___x_1297_);
lean_dec_ref_known(v_code_1110_, 2);
v_val_1351_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_val_1351_);
lean_dec_ref_known(v___x_1298_, 1);
v___x_1352_ = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(v_a_1292_, v_val_1351_, v_a_1111_, v_a_1113_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_dec_ref_known(v___x_1352_, 1);
v_code_1110_ = v_k_1250_;
goto _start;
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref(v_k_1250_);
v_a_1354_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1352_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1352_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref_known(v_code_1110_, 2);
v_a_1362_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1251_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1251_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
case 2:
{
lean_object* v_decl_1370_; lean_object* v_k_1371_; lean_object* v___x_1372_; 
v_decl_1370_ = lean_ctor_get(v_code_1110_, 0);
v_k_1371_ = lean_ctor_get(v_code_1110_, 1);
lean_inc_ref(v_decl_1370_);
v___x_1372_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_1109_, v_decl_1370_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1374_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1372_, 1);
lean_inc_ref(v_k_1371_);
v___x_1374_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1109_, v_k_1371_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1412_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1377_ = v___x_1374_;
v_isShared_1378_ = v_isSharedCheck_1412_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1374_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1412_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
size_t v___x_1379_; size_t v___x_1380_; uint8_t v___x_1381_; 
v___x_1379_ = lean_ptr_addr(v_k_1371_);
v___x_1380_ = lean_ptr_addr(v_a_1375_);
v___x_1381_ = lean_usize_dec_eq(v___x_1379_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1391_; 
v_isSharedCheck_1391_ = !lean_is_exclusive(v_code_1110_);
if (v_isSharedCheck_1391_ == 0)
{
lean_object* v_unused_1392_; lean_object* v_unused_1393_; 
v_unused_1392_ = lean_ctor_get(v_code_1110_, 1);
lean_dec(v_unused_1392_);
v_unused_1393_ = lean_ctor_get(v_code_1110_, 0);
lean_dec(v_unused_1393_);
v___x_1383_ = v_code_1110_;
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
else
{
lean_dec(v_code_1110_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v_a_1375_);
lean_ctor_set(v___x_1383_, 0, v_a_1373_);
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1373_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_a_1375_);
v___x_1386_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1388_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1386_);
v___x_1388_ = v___x_1377_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
else
{
size_t v___x_1394_; size_t v___x_1395_; uint8_t v___x_1396_; 
v___x_1394_ = lean_ptr_addr(v_decl_1370_);
v___x_1395_ = lean_ptr_addr(v_a_1373_);
v___x_1396_ = lean_usize_dec_eq(v___x_1394_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1406_; 
v_isSharedCheck_1406_ = !lean_is_exclusive(v_code_1110_);
if (v_isSharedCheck_1406_ == 0)
{
lean_object* v_unused_1407_; lean_object* v_unused_1408_; 
v_unused_1407_ = lean_ctor_get(v_code_1110_, 1);
lean_dec(v_unused_1407_);
v_unused_1408_ = lean_ctor_get(v_code_1110_, 0);
lean_dec(v_unused_1408_);
v___x_1398_ = v_code_1110_;
v_isShared_1399_ = v_isSharedCheck_1406_;
goto v_resetjp_1397_;
}
else
{
lean_dec(v_code_1110_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1406_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 1, v_a_1375_);
lean_ctor_set(v___x_1398_, 0, v_a_1373_);
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1373_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_a_1375_);
v___x_1401_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1403_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1401_);
v___x_1403_ = v___x_1377_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
else
{
lean_object* v___x_1410_; 
lean_dec(v_a_1375_);
lean_dec(v_a_1373_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v_code_1110_);
v___x_1410_ = v___x_1377_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_code_1110_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
else
{
lean_dec(v_a_1373_);
lean_dec_ref_known(v_code_1110_, 2);
return v___x_1374_;
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref_known(v_code_1110_, 2);
v_a_1413_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1372_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1372_);
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
case 3:
{
lean_object* v_fvarId_1421_; lean_object* v_args_1422_; lean_object* v___x_1423_; lean_object* v_subst_1424_; uint8_t v___x_1425_; uint8_t v___x_1426_; lean_object* v___x_1427_; 
v_fvarId_1421_ = lean_ctor_get(v_code_1110_, 0);
v_args_1422_ = lean_ctor_get(v_code_1110_, 1);
v___x_1423_ = lean_st_ref_get(v_a_1111_);
v_subst_1424_ = lean_ctor_get(v___x_1423_, 1);
lean_inc_ref(v_subst_1424_);
lean_dec(v___x_1423_);
v___x_1425_ = 0;
v___x_1426_ = 0;
lean_inc(v_fvarId_1421_);
v___x_1427_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1424_, v_fvarId_1421_, v___x_1426_);
lean_dec_ref(v_subst_1424_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_fvarId_1428_; lean_object* v___x_1429_; 
v_fvarId_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_fvarId_1428_);
lean_dec_ref_known(v___x_1427_, 1);
lean_inc_ref(v_args_1422_);
v___x_1429_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v___x_1425_, v___x_1426_, v_args_1422_, v_a_1111_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1455_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1455_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1455_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
uint8_t v___y_1435_; uint8_t v___x_1451_; 
v___x_1451_ = l_Lean_instBEqFVarId_beq(v_fvarId_1421_, v_fvarId_1428_);
if (v___x_1451_ == 0)
{
v___y_1435_ = v___x_1451_;
goto v___jp_1434_;
}
else
{
size_t v___x_1452_; size_t v___x_1453_; uint8_t v___x_1454_; 
v___x_1452_ = lean_ptr_addr(v_args_1422_);
v___x_1453_ = lean_ptr_addr(v_a_1430_);
v___x_1454_ = lean_usize_dec_eq(v___x_1452_, v___x_1453_);
v___y_1435_ = v___x_1454_;
goto v___jp_1434_;
}
v___jp_1434_:
{
if (v___y_1435_ == 0)
{
lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1445_; 
v_isSharedCheck_1445_ = !lean_is_exclusive(v_code_1110_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; lean_object* v_unused_1447_; 
v_unused_1446_ = lean_ctor_get(v_code_1110_, 1);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_code_1110_, 0);
lean_dec(v_unused_1447_);
v___x_1437_ = v_code_1110_;
v_isShared_1438_ = v_isSharedCheck_1445_;
goto v_resetjp_1436_;
}
else
{
lean_dec(v_code_1110_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1445_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 1, v_a_1430_);
lean_ctor_set(v___x_1437_, 0, v_fvarId_1428_);
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_fvarId_1428_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_a_1430_);
v___x_1440_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1442_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1440_);
v___x_1442_ = v___x_1432_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
else
{
lean_object* v___x_1449_; 
lean_dec(v_a_1430_);
lean_dec(v_fvarId_1428_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v_code_1110_);
v___x_1449_ = v___x_1432_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_code_1110_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_fvarId_1428_);
lean_dec_ref_known(v_code_1110_, 2);
v_a_1456_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1429_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1429_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
else
{
lean_object* v___x_1464_; 
lean_dec_ref_known(v_code_1110_, 2);
v___x_1464_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1425_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
return v___x_1464_;
}
}
case 4:
{
lean_object* v_cases_1465_; lean_object* v_typeName_1466_; lean_object* v_resultType_1467_; lean_object* v_discr_1468_; lean_object* v_alts_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1520_; 
v_cases_1465_ = lean_ctor_get(v_code_1110_, 0);
lean_inc_ref(v_cases_1465_);
v_typeName_1466_ = lean_ctor_get(v_cases_1465_, 0);
v_resultType_1467_ = lean_ctor_get(v_cases_1465_, 1);
v_discr_1468_ = lean_ctor_get(v_cases_1465_, 2);
v_alts_1469_ = lean_ctor_get(v_cases_1465_, 3);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_cases_1465_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1471_ = v_cases_1465_;
v_isShared_1472_ = v_isSharedCheck_1520_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_alts_1469_);
lean_inc(v_discr_1468_);
lean_inc(v_resultType_1467_);
lean_inc(v_typeName_1466_);
lean_dec(v_cases_1465_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1520_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v_subst_1474_; uint8_t v___x_1475_; uint8_t v___x_1476_; lean_object* v___x_1477_; 
v___x_1473_ = lean_st_ref_get(v_a_1111_);
v_subst_1474_ = lean_ctor_get(v___x_1473_, 1);
lean_inc_ref(v_subst_1474_);
lean_dec(v___x_1473_);
v___x_1475_ = 0;
v___x_1476_ = 0;
lean_inc(v_discr_1468_);
v___x_1477_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1474_, v_discr_1468_, v___x_1476_);
lean_dec_ref(v_subst_1474_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_fvarId_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1518_; 
v_fvarId_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1518_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_fvarId_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1518_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = lean_st_ref_get(v_a_1111_);
v___x_1483_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1469_);
v___x_1484_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(v_shouldElimFunDecls_1109_, v___x_1483_, v_alts_1469_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1509_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1509_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1509_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v_subst_1489_; lean_object* v___x_1490_; size_t v___x_1501_; size_t v___x_1502_; uint8_t v___x_1503_; 
v_subst_1489_ = lean_ctor_get(v___x_1482_, 1);
lean_inc_ref(v_subst_1489_);
lean_dec(v___x_1482_);
lean_inc_ref(v_resultType_1467_);
v___x_1490_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_1475_, v_subst_1489_, v___x_1476_, v_resultType_1467_);
lean_dec_ref(v_subst_1489_);
v___x_1501_ = lean_ptr_addr(v_alts_1469_);
lean_dec_ref(v_alts_1469_);
v___x_1502_ = lean_ptr_addr(v_a_1485_);
v___x_1503_ = lean_usize_dec_eq(v___x_1501_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_dec(v_discr_1468_);
lean_dec_ref(v_resultType_1467_);
lean_dec_ref_known(v_code_1110_, 1);
goto v___jp_1491_;
}
else
{
size_t v___x_1504_; size_t v___x_1505_; uint8_t v___x_1506_; 
v___x_1504_ = lean_ptr_addr(v_resultType_1467_);
lean_dec_ref(v_resultType_1467_);
v___x_1505_ = lean_ptr_addr(v___x_1490_);
v___x_1506_ = lean_usize_dec_eq(v___x_1504_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_dec(v_discr_1468_);
lean_dec_ref_known(v_code_1110_, 1);
goto v___jp_1491_;
}
else
{
uint8_t v___x_1507_; 
v___x_1507_ = l_Lean_instBEqFVarId_beq(v_discr_1468_, v_fvarId_1478_);
lean_dec(v_discr_1468_);
if (v___x_1507_ == 0)
{
lean_dec_ref_known(v_code_1110_, 1);
goto v___jp_1491_;
}
else
{
lean_object* v___x_1508_; 
lean_dec_ref(v___x_1490_);
lean_del_object(v___x_1487_);
lean_dec(v_a_1485_);
lean_del_object(v___x_1480_);
lean_dec(v_fvarId_1478_);
lean_del_object(v___x_1471_);
lean_dec(v_typeName_1466_);
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v_code_1110_);
return v___x_1508_;
}
}
}
v___jp_1491_:
{
lean_object* v___x_1493_; 
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 3, v_a_1485_);
lean_ctor_set(v___x_1471_, 2, v_fvarId_1478_);
lean_ctor_set(v___x_1471_, 1, v___x_1490_);
v___x_1493_ = v___x_1471_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_typeName_1466_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_fvarId_1478_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_a_1485_);
v___x_1493_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set_tag(v___x_1480_, 4);
lean_ctor_set(v___x_1480_, 0, v___x_1493_);
v___x_1495_ = v___x_1480_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1497_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1495_);
v___x_1497_ = v___x_1487_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec(v___x_1482_);
lean_del_object(v___x_1480_);
lean_dec(v_fvarId_1478_);
lean_del_object(v___x_1471_);
lean_dec_ref(v_alts_1469_);
lean_dec(v_discr_1468_);
lean_dec_ref(v_resultType_1467_);
lean_dec(v_typeName_1466_);
lean_dec_ref_known(v_code_1110_, 1);
v_a_1510_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1484_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1484_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
else
{
lean_object* v___x_1519_; 
lean_del_object(v___x_1471_);
lean_dec_ref(v_alts_1469_);
lean_dec(v_discr_1468_);
lean_dec_ref(v_resultType_1467_);
lean_dec(v_typeName_1466_);
lean_dec_ref_known(v_code_1110_, 1);
v___x_1519_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1475_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
return v___x_1519_;
}
}
}
case 5:
{
lean_object* v_fvarId_1521_; lean_object* v___x_1522_; lean_object* v_subst_1523_; uint8_t v___x_1524_; lean_object* v___x_1525_; 
v_fvarId_1521_ = lean_ctor_get(v_code_1110_, 0);
v___x_1522_ = lean_st_ref_get(v_a_1111_);
v_subst_1523_ = lean_ctor_get(v___x_1522_, 1);
lean_inc_ref(v_subst_1523_);
lean_dec(v___x_1522_);
v___x_1524_ = 0;
lean_inc(v_fvarId_1521_);
v___x_1525_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1523_, v_fvarId_1521_, v___x_1524_);
lean_dec_ref(v_subst_1523_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_fvarId_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1545_; 
v_fvarId_1526_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1528_ = v___x_1525_;
v_isShared_1529_ = v_isSharedCheck_1545_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_fvarId_1526_);
lean_dec(v___x_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1545_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
uint8_t v___x_1530_; 
v___x_1530_ = l_Lean_instBEqFVarId_beq(v_fvarId_1521_, v_fvarId_1526_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1540_; 
v_isSharedCheck_1540_ = !lean_is_exclusive(v_code_1110_);
if (v_isSharedCheck_1540_ == 0)
{
lean_object* v_unused_1541_; 
v_unused_1541_ = lean_ctor_get(v_code_1110_, 0);
lean_dec(v_unused_1541_);
v___x_1532_ = v_code_1110_;
v_isShared_1533_ = v_isSharedCheck_1540_;
goto v_resetjp_1531_;
}
else
{
lean_dec(v_code_1110_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1540_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v_fvarId_1526_);
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_fvarId_1526_);
v___x_1535_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1537_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v___x_1535_);
v___x_1537_ = v___x_1528_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
else
{
lean_object* v___x_1543_; 
lean_dec(v_fvarId_1526_);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v_code_1110_);
v___x_1543_ = v___x_1528_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_code_1110_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
else
{
uint8_t v___x_1546_; lean_object* v___x_1547_; 
lean_dec_ref_known(v_code_1110_, 1);
v___x_1546_ = 0;
v___x_1547_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1546_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
return v___x_1547_;
}
}
default: 
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_code_1110_);
return v___x_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(uint8_t v_shouldElimFunDecls_1549_, lean_object* v_decl_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_params_1557_; lean_object* v_type_1558_; lean_object* v_value_1559_; lean_object* v___x_1560_; lean_object* v_subst_1561_; uint8_t v___x_1562_; uint8_t v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_params_1557_ = lean_ctor_get(v_decl_1550_, 2);
v_type_1558_ = lean_ctor_get(v_decl_1550_, 3);
v_value_1559_ = lean_ctor_get(v_decl_1550_, 4);
v___x_1560_ = lean_st_ref_get(v_a_1551_);
v_subst_1561_ = lean_ctor_get(v___x_1560_, 1);
lean_inc_ref(v_subst_1561_);
lean_dec(v___x_1560_);
v___x_1562_ = 0;
v___x_1563_ = 0;
lean_inc_ref(v_type_1558_);
v___x_1564_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_1562_, v_subst_1561_, v___x_1563_, v_type_1558_);
lean_dec_ref(v_subst_1561_);
lean_inc_ref(v_params_1557_);
v___x_1565_ = l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(v___x_1562_, v___x_1563_, v_params_1557_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1567_; lean_object* v_map_1568_; lean_object* v_r_1569_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
v___x_1567_ = lean_st_ref_get(v_a_1551_);
v_map_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc_ref(v_map_1568_);
lean_dec(v___x_1567_);
lean_inc_ref(v_value_1559_);
v_r_1569_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1549_, v_value_1559_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v_r_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1587_; 
v_a_1570_ = lean_ctor_get(v_r_1569_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_r_1569_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1572_ = v_r_1569_;
v_isShared_1573_ = v_isSharedCheck_1587_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v_r_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1587_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
lean_inc(v_a_1570_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set_tag(v___x_1572_, 1);
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1576_; 
v___x_1576_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(v_a_1551_, v_map_1568_, v___x_1575_);
lean_dec_ref(v___x_1575_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v___x_1577_; 
lean_dec_ref_known(v___x_1576_, 1);
v___x_1577_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1562_, v_decl_1550_, v___x_1564_, v_a_1566_, v_a_1570_, v_a_1553_);
return v___x_1577_;
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec(v_a_1570_);
lean_dec(v_a_1566_);
lean_dec_ref(v___x_1564_);
lean_dec_ref(v_decl_1550_);
v_a_1578_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1576_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1576_);
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
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec(v_a_1566_);
lean_dec_ref(v___x_1564_);
lean_dec_ref(v_decl_1550_);
v_a_1588_ = lean_ctor_get(v_r_1569_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v_r_1569_, 1);
v___x_1589_ = lean_box(0);
v___x_1590_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(v_a_1551_, v_map_1568_, v___x_1589_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; 
v_unused_1598_ = lean_ctor_get(v___x_1590_, 0);
lean_dec(v_unused_1598_);
v___x_1592_ = v___x_1590_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_dec(v___x_1590_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 1);
lean_ctor_set(v___x_1592_, 0, v_a_1588_);
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1588_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v_a_1588_);
v_a_1599_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1590_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1590_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec_ref(v___x_1564_);
lean_dec_ref(v_decl_1550_);
v_a_1607_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1565_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1565_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___boxed(lean_object* v_shouldElimFunDecls_1615_, lean_object* v_decl_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1623_; lean_object* v_res_1624_; 
v_shouldElimFunDecls_boxed_1623_ = lean_unbox(v_shouldElimFunDecls_1615_);
v_res_1624_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_boxed_1623_, v_decl_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec(v_a_1617_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___boxed(lean_object* v_shouldElimFunDecls_1625_, lean_object* v_i_1626_, lean_object* v_as_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1634_; lean_object* v_res_1635_; 
v_shouldElimFunDecls_boxed_1634_ = lean_unbox(v_shouldElimFunDecls_1625_);
v_res_1635_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(v_shouldElimFunDecls_boxed_1634_, v_i_1626_, v_as_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___boxed(lean_object* v_shouldElimFunDecls_1636_, lean_object* v_code_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1644_; lean_object* v_res_1645_; 
v_shouldElimFunDecls_boxed_1644_ = lean_unbox(v_shouldElimFunDecls_1636_);
v_res_1645_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_boxed_1644_, v_code_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
lean_dec(v_a_1638_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2(uint8_t v_pu_1646_, uint8_t v_t_1647_, lean_object* v_decl_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v_pu_1646_, v_t_1647_, v_decl_1648_, v___y_1649_, v___y_1651_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___boxed(lean_object* v_pu_1656_, lean_object* v_t_1657_, lean_object* v_decl_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
uint8_t v_pu_boxed_1665_; uint8_t v_t_boxed_1666_; lean_object* v_res_1667_; 
v_pu_boxed_1665_ = lean_unbox(v_pu_1656_);
v_t_boxed_1666_ = lean_unbox(v_t_1657_);
v_res_1667_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2(v_pu_boxed_1665_, v_t_boxed_1666_, v_decl_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5(uint8_t v_pu_1668_, uint8_t v_t_1669_, lean_object* v_args_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v_pu_1668_, v_t_1669_, v_args_1670_, v___y_1671_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___boxed(lean_object* v_pu_1678_, lean_object* v_t_1679_, lean_object* v_args_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
uint8_t v_pu_boxed_1687_; uint8_t v_t_boxed_1688_; lean_object* v_res_1689_; 
v_pu_boxed_1687_ = lean_unbox(v_pu_1678_);
v_t_boxed_1688_ = lean_unbox(v_t_1679_);
v_res_1689_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5(v_pu_boxed_1687_, v_t_boxed_1688_, v_args_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3(lean_object* v_00_u03b2_1690_, lean_object* v_x_1691_, lean_object* v_x_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_x_1691_, v_x_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___boxed(lean_object* v_00_u03b2_1694_, lean_object* v_x_1695_, lean_object* v_x_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3(v_00_u03b2_1694_, v_x_1695_, v_x_1696_);
lean_dec_ref(v_x_1696_);
lean_dec_ref(v_x_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4(lean_object* v_00_u03b2_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_, lean_object* v_x_1701_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_x_1699_, v_x_1700_, v_x_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(uint8_t v_pu_1703_, uint8_t v_t_1704_, lean_object* v_i_1705_, lean_object* v_as_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(v_pu_1703_, v_t_1704_, v_i_1705_, v_as_1706_, v___y_1707_, v___y_1709_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___boxed(lean_object* v_pu_1714_, lean_object* v_t_1715_, lean_object* v_i_1716_, lean_object* v_as_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
uint8_t v_pu_boxed_1724_; uint8_t v_t_boxed_1725_; lean_object* v_res_1726_; 
v_pu_boxed_1724_ = lean_unbox(v_pu_1714_);
v_t_boxed_1725_ = lean_unbox(v_t_1715_);
v_res_1726_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(v_pu_boxed_1724_, v_t_boxed_1725_, v_i_1716_, v_as_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4(lean_object* v_00_u03b2_1727_, lean_object* v_x_1728_, size_t v_x_1729_, lean_object* v_x_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_1728_, v_x_1729_, v_x_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1732_, lean_object* v_x_1733_, lean_object* v_x_1734_, lean_object* v_x_1735_){
_start:
{
size_t v_x_17066__boxed_1736_; lean_object* v_res_1737_; 
v_x_17066__boxed_1736_ = lean_unbox_usize(v_x_1734_);
lean_dec(v_x_1734_);
v_res_1737_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4(v_00_u03b2_1732_, v_x_1733_, v_x_17066__boxed_1736_, v_x_1735_);
lean_dec_ref(v_x_1735_);
lean_dec_ref(v_x_1733_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6(lean_object* v_00_u03b2_1738_, lean_object* v_x_1739_, size_t v_x_1740_, size_t v_x_1741_, lean_object* v_x_1742_, lean_object* v_x_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_1739_, v_x_1740_, v_x_1741_, v_x_1742_, v_x_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1745_, lean_object* v_x_1746_, lean_object* v_x_1747_, lean_object* v_x_1748_, lean_object* v_x_1749_, lean_object* v_x_1750_){
_start:
{
size_t v_x_17077__boxed_1751_; size_t v_x_17078__boxed_1752_; lean_object* v_res_1753_; 
v_x_17077__boxed_1751_ = lean_unbox_usize(v_x_1747_);
lean_dec(v_x_1747_);
v_x_17078__boxed_1752_ = lean_unbox_usize(v_x_1748_);
lean_dec(v_x_1748_);
v_res_1753_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6(v_00_u03b2_1745_, v_x_1746_, v_x_17077__boxed_1751_, v_x_17078__boxed_1752_, v_x_1749_, v_x_1750_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1754_, lean_object* v_keys_1755_, lean_object* v_vals_1756_, lean_object* v_heq_1757_, lean_object* v_i_1758_, lean_object* v_k_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(v_keys_1755_, v_vals_1756_, v_i_1758_, v_k_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1761_, lean_object* v_keys_1762_, lean_object* v_vals_1763_, lean_object* v_heq_1764_, lean_object* v_i_1765_, lean_object* v_k_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6(v_00_u03b2_1761_, v_keys_1762_, v_vals_1763_, v_heq_1764_, v_i_1765_, v_k_1766_);
lean_dec_ref(v_k_1766_);
lean_dec_ref(v_vals_1763_);
lean_dec_ref(v_keys_1762_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_1768_, lean_object* v_n_1769_, lean_object* v_k_1770_, lean_object* v_v_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(v_n_1769_, v_k_1770_, v_v_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_1773_, size_t v_depth_1774_, lean_object* v_keys_1775_, lean_object* v_vals_1776_, lean_object* v_heq_1777_, lean_object* v_i_1778_, lean_object* v_entries_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_depth_1774_, v_keys_1775_, v_vals_1776_, v_i_1778_, v_entries_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1781_, lean_object* v_depth_1782_, lean_object* v_keys_1783_, lean_object* v_vals_1784_, lean_object* v_heq_1785_, lean_object* v_i_1786_, lean_object* v_entries_1787_){
_start:
{
size_t v_depth_boxed_1788_; lean_object* v_res_1789_; 
v_depth_boxed_1788_ = lean_unbox_usize(v_depth_1782_);
lean_dec(v_depth_1782_);
v_res_1789_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10(v_00_u03b2_1781_, v_depth_boxed_1788_, v_keys_1783_, v_vals_1784_, v_heq_1785_, v_i_1786_, v_entries_1787_);
lean_dec_ref(v_vals_1784_);
lean_dec_ref(v_keys_1783_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_1790_, lean_object* v_x_1791_, lean_object* v_x_1792_, lean_object* v_x_1793_, lean_object* v_x_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(v_x_1791_, v_x_1792_, v_x_1793_, v_x_1794_);
return v___x_1795_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__0(void){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1796_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__1(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__0, &l_Lean_Compiler_LCNF_Code_cse___closed__0_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__0);
v___x_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
return v___x_1798_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__2(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = lean_box(0);
v___x_1800_ = lean_unsigned_to_nat(16u);
v___x_1801_ = lean_mk_array(v___x_1800_, v___x_1799_);
return v___x_1801_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__3(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__2, &l_Lean_Compiler_LCNF_Code_cse___closed__2_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__2);
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
lean_ctor_set(v___x_1804_, 1, v___x_1802_);
return v___x_1804_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__4(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__3, &l_Lean_Compiler_LCNF_Code_cse___closed__3_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__3);
v___x_1806_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__1, &l_Lean_Compiler_LCNF_Code_cse___closed__1_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__1);
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
lean_ctor_set(v___x_1807_, 1, v___x_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse(uint8_t v_shouldElimFunDecls_1808_, lean_object* v_code_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_cse___closed__4, &l_Lean_Compiler_LCNF_Code_cse___closed__4_once, _init_l_Lean_Compiler_LCNF_Code_cse___closed__4);
v___x_1816_ = lean_st_mk_ref(v___x_1815_);
v___x_1817_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_1808_, v_code_1809_, v___x_1816_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1826_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1826_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1826_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1822_ = lean_st_ref_get(v___x_1816_);
lean_dec(v___x_1816_);
lean_dec(v___x_1822_);
if (v_isShared_1821_ == 0)
{
v___x_1824_ = v___x_1820_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1818_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
else
{
lean_dec(v___x_1816_);
return v___x_1817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse___boxed(lean_object* v_shouldElimFunDecls_1827_, lean_object* v_code_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1834_; lean_object* v_res_1835_; 
v_shouldElimFunDecls_boxed_1834_ = lean_unbox(v_shouldElimFunDecls_1827_);
v_res_1835_ = l_Lean_Compiler_LCNF_Code_cse(v_shouldElimFunDecls_boxed_1834_, v_code_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(lean_object* v_f_1836_, lean_object* v_v_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
if (lean_obj_tag(v_v_1837_) == 0)
{
lean_object* v_code_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1867_; 
v_code_1843_ = lean_ctor_get(v_v_1837_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_v_1837_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1845_ = v_v_1837_;
v_isShared_1846_ = v_isSharedCheck_1867_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_code_1843_);
lean_dec(v_v_1837_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1867_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; 
lean_inc(v___y_1841_);
lean_inc_ref(v___y_1840_);
lean_inc(v___y_1839_);
lean_inc_ref(v___y_1838_);
v___x_1847_ = lean_apply_6(v_f_1836_, v_code_1843_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, lean_box(0));
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1858_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1858_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1858_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v_a_1848_);
v___x_1853_ = v___x_1845_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1855_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1853_);
v___x_1855_ = v___x_1850_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_del_object(v___x_1845_);
v_a_1859_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1847_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1847_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
else
{
lean_object* v___x_1868_; 
lean_dec_ref(v_f_1836_);
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v_v_1837_);
return v___x_1868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg___boxed(lean_object* v_f_1869_, lean_object* v_v_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v_f_1869_, v_v_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0(uint8_t v_pu_1877_, lean_object* v_f_1878_, lean_object* v_v_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v_f_1878_, v_v_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___boxed(lean_object* v_pu_1886_, lean_object* v_f_1887_, lean_object* v_v_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
uint8_t v_pu_boxed_1894_; lean_object* v_res_1895_; 
v_pu_boxed_1894_ = lean_unbox(v_pu_1886_);
v_res_1895_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0(v_pu_boxed_1894_, v_f_1887_, v_v_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0(uint8_t v_shouldElimFunDecls_1896_, lean_object* v_x_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_Compiler_LCNF_Code_cse(v_shouldElimFunDecls_1896_, v_x_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed(lean_object* v_shouldElimFunDecls_1904_, lean_object* v_x_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1911_; lean_object* v_res_1912_; 
v_shouldElimFunDecls_boxed_1911_ = lean_unbox(v_shouldElimFunDecls_1904_);
v_res_1912_ = l_Lean_Compiler_LCNF_Decl_cse___lam__0(v_shouldElimFunDecls_boxed_1911_, v_x_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse(uint8_t v_shouldElimFunDecls_1913_, lean_object* v_decl_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v_toSignature_1920_; lean_object* v_value_1921_; uint8_t v_recursive_1922_; lean_object* v_inlineAttr_x3f_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1949_; 
v_toSignature_1920_ = lean_ctor_get(v_decl_1914_, 0);
v_value_1921_ = lean_ctor_get(v_decl_1914_, 1);
v_recursive_1922_ = lean_ctor_get_uint8(v_decl_1914_, sizeof(void*)*3);
v_inlineAttr_x3f_1923_ = lean_ctor_get(v_decl_1914_, 2);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_decl_1914_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1925_ = v_decl_1914_;
v_isShared_1926_ = v_isSharedCheck_1949_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_inlineAttr_x3f_1923_);
lean_inc(v_value_1921_);
lean_inc(v_toSignature_1920_);
lean_dec(v_decl_1914_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1949_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; lean_object* v___f_1928_; lean_object* v___x_1929_; 
v___x_1927_ = lean_box(v_shouldElimFunDecls_1913_);
v___f_1928_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1928_, 0, v___x_1927_);
v___x_1929_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v___f_1928_, v_value_1921_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1940_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1940_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1940_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 1, v_a_1930_);
v___x_1935_ = v___x_1925_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_toSignature_1920_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_a_1930_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v_inlineAttr_x3f_1923_);
lean_ctor_set_uint8(v_reuseFailAlloc_1939_, sizeof(void*)*3, v_recursive_1922_);
v___x_1935_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1937_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1935_);
v___x_1937_ = v___x_1932_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_del_object(v___x_1925_);
lean_dec(v_inlineAttr_x3f_1923_);
lean_dec_ref(v_toSignature_1920_);
v_a_1941_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1929_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1929_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse___boxed(lean_object* v_shouldElimFunDecls_1950_, lean_object* v_decl_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1957_; lean_object* v_res_1958_; 
v_shouldElimFunDecls_boxed_1957_ = lean_unbox(v_shouldElimFunDecls_1950_);
v_res_1958_ = l_Lean_Compiler_LCNF_Decl_cse(v_shouldElimFunDecls_boxed_1957_, v_decl_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___lam__0(uint8_t v_shouldElimFunDecls_1962_, uint8_t v_phase_1963_, lean_object* v_occurrence_1964_, lean_object* v_h_1965_){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1966_ = ((lean_object*)(l_Lean_Compiler_LCNF_cse___lam__0___closed__1));
v___x_1967_ = lean_box(v_shouldElimFunDecls_1962_);
v___x_1968_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_cse___boxed), 7, 1);
lean_closure_set(v___x_1968_, 0, v___x_1967_);
v___x_1969_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1966_, v_phase_1963_, v___x_1968_, v_occurrence_1964_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___lam__0___boxed(lean_object* v_shouldElimFunDecls_1970_, lean_object* v_phase_1971_, lean_object* v_occurrence_1972_, lean_object* v_h_1973_){
_start:
{
uint8_t v_shouldElimFunDecls_boxed_1974_; uint8_t v_phase_boxed_1975_; lean_object* v_res_1976_; 
v_shouldElimFunDecls_boxed_1974_ = lean_unbox(v_shouldElimFunDecls_1970_);
v_phase_boxed_1975_ = lean_unbox(v_phase_1971_);
v_res_1976_ = l_Lean_Compiler_LCNF_cse___lam__0(v_shouldElimFunDecls_boxed_1974_, v_phase_boxed_1975_, v_occurrence_1972_, v_h_1973_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse(uint8_t v_phase_1977_, uint8_t v_shouldElimFunDecls_1978_, lean_object* v_occurrence_1979_){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___f_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; lean_object* v___x_1985_; 
v___x_1980_ = lean_box(v_shouldElimFunDecls_1978_);
v___x_1981_ = lean_box(v_phase_1977_);
v___f_1982_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_cse___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1982_, 0, v___x_1980_);
lean_closure_set(v___f_1982_, 1, v___x_1981_);
lean_closure_set(v___f_1982_, 2, v_occurrence_1979_);
v___x_1983_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_1984_ = 0;
v___x_1985_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_1983_, v_phase_1977_, v___x_1984_, v___f_1982_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___boxed(lean_object* v_phase_1986_, lean_object* v_shouldElimFunDecls_1987_, lean_object* v_occurrence_1988_){
_start:
{
uint8_t v_phase_boxed_1989_; uint8_t v_shouldElimFunDecls_boxed_1990_; lean_object* v_res_1991_; 
v_phase_boxed_1989_ = lean_unbox(v_phase_1986_);
v_shouldElimFunDecls_boxed_1990_ = lean_unbox(v_shouldElimFunDecls_1987_);
v_res_1991_ = l_Lean_Compiler_LCNF_cse(v_phase_boxed_1989_, v_shouldElimFunDecls_boxed_1990_, v_occurrence_1988_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2062_; uint8_t v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2062_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_));
v___x_2063_ = 1;
v___x_2064_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_));
v___x_2065_ = l_Lean_registerTraceClass(v___x_2062_, v___x_2063_, v___x_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2____boxed(lean_object* v_a_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_();
return v_res_2067_;
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
