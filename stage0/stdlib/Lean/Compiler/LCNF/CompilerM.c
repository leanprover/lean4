// Lean compiler output
// Module: Lean.Compiler.LCNF.CompilerM
// Imports: public import Lean.Compiler.LCNF.LCtx public import Lean.Compiler.LCNF.ConfigOptions public import Lean.Compiler.InductiveOverride
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
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_toConfigOptions(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParam(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(uint8_t, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Compiler_hasInductiveOverride(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getInductiveOverride_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseCode(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParams(uint8_t, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instInhabitedPhase_default;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instInhabitedPhase;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Phase_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableEqPhase(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableEqPhase___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toPurity___boxed(lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedState;
static lean_once_cell_t l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1;
static const lean_closure_object l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM = (const lean_object*)&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_getType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "unknown free variable "};
static const lean_object* l_Lean_Compiler_LCNF_getType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_getType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_getParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown parameter "};
static const lean_object* l_Lean_Compiler_LCNF_getParam___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_getParam___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getParam___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getParam___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_getLetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "unknown let-declaration "};
static const lean_object* l_Lean_Compiler_LCNF_getLetDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_getLetDecl___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getLetDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getLetDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_getFunDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "unknown local function "};
static const lean_object* l_Lean_Compiler_LCNF_getFunDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_getFunDecl___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getFunDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getFunDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "_private.Lean.Compiler.LCNF.CompilerM.0.Lean.Compiler.LCNF.normExprImp.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Compiler.LCNF.CompilerM"};
static const lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instInhabitedNormFVarResult = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_addSubst___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_addSubst___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_addSubst___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_addSubst___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_mkParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_y"};
static const lean_object* l_Lean_Compiler_LCNF_mkParam___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkParam___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 112, 10, 137, 239, 103, 163, 90)}};
static const lean_object* l_Lean_Compiler_LCNF_mkParam___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_mkParam___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_mkLetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l_Lean_Compiler_LCNF_mkLetDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkLetDecl___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkLetDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkLetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l_Lean_Compiler_LCNF_mkLetDecl___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_mkLetDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_mkFunDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_f"};
static const lean_object* l_Lean_Compiler_LCNF_mkFunDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkFunDecl___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkFunDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkFunDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 65, 185, 154, 193, 83, 240, 170)}};
static const lean_object* l_Lean_Compiler_LCNF_mkFunDecl___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_mkFunDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "_jp"};
static const lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 69, 15, 56, 172, 246, 212, 179)}};
static const lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Data.PersistentHashMap"};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.PersistentHashMap.find!"};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "key is not in the map"};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Compiler_LCNF_Phase_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Compiler_LCNF_Phase_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg(lean_object* v_base_28_){
_start:
{
lean_inc(v_base_28_);
return v_base_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg___boxed(lean_object* v_base_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Compiler_LCNF_Phase_base_elim___redArg(v_base_29_);
lean_dec(v_base_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_base_34_){
_start:
{
lean_inc(v_base_34_);
return v_base_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_base_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Compiler_LCNF_Phase_base_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_base_38_);
lean_dec(v_base_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(lean_object* v_mono_41_){
_start:
{
lean_inc(v_mono_41_);
return v_mono_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg___boxed(lean_object* v_mono_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(v_mono_42_);
lean_dec(v_mono_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_mono_47_){
_start:
{
lean_inc(v_mono_47_);
return v_mono_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_mono_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Compiler_LCNF_Phase_mono_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_mono_51_);
lean_dec(v_mono_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(lean_object* v_impure_54_){
_start:
{
lean_inc(v_impure_54_);
return v_impure_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg___boxed(lean_object* v_impure_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(v_impure_55_);
lean_dec(v_impure_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_impure_60_){
_start:
{
lean_inc(v_impure_60_);
return v_impure_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_impure_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Compiler_LCNF_Phase_impure_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_impure_64_);
lean_dec(v_impure_64_);
return v_res_66_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_instInhabitedPhase_default(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_instInhabitedPhase(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Phase_ofNat(lean_object* v_n_69_){
_start:
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_nat_dec_le(v_n_69_, v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_dec_le(v_n_69_, v___x_72_);
if (v___x_73_ == 0)
{
uint8_t v___x_74_; 
v___x_74_ = 2;
return v___x_74_;
}
else
{
uint8_t v___x_75_; 
v___x_75_ = 1;
return v___x_75_;
}
}
else
{
uint8_t v___x_76_; 
v___x_76_ = 0;
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ofNat___boxed(lean_object* v_n_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Lean_Compiler_LCNF_Phase_ofNat(v_n_77_);
lean_dec(v_n_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableEqPhase(uint8_t v_x_80_, uint8_t v_y_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_82_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_x_80_);
v___x_83_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_y_81_);
v___x_84_ = lean_nat_dec_eq(v___x_82_, v___x_83_);
lean_dec(v___x_83_);
lean_dec(v___x_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableEqPhase___boxed(lean_object* v_x_85_, lean_object* v_y_86_){
_start:
{
uint8_t v_x_13__boxed_87_; uint8_t v_y_14__boxed_88_; uint8_t v_res_89_; lean_object* v_r_90_; 
v_x_13__boxed_87_ = lean_unbox(v_x_85_);
v_y_14__boxed_88_ = lean_unbox(v_y_86_);
v_res_89_ = l_Lean_Compiler_LCNF_instDecidableEqPhase(v_x_13__boxed_87_, v_y_14__boxed_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t v_x_91_){
_start:
{
if (v_x_91_ == 2)
{
uint8_t v___x_92_; 
v___x_92_ = 1;
return v___x_92_;
}
else
{
uint8_t v___x_93_; 
v___x_93_ = 0;
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toPurity___boxed(lean_object* v_x_94_){
_start:
{
uint8_t v_x_23__boxed_95_; uint8_t v_res_96_; lean_object* v_r_97_; 
v_x_23__boxed_95_ = lean_unbox(v_x_94_);
v_res_96_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_x_23__boxed_95_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = lean_box(0);
v___x_99_ = lean_unsigned_to_nat(16u);
v___x_100_ = lean_mk_array(v___x_99_, v___x_98_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0);
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_101_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1);
v___x_105_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
lean_ctor_set(v___x_105_, 2, v___x_104_);
lean_ctor_set(v___x_105_, 3, v___x_104_);
lean_ctor_set(v___x_105_, 4, v___x_104_);
lean_ctor_set(v___x_105_, 5, v___x_104_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_106_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default(void){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default;
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0(void){
_start:
{
lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_113_; 
v___x_111_ = l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default;
v___x_112_ = 0;
v___x_113_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*1, v___x_112_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext(void){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default;
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(lean_object* v_00_u03b1_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v___y_117_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object* v_00_u03b1_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(v_00_u03b1_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object* v_00_u03b1_132_, lean_object* v_00_u03b2_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v___x_141_; 
lean_inc(v___y_139_);
lean_inc_ref(v___y_138_);
lean_inc(v___y_137_);
lean_inc_ref(v___y_136_);
v___x_141_ = lean_apply_5(v___y_134_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, lean_box(0));
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_143_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_a_142_);
lean_dec_ref_known(v___x_141_, 1);
lean_inc(v___y_139_);
lean_inc_ref(v___y_138_);
lean_inc(v___y_137_);
lean_inc_ref(v___y_136_);
v___x_143_ = lean_apply_6(v___y_135_, v_a_142_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, lean_box(0));
return v___x_143_;
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
lean_dec_ref(v___y_135_);
v_a_144_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_141_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_141_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object* v_00_u03b1_152_, lean_object* v_00_u03b2_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(v_00_u03b1_152_, v_00_u03b2_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
return v_res_161_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0(void){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_instMonadEIO(lean_box(0));
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0);
v___x_164_ = l_StateRefT_x27_instMonad___redArg(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM(void){
_start:
{
lean_object* v___x_169_; lean_object* v_toApplicative_170_; lean_object* v_toFunctor_171_; lean_object* v_toSeq_172_; lean_object* v_toSeqLeft_173_; lean_object* v_toSeqRight_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___f_177_; lean_object* v___f_178_; lean_object* v___x_179_; lean_object* v___f_180_; lean_object* v___f_181_; lean_object* v___f_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_toApplicative_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_213_; 
v___x_169_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_170_ = lean_ctor_get(v___x_169_, 0);
v_toFunctor_171_ = lean_ctor_get(v_toApplicative_170_, 0);
v_toSeq_172_ = lean_ctor_get(v_toApplicative_170_, 2);
v_toSeqLeft_173_ = lean_ctor_get(v_toApplicative_170_, 3);
v_toSeqRight_174_ = lean_ctor_get(v_toApplicative_170_, 4);
v___f_175_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_176_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_171_, 2);
v___f_177_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_177_, 0, v_toFunctor_171_);
v___f_178_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_178_, 0, v_toFunctor_171_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___f_177_);
lean_ctor_set(v___x_179_, 1, v___f_178_);
lean_inc(v_toSeqRight_174_);
v___f_180_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_180_, 0, v_toSeqRight_174_);
lean_inc(v_toSeqLeft_173_);
v___f_181_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_181_, 0, v_toSeqLeft_173_);
lean_inc(v_toSeq_172_);
v___f_182_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_182_, 0, v_toSeq_172_);
v___x_183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_183_, 0, v___x_179_);
lean_ctor_set(v___x_183_, 1, v___f_175_);
lean_ctor_set(v___x_183_, 2, v___f_182_);
lean_ctor_set(v___x_183_, 3, v___f_181_);
lean_ctor_set(v___x_183_, 4, v___f_180_);
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___f_176_);
v___x_185_ = l_StateRefT_x27_instMonad___redArg(v___x_184_);
v_toApplicative_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v___x_185_, 1);
lean_dec(v_unused_214_);
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_213_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_toApplicative_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_213_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v_toFunctor_190_; lean_object* v_toSeq_191_; lean_object* v_toSeqLeft_192_; lean_object* v_toSeqRight_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_211_; 
v_toFunctor_190_ = lean_ctor_get(v_toApplicative_186_, 0);
v_toSeq_191_ = lean_ctor_get(v_toApplicative_186_, 2);
v_toSeqLeft_192_ = lean_ctor_get(v_toApplicative_186_, 3);
v_toSeqRight_193_ = lean_ctor_get(v_toApplicative_186_, 4);
v_isSharedCheck_211_ = !lean_is_exclusive(v_toApplicative_186_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v_toApplicative_186_, 1);
lean_dec(v_unused_212_);
v___x_195_ = v_toApplicative_186_;
v_isShared_196_ = v_isSharedCheck_211_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_toSeqRight_193_);
lean_inc(v_toSeqLeft_192_);
lean_inc(v_toSeq_191_);
lean_inc(v_toFunctor_190_);
lean_dec(v_toApplicative_186_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_211_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___x_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___f_204_; lean_object* v___x_206_; 
v___f_197_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_198_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_190_);
v___f_199_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_199_, 0, v_toFunctor_190_);
v___f_200_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_200_, 0, v_toFunctor_190_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___f_199_);
lean_ctor_set(v___x_201_, 1, v___f_200_);
v___f_202_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_202_, 0, v_toSeqRight_193_);
v___f_203_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_203_, 0, v_toSeqLeft_192_);
v___f_204_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_204_, 0, v_toSeq_191_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 4, v___f_202_);
lean_ctor_set(v___x_195_, 3, v___f_203_);
lean_ctor_set(v___x_195_, 2, v___f_204_);
lean_ctor_set(v___x_195_, 1, v___f_197_);
lean_ctor_set(v___x_195_, 0, v___x_201_);
v___x_206_ = v___x_195_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v___f_197_);
lean_ctor_set(v_reuseFailAlloc_210_, 2, v___f_204_);
lean_ctor_set(v_reuseFailAlloc_210_, 3, v___f_203_);
lean_ctor_set(v_reuseFailAlloc_210_, 4, v___f_202_);
v___x_206_ = v_reuseFailAlloc_210_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_208_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 1, v___f_198_);
lean_ctor_set(v___x_188_, 0, v___x_206_);
v___x_208_ = v___x_188_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v___f_198_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg(uint8_t v_phase_215_, lean_object* v_x_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_config_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_config_222_ = lean_ctor_get(v_a_217_, 0);
lean_inc_ref(v_config_222_);
v___x_223_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_223_, 0, v_config_222_);
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*1, v_phase_215_);
lean_inc(v_a_220_);
lean_inc_ref(v_a_219_);
lean_inc(v_a_218_);
v___x_224_ = lean_apply_5(v_x_216_, v___x_223_, v_a_218_, v_a_219_, v_a_220_, lean_box(0));
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg___boxed(lean_object* v_phase_225_, lean_object* v_x_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
uint8_t v_phase_boxed_232_; lean_object* v_res_233_; 
v_phase_boxed_232_ = lean_unbox(v_phase_225_);
v_res_233_ = l_Lean_Compiler_LCNF_withPhase___redArg(v_phase_boxed_232_, v_x_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase(lean_object* v_00_u03b1_234_, uint8_t v_phase_235_, lean_object* v_x_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_config_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_config_242_ = lean_ctor_get(v_a_237_, 0);
lean_inc_ref(v_config_242_);
v___x_243_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_243_, 0, v_config_242_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*1, v_phase_235_);
lean_inc(v_a_240_);
lean_inc_ref(v_a_239_);
lean_inc(v_a_238_);
v___x_244_ = lean_apply_5(v_x_236_, v___x_243_, v_a_238_, v_a_239_, v_a_240_, lean_box(0));
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___boxed(lean_object* v_00_u03b1_245_, lean_object* v_phase_246_, lean_object* v_x_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
uint8_t v_phase_boxed_253_; lean_object* v_res_254_; 
v_phase_boxed_253_ = lean_unbox(v_phase_246_);
v_res_254_ = l_Lean_Compiler_LCNF_withPhase(v_00_u03b1_245_, v_phase_boxed_253_, v_x_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object* v_a_255_){
_start:
{
uint8_t v_phase_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_phase_257_ = lean_ctor_get_uint8(v_a_255_, sizeof(void*)*1);
v___x_258_ = lean_box(v_phase_257_);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg___boxed(lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_260_);
lean_dec_ref(v_a_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase(lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_263_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___boxed(lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Compiler_LCNF_getPhase(v_a_269_, v_a_270_, v_a_271_, v_a_272_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object* v_a_275_){
_start:
{
lean_object* v___x_277_; lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_288_; 
v___x_277_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_275_);
v_a_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_288_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_288_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_288_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
uint8_t v___x_282_; uint8_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_282_ = lean_unbox(v_a_278_);
lean_dec(v_a_278_);
v___x_283_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_282_);
v___x_284_ = lean_box(v___x_283_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_284_);
v___x_286_ = v___x_280_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg___boxed(lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_289_);
lean_dec_ref(v_a_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity(lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_292_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___boxed(lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Compiler_LCNF_getPurity(v_a_298_, v_a_299_, v_a_300_, v_a_301_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg(lean_object* v_a_304_){
_start:
{
lean_object* v___x_306_; lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_322_; 
v___x_306_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_304_);
v_a_307_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_322_ == 0)
{
v___x_309_ = v___x_306_;
v_isShared_310_ = v_isSharedCheck_322_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_322_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
uint8_t v___x_311_; 
v___x_311_ = lean_unbox(v_a_307_);
lean_dec(v_a_307_);
if (v___x_311_ == 0)
{
uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_312_ = 1;
v___x_313_ = lean_box(v___x_312_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_313_);
v___x_315_ = v___x_309_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
else
{
uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_317_ = 0;
v___x_318_ = lean_box(v___x_317_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_318_);
v___x_320_ = v___x_309_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg___boxed(lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_323_);
lean_dec_ref(v_a_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase(lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_326_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___boxed(lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Compiler_LCNF_inBasePhase(v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
return v_res_337_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0(void){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_338_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1);
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
lean_ctor_set(v___x_343_, 2, v___x_342_);
lean_ctor_set(v___x_343_, 3, v___x_342_);
lean_ctor_set(v___x_343_, 4, v___x_341_);
lean_ctor_set(v___x_343_, 5, v___x_341_);
lean_ctor_set(v___x_343_, 6, v___x_341_);
lean_ctor_set(v___x_343_, 7, v___x_341_);
lean_ctor_set(v___x_343_, 8, v___x_341_);
lean_ctor_set(v___x_343_, 9, v___x_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(lean_object* v_msgData_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = lean_st_ref_get(v___y_348_);
v___x_351_ = lean_st_ref_get(v___y_346_);
v___x_352_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_345_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_375_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_375_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_375_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_375_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v_env_357_; lean_object* v_lctx_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_373_; 
v_env_357_ = lean_ctor_get(v___x_350_, 0);
lean_inc_ref(v_env_357_);
lean_dec(v___x_350_);
v_lctx_358_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; 
v_unused_374_ = lean_ctor_get(v___x_351_, 1);
lean_dec(v_unused_374_);
v___x_360_ = v___x_351_;
v_isShared_361_ = v_isSharedCheck_373_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_lctx_358_);
lean_dec(v___x_351_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_373_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_options_362_; uint8_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v_options_362_ = lean_ctor_get(v___y_347_, 2);
v___x_363_ = lean_unbox(v_a_353_);
lean_dec(v_a_353_);
v___x_364_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_358_, v___x_363_);
lean_dec_ref(v_lctx_358_);
v___x_365_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_362_);
v___x_366_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_366_, 0, v_env_357_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
lean_ctor_set(v___x_366_, 2, v___x_364_);
lean_ctor_set(v___x_366_, 3, v_options_362_);
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 3);
lean_ctor_set(v___x_360_, 1, v_msgData_344_);
lean_ctor_set(v___x_360_, 0, v___x_366_);
v___x_368_ = v___x_360_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_msgData_344_);
v___x_368_ = v_reuseFailAlloc_372_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_370_; 
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_368_);
v___x_370_ = v___x_355_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec(v___x_351_);
lean_dec(v___x_350_);
lean_dec_ref(v_msgData_344_);
v_a_376_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_352_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_352_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed(lean_object* v_msgData_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(v_msgData_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(lean_object* v_msg_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_options_399_; lean_object* v_ref_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_options_399_ = lean_ctor_get(v___y_396_, 2);
v_ref_400_ = lean_ctor_get(v___y_396_, 5);
v___x_401_ = lean_st_ref_get(v___y_397_);
v___x_402_ = lean_st_ref_get(v___y_395_);
v___x_403_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_394_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_426_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_426_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_426_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_426_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v_env_408_; lean_object* v_lctx_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_424_; 
v_env_408_ = lean_ctor_get(v___x_401_, 0);
lean_inc_ref(v_env_408_);
lean_dec(v___x_401_);
v_lctx_409_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v___x_402_, 1);
lean_dec(v_unused_425_);
v___x_411_ = v___x_402_;
v_isShared_412_ = v_isSharedCheck_424_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_lctx_409_);
lean_dec(v___x_402_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_424_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_413_ = lean_unbox(v_a_404_);
lean_dec(v_a_404_);
v___x_414_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_409_, v___x_413_);
lean_dec_ref(v_lctx_409_);
v___x_415_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_399_);
v___x_416_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_416_, 0, v_env_408_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
lean_ctor_set(v___x_416_, 2, v___x_414_);
lean_ctor_set(v___x_416_, 3, v_options_399_);
if (v_isShared_412_ == 0)
{
lean_ctor_set_tag(v___x_411_, 3);
lean_ctor_set(v___x_411_, 1, v_msg_393_);
lean_ctor_set(v___x_411_, 0, v___x_416_);
v___x_418_ = v___x_411_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_msg_393_);
v___x_418_ = v_reuseFailAlloc_423_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
lean_inc(v_ref_400_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v_ref_400_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 1);
lean_ctor_set(v___x_406_, 0, v___x_419_);
v___x_421_ = v___x_406_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec(v___x_402_);
lean_dec(v___x_401_);
lean_dec_ref(v_msg_393_);
v_a_427_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_403_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_403_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg___boxed(lean_object* v_msg_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(lean_object* v_00_u03b1_442_, lean_object* v_msg_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___boxed(lean_object* v_00_u03b1_450_, lean_object* v_msg_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(v_00_u03b1_450_, v_msg_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(lean_object* v_a_458_, lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_459_) == 0)
{
lean_object* v___x_460_; 
v___x_460_ = lean_box(0);
return v___x_460_;
}
else
{
lean_object* v_key_461_; lean_object* v_value_462_; lean_object* v_tail_463_; uint8_t v___x_464_; 
v_key_461_ = lean_ctor_get(v_x_459_, 0);
v_value_462_ = lean_ctor_get(v_x_459_, 1);
v_tail_463_ = lean_ctor_get(v_x_459_, 2);
v___x_464_ = l_Lean_instBEqFVarId_beq(v_key_461_, v_a_458_);
if (v___x_464_ == 0)
{
v_x_459_ = v_tail_463_;
goto _start;
}
else
{
lean_object* v___x_466_; 
lean_inc(v_value_462_);
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v_value_462_);
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg___boxed(lean_object* v_a_467_, lean_object* v_x_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_467_, v_x_468_);
lean_dec(v_x_468_);
lean_dec(v_a_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object* v_m_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_buckets_472_; lean_object* v___x_473_; uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v___x_476_; uint64_t v_fold_477_; uint64_t v___x_478_; uint64_t v___x_479_; uint64_t v___x_480_; size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_buckets_472_ = lean_ctor_get(v_m_470_, 1);
v___x_473_ = lean_array_get_size(v_buckets_472_);
v___x_474_ = l_Lean_instHashableFVarId_hash(v_a_471_);
v___x_475_ = 32ULL;
v___x_476_ = lean_uint64_shift_right(v___x_474_, v___x_475_);
v_fold_477_ = lean_uint64_xor(v___x_474_, v___x_476_);
v___x_478_ = 16ULL;
v___x_479_ = lean_uint64_shift_right(v_fold_477_, v___x_478_);
v___x_480_ = lean_uint64_xor(v_fold_477_, v___x_479_);
v___x_481_ = lean_uint64_to_usize(v___x_480_);
v___x_482_ = lean_usize_of_nat(v___x_473_);
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_sub(v___x_482_, v___x_483_);
v___x_485_ = lean_usize_land(v___x_481_, v___x_484_);
v___x_486_ = lean_array_uget_borrowed(v_buckets_472_, v___x_485_);
v___x_487_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_471_, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg___boxed(lean_object* v_m_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_488_, v_a_489_);
lean_dec(v_a_489_);
lean_dec_ref(v_m_488_);
return v_res_490_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getType___closed__1(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_Compiler_LCNF_getType___closed__0));
v___x_493_ = l_Lean_stringToMessageData(v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType(lean_object* v_fvarId_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_st_ref_get(v_a_496_);
v___x_501_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_495_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_552_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_552_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_552_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_552_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___y_507_; lean_object* v_lctx_518_; lean_object* v___y_520_; lean_object* v___y_535_; uint8_t v___x_549_; 
v_lctx_518_ = lean_ctor_get(v___x_500_, 0);
lean_inc_ref(v_lctx_518_);
lean_dec(v___x_500_);
v___x_549_ = lean_unbox(v_a_502_);
if (v___x_549_ == 0)
{
lean_object* v_letDeclsPure_550_; 
v_letDeclsPure_550_ = lean_ctor_get(v_lctx_518_, 2);
lean_inc_ref(v_letDeclsPure_550_);
v___y_535_ = v_letDeclsPure_550_;
goto v___jp_534_;
}
else
{
lean_object* v_letDeclsImpure_551_; 
v_letDeclsImpure_551_ = lean_ctor_get(v_lctx_518_, 3);
lean_inc_ref(v_letDeclsImpure_551_);
v___y_535_ = v_letDeclsImpure_551_;
goto v___jp_534_;
}
v___jp_506_:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_507_, v_fvarId_494_);
lean_dec_ref(v___y_507_);
if (lean_obj_tag(v___x_508_) == 1)
{
lean_object* v_val_509_; lean_object* v_type_510_; lean_object* v___x_512_; 
lean_dec(v_fvarId_494_);
v_val_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_val_509_);
lean_dec_ref_known(v___x_508_, 1);
v_type_510_ = lean_ctor_get(v_val_509_, 3);
lean_inc_ref(v_type_510_);
lean_dec(v_val_509_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v_type_510_);
v___x_512_ = v___x_504_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_type_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec(v___x_508_);
lean_del_object(v___x_504_);
v___x_514_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_515_ = l_Lean_MessageData_ofName(v_fvarId_494_);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_516_, v_a_495_, v_a_496_, v_a_497_, v_a_498_);
return v___x_517_;
}
}
v___jp_519_:
{
lean_object* v___x_521_; 
v___x_521_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_520_, v_fvarId_494_);
lean_dec_ref(v___y_520_);
if (lean_obj_tag(v___x_521_) == 1)
{
lean_object* v_val_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_530_; 
lean_dec_ref(v_lctx_518_);
lean_del_object(v___x_504_);
lean_dec(v_a_502_);
lean_dec(v_fvarId_494_);
v_val_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_530_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_val_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_type_526_; lean_object* v___x_528_; 
v_type_526_ = lean_ctor_get(v_val_522_, 2);
lean_inc_ref(v_type_526_);
lean_dec(v_val_522_);
if (v_isShared_525_ == 0)
{
lean_ctor_set_tag(v___x_524_, 0);
lean_ctor_set(v___x_524_, 0, v_type_526_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_type_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
else
{
uint8_t v___x_531_; 
lean_dec(v___x_521_);
v___x_531_ = lean_unbox(v_a_502_);
lean_dec(v_a_502_);
if (v___x_531_ == 0)
{
lean_object* v_funDeclsPure_532_; 
v_funDeclsPure_532_ = lean_ctor_get(v_lctx_518_, 4);
lean_inc_ref(v_funDeclsPure_532_);
lean_dec_ref(v_lctx_518_);
v___y_507_ = v_funDeclsPure_532_;
goto v___jp_506_;
}
else
{
lean_object* v_funDeclsImpure_533_; 
v_funDeclsImpure_533_ = lean_ctor_get(v_lctx_518_, 5);
lean_inc_ref(v_funDeclsImpure_533_);
lean_dec_ref(v_lctx_518_);
v___y_507_ = v_funDeclsImpure_533_;
goto v___jp_506_;
}
}
}
v___jp_534_:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_535_, v_fvarId_494_);
lean_dec_ref(v___y_535_);
if (lean_obj_tag(v___x_536_) == 1)
{
lean_object* v_val_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v_lctx_518_);
lean_del_object(v___x_504_);
lean_dec(v_a_502_);
lean_dec(v_fvarId_494_);
v_val_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_545_ == 0)
{
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_545_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_val_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_545_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_type_541_; lean_object* v___x_543_; 
v_type_541_ = lean_ctor_get(v_val_537_, 2);
lean_inc_ref(v_type_541_);
lean_dec(v_val_537_);
if (v_isShared_540_ == 0)
{
lean_ctor_set_tag(v___x_539_, 0);
lean_ctor_set(v___x_539_, 0, v_type_541_);
v___x_543_ = v___x_539_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_type_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
else
{
uint8_t v___x_546_; 
lean_dec(v___x_536_);
v___x_546_ = lean_unbox(v_a_502_);
if (v___x_546_ == 0)
{
lean_object* v_paramsPure_547_; 
v_paramsPure_547_ = lean_ctor_get(v_lctx_518_, 0);
lean_inc_ref(v_paramsPure_547_);
v___y_520_ = v_paramsPure_547_;
goto v___jp_519_;
}
else
{
lean_object* v_paramsImpure_548_; 
v_paramsImpure_548_ = lean_ctor_get(v_lctx_518_, 1);
lean_inc_ref(v_paramsImpure_548_);
v___y_520_ = v_paramsImpure_548_;
goto v___jp_519_;
}
}
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec(v___x_500_);
lean_dec(v_fvarId_494_);
v_a_553_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_501_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_501_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType___boxed(lean_object* v_fvarId_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Compiler_LCNF_getType(v_fvarId_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(lean_object* v_00_u03b2_568_, lean_object* v_m_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_569_, v_a_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(lean_object* v_00_u03b2_572_, lean_object* v_m_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(v_00_u03b2_572_, v_m_573_, v_a_574_);
lean_dec(v_a_574_);
lean_dec_ref(v_m_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(lean_object* v_00_u03b2_576_, lean_object* v_a_577_, lean_object* v_x_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_577_, v_x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_580_, lean_object* v_a_581_, lean_object* v_x_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(v_00_u03b2_580_, v_a_581_, v_x_582_);
lean_dec(v_x_582_);
lean_dec(v_a_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object* v_fvarId_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_st_ref_get(v_a_586_);
v___x_591_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_585_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_642_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_642_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_642_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_642_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___y_597_; lean_object* v_lctx_608_; lean_object* v___y_610_; lean_object* v___y_625_; uint8_t v___x_639_; 
v_lctx_608_ = lean_ctor_get(v___x_590_, 0);
lean_inc_ref(v_lctx_608_);
lean_dec(v___x_590_);
v___x_639_ = lean_unbox(v_a_592_);
if (v___x_639_ == 0)
{
lean_object* v_letDeclsPure_640_; 
v_letDeclsPure_640_ = lean_ctor_get(v_lctx_608_, 2);
lean_inc_ref(v_letDeclsPure_640_);
v___y_625_ = v_letDeclsPure_640_;
goto v___jp_624_;
}
else
{
lean_object* v_letDeclsImpure_641_; 
v_letDeclsImpure_641_ = lean_ctor_get(v_lctx_608_, 3);
lean_inc_ref(v_letDeclsImpure_641_);
v___y_625_ = v_letDeclsImpure_641_;
goto v___jp_624_;
}
v___jp_596_:
{
lean_object* v___x_598_; 
v___x_598_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_597_, v_fvarId_584_);
lean_dec_ref(v___y_597_);
if (lean_obj_tag(v___x_598_) == 1)
{
lean_object* v_val_599_; lean_object* v_binderName_600_; lean_object* v___x_602_; 
lean_dec(v_fvarId_584_);
v_val_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_val_599_);
lean_dec_ref_known(v___x_598_, 1);
v_binderName_600_ = lean_ctor_get(v_val_599_, 1);
lean_inc(v_binderName_600_);
lean_dec(v_val_599_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v_binderName_600_);
v___x_602_ = v___x_594_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_binderName_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec(v___x_598_);
lean_del_object(v___x_594_);
v___x_604_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_605_ = l_Lean_MessageData_ofName(v_fvarId_584_);
v___x_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_606_, v_a_585_, v_a_586_, v_a_587_, v_a_588_);
return v___x_607_;
}
}
v___jp_609_:
{
lean_object* v___x_611_; 
v___x_611_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_610_, v_fvarId_584_);
lean_dec_ref(v___y_610_);
if (lean_obj_tag(v___x_611_) == 1)
{
lean_object* v_val_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_620_; 
lean_dec_ref(v_lctx_608_);
lean_del_object(v___x_594_);
lean_dec(v_a_592_);
lean_dec(v_fvarId_584_);
v_val_612_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_620_ == 0)
{
v___x_614_ = v___x_611_;
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_val_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_binderName_616_; lean_object* v___x_618_; 
v_binderName_616_ = lean_ctor_get(v_val_612_, 1);
lean_inc(v_binderName_616_);
lean_dec(v_val_612_);
if (v_isShared_615_ == 0)
{
lean_ctor_set_tag(v___x_614_, 0);
lean_ctor_set(v___x_614_, 0, v_binderName_616_);
v___x_618_ = v___x_614_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_binderName_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
else
{
uint8_t v___x_621_; 
lean_dec(v___x_611_);
v___x_621_ = lean_unbox(v_a_592_);
lean_dec(v_a_592_);
if (v___x_621_ == 0)
{
lean_object* v_funDeclsPure_622_; 
v_funDeclsPure_622_ = lean_ctor_get(v_lctx_608_, 4);
lean_inc_ref(v_funDeclsPure_622_);
lean_dec_ref(v_lctx_608_);
v___y_597_ = v_funDeclsPure_622_;
goto v___jp_596_;
}
else
{
lean_object* v_funDeclsImpure_623_; 
v_funDeclsImpure_623_ = lean_ctor_get(v_lctx_608_, 5);
lean_inc_ref(v_funDeclsImpure_623_);
lean_dec_ref(v_lctx_608_);
v___y_597_ = v_funDeclsImpure_623_;
goto v___jp_596_;
}
}
}
v___jp_624_:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_625_, v_fvarId_584_);
lean_dec_ref(v___y_625_);
if (lean_obj_tag(v___x_626_) == 1)
{
lean_object* v_val_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v_lctx_608_);
lean_del_object(v___x_594_);
lean_dec(v_a_592_);
lean_dec(v_fvarId_584_);
v_val_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_635_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_val_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v_binderName_631_; lean_object* v___x_633_; 
v_binderName_631_ = lean_ctor_get(v_val_627_, 1);
lean_inc(v_binderName_631_);
lean_dec(v_val_627_);
if (v_isShared_630_ == 0)
{
lean_ctor_set_tag(v___x_629_, 0);
lean_ctor_set(v___x_629_, 0, v_binderName_631_);
v___x_633_ = v___x_629_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_binderName_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
else
{
uint8_t v___x_636_; 
lean_dec(v___x_626_);
v___x_636_ = lean_unbox(v_a_592_);
if (v___x_636_ == 0)
{
lean_object* v_paramsPure_637_; 
v_paramsPure_637_ = lean_ctor_get(v_lctx_608_, 0);
lean_inc_ref(v_paramsPure_637_);
v___y_610_ = v_paramsPure_637_;
goto v___jp_609_;
}
else
{
lean_object* v_paramsImpure_638_; 
v_paramsImpure_638_ = lean_ctor_get(v_lctx_608_, 1);
lean_inc_ref(v_paramsImpure_638_);
v___y_610_ = v_paramsImpure_638_;
goto v___jp_609_;
}
}
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v___x_590_);
lean_dec(v_fvarId_584_);
v_a_643_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_591_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_591_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName___boxed(lean_object* v_fvarId_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t v_pu_658_, lean_object* v_fvarId_659_, lean_object* v_a_660_){
_start:
{
lean_object* v___x_662_; lean_object* v___y_664_; 
v___x_662_ = lean_st_ref_get(v_a_660_);
if (v_pu_658_ == 0)
{
lean_object* v_lctx_667_; lean_object* v_paramsPure_668_; 
v_lctx_667_ = lean_ctor_get(v___x_662_, 0);
lean_inc_ref(v_lctx_667_);
lean_dec(v___x_662_);
v_paramsPure_668_ = lean_ctor_get(v_lctx_667_, 0);
lean_inc_ref(v_paramsPure_668_);
lean_dec_ref(v_lctx_667_);
v___y_664_ = v_paramsPure_668_;
goto v___jp_663_;
}
else
{
lean_object* v_lctx_669_; lean_object* v_paramsImpure_670_; 
v_lctx_669_ = lean_ctor_get(v___x_662_, 0);
lean_inc_ref(v_lctx_669_);
lean_dec(v___x_662_);
v_paramsImpure_670_ = lean_ctor_get(v_lctx_669_, 1);
lean_inc_ref(v_paramsImpure_670_);
lean_dec_ref(v_lctx_669_);
v___y_664_ = v_paramsImpure_670_;
goto v___jp_663_;
}
v___jp_663_:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_664_, v_fvarId_659_);
lean_dec_ref(v___y_664_);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(lean_object* v_pu_671_, lean_object* v_fvarId_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
uint8_t v_pu_boxed_675_; lean_object* v_res_676_; 
v_pu_boxed_675_ = lean_unbox(v_pu_671_);
v_res_676_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_boxed_675_, v_fvarId_672_, v_a_673_);
lean_dec(v_a_673_);
lean_dec(v_fvarId_672_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f(uint8_t v_pu_677_, lean_object* v_fvarId_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_677_, v_fvarId_678_, v_a_680_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___boxed(lean_object* v_pu_685_, lean_object* v_fvarId_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
uint8_t v_pu_boxed_692_; lean_object* v_res_693_; 
v_pu_boxed_692_ = lean_unbox(v_pu_685_);
v_res_693_ = l_Lean_Compiler_LCNF_findParam_x3f(v_pu_boxed_692_, v_fvarId_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_fvarId_686_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t v_pu_694_, lean_object* v_fvarId_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___x_698_; lean_object* v___y_700_; 
v___x_698_ = lean_st_ref_get(v_a_696_);
if (v_pu_694_ == 0)
{
lean_object* v_lctx_703_; lean_object* v_letDeclsPure_704_; 
v_lctx_703_ = lean_ctor_get(v___x_698_, 0);
lean_inc_ref(v_lctx_703_);
lean_dec(v___x_698_);
v_letDeclsPure_704_ = lean_ctor_get(v_lctx_703_, 2);
lean_inc_ref(v_letDeclsPure_704_);
lean_dec_ref(v_lctx_703_);
v___y_700_ = v_letDeclsPure_704_;
goto v___jp_699_;
}
else
{
lean_object* v_lctx_705_; lean_object* v_letDeclsImpure_706_; 
v_lctx_705_ = lean_ctor_get(v___x_698_, 0);
lean_inc_ref(v_lctx_705_);
lean_dec(v___x_698_);
v_letDeclsImpure_706_ = lean_ctor_get(v_lctx_705_, 3);
lean_inc_ref(v_letDeclsImpure_706_);
lean_dec_ref(v_lctx_705_);
v___y_700_ = v_letDeclsImpure_706_;
goto v___jp_699_;
}
v___jp_699_:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_700_, v_fvarId_695_);
lean_dec_ref(v___y_700_);
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(lean_object* v_pu_707_, lean_object* v_fvarId_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
uint8_t v_pu_boxed_711_; lean_object* v_res_712_; 
v_pu_boxed_711_ = lean_unbox(v_pu_707_);
v_res_712_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_boxed_711_, v_fvarId_708_, v_a_709_);
lean_dec(v_a_709_);
lean_dec(v_fvarId_708_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(uint8_t v_pu_713_, lean_object* v_fvarId_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_713_, v_fvarId_714_, v_a_716_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(lean_object* v_pu_721_, lean_object* v_fvarId_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
uint8_t v_pu_boxed_728_; lean_object* v_res_729_; 
v_pu_boxed_728_ = lean_unbox(v_pu_721_);
v_res_729_ = l_Lean_Compiler_LCNF_findLetDecl_x3f(v_pu_boxed_728_, v_fvarId_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_fvarId_722_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t v_pu_730_, lean_object* v_fvarId_731_, lean_object* v_a_732_){
_start:
{
lean_object* v___x_734_; lean_object* v___y_736_; 
v___x_734_ = lean_st_ref_get(v_a_732_);
if (v_pu_730_ == 0)
{
lean_object* v_lctx_739_; lean_object* v_funDeclsPure_740_; 
v_lctx_739_ = lean_ctor_get(v___x_734_, 0);
lean_inc_ref(v_lctx_739_);
lean_dec(v___x_734_);
v_funDeclsPure_740_ = lean_ctor_get(v_lctx_739_, 4);
lean_inc_ref(v_funDeclsPure_740_);
lean_dec_ref(v_lctx_739_);
v___y_736_ = v_funDeclsPure_740_;
goto v___jp_735_;
}
else
{
lean_object* v_lctx_741_; lean_object* v_funDeclsImpure_742_; 
v_lctx_741_ = lean_ctor_get(v___x_734_, 0);
lean_inc_ref(v_lctx_741_);
lean_dec(v___x_734_);
v_funDeclsImpure_742_ = lean_ctor_get(v_lctx_741_, 5);
lean_inc_ref(v_funDeclsImpure_742_);
lean_dec_ref(v_lctx_741_);
v___y_736_ = v_funDeclsImpure_742_;
goto v___jp_735_;
}
v___jp_735_:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_736_, v_fvarId_731_);
lean_dec_ref(v___y_736_);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(lean_object* v_pu_743_, lean_object* v_fvarId_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
uint8_t v_pu_boxed_747_; lean_object* v_res_748_; 
v_pu_boxed_747_ = lean_unbox(v_pu_743_);
v_res_748_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_boxed_747_, v_fvarId_744_, v_a_745_);
lean_dec(v_a_745_);
lean_dec(v_fvarId_744_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(uint8_t v_pu_749_, lean_object* v_fvarId_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_749_, v_fvarId_750_, v_a_752_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(lean_object* v_pu_757_, lean_object* v_fvarId_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
uint8_t v_pu_boxed_764_; lean_object* v_res_765_; 
v_pu_boxed_764_ = lean_unbox(v_pu_757_);
v_res_765_ = l_Lean_Compiler_LCNF_findFunDecl_x3f(v_pu_boxed_764_, v_fvarId_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_fvarId_758_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t v_pu_766_, lean_object* v_fvarId_767_, lean_object* v_a_768_){
_start:
{
lean_object* v___x_770_; lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_791_; 
v___x_770_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_766_, v_fvarId_767_, v_a_768_);
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_791_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_791_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_791_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
if (lean_obj_tag(v_a_771_) == 1)
{
lean_object* v_val_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_786_; 
v_val_775_ = lean_ctor_get(v_a_771_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v_a_771_);
if (v_isSharedCheck_786_ == 0)
{
v___x_777_ = v_a_771_;
v_isShared_778_ = v_isSharedCheck_786_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_val_775_);
lean_dec(v_a_771_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_786_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_value_779_; lean_object* v___x_781_; 
v_value_779_ = lean_ctor_get(v_val_775_, 3);
lean_inc(v_value_779_);
lean_dec(v_val_775_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v_value_779_);
v___x_781_ = v___x_777_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_value_779_);
v___x_781_ = v_reuseFailAlloc_785_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_781_);
v___x_783_ = v___x_773_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v___x_787_; lean_object* v___x_789_; 
lean_dec(v_a_771_);
v___x_787_ = lean_box(0);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_787_);
v___x_789_ = v___x_773_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg___boxed(lean_object* v_pu_792_, lean_object* v_fvarId_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
uint8_t v_pu_boxed_796_; lean_object* v_res_797_; 
v_pu_boxed_796_ = lean_unbox(v_pu_792_);
v_res_797_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_boxed_796_, v_fvarId_793_, v_a_794_);
lean_dec(v_a_794_);
lean_dec(v_fvarId_793_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f(uint8_t v_pu_798_, lean_object* v_fvarId_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_798_, v_fvarId_799_, v_a_801_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(lean_object* v_pu_806_, lean_object* v_fvarId_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
uint8_t v_pu_boxed_813_; lean_object* v_res_814_; 
v_pu_boxed_813_ = lean_unbox(v_pu_806_);
v_res_814_ = l_Lean_Compiler_LCNF_findLetValue_x3f(v_pu_boxed_813_, v_fvarId_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_fvarId_807_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg(lean_object* v_fvarId_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
uint8_t v___x_819_; lean_object* v___x_820_; 
v___x_819_ = 0;
v___x_820_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_819_, v_fvarId_815_, v_a_816_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_858_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_858_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_858_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_858_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
if (lean_obj_tag(v_a_821_) == 1)
{
lean_object* v_val_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_857_; 
v_val_831_ = lean_ctor_get(v_a_821_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v_a_821_);
if (v_isSharedCheck_857_ == 0)
{
v___x_833_ = v_a_821_;
v_isShared_834_ = v_isSharedCheck_857_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_val_831_);
lean_dec(v_a_821_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_857_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
if (lean_obj_tag(v_val_831_) == 3)
{
lean_object* v_declName_835_; lean_object* v___x_836_; lean_object* v_env_847_; lean_object* v___x_855_; 
lean_del_object(v___x_823_);
v_declName_835_ = lean_ctor_get(v_val_831_, 0);
lean_inc_n(v_declName_835_, 2);
lean_dec_ref_known(v_val_831_, 3);
v___x_836_ = lean_st_ref_get(v_a_817_);
v_env_847_ = lean_ctor_get(v___x_836_, 0);
lean_inc_ref_n(v_env_847_, 2);
lean_dec(v___x_836_);
v___x_855_ = l_Lean_Compiler_getInductiveOverride_x3f(v_env_847_, v_declName_835_);
if (lean_obj_tag(v___x_855_) == 1)
{
lean_object* v_val_856_; 
v_val_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_val_856_);
lean_dec_ref_known(v___x_855_, 1);
if (lean_obj_tag(v_val_856_) == 2)
{
lean_dec_ref_known(v_val_856_, 2);
lean_dec_ref(v_env_847_);
lean_dec(v_declName_835_);
lean_del_object(v___x_833_);
goto v___jp_843_;
}
else
{
lean_dec(v_val_856_);
goto v___jp_848_;
}
}
else
{
lean_dec(v___x_855_);
goto v___jp_848_;
}
v___jp_837_:
{
uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_838_ = 0;
v___x_839_ = lean_box(v___x_838_);
if (v_isShared_834_ == 0)
{
lean_ctor_set_tag(v___x_833_, 0);
lean_ctor_set(v___x_833_, 0, v___x_839_);
v___x_841_ = v___x_833_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
v___jp_843_:
{
uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = 1;
v___x_845_ = lean_box(v___x_844_);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
return v___x_846_;
}
v___jp_848_:
{
uint8_t v___x_849_; lean_object* v___x_850_; 
v___x_849_ = 0;
lean_inc_ref(v_env_847_);
v___x_850_ = l_Lean_Environment_find_x3f(v_env_847_, v_declName_835_, v___x_849_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_dec_ref(v_env_847_);
goto v___jp_837_;
}
else
{
lean_object* v_val_851_; 
v_val_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_val_851_);
lean_dec_ref_known(v___x_850_, 1);
if (lean_obj_tag(v_val_851_) == 6)
{
lean_object* v_val_852_; lean_object* v_induct_853_; uint8_t v___x_854_; 
v_val_852_ = lean_ctor_get(v_val_851_, 0);
lean_inc_ref(v_val_852_);
lean_dec_ref_known(v_val_851_, 1);
v_induct_853_ = lean_ctor_get(v_val_852_, 1);
lean_inc(v_induct_853_);
lean_dec_ref(v_val_852_);
v___x_854_ = l_Lean_Compiler_hasInductiveOverride(v_env_847_, v_induct_853_);
if (v___x_854_ == 0)
{
lean_del_object(v___x_833_);
goto v___jp_843_;
}
else
{
goto v___jp_837_;
}
}
else
{
lean_dec(v_val_851_);
lean_dec_ref(v_env_847_);
goto v___jp_837_;
}
}
}
}
else
{
lean_del_object(v___x_833_);
lean_dec(v_val_831_);
goto v___jp_825_;
}
}
}
else
{
lean_dec(v_a_821_);
goto v___jp_825_;
}
v___jp_825_:
{
uint8_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_826_ = 0;
v___x_827_ = lean_box(v___x_826_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_827_);
v___x_829_ = v___x_823_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
v_a_859_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_820_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_820_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg___boxed(lean_object* v_fvarId_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_867_, v_a_868_, v_a_869_);
lean_dec(v_a_869_);
lean_dec(v_a_868_);
lean_dec(v_fvarId_867_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp(lean_object* v_fvarId_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_872_, v_a_874_, v_a_876_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___boxed(lean_object* v_fvarId_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_Compiler_LCNF_isConstructorApp(v_fvarId_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_fvarId_879_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object* v_arg_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
if (lean_obj_tag(v_arg_886_) == 1)
{
lean_object* v_fvarId_890_; lean_object* v___x_891_; 
v_fvarId_890_ = lean_ctor_get(v_arg_886_, 0);
v___x_891_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_890_, v_a_887_, v_a_888_);
return v___x_891_;
}
else
{
uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = 0;
v___x_893_ = lean_box(v___x_892_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(lean_object* v_arg_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_895_, v_a_896_, v_a_897_);
lean_dec(v_a_897_);
lean_dec(v_a_896_);
lean_dec(v_arg_895_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp(uint8_t v_pu_900_, lean_object* v_arg_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_901_, v_a_903_, v_a_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(lean_object* v_pu_908_, lean_object* v_arg_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
uint8_t v_pu_boxed_915_; lean_object* v_res_916_; 
v_pu_boxed_915_ = lean_unbox(v_pu_908_);
v_res_916_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp(v_pu_boxed_915_, v_arg_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_arg_909_);
return v_res_916_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getParam___closed__1(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParam___closed__0));
v___x_919_ = l_Lean_stringToMessageData(v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam(uint8_t v_pu_920_, lean_object* v_fvarId_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v___x_927_; lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_940_; 
v___x_927_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_920_, v_fvarId_921_, v_a_923_);
v_a_928_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_940_ == 0)
{
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_940_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_940_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
if (lean_obj_tag(v_a_928_) == 1)
{
lean_object* v_val_932_; lean_object* v___x_934_; 
lean_dec(v_fvarId_921_);
v_val_932_ = lean_ctor_get(v_a_928_, 0);
lean_inc(v_val_932_);
lean_dec_ref_known(v_a_928_, 1);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v_val_932_);
v___x_934_ = v___x_930_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_val_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
lean_del_object(v___x_930_);
lean_dec(v_a_928_);
v___x_936_ = lean_obj_once(&l_Lean_Compiler_LCNF_getParam___closed__1, &l_Lean_Compiler_LCNF_getParam___closed__1_once, _init_l_Lean_Compiler_LCNF_getParam___closed__1);
v___x_937_ = l_Lean_MessageData_ofName(v_fvarId_921_);
v___x_938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_938_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
return v___x_939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam___boxed(lean_object* v_pu_941_, lean_object* v_fvarId_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
uint8_t v_pu_boxed_948_; lean_object* v_res_949_; 
v_pu_boxed_948_ = lean_unbox(v_pu_941_);
v_res_949_ = l_Lean_Compiler_LCNF_getParam(v_pu_boxed_948_, v_fvarId_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
return v_res_949_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l_Lean_Compiler_LCNF_getLetDecl___closed__0));
v___x_952_ = l_Lean_stringToMessageData(v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl(uint8_t v_pu_953_, lean_object* v_fvarId_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___x_960_; lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_973_; 
v___x_960_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_953_, v_fvarId_954_, v_a_956_);
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_973_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_973_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_973_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
if (lean_obj_tag(v_a_961_) == 1)
{
lean_object* v_val_965_; lean_object* v___x_967_; 
lean_dec(v_fvarId_954_);
v_val_965_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_val_965_);
lean_dec_ref_known(v_a_961_, 1);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v_val_965_);
v___x_967_ = v___x_963_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_val_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
lean_del_object(v___x_963_);
lean_dec(v_a_961_);
v___x_969_ = lean_obj_once(&l_Lean_Compiler_LCNF_getLetDecl___closed__1, &l_Lean_Compiler_LCNF_getLetDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1);
v___x_970_ = l_Lean_MessageData_ofName(v_fvarId_954_);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_971_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
return v___x_972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl___boxed(lean_object* v_pu_974_, lean_object* v_fvarId_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
uint8_t v_pu_boxed_981_; lean_object* v_res_982_; 
v_pu_boxed_981_ = lean_unbox(v_pu_974_);
v_res_982_ = l_Lean_Compiler_LCNF_getLetDecl(v_pu_boxed_981_, v_fvarId_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
return v_res_982_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_Compiler_LCNF_getFunDecl___closed__0));
v___x_985_ = l_Lean_stringToMessageData(v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t v_pu_986_, lean_object* v_fvarId_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___x_993_; lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1006_; 
v___x_993_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_986_, v_fvarId_987_, v_a_989_);
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1006_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1006_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
if (lean_obj_tag(v_a_994_) == 1)
{
lean_object* v_val_998_; lean_object* v___x_1000_; 
lean_dec(v_fvarId_987_);
v_val_998_ = lean_ctor_get(v_a_994_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v_a_994_, 1);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v_val_998_);
v___x_1000_ = v___x_996_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_val_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_del_object(v___x_996_);
lean_dec(v_a_994_);
v___x_1002_ = lean_obj_once(&l_Lean_Compiler_LCNF_getFunDecl___closed__1, &l_Lean_Compiler_LCNF_getFunDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1);
v___x_1003_ = l_Lean_MessageData_ofName(v_fvarId_987_);
v___x_1004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_1004_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
return v___x_1005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl___boxed(lean_object* v_pu_1007_, lean_object* v_fvarId_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
uint8_t v_pu_boxed_1014_; lean_object* v_res_1015_; 
v_pu_boxed_1014_ = lean_unbox(v_pu_1007_);
v_res_1015_ = l_Lean_Compiler_LCNF_getFunDecl(v_pu_boxed_1014_, v_fvarId_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg(lean_object* v_f_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___x_1019_; lean_object* v_lctx_1020_; lean_object* v_nextIdx_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1032_; 
v___x_1019_ = lean_st_ref_take(v_a_1017_);
v_lctx_1020_ = lean_ctor_get(v___x_1019_, 0);
v_nextIdx_1021_ = lean_ctor_get(v___x_1019_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1023_ = v___x_1019_;
v_isShared_1024_ = v_isSharedCheck_1032_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_nextIdx_1021_);
lean_inc(v_lctx_1020_);
lean_dec(v___x_1019_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1032_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1025_ = lean_apply_1(v_f_1016_, v_lctx_1020_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1025_);
v___x_1027_ = v___x_1023_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_nextIdx_1021_);
v___x_1027_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = lean_st_ref_set(v_a_1017_, v___x_1027_);
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(lean_object* v_f_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_Compiler_LCNF_modifyLCtx___redArg(v_f_1033_, v_a_1034_);
lean_dec(v_a_1034_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx(lean_object* v_f_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v_lctx_1044_; lean_object* v_nextIdx_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1056_; 
v___x_1043_ = lean_st_ref_take(v_a_1039_);
v_lctx_1044_ = lean_ctor_get(v___x_1043_, 0);
v_nextIdx_1045_ = lean_ctor_get(v___x_1043_, 1);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1047_ = v___x_1043_;
v_isShared_1048_ = v_isSharedCheck_1056_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_nextIdx_1045_);
lean_inc(v_lctx_1044_);
lean_dec(v___x_1043_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1056_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1049_ = lean_apply_1(v_f_1037_, v_lctx_1044_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1049_);
v___x_1051_ = v___x_1047_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_nextIdx_1045_);
v___x_1051_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = lean_st_ref_set(v_a_1039_, v___x_1051_);
v___x_1053_ = lean_box(0);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___boxed(lean_object* v_f_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_Compiler_LCNF_modifyLCtx(v_f_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t v_pu_1064_, lean_object* v_decl_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v___x_1068_; lean_object* v_lctx_1069_; lean_object* v_nextIdx_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1081_; 
v___x_1068_ = lean_st_ref_take(v_a_1066_);
v_lctx_1069_ = lean_ctor_get(v___x_1068_, 0);
v_nextIdx_1070_ = lean_ctor_get(v___x_1068_, 1);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1072_ = v___x_1068_;
v_isShared_1073_ = v_isSharedCheck_1081_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_nextIdx_1070_);
lean_inc(v_lctx_1069_);
lean_dec(v___x_1068_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1081_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_1064_, v_lctx_1069_, v_decl_1065_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1074_);
v___x_1076_ = v___x_1072_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_nextIdx_1070_);
v___x_1076_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = lean_st_ref_set(v_a_1066_, v___x_1076_);
v___x_1078_ = lean_box(0);
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(lean_object* v_pu_1082_, lean_object* v_decl_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
uint8_t v_pu_boxed_1086_; lean_object* v_res_1087_; 
v_pu_boxed_1086_ = lean_unbox(v_pu_1082_);
v_res_1087_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_boxed_1086_, v_decl_1083_, v_a_1084_);
lean_dec(v_a_1084_);
lean_dec_ref(v_decl_1083_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(uint8_t v_pu_1088_, lean_object* v_decl_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1088_, v_decl_1089_, v_a_1091_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___boxed(lean_object* v_pu_1096_, lean_object* v_decl_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
uint8_t v_pu_boxed_1103_; lean_object* v_res_1104_; 
v_pu_boxed_1103_ = lean_unbox(v_pu_1096_);
v_res_1104_ = l_Lean_Compiler_LCNF_eraseLetDecl(v_pu_boxed_1103_, v_decl_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec_ref(v_decl_1097_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t v_pu_1105_, lean_object* v_decl_1106_, uint8_t v_recursive_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v_lctx_1111_; lean_object* v_nextIdx_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1123_; 
v___x_1110_ = lean_st_ref_take(v_a_1108_);
v_lctx_1111_ = lean_ctor_get(v___x_1110_, 0);
v_nextIdx_1112_ = lean_ctor_get(v___x_1110_, 1);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1114_ = v___x_1110_;
v_isShared_1115_ = v_isSharedCheck_1123_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_nextIdx_1112_);
lean_inc(v_lctx_1111_);
lean_dec(v___x_1110_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1123_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1116_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_1105_, v_lctx_1111_, v_decl_1106_, v_recursive_1107_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1116_);
v___x_1118_ = v___x_1114_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_nextIdx_1112_);
v___x_1118_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_st_ref_set(v_a_1108_, v___x_1118_);
v___x_1120_ = lean_box(0);
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
return v___x_1121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(lean_object* v_pu_1124_, lean_object* v_decl_1125_, lean_object* v_recursive_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
uint8_t v_pu_boxed_1129_; uint8_t v_recursive_boxed_1130_; lean_object* v_res_1131_; 
v_pu_boxed_1129_ = lean_unbox(v_pu_1124_);
v_recursive_boxed_1130_ = lean_unbox(v_recursive_1126_);
v_res_1131_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_boxed_1129_, v_decl_1125_, v_recursive_boxed_1130_, v_a_1127_);
lean_dec(v_a_1127_);
lean_dec_ref(v_decl_1125_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(uint8_t v_pu_1132_, lean_object* v_decl_1133_, uint8_t v_recursive_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1132_, v_decl_1133_, v_recursive_1134_, v_a_1136_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___boxed(lean_object* v_pu_1141_, lean_object* v_decl_1142_, lean_object* v_recursive_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
uint8_t v_pu_boxed_1149_; uint8_t v_recursive_boxed_1150_; lean_object* v_res_1151_; 
v_pu_boxed_1149_ = lean_unbox(v_pu_1141_);
v_recursive_boxed_1150_ = lean_unbox(v_recursive_1143_);
v_res_1151_ = l_Lean_Compiler_LCNF_eraseFunDecl(v_pu_boxed_1149_, v_decl_1142_, v_recursive_boxed_1150_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec_ref(v_decl_1142_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t v_pu_1152_, lean_object* v_code_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v___x_1156_; lean_object* v_lctx_1157_; lean_object* v_nextIdx_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1169_; 
v___x_1156_ = lean_st_ref_take(v_a_1154_);
v_lctx_1157_ = lean_ctor_get(v___x_1156_, 0);
v_nextIdx_1158_ = lean_ctor_get(v___x_1156_, 1);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1160_ = v___x_1156_;
v_isShared_1161_ = v_isSharedCheck_1169_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_nextIdx_1158_);
lean_inc(v_lctx_1157_);
lean_dec(v___x_1156_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1169_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1162_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1152_, v_code_1153_, v_lctx_1157_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1162_);
v___x_1164_ = v___x_1160_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_nextIdx_1158_);
v___x_1164_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = lean_st_ref_set(v_a_1154_, v___x_1164_);
v___x_1166_ = lean_box(0);
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
return v___x_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(lean_object* v_pu_1170_, lean_object* v_code_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
uint8_t v_pu_boxed_1174_; lean_object* v_res_1175_; 
v_pu_boxed_1174_ = lean_unbox(v_pu_1170_);
v_res_1175_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_boxed_1174_, v_code_1171_, v_a_1172_);
lean_dec(v_a_1172_);
lean_dec_ref(v_code_1171_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode(uint8_t v_pu_1176_, lean_object* v_code_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_1176_, v_code_1177_, v_a_1179_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___boxed(lean_object* v_pu_1184_, lean_object* v_code_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
uint8_t v_pu_boxed_1191_; lean_object* v_res_1192_; 
v_pu_boxed_1191_ = lean_unbox(v_pu_1184_);
v_res_1192_ = l_Lean_Compiler_LCNF_eraseCode(v_pu_boxed_1191_, v_code_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
lean_dec_ref(v_code_1185_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t v_pu_1193_, lean_object* v_param_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v___x_1197_; lean_object* v_lctx_1198_; lean_object* v_nextIdx_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1210_; 
v___x_1197_ = lean_st_ref_take(v_a_1195_);
v_lctx_1198_ = lean_ctor_get(v___x_1197_, 0);
v_nextIdx_1199_ = lean_ctor_get(v___x_1197_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1201_ = v___x_1197_;
v_isShared_1202_ = v_isSharedCheck_1210_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_nextIdx_1199_);
lean_inc(v_lctx_1198_);
lean_dec(v___x_1197_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1210_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_1193_, v_lctx_1198_, v_param_1194_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1203_);
v___x_1205_ = v___x_1201_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_nextIdx_1199_);
v___x_1205_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = lean_st_ref_set(v_a_1195_, v___x_1205_);
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(lean_object* v_pu_1211_, lean_object* v_param_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
uint8_t v_pu_boxed_1215_; lean_object* v_res_1216_; 
v_pu_boxed_1215_ = lean_unbox(v_pu_1211_);
v_res_1216_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_boxed_1215_, v_param_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_param_1212_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam(uint8_t v_pu_1217_, lean_object* v_param_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_1217_, v_param_1218_, v_a_1220_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___boxed(lean_object* v_pu_1225_, lean_object* v_param_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
uint8_t v_pu_boxed_1232_; lean_object* v_res_1233_; 
v_pu_boxed_1232_ = lean_unbox(v_pu_1225_);
v_res_1233_ = l_Lean_Compiler_LCNF_eraseParam(v_pu_boxed_1232_, v_param_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec_ref(v_param_1226_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t v_pu_1234_, lean_object* v_params_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v___x_1238_; lean_object* v_lctx_1239_; lean_object* v_nextIdx_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1251_; 
v___x_1238_ = lean_st_ref_take(v_a_1236_);
v_lctx_1239_ = lean_ctor_get(v___x_1238_, 0);
v_nextIdx_1240_ = lean_ctor_get(v___x_1238_, 1);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1242_ = v___x_1238_;
v_isShared_1243_ = v_isSharedCheck_1251_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_nextIdx_1240_);
lean_inc(v_lctx_1239_);
lean_dec(v___x_1238_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1251_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1244_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_1234_, v_lctx_1239_, v_params_1235_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1244_);
v___x_1246_ = v___x_1242_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1244_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_nextIdx_1240_);
v___x_1246_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = lean_st_ref_set(v_a_1236_, v___x_1246_);
v___x_1248_ = lean_box(0);
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
return v___x_1249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(lean_object* v_pu_1252_, lean_object* v_params_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
uint8_t v_pu_boxed_1256_; lean_object* v_res_1257_; 
v_pu_boxed_1256_ = lean_unbox(v_pu_1252_);
v_res_1257_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_boxed_1256_, v_params_1253_, v_a_1254_);
lean_dec(v_a_1254_);
lean_dec_ref(v_params_1253_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams(uint8_t v_pu_1258_, lean_object* v_params_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1258_, v_params_1259_, v_a_1261_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___boxed(lean_object* v_pu_1266_, lean_object* v_params_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
uint8_t v_pu_boxed_1273_; lean_object* v_res_1274_; 
v_pu_boxed_1273_ = lean_unbox(v_pu_1266_);
v_res_1274_ = l_Lean_Compiler_LCNF_eraseParams(v_pu_boxed_1273_, v_params_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec_ref(v_params_1267_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t v_pu_1275_, lean_object* v_decl_1276_, lean_object* v_a_1277_){
_start:
{
switch(lean_obj_tag(v_decl_1276_))
{
case 0:
{
lean_object* v_decl_1279_; lean_object* v___x_1280_; 
v_decl_1279_ = lean_ctor_get(v_decl_1276_, 0);
v___x_1280_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1275_, v_decl_1279_, v_a_1277_);
return v___x_1280_;
}
case 1:
{
lean_object* v_decl_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; 
v_decl_1281_ = lean_ctor_get(v_decl_1276_, 0);
v___x_1282_ = 1;
v___x_1283_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1275_, v_decl_1281_, v___x_1282_, v_a_1277_);
return v___x_1283_;
}
case 2:
{
lean_object* v_decl_1284_; uint8_t v___x_1285_; lean_object* v___x_1286_; 
v_decl_1284_ = lean_ctor_get(v_decl_1276_, 0);
v___x_1285_ = 1;
v___x_1286_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1275_, v_decl_1284_, v___x_1285_, v_a_1277_);
return v___x_1286_;
}
default: 
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_box(0);
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
return v___x_1288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(lean_object* v_pu_1289_, lean_object* v_decl_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_){
_start:
{
uint8_t v_pu_boxed_1293_; lean_object* v_res_1294_; 
v_pu_boxed_1293_ = lean_unbox(v_pu_1289_);
v_res_1294_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_boxed_1293_, v_decl_1290_, v_a_1291_);
lean_dec(v_a_1291_);
lean_dec_ref(v_decl_1290_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(uint8_t v_pu_1295_, lean_object* v_decl_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1295_, v_decl_1296_, v_a_1298_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(lean_object* v_pu_1303_, lean_object* v_decl_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
uint8_t v_pu_boxed_1310_; lean_object* v_res_1311_; 
v_pu_boxed_1310_ = lean_unbox(v_pu_1303_);
v_res_1311_ = l_Lean_Compiler_LCNF_eraseCodeDecl(v_pu_boxed_1310_, v_decl_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec_ref(v_decl_1304_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(uint8_t v_pu_1312_, lean_object* v_as_1313_, size_t v_i_1314_, size_t v_stop_1315_, lean_object* v_b_1316_, lean_object* v___y_1317_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_usize_dec_eq(v_i_1314_, v_stop_1315_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_array_uget_borrowed(v_as_1313_, v_i_1314_);
v___x_1321_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1312_, v___x_1320_, v___y_1317_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; size_t v___x_1323_; size_t v___x_1324_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref_known(v___x_1321_, 1);
v___x_1323_ = ((size_t)1ULL);
v___x_1324_ = lean_usize_add(v_i_1314_, v___x_1323_);
v_i_1314_ = v___x_1324_;
v_b_1316_ = v_a_1322_;
goto _start;
}
else
{
return v___x_1321_;
}
}
else
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1326_, 0, v_b_1316_);
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(lean_object* v_pu_1327_, lean_object* v_as_1328_, lean_object* v_i_1329_, lean_object* v_stop_1330_, lean_object* v_b_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
uint8_t v_pu_boxed_1334_; size_t v_i_boxed_1335_; size_t v_stop_boxed_1336_; lean_object* v_res_1337_; 
v_pu_boxed_1334_ = lean_unbox(v_pu_1327_);
v_i_boxed_1335_ = lean_unbox_usize(v_i_1329_);
lean_dec(v_i_1329_);
v_stop_boxed_1336_ = lean_unbox_usize(v_stop_1330_);
lean_dec(v_stop_1330_);
v_res_1337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_boxed_1334_, v_as_1328_, v_i_boxed_1335_, v_stop_boxed_1336_, v_b_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v_as_1328_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(uint8_t v_pu_1338_, lean_object* v_decls_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_array_get_size(v_decls_1339_);
v___x_1347_ = lean_box(0);
v___x_1348_ = lean_nat_dec_lt(v___x_1345_, v___x_1346_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1347_);
return v___x_1349_;
}
else
{
uint8_t v___x_1350_; 
v___x_1350_ = lean_nat_dec_le(v___x_1346_, v___x_1346_);
if (v___x_1350_ == 0)
{
if (v___x_1348_ == 0)
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1347_);
return v___x_1351_;
}
else
{
size_t v___x_1352_; size_t v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = ((size_t)0ULL);
v___x_1353_ = lean_usize_of_nat(v___x_1346_);
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1338_, v_decls_1339_, v___x_1352_, v___x_1353_, v___x_1347_, v_a_1341_);
return v___x_1354_;
}
}
else
{
size_t v___x_1355_; size_t v___x_1356_; lean_object* v___x_1357_; 
v___x_1355_ = ((size_t)0ULL);
v___x_1356_ = lean_usize_of_nat(v___x_1346_);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1338_, v_decls_1339_, v___x_1355_, v___x_1356_, v___x_1347_, v_a_1341_);
return v___x_1357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(lean_object* v_pu_1358_, lean_object* v_decls_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
uint8_t v_pu_boxed_1365_; lean_object* v_res_1366_; 
v_pu_boxed_1365_ = lean_unbox(v_pu_1358_);
v_res_1366_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v_pu_boxed_1365_, v_decls_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec_ref(v_decls_1359_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(uint8_t v_pu_1367_, lean_object* v_as_1368_, size_t v_i_1369_, size_t v_stop_1370_, lean_object* v_b_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1367_, v_as_1368_, v_i_1369_, v_stop_1370_, v_b_1371_, v___y_1373_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(lean_object* v_pu_1378_, lean_object* v_as_1379_, lean_object* v_i_1380_, lean_object* v_stop_1381_, lean_object* v_b_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
uint8_t v_pu_boxed_1388_; size_t v_i_boxed_1389_; size_t v_stop_boxed_1390_; lean_object* v_res_1391_; 
v_pu_boxed_1388_ = lean_unbox(v_pu_1378_);
v_i_boxed_1389_ = lean_unbox_usize(v_i_1380_);
lean_dec(v_i_1380_);
v_stop_boxed_1390_ = lean_unbox_usize(v_stop_1381_);
lean_dec(v_stop_1381_);
v_res_1391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(v_pu_boxed_1388_, v_as_1379_, v_i_boxed_1389_, v_stop_boxed_1390_, v_b_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec_ref(v_as_1379_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(lean_object* v_f_1392_, lean_object* v_v_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
if (lean_obj_tag(v_v_1393_) == 0)
{
lean_object* v_code_1399_; lean_object* v___x_1400_; 
v_code_1399_ = lean_ctor_get(v_v_1393_, 0);
lean_inc_ref(v_code_1399_);
lean_dec_ref_known(v_v_1393_, 1);
lean_inc(v___y_1397_);
lean_inc_ref(v___y_1396_);
lean_inc(v___y_1395_);
lean_inc_ref(v___y_1394_);
v___x_1400_ = lean_apply_6(v_f_1392_, v_code_1399_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, lean_box(0));
return v___x_1400_;
}
else
{
lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1408_; 
lean_dec_ref(v_f_1392_);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_v_1393_);
if (v_isSharedCheck_1408_ == 0)
{
lean_object* v_unused_1409_; 
v_unused_1409_ = lean_ctor_get(v_v_1393_, 0);
lean_dec(v_unused_1409_);
v___x_1402_ = v_v_1393_;
v_isShared_1403_ = v_isSharedCheck_1408_;
goto v_resetjp_1401_;
}
else
{
lean_dec(v_v_1393_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1408_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1404_ = lean_box(0);
if (v_isShared_1403_ == 0)
{
lean_ctor_set_tag(v___x_1402_, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1404_);
v___x_1406_ = v___x_1402_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg___boxed(lean_object* v_f_1410_, lean_object* v_v_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1410_, v_v_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(uint8_t v_pu_1418_, lean_object* v_f_1419_, lean_object* v_v_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1419_, v_v_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(lean_object* v_pu_1427_, lean_object* v_f_1428_, lean_object* v_v_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
uint8_t v_pu_boxed_1435_; lean_object* v_res_1436_; 
v_pu_boxed_1435_ = lean_unbox(v_pu_1427_);
v_res_1436_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(v_pu_boxed_1435_, v_f_1428_, v_v_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t v_pu_1437_, lean_object* v_decl_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_toSignature_1444_; lean_object* v_value_1445_; lean_object* v_params_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v_toSignature_1444_ = lean_ctor_get(v_decl_1438_, 0);
lean_inc_ref(v_toSignature_1444_);
v_value_1445_ = lean_ctor_get(v_decl_1438_, 1);
lean_inc_ref(v_value_1445_);
lean_dec_ref(v_decl_1438_);
v_params_1446_ = lean_ctor_get(v_toSignature_1444_, 3);
lean_inc_ref(v_params_1446_);
lean_dec_ref(v_toSignature_1444_);
v___x_1447_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1437_, v_params_1446_, v_a_1440_);
lean_dec_ref(v_params_1446_);
lean_dec_ref(v___x_1447_);
v___x_1448_ = lean_box(v_pu_1437_);
v___x_1449_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_eraseCode___boxed), 7, 1);
lean_closure_set(v___x_1449_, 0, v___x_1448_);
v___x_1450_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v___x_1449_, v_value_1445_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl___boxed(lean_object* v_pu_1451_, lean_object* v_decl_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_){
_start:
{
uint8_t v_pu_boxed_1458_; lean_object* v_res_1459_; 
v_pu_boxed_1458_ = lean_unbox(v_pu_1451_);
v_res_1459_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_boxed_1458_, v_decl_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_);
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1455_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase(uint8_t v_pu_1460_, lean_object* v_decl_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_1460_, v_decl_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase___boxed(lean_object* v_pu_1468_, lean_object* v_decl_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
uint8_t v_pu_boxed_1475_; lean_object* v_res_1476_; 
v_pu_boxed_1475_ = lean_unbox(v_pu_1468_);
v_res_1476_ = l_Lean_Compiler_LCNF_Decl_erase(v_pu_boxed_1475_, v_decl_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(lean_object* v_msg_1477_){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = l_Lean_instInhabitedExpr;
v___x_1479_ = lean_panic_fn_borrowed(v___x_1478_, v_msg_1477_);
return v___x_1479_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1483_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2));
v___x_1484_ = lean_unsigned_to_nat(20u);
v___x_1485_ = lean_unsigned_to_nat(216u);
v___x_1486_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1));
v___x_1487_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0));
v___x_1488_ = l_mkPanicMessageWithDecl(v___x_1487_, v___x_1486_, v___x_1485_, v___x_1484_, v___x_1483_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t v_pu_1489_, lean_object* v_s_1490_, uint8_t v_translator_1491_, lean_object* v_e_1492_){
_start:
{
uint8_t v___x_1493_; 
v___x_1493_ = l_Lean_Expr_hasFVar(v_e_1492_);
if (v___x_1493_ == 0)
{
return v_e_1492_;
}
else
{
switch(lean_obj_tag(v_e_1492_))
{
case 1:
{
lean_object* v_fvarId_1494_; lean_object* v___x_1495_; 
v_fvarId_1494_ = lean_ctor_get(v_e_1492_, 0);
v___x_1495_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1490_, v_fvarId_1494_);
if (lean_obj_tag(v___x_1495_) == 0)
{
return v_e_1492_;
}
else
{
lean_object* v_val_1496_; 
lean_dec_ref_known(v_e_1492_, 1);
v_val_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_val_1496_);
lean_dec_ref_known(v___x_1495_, 1);
switch(lean_obj_tag(v_val_1496_))
{
case 0:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_Compiler_LCNF_erasedExpr;
return v___x_1497_;
}
case 1:
{
if (v_translator_1491_ == 0)
{
lean_object* v_fvarId_1498_; lean_object* v___x_1499_; 
v_fvarId_1498_ = lean_ctor_get(v_val_1496_, 0);
lean_inc(v_fvarId_1498_);
lean_dec_ref_known(v_val_1496_, 1);
v___x_1499_ = l_Lean_Expr_fvar___override(v_fvarId_1498_);
v_e_1492_ = v___x_1499_;
goto _start;
}
else
{
lean_object* v_fvarId_1501_; lean_object* v___x_1502_; 
v_fvarId_1501_ = lean_ctor_get(v_val_1496_, 0);
lean_inc(v_fvarId_1501_);
lean_dec_ref_known(v_val_1496_, 1);
v___x_1502_ = l_Lean_Expr_fvar___override(v_fvarId_1501_);
return v___x_1502_;
}
}
default: 
{
if (v_translator_1491_ == 0)
{
lean_object* v_expr_1503_; 
v_expr_1503_ = lean_ctor_get(v_val_1496_, 0);
lean_inc_ref(v_expr_1503_);
lean_dec_ref_known(v_val_1496_, 1);
v_e_1492_ = v_expr_1503_;
goto _start;
}
else
{
lean_object* v_expr_1505_; 
v_expr_1505_ = lean_ctor_get(v_val_1496_, 0);
lean_inc_ref(v_expr_1505_);
lean_dec_ref_known(v_val_1496_, 1);
return v_expr_1505_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_1506_; lean_object* v_arg_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___y_1511_; size_t v___x_1515_; size_t v___x_1516_; uint8_t v___x_1517_; 
v_fn_1506_ = lean_ctor_get(v_e_1492_, 0);
v_arg_1507_ = lean_ctor_get(v_e_1492_, 1);
lean_inc_ref(v_fn_1506_);
v___x_1508_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1489_, v_s_1490_, v_translator_1491_, v_fn_1506_);
lean_inc_ref(v_arg_1507_);
v___x_1509_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1489_, v_s_1490_, v_translator_1491_, v_arg_1507_);
v___x_1515_ = lean_ptr_addr(v_fn_1506_);
v___x_1516_ = lean_ptr_addr(v___x_1508_);
v___x_1517_ = lean_usize_dec_eq(v___x_1515_, v___x_1516_);
if (v___x_1517_ == 0)
{
v___y_1511_ = v___x_1517_;
goto v___jp_1510_;
}
else
{
size_t v___x_1518_; size_t v___x_1519_; uint8_t v___x_1520_; 
v___x_1518_ = lean_ptr_addr(v_arg_1507_);
v___x_1519_ = lean_ptr_addr(v___x_1509_);
v___x_1520_ = lean_usize_dec_eq(v___x_1518_, v___x_1519_);
v___y_1511_ = v___x_1520_;
goto v___jp_1510_;
}
v___jp_1510_:
{
if (v___y_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_dec_ref_known(v_e_1492_, 2);
v___x_1512_ = l_Lean_Expr_app___override(v___x_1508_, v___x_1509_);
v___x_1513_ = l_Lean_Expr_headBeta(v___x_1512_);
return v___x_1513_;
}
else
{
lean_object* v___x_1514_; 
lean_dec_ref(v___x_1509_);
lean_dec_ref(v___x_1508_);
v___x_1514_ = l_Lean_Expr_headBeta(v_e_1492_);
return v___x_1514_;
}
}
}
case 6:
{
lean_object* v_binderName_1521_; lean_object* v_binderType_1522_; lean_object* v_body_1523_; uint8_t v_binderInfo_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___y_1528_; size_t v___x_1532_; size_t v___x_1533_; uint8_t v___x_1534_; 
v_binderName_1521_ = lean_ctor_get(v_e_1492_, 0);
v_binderType_1522_ = lean_ctor_get(v_e_1492_, 1);
v_body_1523_ = lean_ctor_get(v_e_1492_, 2);
v_binderInfo_1524_ = lean_ctor_get_uint8(v_e_1492_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1522_);
v___x_1525_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1489_, v_s_1490_, v_translator_1491_, v_binderType_1522_);
lean_inc_ref(v_body_1523_);
v___x_1526_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1489_, v_s_1490_, v_translator_1491_, v_body_1523_);
v___x_1532_ = lean_ptr_addr(v_binderType_1522_);
v___x_1533_ = lean_ptr_addr(v___x_1525_);
v___x_1534_ = lean_usize_dec_eq(v___x_1532_, v___x_1533_);
if (v___x_1534_ == 0)
{
v___y_1528_ = v___x_1534_;
goto v___jp_1527_;
}
else
{
size_t v___x_1535_; size_t v___x_1536_; uint8_t v___x_1537_; 
v___x_1535_ = lean_ptr_addr(v_body_1523_);
v___x_1536_ = lean_ptr_addr(v___x_1526_);
v___x_1537_ = lean_usize_dec_eq(v___x_1535_, v___x_1536_);
v___y_1528_ = v___x_1537_;
goto v___jp_1527_;
}
v___jp_1527_:
{
if (v___y_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_inc(v_binderName_1521_);
lean_dec_ref_known(v_e_1492_, 3);
v___x_1529_ = l_Lean_Expr_lam___override(v_binderName_1521_, v___x_1525_, v___x_1526_, v_binderInfo_1524_);
return v___x_1529_;
}
else
{
uint8_t v___x_1530_; 
v___x_1530_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1524_, v_binderInfo_1524_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; 
lean_inc(v_binderName_1521_);
lean_dec_ref_known(v_e_1492_, 3);
v___x_1531_ = l_Lean_Expr_lam___override(v_binderName_1521_, v___x_1525_, v___x_1526_, v_binderInfo_1524_);
return v___x_1531_;
}
else
{
lean_dec_ref(v___x_1526_);
lean_dec_ref(v___x_1525_);
return v_e_1492_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1538_; lean_object* v_binderType_1539_; lean_object* v_body_1540_; uint8_t v_binderInfo_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___y_1545_; size_t v___x_1549_; size_t v___x_1550_; uint8_t v___x_1551_; 
v_binderName_1538_ = lean_ctor_get(v_e_1492_, 0);
v_binderType_1539_ = lean_ctor_get(v_e_1492_, 1);
v_body_1540_ = lean_ctor_get(v_e_1492_, 2);
v_binderInfo_1541_ = lean_ctor_get_uint8(v_e_1492_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1539_);
v___x_1542_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1489_, v_s_1490_, v_translator_1491_, v_binderType_1539_);
lean_inc_ref(v_body_1540_);
v___x_1543_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1489_, v_s_1490_, v_translator_1491_, v_body_1540_);
v___x_1549_ = lean_ptr_addr(v_binderType_1539_);
v___x_1550_ = lean_ptr_addr(v___x_1542_);
v___x_1551_ = lean_usize_dec_eq(v___x_1549_, v___x_1550_);
if (v___x_1551_ == 0)
{
v___y_1545_ = v___x_1551_;
goto v___jp_1544_;
}
else
{
size_t v___x_1552_; size_t v___x_1553_; uint8_t v___x_1554_; 
v___x_1552_ = lean_ptr_addr(v_body_1540_);
v___x_1553_ = lean_ptr_addr(v___x_1543_);
v___x_1554_ = lean_usize_dec_eq(v___x_1552_, v___x_1553_);
v___y_1545_ = v___x_1554_;
goto v___jp_1544_;
}
v___jp_1544_:
{
if (v___y_1545_ == 0)
{
lean_object* v___x_1546_; 
lean_inc(v_binderName_1538_);
lean_dec_ref_known(v_e_1492_, 3);
v___x_1546_ = l_Lean_Expr_forallE___override(v_binderName_1538_, v___x_1542_, v___x_1543_, v_binderInfo_1541_);
return v___x_1546_;
}
else
{
uint8_t v___x_1547_; 
v___x_1547_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1541_, v_binderInfo_1541_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; 
lean_inc(v_binderName_1538_);
lean_dec_ref_known(v_e_1492_, 3);
v___x_1548_ = l_Lean_Expr_forallE___override(v_binderName_1538_, v___x_1542_, v___x_1543_, v_binderInfo_1541_);
return v___x_1548_;
}
else
{
lean_dec_ref(v___x_1543_);
lean_dec_ref(v___x_1542_);
return v_e_1492_;
}
}
}
}
case 8:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_dec_ref_known(v_e_1492_, 4);
v___x_1555_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3, &l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
v___x_1556_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_1555_);
return v___x_1556_;
}
case 10:
{
lean_object* v_data_1557_; lean_object* v_expr_1558_; lean_object* v___x_1559_; size_t v___x_1560_; size_t v___x_1561_; uint8_t v___x_1562_; 
v_data_1557_ = lean_ctor_get(v_e_1492_, 0);
v_expr_1558_ = lean_ctor_get(v_e_1492_, 1);
lean_inc_ref(v_expr_1558_);
v___x_1559_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1489_, v_s_1490_, v_translator_1491_, v_expr_1558_);
v___x_1560_ = lean_ptr_addr(v_expr_1558_);
v___x_1561_ = lean_ptr_addr(v___x_1559_);
v___x_1562_ = lean_usize_dec_eq(v___x_1560_, v___x_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; 
lean_inc(v_data_1557_);
lean_dec_ref_known(v_e_1492_, 2);
v___x_1563_ = l_Lean_Expr_mdata___override(v_data_1557_, v___x_1559_);
return v___x_1563_;
}
else
{
lean_dec_ref(v___x_1559_);
return v_e_1492_;
}
}
case 11:
{
lean_object* v_typeName_1564_; lean_object* v_idx_1565_; lean_object* v_struct_1566_; lean_object* v___x_1567_; size_t v___x_1568_; size_t v___x_1569_; uint8_t v___x_1570_; 
v_typeName_1564_ = lean_ctor_get(v_e_1492_, 0);
v_idx_1565_ = lean_ctor_get(v_e_1492_, 1);
v_struct_1566_ = lean_ctor_get(v_e_1492_, 2);
lean_inc_ref(v_struct_1566_);
v___x_1567_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1489_, v_s_1490_, v_translator_1491_, v_struct_1566_);
v___x_1568_ = lean_ptr_addr(v_struct_1566_);
v___x_1569_ = lean_ptr_addr(v___x_1567_);
v___x_1570_ = lean_usize_dec_eq(v___x_1568_, v___x_1569_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; 
lean_inc(v_idx_1565_);
lean_inc(v_typeName_1564_);
lean_dec_ref_known(v_e_1492_, 3);
v___x_1571_ = l_Lean_Expr_proj___override(v_typeName_1564_, v_idx_1565_, v___x_1567_);
return v___x_1571_;
}
else
{
lean_dec_ref(v___x_1567_);
return v_e_1492_;
}
}
default: 
{
return v_e_1492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t v_pu_1572_, lean_object* v_s_1573_, uint8_t v_translator_1574_, lean_object* v_e_1575_){
_start:
{
if (lean_obj_tag(v_e_1575_) == 5)
{
lean_object* v_fn_1576_; lean_object* v_arg_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___y_1581_; size_t v___x_1583_; size_t v___x_1584_; uint8_t v___x_1585_; 
v_fn_1576_ = lean_ctor_get(v_e_1575_, 0);
v_arg_1577_ = lean_ctor_get(v_e_1575_, 1);
lean_inc_ref(v_fn_1576_);
v___x_1578_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1572_, v_s_1573_, v_translator_1574_, v_fn_1576_);
lean_inc_ref(v_arg_1577_);
v___x_1579_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1572_, v_s_1573_, v_translator_1574_, v_arg_1577_);
v___x_1583_ = lean_ptr_addr(v_fn_1576_);
v___x_1584_ = lean_ptr_addr(v___x_1578_);
v___x_1585_ = lean_usize_dec_eq(v___x_1583_, v___x_1584_);
if (v___x_1585_ == 0)
{
v___y_1581_ = v___x_1585_;
goto v___jp_1580_;
}
else
{
size_t v___x_1586_; size_t v___x_1587_; uint8_t v___x_1588_; 
v___x_1586_ = lean_ptr_addr(v_arg_1577_);
v___x_1587_ = lean_ptr_addr(v___x_1579_);
v___x_1588_ = lean_usize_dec_eq(v___x_1586_, v___x_1587_);
v___y_1581_ = v___x_1588_;
goto v___jp_1580_;
}
v___jp_1580_:
{
if (v___y_1581_ == 0)
{
lean_object* v___x_1582_; 
lean_dec_ref_known(v_e_1575_, 2);
v___x_1582_ = l_Lean_Expr_app___override(v___x_1578_, v___x_1579_);
return v___x_1582_;
}
else
{
lean_dec_ref(v___x_1579_);
lean_dec_ref(v___x_1578_);
return v_e_1575_;
}
}
}
else
{
lean_object* v___x_1589_; 
v___x_1589_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1572_, v_s_1573_, v_translator_1574_, v_e_1575_);
return v___x_1589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object* v_pu_1590_, lean_object* v_s_1591_, lean_object* v_translator_1592_, lean_object* v_e_1593_){
_start:
{
uint8_t v_pu_boxed_1594_; uint8_t v_translator_boxed_1595_; lean_object* v_res_1596_; 
v_pu_boxed_1594_ = lean_unbox(v_pu_1590_);
v_translator_boxed_1595_ = lean_unbox(v_translator_1592_);
v_res_1596_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_boxed_1594_, v_s_1591_, v_translator_boxed_1595_, v_e_1593_);
lean_dec_ref(v_s_1591_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object* v_pu_1597_, lean_object* v_s_1598_, lean_object* v_translator_1599_, lean_object* v_e_1600_){
_start:
{
uint8_t v_pu_boxed_1601_; uint8_t v_translator_boxed_1602_; lean_object* v_res_1603_; 
v_pu_boxed_1601_ = lean_unbox(v_pu_1597_);
v_translator_boxed_1602_ = lean_unbox(v_translator_1599_);
v_res_1603_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_boxed_1601_, v_s_1598_, v_translator_boxed_1602_, v_e_1600_);
lean_dec_ref(v_s_1598_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t v_pu_1604_, lean_object* v_s_1605_, lean_object* v_e_1606_, uint8_t v_translator_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1604_, v_s_1605_, v_translator_1607_, v_e_1606_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object* v_pu_1609_, lean_object* v_s_1610_, lean_object* v_e_1611_, lean_object* v_translator_1612_){
_start:
{
uint8_t v_pu_boxed_1613_; uint8_t v_translator_boxed_1614_; lean_object* v_res_1615_; 
v_pu_boxed_1613_ = lean_unbox(v_pu_1609_);
v_translator_boxed_1614_ = lean_unbox(v_translator_1612_);
v_res_1615_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(v_pu_boxed_1613_, v_s_1610_, v_e_1611_, v_translator_boxed_1614_);
lean_dec_ref(v_s_1610_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(lean_object* v_x_1616_){
_start:
{
if (lean_obj_tag(v_x_1616_) == 0)
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_unsigned_to_nat(0u);
return v___x_1617_;
}
else
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_unsigned_to_nat(1u);
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___boxed(lean_object* v_x_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(v_x_1619_);
lean_dec(v_x_1619_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(lean_object* v_t_1621_, lean_object* v_k_1622_){
_start:
{
if (lean_obj_tag(v_t_1621_) == 0)
{
lean_object* v_fvarId_1623_; lean_object* v___x_1624_; 
v_fvarId_1623_ = lean_ctor_get(v_t_1621_, 0);
lean_inc(v_fvarId_1623_);
lean_dec_ref_known(v_t_1621_, 1);
v___x_1624_ = lean_apply_1(v_k_1622_, v_fvarId_1623_);
return v___x_1624_;
}
else
{
return v_k_1622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(lean_object* v_motive_1625_, lean_object* v_ctorIdx_1626_, lean_object* v_t_1627_, lean_object* v_h_1628_, lean_object* v_k_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1627_, v_k_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(lean_object* v_motive_1631_, lean_object* v_ctorIdx_1632_, lean_object* v_t_1633_, lean_object* v_h_1634_, lean_object* v_k_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(v_motive_1631_, v_ctorIdx_1632_, v_t_1633_, v_h_1634_, v_k_1635_);
lean_dec(v_ctorIdx_1632_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(lean_object* v_t_1637_, lean_object* v_fvar_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1637_, v_fvar_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(lean_object* v_motive_1640_, lean_object* v_t_1641_, lean_object* v_h_1642_, lean_object* v_fvar_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1641_, v_fvar_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(lean_object* v_t_1645_, lean_object* v_erased_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1645_, v_erased_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(lean_object* v_motive_1648_, lean_object* v_t_1649_, lean_object* v_h_1650_, lean_object* v_erased_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1649_, v_erased_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object* v_s_1657_, lean_object* v_fvarId_1658_, uint8_t v_translator_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1657_, v_fvarId_1658_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_fvarId_1658_);
return v___x_1661_;
}
else
{
lean_object* v_val_1662_; 
lean_dec(v_fvarId_1658_);
v_val_1662_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_val_1662_);
lean_dec_ref_known(v___x_1660_, 1);
if (lean_obj_tag(v_val_1662_) == 1)
{
if (v_translator_1659_ == 0)
{
lean_object* v_fvarId_1663_; 
v_fvarId_1663_ = lean_ctor_get(v_val_1662_, 0);
lean_inc(v_fvarId_1663_);
lean_dec_ref_known(v_val_1662_, 1);
v_fvarId_1658_ = v_fvarId_1663_;
goto _start;
}
else
{
lean_object* v_fvarId_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
v_fvarId_1665_ = lean_ctor_get(v_val_1662_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_val_1662_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v_val_1662_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_fvarId_1665_);
lean_dec(v_val_1662_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 0);
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_fvarId_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_object* v___x_1673_; 
lean_dec(v_val_1662_);
v___x_1673_ = lean_box(1);
return v___x_1673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg___boxed(lean_object* v_s_1674_, lean_object* v_fvarId_1675_, lean_object* v_translator_1676_){
_start:
{
uint8_t v_translator_boxed_1677_; lean_object* v_res_1678_; 
v_translator_boxed_1677_ = lean_unbox(v_translator_1676_);
v_res_1678_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1674_, v_fvarId_1675_, v_translator_boxed_1677_);
lean_dec_ref(v_s_1674_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp(uint8_t v_pu_1679_, lean_object* v_s_1680_, lean_object* v_fvarId_1681_, uint8_t v_translator_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1680_, v_fvarId_1681_, v_translator_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___boxed(lean_object* v_pu_1684_, lean_object* v_s_1685_, lean_object* v_fvarId_1686_, lean_object* v_translator_1687_){
_start:
{
uint8_t v_pu_boxed_1688_; uint8_t v_translator_boxed_1689_; lean_object* v_res_1690_; 
v_pu_boxed_1688_ = lean_unbox(v_pu_1684_);
v_translator_boxed_1689_ = lean_unbox(v_translator_1687_);
v_res_1690_ = l_Lean_Compiler_LCNF_normFVarImp(v_pu_boxed_1688_, v_s_1685_, v_fvarId_1686_, v_translator_boxed_1689_);
lean_dec_ref(v_s_1685_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t v_pu_1691_, lean_object* v_s_1692_, lean_object* v_arg_1693_, uint8_t v_translator_1694_){
_start:
{
switch(lean_obj_tag(v_arg_1693_))
{
case 0:
{
return v_arg_1693_;
}
case 1:
{
lean_object* v_fvarId_1695_; lean_object* v___x_1696_; 
v_fvarId_1695_ = lean_ctor_get(v_arg_1693_, 0);
v___x_1696_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1692_, v_fvarId_1695_);
if (lean_obj_tag(v___x_1696_) == 0)
{
return v_arg_1693_;
}
else
{
lean_object* v_val_1697_; 
lean_dec_ref_known(v_arg_1693_, 1);
v_val_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_val_1697_);
lean_dec_ref_known(v___x_1696_, 1);
switch(lean_obj_tag(v_val_1697_))
{
case 0:
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_box(0);
return v___x_1698_;
}
case 1:
{
lean_object* v_fvarId_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1707_; 
v_fvarId_1699_ = lean_ctor_get(v_val_1697_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_val_1697_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1701_ = v_val_1697_;
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_fvarId_1699_);
lean_dec(v_val_1697_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_fvarId_1699_);
v___x_1704_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
if (v_translator_1694_ == 0)
{
v_arg_1693_ = v___x_1704_;
goto _start;
}
else
{
return v___x_1704_;
}
}
}
}
default: 
{
lean_object* v_expr_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
v_expr_1708_ = lean_ctor_get(v_val_1697_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_val_1697_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v_val_1697_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_expr_1708_);
lean_dec(v_val_1697_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_expr_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
}
default: 
{
lean_object* v_expr_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v_expr_1716_ = lean_ctor_get(v_arg_1693_, 0);
lean_inc_ref(v_expr_1716_);
v___x_1717_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1691_, v_s_1692_, v_translator_1694_, v_expr_1716_);
v___x_1718_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1691_, v_arg_1693_, v___x_1717_);
return v___x_1718_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp___boxed(lean_object* v_pu_1719_, lean_object* v_s_1720_, lean_object* v_arg_1721_, lean_object* v_translator_1722_){
_start:
{
uint8_t v_pu_boxed_1723_; uint8_t v_translator_boxed_1724_; lean_object* v_res_1725_; 
v_pu_boxed_1723_ = lean_unbox(v_pu_1719_);
v_translator_boxed_1724_ = lean_unbox(v_translator_1722_);
v_res_1725_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_boxed_1723_, v_s_1720_, v_arg_1721_, v_translator_boxed_1724_);
lean_dec_ref(v_s_1720_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(uint8_t v_pu_1726_, lean_object* v_s_1727_, uint8_t v_translator_1728_, lean_object* v_i_1729_, lean_object* v_as_1730_){
_start:
{
lean_object* v___x_1731_; uint8_t v___x_1732_; 
v___x_1731_ = lean_array_get_size(v_as_1730_);
v___x_1732_ = lean_nat_dec_lt(v_i_1729_, v___x_1731_);
if (v___x_1732_ == 0)
{
lean_dec(v_i_1729_);
return v_as_1730_;
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1734_; size_t v___x_1735_; size_t v___x_1736_; uint8_t v___x_1737_; 
v_a_1733_ = lean_array_fget_borrowed(v_as_1730_, v_i_1729_);
lean_inc(v_a_1733_);
v___x_1734_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1726_, v_s_1727_, v_a_1733_, v_translator_1728_);
v___x_1735_ = lean_ptr_addr(v_a_1733_);
v___x_1736_ = lean_ptr_addr(v___x_1734_);
v___x_1737_ = lean_usize_dec_eq(v___x_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = lean_nat_add(v_i_1729_, v___x_1738_);
v___x_1740_ = lean_array_fset(v_as_1730_, v_i_1729_, v___x_1734_);
lean_dec(v_i_1729_);
v_i_1729_ = v___x_1739_;
v_as_1730_ = v___x_1740_;
goto _start;
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_dec(v___x_1734_);
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = lean_nat_add(v_i_1729_, v___x_1742_);
lean_dec(v_i_1729_);
v_i_1729_ = v___x_1743_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0___boxed(lean_object* v_pu_1745_, lean_object* v_s_1746_, lean_object* v_translator_1747_, lean_object* v_i_1748_, lean_object* v_as_1749_){
_start:
{
uint8_t v_pu_boxed_1750_; uint8_t v_translator_boxed_1751_; lean_object* v_res_1752_; 
v_pu_boxed_1750_ = lean_unbox(v_pu_1745_);
v_translator_boxed_1751_ = lean_unbox(v_translator_1747_);
v_res_1752_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_boxed_1750_, v_s_1746_, v_translator_boxed_1751_, v_i_1748_, v_as_1749_);
lean_dec_ref(v_s_1746_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t v_pu_1753_, lean_object* v_s_1754_, lean_object* v_args_1755_, uint8_t v_translator_1756_){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_unsigned_to_nat(0u);
v___x_1758_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_1753_, v_s_1754_, v_translator_1756_, v___x_1757_, v_args_1755_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(lean_object* v_pu_1759_, lean_object* v_s_1760_, lean_object* v_args_1761_, lean_object* v_translator_1762_){
_start:
{
uint8_t v_pu_boxed_1763_; uint8_t v_translator_boxed_1764_; lean_object* v_res_1765_; 
v_pu_boxed_1763_ = lean_unbox(v_pu_1759_);
v_translator_boxed_1764_ = lean_unbox(v_translator_1762_);
v_res_1765_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_boxed_1763_, v_s_1760_, v_args_1761_, v_translator_boxed_1764_);
lean_dec_ref(v_s_1760_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t v_pu_1766_, lean_object* v_s_1767_, lean_object* v_e_1768_, uint8_t v_translator_1769_){
_start:
{
lean_object* v_fvarId_1771_; lean_object* v_args_1777_; 
switch(lean_obj_tag(v_e_1768_))
{
case 2:
{
lean_object* v_struct_1780_; lean_object* v___x_1781_; 
v_struct_1780_ = lean_ctor_get(v_e_1768_, 2);
lean_inc(v_struct_1780_);
v___x_1781_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_struct_1780_, v_translator_1769_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_fvarId_1782_; lean_object* v___x_1783_; 
v_fvarId_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_fvarId_1782_);
lean_dec_ref_known(v___x_1781_, 1);
v___x_1783_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1766_, v_e_1768_, v_fvarId_1782_);
return v___x_1783_;
}
else
{
lean_object* v___x_1784_; 
lean_dec_ref_known(v_e_1768_, 3);
v___x_1784_ = lean_box(1);
return v___x_1784_;
}
}
case 3:
{
lean_object* v_args_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_args_1785_ = lean_ctor_get(v_e_1768_, 2);
lean_inc_ref(v_args_1785_);
v___x_1786_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1766_, v_s_1767_, v_args_1785_, v_translator_1769_);
v___x_1787_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1766_, v_e_1768_, v___x_1786_);
return v___x_1787_;
}
case 4:
{
lean_object* v_fvarId_1788_; lean_object* v_args_1789_; lean_object* v___x_1790_; 
v_fvarId_1788_ = lean_ctor_get(v_e_1768_, 0);
v_args_1789_ = lean_ctor_get(v_e_1768_, 1);
lean_inc(v_fvarId_1788_);
v___x_1790_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_fvarId_1788_, v_translator_1769_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_fvarId_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v_fvarId_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_fvarId_1791_);
lean_dec_ref_known(v___x_1790_, 1);
lean_inc_ref(v_args_1789_);
v___x_1792_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1766_, v_s_1767_, v_args_1789_, v_translator_1769_);
v___x_1793_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_1766_, v_e_1768_, v_fvarId_1791_, v___x_1792_);
lean_dec_ref_known(v_e_1768_, 2);
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; 
lean_dec_ref_known(v_e_1768_, 2);
v___x_1794_ = lean_box(1);
return v___x_1794_;
}
}
case 5:
{
lean_object* v_args_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v_args_1795_ = lean_ctor_get(v_e_1768_, 1);
lean_inc_ref(v_args_1795_);
v___x_1796_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1766_, v_s_1767_, v_args_1795_, v_translator_1769_);
v___x_1797_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1766_, v_e_1768_, v___x_1796_);
return v___x_1797_;
}
case 6:
{
lean_object* v_var_1798_; 
v_var_1798_ = lean_ctor_get(v_e_1768_, 1);
lean_inc(v_var_1798_);
v_fvarId_1771_ = v_var_1798_;
goto v___jp_1770_;
}
case 7:
{
lean_object* v_var_1799_; 
v_var_1799_ = lean_ctor_get(v_e_1768_, 1);
lean_inc(v_var_1799_);
v_fvarId_1771_ = v_var_1799_;
goto v___jp_1770_;
}
case 8:
{
lean_object* v_var_1800_; lean_object* v___x_1801_; 
v_var_1800_ = lean_ctor_get(v_e_1768_, 2);
lean_inc(v_var_1800_);
v___x_1801_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_var_1800_, v_translator_1769_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_fvarId_1802_; lean_object* v___x_1803_; 
v_fvarId_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_fvarId_1802_);
lean_dec_ref_known(v___x_1801_, 1);
v___x_1803_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1766_, v_e_1768_, v_fvarId_1802_);
return v___x_1803_;
}
else
{
lean_object* v___x_1804_; 
lean_dec_ref_known(v_e_1768_, 3);
v___x_1804_ = lean_box(1);
return v___x_1804_;
}
}
case 9:
{
lean_object* v_args_1805_; 
v_args_1805_ = lean_ctor_get(v_e_1768_, 1);
lean_inc_ref(v_args_1805_);
v_args_1777_ = v_args_1805_;
goto v___jp_1776_;
}
case 10:
{
lean_object* v_args_1806_; 
v_args_1806_ = lean_ctor_get(v_e_1768_, 1);
lean_inc_ref(v_args_1806_);
v_args_1777_ = v_args_1806_;
goto v___jp_1776_;
}
case 11:
{
lean_object* v_n_1807_; lean_object* v_var_1808_; lean_object* v___x_1809_; 
v_n_1807_ = lean_ctor_get(v_e_1768_, 0);
lean_inc(v_n_1807_);
v_var_1808_ = lean_ctor_get(v_e_1768_, 1);
lean_inc(v_var_1808_);
v___x_1809_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_var_1808_, v_translator_1769_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_fvarId_1810_; lean_object* v___x_1811_; 
v_fvarId_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_fvarId_1810_);
lean_dec_ref_known(v___x_1809_, 1);
v___x_1811_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_1766_, v_e_1768_, v_n_1807_, v_fvarId_1810_);
lean_dec_ref_known(v_e_1768_, 2);
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; 
lean_dec(v_n_1807_);
lean_dec_ref_known(v_e_1768_, 2);
v___x_1812_ = lean_box(1);
return v___x_1812_;
}
}
case 12:
{
lean_object* v_var_1813_; lean_object* v_i_1814_; uint8_t v_updateHeader_1815_; lean_object* v_args_1816_; lean_object* v___x_1817_; 
v_var_1813_ = lean_ctor_get(v_e_1768_, 0);
v_i_1814_ = lean_ctor_get(v_e_1768_, 1);
lean_inc_ref(v_i_1814_);
v_updateHeader_1815_ = lean_ctor_get_uint8(v_e_1768_, sizeof(void*)*3);
v_args_1816_ = lean_ctor_get(v_e_1768_, 2);
lean_inc(v_var_1813_);
v___x_1817_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_var_1813_, v_translator_1769_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_fvarId_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v_fvarId_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_fvarId_1818_);
lean_dec_ref_known(v___x_1817_, 1);
lean_inc_ref(v_args_1816_);
v___x_1819_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1766_, v_s_1767_, v_args_1816_, v_translator_1769_);
v___x_1820_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_1766_, v_e_1768_, v_fvarId_1818_, v_i_1814_, v_updateHeader_1815_, v___x_1819_);
return v___x_1820_;
}
else
{
lean_object* v___x_1821_; 
lean_dec_ref(v_i_1814_);
lean_dec_ref_known(v_e_1768_, 3);
v___x_1821_ = lean_box(1);
return v___x_1821_;
}
}
case 13:
{
lean_object* v_ty_1822_; lean_object* v_fvarId_1823_; lean_object* v___x_1824_; 
v_ty_1822_ = lean_ctor_get(v_e_1768_, 0);
lean_inc_ref(v_ty_1822_);
v_fvarId_1823_ = lean_ctor_get(v_e_1768_, 1);
lean_inc(v_fvarId_1823_);
v___x_1824_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_fvarId_1823_, v_translator_1769_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_fvarId_1825_; lean_object* v___x_1826_; 
v_fvarId_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_fvarId_1825_);
lean_dec_ref_known(v___x_1824_, 1);
v___x_1826_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_1766_, v_e_1768_, v_ty_1822_, v_fvarId_1825_);
lean_dec_ref_known(v_e_1768_, 2);
return v___x_1826_;
}
else
{
lean_object* v___x_1827_; 
lean_dec_ref(v_ty_1822_);
lean_dec_ref_known(v_e_1768_, 2);
v___x_1827_ = lean_box(1);
return v___x_1827_;
}
}
case 14:
{
lean_object* v_fvarId_1828_; lean_object* v___x_1829_; 
v_fvarId_1828_ = lean_ctor_get(v_e_1768_, 0);
lean_inc(v_fvarId_1828_);
v___x_1829_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_fvarId_1828_, v_translator_1769_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_fvarId_1830_; lean_object* v___x_1831_; 
v_fvarId_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_fvarId_1830_);
lean_dec_ref_known(v___x_1829_, 1);
v___x_1831_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_1766_, v_e_1768_, v_fvarId_1830_);
return v___x_1831_;
}
else
{
lean_object* v___x_1832_; 
lean_dec_ref_known(v_e_1768_, 1);
v___x_1832_ = lean_box(1);
return v___x_1832_;
}
}
case 15:
{
lean_object* v_fvarId_1833_; lean_object* v___x_1834_; 
v_fvarId_1833_ = lean_ctor_get(v_e_1768_, 0);
lean_inc(v_fvarId_1833_);
v___x_1834_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_fvarId_1833_, v_translator_1769_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_fvarId_1835_; lean_object* v___x_1836_; 
v_fvarId_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_fvarId_1835_);
lean_dec_ref_known(v___x_1834_, 1);
v___x_1836_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_1766_, v_e_1768_, v_fvarId_1835_);
return v___x_1836_;
}
else
{
lean_object* v___x_1837_; 
lean_dec_ref_known(v_e_1768_, 1);
v___x_1837_ = lean_box(1);
return v___x_1837_;
}
}
default: 
{
return v_e_1768_;
}
}
v___jp_1770_:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1767_, v_fvarId_1771_, v_translator_1769_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_fvarId_1773_; lean_object* v___x_1774_; 
v_fvarId_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_fvarId_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v___x_1774_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1766_, v_e_1768_, v_fvarId_1773_);
return v___x_1774_;
}
else
{
lean_object* v___x_1775_; 
lean_dec(v_e_1768_);
v___x_1775_ = lean_box(1);
return v___x_1775_;
}
}
v___jp_1776_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1766_, v_s_1767_, v_args_1777_, v_translator_1769_);
v___x_1779_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1766_, v_e_1768_, v___x_1778_);
return v___x_1779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp___boxed(lean_object* v_pu_1838_, lean_object* v_s_1839_, lean_object* v_e_1840_, lean_object* v_translator_1841_){
_start:
{
uint8_t v_pu_boxed_1842_; uint8_t v_translator_boxed_1843_; lean_object* v_res_1844_; 
v_pu_boxed_1842_ = lean_unbox(v_pu_1838_);
v_translator_boxed_1843_ = lean_unbox(v_translator_1841_);
v_res_1844_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_boxed_1842_, v_s_1839_, v_e_1840_, v_translator_boxed_1843_);
lean_dec_ref(v_s_1839_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(lean_object* v_inst_1845_, lean_object* v_inst_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_apply_2(v_inst_1845_, lean_box(0), v_inst_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(uint8_t v_pu_1848_, uint8_t v_t_1849_, lean_object* v_m_1850_, lean_object* v_n_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_apply_2(v_inst_1852_, lean_box(0), v_inst_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(lean_object* v_pu_1855_, lean_object* v_t_1856_, lean_object* v_m_1857_, lean_object* v_n_1858_, lean_object* v_inst_1859_, lean_object* v_inst_1860_){
_start:
{
uint8_t v_pu_boxed_1861_; uint8_t v_t_boxed_1862_; lean_object* v_res_1863_; 
v_pu_boxed_1861_ = lean_unbox(v_pu_1855_);
v_t_boxed_1862_ = lean_unbox(v_t_1856_);
v_res_1863_ = l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(v_pu_boxed_1861_, v_t_boxed_1862_, v_m_1857_, v_n_1858_, v_inst_1859_, v_inst_1860_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0(lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_f_1866_){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = lean_apply_1(v_inst_1864_, v_f_1866_);
v___x_1868_ = lean_apply_2(v_inst_1865_, lean_box(0), v___x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(lean_object* v_inst_1869_, lean_object* v_inst_1870_){
_start:
{
lean_object* v___f_1871_; 
v___f_1871_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1871_, 0, v_inst_1870_);
lean_closure_set(v___f_1871_, 1, v_inst_1869_);
return v___f_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(uint8_t v_pu_1872_, lean_object* v_m_1873_, lean_object* v_n_1874_, lean_object* v_inst_1875_, lean_object* v_inst_1876_){
_start:
{
lean_object* v___f_1877_; 
v___f_1877_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1877_, 0, v_inst_1876_);
lean_closure_set(v___f_1877_, 1, v_inst_1875_);
return v___f_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(lean_object* v_pu_1878_, lean_object* v_m_1879_, lean_object* v_n_1880_, lean_object* v_inst_1881_, lean_object* v_inst_1882_){
_start:
{
uint8_t v_pu_boxed_1883_; lean_object* v_res_1884_; 
v_pu_boxed_1883_ = lean_unbox(v_pu_1878_);
v_res_1884_ = l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(v_pu_boxed_1883_, v_m_1879_, v_n_1880_, v_inst_1881_, v_inst_1882_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___lam__0(lean_object* v___x_1885_, lean_object* v___x_1886_, lean_object* v_fvarId_1887_, lean_object* v_arg_1888_, lean_object* v_s_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1885_, v___x_1886_, v_s_1889_, v_fvarId_1887_, v_arg_1888_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg(lean_object* v_inst_1893_, lean_object* v_fvarId_1894_, lean_object* v_arg_1895_){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___f_1898_; lean_object* v___x_1899_; 
v___x_1896_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1897_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1898_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1898_, 0, v___x_1896_);
lean_closure_set(v___f_1898_, 1, v___x_1897_);
lean_closure_set(v___f_1898_, 2, v_fvarId_1894_);
lean_closure_set(v___f_1898_, 3, v_arg_1895_);
v___x_1899_ = lean_apply_1(v_inst_1893_, v___f_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst(lean_object* v_m_1900_, uint8_t v_pu_1901_, lean_object* v_inst_1902_, lean_object* v_fvarId_1903_, lean_object* v_arg_1904_){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___f_1907_; lean_object* v___x_1908_; 
v___x_1905_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1906_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1907_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1907_, 0, v___x_1905_);
lean_closure_set(v___f_1907_, 1, v___x_1906_);
lean_closure_set(v___f_1907_, 2, v_fvarId_1903_);
lean_closure_set(v___f_1907_, 3, v_arg_1904_);
v___x_1908_ = lean_apply_1(v_inst_1902_, v___f_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___boxed(lean_object* v_m_1909_, lean_object* v_pu_1910_, lean_object* v_inst_1911_, lean_object* v_fvarId_1912_, lean_object* v_arg_1913_){
_start:
{
uint8_t v_pu_boxed_1914_; lean_object* v_res_1915_; 
v_pu_boxed_1914_ = lean_unbox(v_pu_1910_);
v_res_1915_ = l_Lean_Compiler_LCNF_addSubst(v_m_1909_, v_pu_boxed_1914_, v_inst_1911_, v_fvarId_1912_, v_arg_1913_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0(lean_object* v_fvarId_x27_1916_, lean_object* v___x_1917_, lean_object* v___x_1918_, lean_object* v_fvarId_1919_, lean_object* v_s_1920_){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1921_, 0, v_fvarId_x27_1916_);
v___x_1922_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1917_, v___x_1918_, v_s_1920_, v_fvarId_1919_, v___x_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg(lean_object* v_inst_1923_, lean_object* v_fvarId_1924_, lean_object* v_fvarId_x27_1925_){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___f_1928_; lean_object* v___x_1929_; 
v___x_1926_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1927_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1928_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1928_, 0, v_fvarId_x27_1925_);
lean_closure_set(v___f_1928_, 1, v___x_1926_);
lean_closure_set(v___f_1928_, 2, v___x_1927_);
lean_closure_set(v___f_1928_, 3, v_fvarId_1924_);
v___x_1929_ = lean_apply_1(v_inst_1923_, v___f_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst(lean_object* v_m_1930_, uint8_t v_ph_1931_, lean_object* v_inst_1932_, lean_object* v_fvarId_1933_, lean_object* v_fvarId_x27_1934_){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___f_1937_; lean_object* v___x_1938_; 
v___x_1935_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1936_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1937_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1937_, 0, v_fvarId_x27_1934_);
lean_closure_set(v___f_1937_, 1, v___x_1935_);
lean_closure_set(v___f_1937_, 2, v___x_1936_);
lean_closure_set(v___f_1937_, 3, v_fvarId_1933_);
v___x_1938_ = lean_apply_1(v_inst_1932_, v___f_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___boxed(lean_object* v_m_1939_, lean_object* v_ph_1940_, lean_object* v_inst_1941_, lean_object* v_fvarId_1942_, lean_object* v_fvarId_x27_1943_){
_start:
{
uint8_t v_ph_boxed_1944_; lean_object* v_res_1945_; 
v_ph_boxed_1944_ = lean_unbox(v_ph_1940_);
v_res_1945_ = l_Lean_Compiler_LCNF_addFVarSubst(v_m_1939_, v_ph_boxed_1944_, v_inst_1941_, v_fvarId_1942_, v_fvarId_x27_1943_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(lean_object* v_fvarId_1946_, uint8_t v_t_1947_, lean_object* v_toPure_1948_, lean_object* v_____do__lift_1949_){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_____do__lift_1949_, v_fvarId_1946_, v_t_1947_);
v___x_1951_ = lean_apply_2(v_toPure_1948_, lean_box(0), v___x_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(lean_object* v_fvarId_1952_, lean_object* v_t_1953_, lean_object* v_toPure_1954_, lean_object* v_____do__lift_1955_){
_start:
{
uint8_t v_t_boxed_1956_; lean_object* v_res_1957_; 
v_t_boxed_1956_ = lean_unbox(v_t_1953_);
v_res_1957_ = l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(v_fvarId_1952_, v_t_boxed_1956_, v_toPure_1954_, v_____do__lift_1955_);
lean_dec_ref(v_____do__lift_1955_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg(uint8_t v_t_1958_, lean_object* v_inst_1959_, lean_object* v_inst_1960_, lean_object* v_fvarId_1961_){
_start:
{
lean_object* v_toApplicative_1962_; lean_object* v_toBind_1963_; lean_object* v_toPure_1964_; lean_object* v___x_1965_; lean_object* v___f_1966_; lean_object* v___x_1967_; 
v_toApplicative_1962_ = lean_ctor_get(v_inst_1960_, 0);
lean_inc_ref(v_toApplicative_1962_);
v_toBind_1963_ = lean_ctor_get(v_inst_1960_, 1);
lean_inc(v_toBind_1963_);
lean_dec_ref(v_inst_1960_);
v_toPure_1964_ = lean_ctor_get(v_toApplicative_1962_, 1);
lean_inc(v_toPure_1964_);
lean_dec_ref(v_toApplicative_1962_);
v___x_1965_ = lean_box(v_t_1958_);
v___f_1966_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1966_, 0, v_fvarId_1961_);
lean_closure_set(v___f_1966_, 1, v___x_1965_);
lean_closure_set(v___f_1966_, 2, v_toPure_1964_);
v___x_1967_ = lean_apply_4(v_toBind_1963_, lean_box(0), lean_box(0), v_inst_1959_, v___f_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___boxed(lean_object* v_t_1968_, lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_fvarId_1971_){
_start:
{
uint8_t v_t_boxed_1972_; lean_object* v_res_1973_; 
v_t_boxed_1972_ = lean_unbox(v_t_1968_);
v_res_1973_ = l_Lean_Compiler_LCNF_normFVar___redArg(v_t_boxed_1972_, v_inst_1969_, v_inst_1970_, v_fvarId_1971_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar(lean_object* v_m_1974_, uint8_t v_pu_1975_, uint8_t v_t_1976_, lean_object* v_inst_1977_, lean_object* v_inst_1978_, lean_object* v_fvarId_1979_){
_start:
{
lean_object* v_toApplicative_1980_; lean_object* v_toBind_1981_; lean_object* v_toPure_1982_; lean_object* v___x_1983_; lean_object* v___f_1984_; lean_object* v___x_1985_; 
v_toApplicative_1980_ = lean_ctor_get(v_inst_1978_, 0);
lean_inc_ref(v_toApplicative_1980_);
v_toBind_1981_ = lean_ctor_get(v_inst_1978_, 1);
lean_inc(v_toBind_1981_);
lean_dec_ref(v_inst_1978_);
v_toPure_1982_ = lean_ctor_get(v_toApplicative_1980_, 1);
lean_inc(v_toPure_1982_);
lean_dec_ref(v_toApplicative_1980_);
v___x_1983_ = lean_box(v_t_1976_);
v___f_1984_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1984_, 0, v_fvarId_1979_);
lean_closure_set(v___f_1984_, 1, v___x_1983_);
lean_closure_set(v___f_1984_, 2, v_toPure_1982_);
v___x_1985_ = lean_apply_4(v_toBind_1981_, lean_box(0), lean_box(0), v_inst_1977_, v___f_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___boxed(lean_object* v_m_1986_, lean_object* v_pu_1987_, lean_object* v_t_1988_, lean_object* v_inst_1989_, lean_object* v_inst_1990_, lean_object* v_fvarId_1991_){
_start:
{
uint8_t v_pu_boxed_1992_; uint8_t v_t_boxed_1993_; lean_object* v_res_1994_; 
v_pu_boxed_1992_ = lean_unbox(v_pu_1987_);
v_t_boxed_1993_ = lean_unbox(v_t_1988_);
v_res_1994_ = l_Lean_Compiler_LCNF_normFVar(v_m_1986_, v_pu_boxed_1992_, v_t_boxed_1993_, v_inst_1989_, v_inst_1990_, v_fvarId_1991_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(uint8_t v_pu_1995_, uint8_t v_t_1996_, lean_object* v_e_1997_, lean_object* v_toPure_1998_, lean_object* v_____do__lift_1999_){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1995_, v_____do__lift_1999_, v_t_1996_, v_e_1997_);
v___x_2001_ = lean_apply_2(v_toPure_1998_, lean_box(0), v___x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(lean_object* v_pu_2002_, lean_object* v_t_2003_, lean_object* v_e_2004_, lean_object* v_toPure_2005_, lean_object* v_____do__lift_2006_){
_start:
{
uint8_t v_pu_boxed_2007_; uint8_t v_t_boxed_2008_; lean_object* v_res_2009_; 
v_pu_boxed_2007_ = lean_unbox(v_pu_2002_);
v_t_boxed_2008_ = lean_unbox(v_t_2003_);
v_res_2009_ = l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(v_pu_boxed_2007_, v_t_boxed_2008_, v_e_2004_, v_toPure_2005_, v_____do__lift_2006_);
lean_dec_ref(v_____do__lift_2006_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg(uint8_t v_pu_2010_, uint8_t v_t_2011_, lean_object* v_inst_2012_, lean_object* v_inst_2013_, lean_object* v_e_2014_){
_start:
{
lean_object* v_toApplicative_2015_; lean_object* v_toBind_2016_; lean_object* v_toPure_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___f_2020_; lean_object* v___x_2021_; 
v_toApplicative_2015_ = lean_ctor_get(v_inst_2013_, 0);
lean_inc_ref(v_toApplicative_2015_);
v_toBind_2016_ = lean_ctor_get(v_inst_2013_, 1);
lean_inc(v_toBind_2016_);
lean_dec_ref(v_inst_2013_);
v_toPure_2017_ = lean_ctor_get(v_toApplicative_2015_, 1);
lean_inc(v_toPure_2017_);
lean_dec_ref(v_toApplicative_2015_);
v___x_2018_ = lean_box(v_pu_2010_);
v___x_2019_ = lean_box(v_t_2011_);
v___f_2020_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2020_, 0, v___x_2018_);
lean_closure_set(v___f_2020_, 1, v___x_2019_);
lean_closure_set(v___f_2020_, 2, v_e_2014_);
lean_closure_set(v___f_2020_, 3, v_toPure_2017_);
v___x_2021_ = lean_apply_4(v_toBind_2016_, lean_box(0), lean_box(0), v_inst_2012_, v___f_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___boxed(lean_object* v_pu_2022_, lean_object* v_t_2023_, lean_object* v_inst_2024_, lean_object* v_inst_2025_, lean_object* v_e_2026_){
_start:
{
uint8_t v_pu_boxed_2027_; uint8_t v_t_boxed_2028_; lean_object* v_res_2029_; 
v_pu_boxed_2027_ = lean_unbox(v_pu_2022_);
v_t_boxed_2028_ = lean_unbox(v_t_2023_);
v_res_2029_ = l_Lean_Compiler_LCNF_normExpr___redArg(v_pu_boxed_2027_, v_t_boxed_2028_, v_inst_2024_, v_inst_2025_, v_e_2026_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr(lean_object* v_m_2030_, uint8_t v_pu_2031_, uint8_t v_t_2032_, lean_object* v_inst_2033_, lean_object* v_inst_2034_, lean_object* v_e_2035_){
_start:
{
lean_object* v_toApplicative_2036_; lean_object* v_toBind_2037_; lean_object* v_toPure_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___f_2041_; lean_object* v___x_2042_; 
v_toApplicative_2036_ = lean_ctor_get(v_inst_2034_, 0);
lean_inc_ref(v_toApplicative_2036_);
v_toBind_2037_ = lean_ctor_get(v_inst_2034_, 1);
lean_inc(v_toBind_2037_);
lean_dec_ref(v_inst_2034_);
v_toPure_2038_ = lean_ctor_get(v_toApplicative_2036_, 1);
lean_inc(v_toPure_2038_);
lean_dec_ref(v_toApplicative_2036_);
v___x_2039_ = lean_box(v_pu_2031_);
v___x_2040_ = lean_box(v_t_2032_);
v___f_2041_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2041_, 0, v___x_2039_);
lean_closure_set(v___f_2041_, 1, v___x_2040_);
lean_closure_set(v___f_2041_, 2, v_e_2035_);
lean_closure_set(v___f_2041_, 3, v_toPure_2038_);
v___x_2042_ = lean_apply_4(v_toBind_2037_, lean_box(0), lean_box(0), v_inst_2033_, v___f_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___boxed(lean_object* v_m_2043_, lean_object* v_pu_2044_, lean_object* v_t_2045_, lean_object* v_inst_2046_, lean_object* v_inst_2047_, lean_object* v_e_2048_){
_start:
{
uint8_t v_pu_boxed_2049_; uint8_t v_t_boxed_2050_; lean_object* v_res_2051_; 
v_pu_boxed_2049_ = lean_unbox(v_pu_2044_);
v_t_boxed_2050_ = lean_unbox(v_t_2045_);
v_res_2051_ = l_Lean_Compiler_LCNF_normExpr(v_m_2043_, v_pu_boxed_2049_, v_t_boxed_2050_, v_inst_2046_, v_inst_2047_, v_e_2048_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0(uint8_t v_pu_2052_, lean_object* v_arg_2053_, uint8_t v_t_2054_, lean_object* v_toPure_2055_, lean_object* v_____do__lift_2056_){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2052_, v_____do__lift_2056_, v_arg_2053_, v_t_2054_);
v___x_2058_ = lean_apply_2(v_toPure_2055_, lean_box(0), v___x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(lean_object* v_pu_2059_, lean_object* v_arg_2060_, lean_object* v_t_2061_, lean_object* v_toPure_2062_, lean_object* v_____do__lift_2063_){
_start:
{
uint8_t v_pu_boxed_2064_; uint8_t v_t_boxed_2065_; lean_object* v_res_2066_; 
v_pu_boxed_2064_ = lean_unbox(v_pu_2059_);
v_t_boxed_2065_ = lean_unbox(v_t_2061_);
v_res_2066_ = l_Lean_Compiler_LCNF_normArg___redArg___lam__0(v_pu_boxed_2064_, v_arg_2060_, v_t_boxed_2065_, v_toPure_2062_, v_____do__lift_2063_);
lean_dec_ref(v_____do__lift_2063_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg(uint8_t v_pu_2067_, uint8_t v_t_2068_, lean_object* v_inst_2069_, lean_object* v_inst_2070_, lean_object* v_arg_2071_){
_start:
{
lean_object* v_toApplicative_2072_; lean_object* v_toBind_2073_; lean_object* v_toPure_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___f_2077_; lean_object* v___x_2078_; 
v_toApplicative_2072_ = lean_ctor_get(v_inst_2070_, 0);
lean_inc_ref(v_toApplicative_2072_);
v_toBind_2073_ = lean_ctor_get(v_inst_2070_, 1);
lean_inc(v_toBind_2073_);
lean_dec_ref(v_inst_2070_);
v_toPure_2074_ = lean_ctor_get(v_toApplicative_2072_, 1);
lean_inc(v_toPure_2074_);
lean_dec_ref(v_toApplicative_2072_);
v___x_2075_ = lean_box(v_pu_2067_);
v___x_2076_ = lean_box(v_t_2068_);
v___f_2077_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2077_, 0, v___x_2075_);
lean_closure_set(v___f_2077_, 1, v_arg_2071_);
lean_closure_set(v___f_2077_, 2, v___x_2076_);
lean_closure_set(v___f_2077_, 3, v_toPure_2074_);
v___x_2078_ = lean_apply_4(v_toBind_2073_, lean_box(0), lean_box(0), v_inst_2069_, v___f_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___boxed(lean_object* v_pu_2079_, lean_object* v_t_2080_, lean_object* v_inst_2081_, lean_object* v_inst_2082_, lean_object* v_arg_2083_){
_start:
{
uint8_t v_pu_boxed_2084_; uint8_t v_t_boxed_2085_; lean_object* v_res_2086_; 
v_pu_boxed_2084_ = lean_unbox(v_pu_2079_);
v_t_boxed_2085_ = lean_unbox(v_t_2080_);
v_res_2086_ = l_Lean_Compiler_LCNF_normArg___redArg(v_pu_boxed_2084_, v_t_boxed_2085_, v_inst_2081_, v_inst_2082_, v_arg_2083_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg(lean_object* v_m_2087_, uint8_t v_pu_2088_, uint8_t v_t_2089_, lean_object* v_inst_2090_, lean_object* v_inst_2091_, lean_object* v_arg_2092_){
_start:
{
lean_object* v_toApplicative_2093_; lean_object* v_toBind_2094_; lean_object* v_toPure_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___f_2098_; lean_object* v___x_2099_; 
v_toApplicative_2093_ = lean_ctor_get(v_inst_2091_, 0);
lean_inc_ref(v_toApplicative_2093_);
v_toBind_2094_ = lean_ctor_get(v_inst_2091_, 1);
lean_inc(v_toBind_2094_);
lean_dec_ref(v_inst_2091_);
v_toPure_2095_ = lean_ctor_get(v_toApplicative_2093_, 1);
lean_inc(v_toPure_2095_);
lean_dec_ref(v_toApplicative_2093_);
v___x_2096_ = lean_box(v_pu_2088_);
v___x_2097_ = lean_box(v_t_2089_);
v___f_2098_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2098_, 0, v___x_2096_);
lean_closure_set(v___f_2098_, 1, v_arg_2092_);
lean_closure_set(v___f_2098_, 2, v___x_2097_);
lean_closure_set(v___f_2098_, 3, v_toPure_2095_);
v___x_2099_ = lean_apply_4(v_toBind_2094_, lean_box(0), lean_box(0), v_inst_2090_, v___f_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___boxed(lean_object* v_m_2100_, lean_object* v_pu_2101_, lean_object* v_t_2102_, lean_object* v_inst_2103_, lean_object* v_inst_2104_, lean_object* v_arg_2105_){
_start:
{
uint8_t v_pu_boxed_2106_; uint8_t v_t_boxed_2107_; lean_object* v_res_2108_; 
v_pu_boxed_2106_ = lean_unbox(v_pu_2101_);
v_t_boxed_2107_ = lean_unbox(v_t_2102_);
v_res_2108_ = l_Lean_Compiler_LCNF_normArg(v_m_2100_, v_pu_boxed_2106_, v_t_boxed_2107_, v_inst_2103_, v_inst_2104_, v_arg_2105_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(uint8_t v_pu_2109_, lean_object* v_e_2110_, uint8_t v_t_2111_, lean_object* v_toPure_2112_, lean_object* v_____do__lift_2113_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_2109_, v_____do__lift_2113_, v_e_2110_, v_t_2111_);
v___x_2115_ = lean_apply_2(v_toPure_2112_, lean_box(0), v___x_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(lean_object* v_pu_2116_, lean_object* v_e_2117_, lean_object* v_t_2118_, lean_object* v_toPure_2119_, lean_object* v_____do__lift_2120_){
_start:
{
uint8_t v_pu_boxed_2121_; uint8_t v_t_boxed_2122_; lean_object* v_res_2123_; 
v_pu_boxed_2121_ = lean_unbox(v_pu_2116_);
v_t_boxed_2122_ = lean_unbox(v_t_2118_);
v_res_2123_ = l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(v_pu_boxed_2121_, v_e_2117_, v_t_boxed_2122_, v_toPure_2119_, v_____do__lift_2120_);
lean_dec_ref(v_____do__lift_2120_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg(uint8_t v_pu_2124_, uint8_t v_t_2125_, lean_object* v_inst_2126_, lean_object* v_inst_2127_, lean_object* v_e_2128_){
_start:
{
lean_object* v_toApplicative_2129_; lean_object* v_toBind_2130_; lean_object* v_toPure_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___f_2134_; lean_object* v___x_2135_; 
v_toApplicative_2129_ = lean_ctor_get(v_inst_2127_, 0);
lean_inc_ref(v_toApplicative_2129_);
v_toBind_2130_ = lean_ctor_get(v_inst_2127_, 1);
lean_inc(v_toBind_2130_);
lean_dec_ref(v_inst_2127_);
v_toPure_2131_ = lean_ctor_get(v_toApplicative_2129_, 1);
lean_inc(v_toPure_2131_);
lean_dec_ref(v_toApplicative_2129_);
v___x_2132_ = lean_box(v_pu_2124_);
v___x_2133_ = lean_box(v_t_2125_);
v___f_2134_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2134_, 0, v___x_2132_);
lean_closure_set(v___f_2134_, 1, v_e_2128_);
lean_closure_set(v___f_2134_, 2, v___x_2133_);
lean_closure_set(v___f_2134_, 3, v_toPure_2131_);
v___x_2135_ = lean_apply_4(v_toBind_2130_, lean_box(0), lean_box(0), v_inst_2126_, v___f_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(lean_object* v_pu_2136_, lean_object* v_t_2137_, lean_object* v_inst_2138_, lean_object* v_inst_2139_, lean_object* v_e_2140_){
_start:
{
uint8_t v_pu_boxed_2141_; uint8_t v_t_boxed_2142_; lean_object* v_res_2143_; 
v_pu_boxed_2141_ = lean_unbox(v_pu_2136_);
v_t_boxed_2142_ = lean_unbox(v_t_2137_);
v_res_2143_ = l_Lean_Compiler_LCNF_normLetValue___redArg(v_pu_boxed_2141_, v_t_boxed_2142_, v_inst_2138_, v_inst_2139_, v_e_2140_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue(lean_object* v_m_2144_, uint8_t v_pu_2145_, uint8_t v_t_2146_, lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_e_2149_){
_start:
{
lean_object* v_toApplicative_2150_; lean_object* v_toBind_2151_; lean_object* v_toPure_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___f_2155_; lean_object* v___x_2156_; 
v_toApplicative_2150_ = lean_ctor_get(v_inst_2148_, 0);
lean_inc_ref(v_toApplicative_2150_);
v_toBind_2151_ = lean_ctor_get(v_inst_2148_, 1);
lean_inc(v_toBind_2151_);
lean_dec_ref(v_inst_2148_);
v_toPure_2152_ = lean_ctor_get(v_toApplicative_2150_, 1);
lean_inc(v_toPure_2152_);
lean_dec_ref(v_toApplicative_2150_);
v___x_2153_ = lean_box(v_pu_2145_);
v___x_2154_ = lean_box(v_t_2146_);
v___f_2155_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2155_, 0, v___x_2153_);
lean_closure_set(v___f_2155_, 1, v_e_2149_);
lean_closure_set(v___f_2155_, 2, v___x_2154_);
lean_closure_set(v___f_2155_, 3, v_toPure_2152_);
v___x_2156_ = lean_apply_4(v_toBind_2151_, lean_box(0), lean_box(0), v_inst_2147_, v___f_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___boxed(lean_object* v_m_2157_, lean_object* v_pu_2158_, lean_object* v_t_2159_, lean_object* v_inst_2160_, lean_object* v_inst_2161_, lean_object* v_e_2162_){
_start:
{
uint8_t v_pu_boxed_2163_; uint8_t v_t_boxed_2164_; lean_object* v_res_2165_; 
v_pu_boxed_2163_ = lean_unbox(v_pu_2158_);
v_t_boxed_2164_ = lean_unbox(v_t_2159_);
v_res_2165_ = l_Lean_Compiler_LCNF_normLetValue(v_m_2157_, v_pu_boxed_2163_, v_t_boxed_2164_, v_inst_2160_, v_inst_2161_, v_e_2162_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore(uint8_t v_pu_2166_, lean_object* v_s_2167_, lean_object* v_e_2168_, uint8_t v_translator_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2166_, v_s_2167_, v_translator_2169_, v_e_2168_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore___boxed(lean_object* v_pu_2171_, lean_object* v_s_2172_, lean_object* v_e_2173_, lean_object* v_translator_2174_){
_start:
{
uint8_t v_pu_boxed_2175_; uint8_t v_translator_boxed_2176_; lean_object* v_res_2177_; 
v_pu_boxed_2175_ = lean_unbox(v_pu_2171_);
v_translator_boxed_2176_ = lean_unbox(v_translator_2174_);
v_res_2177_ = l_Lean_Compiler_LCNF_normExprCore(v_pu_boxed_2175_, v_s_2172_, v_e_2173_, v_translator_boxed_2176_);
lean_dec_ref(v_s_2172_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(uint8_t v_pu_2178_, lean_object* v_args_2179_, uint8_t v_t_2180_, lean_object* v_toPure_2181_, lean_object* v_____do__lift_2182_){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_2178_, v_____do__lift_2182_, v_args_2179_, v_t_2180_);
v___x_2184_ = lean_apply_2(v_toPure_2181_, lean_box(0), v___x_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(lean_object* v_pu_2185_, lean_object* v_args_2186_, lean_object* v_t_2187_, lean_object* v_toPure_2188_, lean_object* v_____do__lift_2189_){
_start:
{
uint8_t v_pu_boxed_2190_; uint8_t v_t_boxed_2191_; lean_object* v_res_2192_; 
v_pu_boxed_2190_ = lean_unbox(v_pu_2185_);
v_t_boxed_2191_ = lean_unbox(v_t_2187_);
v_res_2192_ = l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(v_pu_boxed_2190_, v_args_2186_, v_t_boxed_2191_, v_toPure_2188_, v_____do__lift_2189_);
lean_dec_ref(v_____do__lift_2189_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg(uint8_t v_pu_2193_, uint8_t v_t_2194_, lean_object* v_inst_2195_, lean_object* v_inst_2196_, lean_object* v_args_2197_){
_start:
{
lean_object* v_toApplicative_2198_; lean_object* v_toBind_2199_; lean_object* v_toPure_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___f_2203_; lean_object* v___x_2204_; 
v_toApplicative_2198_ = lean_ctor_get(v_inst_2196_, 0);
lean_inc_ref(v_toApplicative_2198_);
v_toBind_2199_ = lean_ctor_get(v_inst_2196_, 1);
lean_inc(v_toBind_2199_);
lean_dec_ref(v_inst_2196_);
v_toPure_2200_ = lean_ctor_get(v_toApplicative_2198_, 1);
lean_inc(v_toPure_2200_);
lean_dec_ref(v_toApplicative_2198_);
v___x_2201_ = lean_box(v_pu_2193_);
v___x_2202_ = lean_box(v_t_2194_);
v___f_2203_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2203_, 0, v___x_2201_);
lean_closure_set(v___f_2203_, 1, v_args_2197_);
lean_closure_set(v___f_2203_, 2, v___x_2202_);
lean_closure_set(v___f_2203_, 3, v_toPure_2200_);
v___x_2204_ = lean_apply_4(v_toBind_2199_, lean_box(0), lean_box(0), v_inst_2195_, v___f_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___boxed(lean_object* v_pu_2205_, lean_object* v_t_2206_, lean_object* v_inst_2207_, lean_object* v_inst_2208_, lean_object* v_args_2209_){
_start:
{
uint8_t v_pu_boxed_2210_; uint8_t v_t_boxed_2211_; lean_object* v_res_2212_; 
v_pu_boxed_2210_ = lean_unbox(v_pu_2205_);
v_t_boxed_2211_ = lean_unbox(v_t_2206_);
v_res_2212_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_boxed_2210_, v_t_boxed_2211_, v_inst_2207_, v_inst_2208_, v_args_2209_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs(lean_object* v_m_2213_, uint8_t v_pu_2214_, uint8_t v_t_2215_, lean_object* v_inst_2216_, lean_object* v_inst_2217_, lean_object* v_args_2218_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_2214_, v_t_2215_, v_inst_2216_, v_inst_2217_, v_args_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___boxed(lean_object* v_m_2220_, lean_object* v_pu_2221_, lean_object* v_t_2222_, lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_args_2225_){
_start:
{
uint8_t v_pu_boxed_2226_; uint8_t v_t_boxed_2227_; lean_object* v_res_2228_; 
v_pu_boxed_2226_ = lean_unbox(v_pu_2221_);
v_t_boxed_2227_ = lean_unbox(v_t_2222_);
v_res_2228_ = l_Lean_Compiler_LCNF_normArgs(v_m_2220_, v_pu_boxed_2226_, v_t_boxed_2227_, v_inst_2223_, v_inst_2224_, v_args_2225_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object* v_binderName_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v_lctx_2234_; lean_object* v_nextIdx_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2248_; 
v___x_2232_ = lean_st_ref_get(v_a_2230_);
v___x_2233_ = lean_st_ref_take(v_a_2230_);
v_lctx_2234_ = lean_ctor_get(v___x_2233_, 0);
v_nextIdx_2235_ = lean_ctor_get(v___x_2233_, 1);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2237_ = v___x_2233_;
v_isShared_2238_ = v_isSharedCheck_2248_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_nextIdx_2235_);
lean_inc(v_lctx_2234_);
lean_dec(v___x_2233_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2248_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2239_ = lean_unsigned_to_nat(1u);
v___x_2240_ = lean_nat_add(v_nextIdx_2235_, v___x_2239_);
lean_dec(v_nextIdx_2235_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 1, v___x_2240_);
v___x_2242_ = v___x_2237_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_lctx_2234_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
lean_object* v___x_2243_; lean_object* v_nextIdx_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2243_ = lean_st_ref_set(v_a_2230_, v___x_2242_);
v_nextIdx_2244_ = lean_ctor_get(v___x_2232_, 1);
lean_inc(v_nextIdx_2244_);
lean_dec(v___x_2232_);
v___x_2245_ = l_Lean_Name_num___override(v_binderName_2229_, v_nextIdx_2244_);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
return v___x_2246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(lean_object* v_binderName_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2249_, v_a_2250_);
lean_dec(v_a_2250_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object* v_binderName_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2253_, v_a_2255_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(lean_object* v_binderName_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_Compiler_LCNF_mkFreshBinderName(v_binderName_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
lean_dec(v_a_2262_);
lean_dec_ref(v_a_2261_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(lean_object* v_binderName_2267_, lean_object* v_baseName_2268_, lean_object* v_a_2269_){
_start:
{
uint8_t v___x_2271_; 
v___x_2271_ = l_Lean_Name_isAnonymous(v_binderName_2267_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; 
lean_dec(v_baseName_2268_);
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v_binderName_2267_);
return v___x_2272_;
}
else
{
lean_object* v___x_2273_; 
lean_dec(v_binderName_2267_);
v___x_2273_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_baseName_2268_, v_a_2269_);
return v___x_2273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(lean_object* v_binderName_2274_, lean_object* v_baseName_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2274_, v_baseName_2275_, v_a_2276_);
lean_dec(v_a_2276_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous(lean_object* v_binderName_2279_, lean_object* v_baseName_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2279_, v_baseName_2280_, v_a_2282_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(lean_object* v_binderName_2287_, lean_object* v_baseName_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_Compiler_LCNF_ensureNotAnonymous(v_binderName_2287_, v_baseName_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(lean_object* v___y_2295_){
_start:
{
lean_object* v___x_2297_; lean_object* v_ngen_2298_; lean_object* v_namePrefix_2299_; lean_object* v_idx_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2329_; 
v___x_2297_ = lean_st_ref_get(v___y_2295_);
v_ngen_2298_ = lean_ctor_get(v___x_2297_, 2);
lean_inc_ref(v_ngen_2298_);
lean_dec(v___x_2297_);
v_namePrefix_2299_ = lean_ctor_get(v_ngen_2298_, 0);
v_idx_2300_ = lean_ctor_get(v_ngen_2298_, 1);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_ngen_2298_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2302_ = v_ngen_2298_;
v_isShared_2303_ = v_isSharedCheck_2329_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_idx_2300_);
lean_inc(v_namePrefix_2299_);
lean_dec(v_ngen_2298_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2329_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v_env_2305_; lean_object* v_nextMacroScope_2306_; lean_object* v_auxDeclNGen_2307_; lean_object* v_traceState_2308_; lean_object* v_cache_2309_; lean_object* v_messages_2310_; lean_object* v_infoState_2311_; lean_object* v_snapshotTasks_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2327_; 
v___x_2304_ = lean_st_ref_take(v___y_2295_);
v_env_2305_ = lean_ctor_get(v___x_2304_, 0);
v_nextMacroScope_2306_ = lean_ctor_get(v___x_2304_, 1);
v_auxDeclNGen_2307_ = lean_ctor_get(v___x_2304_, 3);
v_traceState_2308_ = lean_ctor_get(v___x_2304_, 4);
v_cache_2309_ = lean_ctor_get(v___x_2304_, 5);
v_messages_2310_ = lean_ctor_get(v___x_2304_, 6);
v_infoState_2311_ = lean_ctor_get(v___x_2304_, 7);
v_snapshotTasks_2312_ = lean_ctor_get(v___x_2304_, 8);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; 
v_unused_2328_ = lean_ctor_get(v___x_2304_, 2);
lean_dec(v_unused_2328_);
v___x_2314_ = v___x_2304_;
v_isShared_2315_ = v_isSharedCheck_2327_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_snapshotTasks_2312_);
lean_inc(v_infoState_2311_);
lean_inc(v_messages_2310_);
lean_inc(v_cache_2309_);
lean_inc(v_traceState_2308_);
lean_inc(v_auxDeclNGen_2307_);
lean_inc(v_nextMacroScope_2306_);
lean_inc(v_env_2305_);
lean_dec(v___x_2304_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2327_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v_r_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; 
lean_inc(v_idx_2300_);
lean_inc(v_namePrefix_2299_);
v_r_2316_ = l_Lean_Name_num___override(v_namePrefix_2299_, v_idx_2300_);
v___x_2317_ = lean_unsigned_to_nat(1u);
v___x_2318_ = lean_nat_add(v_idx_2300_, v___x_2317_);
lean_dec(v_idx_2300_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 1, v___x_2318_);
v___x_2320_ = v___x_2302_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_namePrefix_2299_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___x_2318_);
v___x_2320_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2322_; 
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 2, v___x_2320_);
v___x_2322_ = v___x_2314_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_env_2305_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_nextMacroScope_2306_);
lean_ctor_set(v_reuseFailAlloc_2325_, 2, v___x_2320_);
lean_ctor_set(v_reuseFailAlloc_2325_, 3, v_auxDeclNGen_2307_);
lean_ctor_set(v_reuseFailAlloc_2325_, 4, v_traceState_2308_);
lean_ctor_set(v_reuseFailAlloc_2325_, 5, v_cache_2309_);
lean_ctor_set(v_reuseFailAlloc_2325_, 6, v_messages_2310_);
lean_ctor_set(v_reuseFailAlloc_2325_, 7, v_infoState_2311_);
lean_ctor_set(v_reuseFailAlloc_2325_, 8, v_snapshotTasks_2312_);
v___x_2322_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = lean_st_ref_set(v___y_2295_, v___x_2322_);
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v_r_2316_);
return v___x_2324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2330_);
lean_dec(v___y_2330_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
v___x_2338_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2336_);
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2338_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2338_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t v_pu_2356_, lean_object* v_binderName_2357_, lean_object* v_type_2358_, uint8_t v_borrow_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2389_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___x_2365_, 1);
v___x_2367_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_2368_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2357_, v___x_2367_, v_a_2361_);
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2371_ = v___x_2368_;
v_isShared_2372_ = v_isSharedCheck_2389_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2368_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2389_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; lean_object* v_lctx_2374_; lean_object* v_nextIdx_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2388_; 
v___x_2373_ = lean_st_ref_take(v_a_2361_);
v_lctx_2374_ = lean_ctor_get(v___x_2373_, 0);
v_nextIdx_2375_ = lean_ctor_get(v___x_2373_, 1);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2377_ = v___x_2373_;
v_isShared_2378_ = v_isSharedCheck_2388_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_nextIdx_2375_);
lean_inc(v_lctx_2374_);
lean_dec(v___x_2373_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2388_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2379_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2379_, 0, v_a_2366_);
lean_ctor_set(v___x_2379_, 1, v_a_2369_);
lean_ctor_set(v___x_2379_, 2, v_type_2358_);
lean_ctor_set_uint8(v___x_2379_, sizeof(void*)*3, v_borrow_2359_);
lean_inc_ref(v___x_2379_);
v___x_2380_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2356_, v_lctx_2374_, v___x_2379_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2380_);
v___x_2382_ = v___x_2377_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v_nextIdx_2375_);
v___x_2382_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2383_ = lean_st_ref_set(v_a_2361_, v___x_2382_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2379_);
v___x_2385_ = v___x_2371_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2379_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec_ref(v_type_2358_);
lean_dec(v_binderName_2357_);
v_a_2390_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2365_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2365_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam___boxed(lean_object* v_pu_2398_, lean_object* v_binderName_2399_, lean_object* v_type_2400_, lean_object* v_borrow_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_){
_start:
{
uint8_t v_pu_boxed_2407_; uint8_t v_borrow_boxed_2408_; lean_object* v_res_2409_; 
v_pu_boxed_2407_ = lean_unbox(v_pu_2398_);
v_borrow_boxed_2408_ = lean_unbox(v_borrow_2401_);
v_res_2409_ = l_Lean_Compiler_LCNF_mkParam(v_pu_boxed_2407_, v_binderName_2399_, v_type_2400_, v_borrow_boxed_2408_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2413_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t v_pu_2425_, lean_object* v_binderName_2426_, lean_object* v_type_2427_, lean_object* v_value_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2458_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref_known(v___x_2434_, 1);
v___x_2436_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2437_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2426_, v___x_2436_, v_a_2430_);
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2440_ = v___x_2437_;
v_isShared_2441_ = v_isSharedCheck_2458_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2437_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2458_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2442_; lean_object* v_lctx_2443_; lean_object* v_nextIdx_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2457_; 
v___x_2442_ = lean_st_ref_take(v_a_2430_);
v_lctx_2443_ = lean_ctor_get(v___x_2442_, 0);
v_nextIdx_2444_ = lean_ctor_get(v___x_2442_, 1);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2446_ = v___x_2442_;
v_isShared_2447_ = v_isSharedCheck_2457_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_nextIdx_2444_);
lean_inc(v_lctx_2443_);
lean_dec(v___x_2442_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2457_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2451_; 
v___x_2448_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2448_, 0, v_a_2435_);
lean_ctor_set(v___x_2448_, 1, v_a_2438_);
lean_ctor_set(v___x_2448_, 2, v_type_2427_);
lean_ctor_set(v___x_2448_, 3, v_value_2428_);
lean_inc_ref(v___x_2448_);
v___x_2449_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2425_, v_lctx_2443_, v___x_2448_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v___x_2449_);
v___x_2451_ = v___x_2446_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_nextIdx_2444_);
v___x_2451_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
lean_object* v___x_2452_; lean_object* v___x_2454_; 
v___x_2452_ = lean_st_ref_set(v_a_2430_, v___x_2451_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2448_);
v___x_2454_ = v___x_2440_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2448_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec(v_value_2428_);
lean_dec_ref(v_type_2427_);
lean_dec(v_binderName_2426_);
v_a_2459_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2434_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2434_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl___boxed(lean_object* v_pu_2467_, lean_object* v_binderName_2468_, lean_object* v_type_2469_, lean_object* v_value_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
uint8_t v_pu_boxed_2476_; lean_object* v_res_2477_; 
v_pu_boxed_2476_ = lean_unbox(v_pu_2467_);
v_res_2477_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_boxed_2476_, v_binderName_2468_, v_type_2469_, v_value_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t v_pu_2481_, lean_object* v_binderName_2482_, lean_object* v_type_2483_, lean_object* v_params_2484_, lean_object* v_value_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2515_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2492_);
lean_dec_ref_known(v___x_2491_, 1);
v___x_2493_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFunDecl___closed__1));
v___x_2494_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2482_, v___x_2493_, v_a_2487_);
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2497_ = v___x_2494_;
v_isShared_2498_ = v_isSharedCheck_2515_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2494_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2515_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2499_; lean_object* v_lctx_2500_; lean_object* v_nextIdx_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2514_; 
v___x_2499_ = lean_st_ref_take(v_a_2487_);
v_lctx_2500_ = lean_ctor_get(v___x_2499_, 0);
v_nextIdx_2501_ = lean_ctor_get(v___x_2499_, 1);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2503_ = v___x_2499_;
v_isShared_2504_ = v_isSharedCheck_2514_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_nextIdx_2501_);
lean_inc(v_lctx_2500_);
lean_dec(v___x_2499_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2514_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2505_, 0, v_a_2492_);
lean_ctor_set(v___x_2505_, 1, v_a_2495_);
lean_ctor_set(v___x_2505_, 2, v_params_2484_);
lean_ctor_set(v___x_2505_, 3, v_type_2483_);
lean_ctor_set(v___x_2505_, 4, v_value_2485_);
lean_inc_ref(v___x_2505_);
v___x_2506_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2481_, v_lctx_2500_, v___x_2505_);
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 0, v___x_2506_);
v___x_2508_ = v___x_2503_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_nextIdx_2501_);
v___x_2508_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2509_ = lean_st_ref_set(v_a_2487_, v___x_2508_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 0, v___x_2505_);
v___x_2511_ = v___x_2497_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2505_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec_ref(v_value_2485_);
lean_dec_ref(v_params_2484_);
lean_dec_ref(v_type_2483_);
lean_dec(v_binderName_2482_);
v_a_2516_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2491_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2491_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl___boxed(lean_object* v_pu_2524_, lean_object* v_binderName_2525_, lean_object* v_type_2526_, lean_object* v_params_2527_, lean_object* v_value_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
uint8_t v_pu_boxed_2534_; lean_object* v_res_2535_; 
v_pu_boxed_2534_ = lean_unbox(v_pu_2524_);
v_res_2535_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_boxed_2534_, v_binderName_2525_, v_type_2526_, v_params_2527_, v_value_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t v_pu_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v_a_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2542_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2543_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2542_, v_a_2538_);
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref(v___x_2543_);
v___x_2545_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2546_ = lean_box(1);
v___x_2547_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2536_, v_a_2544_, v___x_2545_, v___x_2546_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(lean_object* v_pu_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
uint8_t v_pu_boxed_2554_; lean_object* v_res_2555_; 
v_pu_boxed_2554_ = lean_unbox(v_pu_2548_);
v_res_2555_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_boxed_2554_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t v_pu_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2573_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2565_ = v___x_2562_;
v_isShared_2566_ = v_isSharedCheck_2573_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2573_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v_fvarId_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2571_; 
v_fvarId_2567_ = lean_ctor_get(v_a_2563_, 0);
lean_inc(v_fvarId_2567_);
v___x_2568_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2568_, 0, v_fvarId_2567_);
v___x_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2569_, 0, v_a_2563_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2569_);
v___x_2571_ = v___x_2565_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2569_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
v_a_2574_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2562_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2562_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased___boxed(lean_object* v_pu_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
uint8_t v_pu_boxed_2588_; lean_object* v_res_2589_; 
v_pu_boxed_2588_ = lean_unbox(v_pu_2582_);
v_res_2589_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_boxed_2588_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t v_pu_2590_, lean_object* v_p_2591_, lean_object* v_type_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v_fvarId_2595_; lean_object* v_binderName_2596_; lean_object* v_type_2597_; uint8_t v_borrow_2598_; size_t v___x_2599_; size_t v___x_2600_; uint8_t v___x_2601_; 
v_fvarId_2595_ = lean_ctor_get(v_p_2591_, 0);
v_binderName_2596_ = lean_ctor_get(v_p_2591_, 1);
v_type_2597_ = lean_ctor_get(v_p_2591_, 2);
v_borrow_2598_ = lean_ctor_get_uint8(v_p_2591_, sizeof(void*)*3);
v___x_2599_ = lean_ptr_addr(v_type_2592_);
v___x_2600_ = lean_ptr_addr(v_type_2597_);
v___x_2601_ = lean_usize_dec_eq(v___x_2599_, v___x_2600_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2621_; 
lean_inc(v_binderName_2596_);
lean_inc(v_fvarId_2595_);
v_isSharedCheck_2621_ = !lean_is_exclusive(v_p_2591_);
if (v_isSharedCheck_2621_ == 0)
{
lean_object* v_unused_2622_; lean_object* v_unused_2623_; lean_object* v_unused_2624_; 
v_unused_2622_ = lean_ctor_get(v_p_2591_, 2);
lean_dec(v_unused_2622_);
v_unused_2623_ = lean_ctor_get(v_p_2591_, 1);
lean_dec(v_unused_2623_);
v_unused_2624_ = lean_ctor_get(v_p_2591_, 0);
lean_dec(v_unused_2624_);
v___x_2603_ = v_p_2591_;
v_isShared_2604_ = v_isSharedCheck_2621_;
goto v_resetjp_2602_;
}
else
{
lean_dec(v_p_2591_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2621_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v_lctx_2606_; lean_object* v_nextIdx_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2620_; 
v___x_2605_ = lean_st_ref_take(v_a_2593_);
v_lctx_2606_ = lean_ctor_get(v___x_2605_, 0);
v_nextIdx_2607_ = lean_ctor_get(v___x_2605_, 1);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2609_ = v___x_2605_;
v_isShared_2610_ = v_isSharedCheck_2620_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_nextIdx_2607_);
lean_inc(v_lctx_2606_);
lean_dec(v___x_2605_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2620_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v_p_2612_; 
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 2, v_type_2592_);
v_p_2612_ = v___x_2603_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_fvarId_2595_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_binderName_2596_);
lean_ctor_set(v_reuseFailAlloc_2619_, 2, v_type_2592_);
lean_ctor_set_uint8(v_reuseFailAlloc_2619_, sizeof(void*)*3, v_borrow_2598_);
v_p_2612_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2613_; lean_object* v___x_2615_; 
lean_inc_ref(v_p_2612_);
v___x_2613_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2590_, v_lctx_2606_, v_p_2612_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v___x_2613_);
v___x_2615_ = v___x_2609_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2613_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_nextIdx_2607_);
v___x_2615_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = lean_st_ref_set(v_a_2593_, v___x_2615_);
v___x_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2617_, 0, v_p_2612_);
return v___x_2617_;
}
}
}
}
}
else
{
lean_object* v___x_2625_; 
lean_dec_ref(v_type_2592_);
v___x_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2625_, 0, v_p_2591_);
return v___x_2625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(lean_object* v_pu_2626_, lean_object* v_p_2627_, lean_object* v_type_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_){
_start:
{
uint8_t v_pu_boxed_2631_; lean_object* v_res_2632_; 
v_pu_boxed_2631_ = lean_unbox(v_pu_2626_);
v_res_2632_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_boxed_2631_, v_p_2627_, v_type_2628_, v_a_2629_);
lean_dec(v_a_2629_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(uint8_t v_pu_2633_, lean_object* v_p_2634_, lean_object* v_type_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_2633_, v_p_2634_, v_type_2635_, v_a_2637_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object* v_pu_2642_, lean_object* v_p_2643_, lean_object* v_type_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
uint8_t v_pu_boxed_2650_; lean_object* v_res_2651_; 
v_pu_boxed_2650_ = lean_unbox(v_pu_2642_);
v_res_2651_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(v_pu_boxed_2650_, v_p_2643_, v_type_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t v_pu_2652_, lean_object* v_p_2653_, uint8_t v_borrow_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_fvarId_2657_; lean_object* v_binderName_2658_; lean_object* v_type_2659_; uint8_t v_borrow_2660_; 
v_fvarId_2657_ = lean_ctor_get(v_p_2653_, 0);
v_binderName_2658_ = lean_ctor_get(v_p_2653_, 1);
v_type_2659_ = lean_ctor_get(v_p_2653_, 2);
v_borrow_2660_ = lean_ctor_get_uint8(v_p_2653_, sizeof(void*)*3);
if (v_borrow_2654_ == 0)
{
if (v_borrow_2660_ == 0)
{
lean_object* v___x_2676_; 
v___x_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2676_, 0, v_p_2653_);
return v___x_2676_;
}
else
{
lean_inc_ref(v_type_2659_);
lean_inc(v_binderName_2658_);
lean_inc(v_fvarId_2657_);
lean_dec_ref(v_p_2653_);
goto v___jp_2661_;
}
}
else
{
if (v_borrow_2660_ == 0)
{
lean_inc_ref(v_type_2659_);
lean_inc(v_binderName_2658_);
lean_inc(v_fvarId_2657_);
lean_dec_ref(v_p_2653_);
goto v___jp_2661_;
}
else
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2677_, 0, v_p_2653_);
return v___x_2677_;
}
}
v___jp_2661_:
{
lean_object* v___x_2662_; lean_object* v_lctx_2663_; lean_object* v_nextIdx_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2675_; 
v___x_2662_ = lean_st_ref_take(v_a_2655_);
v_lctx_2663_ = lean_ctor_get(v___x_2662_, 0);
v_nextIdx_2664_ = lean_ctor_get(v___x_2662_, 1);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2666_ = v___x_2662_;
v_isShared_2667_ = v_isSharedCheck_2675_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_nextIdx_2664_);
lean_inc(v_lctx_2663_);
lean_dec(v___x_2662_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2675_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v_p_2668_; lean_object* v___x_2669_; lean_object* v___x_2671_; 
v_p_2668_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_p_2668_, 0, v_fvarId_2657_);
lean_ctor_set(v_p_2668_, 1, v_binderName_2658_);
lean_ctor_set(v_p_2668_, 2, v_type_2659_);
lean_ctor_set_uint8(v_p_2668_, sizeof(void*)*3, v_borrow_2654_);
lean_inc_ref(v_p_2668_);
v___x_2669_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2652_, v_lctx_2663_, v_p_2668_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2669_);
v___x_2671_ = v___x_2666_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2669_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_nextIdx_2664_);
v___x_2671_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2672_ = lean_st_ref_set(v_a_2655_, v___x_2671_);
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v_p_2668_);
return v___x_2673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(lean_object* v_pu_2678_, lean_object* v_p_2679_, lean_object* v_borrow_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
uint8_t v_pu_boxed_2683_; uint8_t v_borrow_boxed_2684_; lean_object* v_res_2685_; 
v_pu_boxed_2683_ = lean_unbox(v_pu_2678_);
v_borrow_boxed_2684_ = lean_unbox(v_borrow_2680_);
v_res_2685_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_boxed_2683_, v_p_2679_, v_borrow_boxed_2684_, v_a_2681_);
lean_dec(v_a_2681_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(uint8_t v_pu_2686_, lean_object* v_p_2687_, uint8_t v_borrow_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_2686_, v_p_2687_, v_borrow_2688_, v_a_2690_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(lean_object* v_pu_2695_, lean_object* v_p_2696_, lean_object* v_borrow_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
uint8_t v_pu_boxed_2703_; uint8_t v_borrow_boxed_2704_; lean_object* v_res_2705_; 
v_pu_boxed_2703_ = lean_unbox(v_pu_2695_);
v_borrow_boxed_2704_ = lean_unbox(v_borrow_2697_);
v_res_2705_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(v_pu_boxed_2703_, v_p_2696_, v_borrow_boxed_2704_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t v_pu_2706_, lean_object* v_decl_2707_, lean_object* v_type_2708_, lean_object* v_value_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v_fvarId_2712_; lean_object* v_binderName_2713_; lean_object* v_type_2714_; lean_object* v_value_2715_; uint8_t v___y_2717_; size_t v___x_2743_; size_t v___x_2744_; uint8_t v___x_2745_; 
v_fvarId_2712_ = lean_ctor_get(v_decl_2707_, 0);
v_binderName_2713_ = lean_ctor_get(v_decl_2707_, 1);
v_type_2714_ = lean_ctor_get(v_decl_2707_, 2);
v_value_2715_ = lean_ctor_get(v_decl_2707_, 3);
v___x_2743_ = lean_ptr_addr(v_type_2708_);
v___x_2744_ = lean_ptr_addr(v_type_2714_);
v___x_2745_ = lean_usize_dec_eq(v___x_2743_, v___x_2744_);
if (v___x_2745_ == 0)
{
v___y_2717_ = v___x_2745_;
goto v___jp_2716_;
}
else
{
size_t v___x_2746_; size_t v___x_2747_; uint8_t v___x_2748_; 
v___x_2746_ = lean_ptr_addr(v_value_2709_);
v___x_2747_ = lean_ptr_addr(v_value_2715_);
v___x_2748_ = lean_usize_dec_eq(v___x_2746_, v___x_2747_);
v___y_2717_ = v___x_2748_;
goto v___jp_2716_;
}
v___jp_2716_:
{
if (v___y_2717_ == 0)
{
lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2737_; 
lean_inc(v_binderName_2713_);
lean_inc(v_fvarId_2712_);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_decl_2707_);
if (v_isSharedCheck_2737_ == 0)
{
lean_object* v_unused_2738_; lean_object* v_unused_2739_; lean_object* v_unused_2740_; lean_object* v_unused_2741_; 
v_unused_2738_ = lean_ctor_get(v_decl_2707_, 3);
lean_dec(v_unused_2738_);
v_unused_2739_ = lean_ctor_get(v_decl_2707_, 2);
lean_dec(v_unused_2739_);
v_unused_2740_ = lean_ctor_get(v_decl_2707_, 1);
lean_dec(v_unused_2740_);
v_unused_2741_ = lean_ctor_get(v_decl_2707_, 0);
lean_dec(v_unused_2741_);
v___x_2719_ = v_decl_2707_;
v_isShared_2720_ = v_isSharedCheck_2737_;
goto v_resetjp_2718_;
}
else
{
lean_dec(v_decl_2707_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2737_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2721_; lean_object* v_lctx_2722_; lean_object* v_nextIdx_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2736_; 
v___x_2721_ = lean_st_ref_take(v_a_2710_);
v_lctx_2722_ = lean_ctor_get(v___x_2721_, 0);
v_nextIdx_2723_ = lean_ctor_get(v___x_2721_, 1);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2725_ = v___x_2721_;
v_isShared_2726_ = v_isSharedCheck_2736_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_nextIdx_2723_);
lean_inc(v_lctx_2722_);
lean_dec(v___x_2721_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2736_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v_decl_2728_; 
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 3, v_value_2709_);
lean_ctor_set(v___x_2719_, 2, v_type_2708_);
v_decl_2728_ = v___x_2719_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_fvarId_2712_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_binderName_2713_);
lean_ctor_set(v_reuseFailAlloc_2735_, 2, v_type_2708_);
lean_ctor_set(v_reuseFailAlloc_2735_, 3, v_value_2709_);
v_decl_2728_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2729_; lean_object* v___x_2731_; 
lean_inc_ref(v_decl_2728_);
v___x_2729_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2706_, v_lctx_2722_, v_decl_2728_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v___x_2729_);
v___x_2731_ = v___x_2725_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2729_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v_nextIdx_2723_);
v___x_2731_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2732_ = lean_st_ref_set(v_a_2710_, v___x_2731_);
v___x_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2733_, 0, v_decl_2728_);
return v___x_2733_;
}
}
}
}
}
else
{
lean_object* v___x_2742_; 
lean_dec(v_value_2709_);
lean_dec_ref(v_type_2708_);
v___x_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2742_, 0, v_decl_2707_);
return v___x_2742_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(lean_object* v_pu_2749_, lean_object* v_decl_2750_, lean_object* v_type_2751_, lean_object* v_value_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_){
_start:
{
uint8_t v_pu_boxed_2755_; lean_object* v_res_2756_; 
v_pu_boxed_2755_ = lean_unbox(v_pu_2749_);
v_res_2756_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_boxed_2755_, v_decl_2750_, v_type_2751_, v_value_2752_, v_a_2753_);
lean_dec(v_a_2753_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(uint8_t v_pu_2757_, lean_object* v_decl_2758_, lean_object* v_type_2759_, lean_object* v_value_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2757_, v_decl_2758_, v_type_2759_, v_value_2760_, v_a_2762_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object* v_pu_2767_, lean_object* v_decl_2768_, lean_object* v_type_2769_, lean_object* v_value_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_){
_start:
{
uint8_t v_pu_boxed_2776_; lean_object* v_res_2777_; 
v_pu_boxed_2776_ = lean_unbox(v_pu_2767_);
v_res_2777_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(v_pu_boxed_2776_, v_decl_2768_, v_type_2769_, v_value_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
lean_dec(v_a_2774_);
lean_dec_ref(v_a_2773_);
lean_dec(v_a_2772_);
lean_dec_ref(v_a_2771_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t v_pu_2778_, lean_object* v_decl_2779_, lean_object* v_value_2780_, lean_object* v_a_2781_){
_start:
{
lean_object* v_type_2783_; lean_object* v___x_2784_; 
v_type_2783_ = lean_ctor_get(v_decl_2779_, 2);
lean_inc_ref(v_type_2783_);
v___x_2784_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2778_, v_decl_2779_, v_type_2783_, v_value_2780_, v_a_2781_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(lean_object* v_pu_2785_, lean_object* v_decl_2786_, lean_object* v_value_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
uint8_t v_pu_boxed_2790_; lean_object* v_res_2791_; 
v_pu_boxed_2790_ = lean_unbox(v_pu_2785_);
v_res_2791_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_boxed_2790_, v_decl_2786_, v_value_2787_, v_a_2788_);
lean_dec(v_a_2788_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(uint8_t v_pu_2792_, lean_object* v_decl_2793_, lean_object* v_value_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_2792_, v_decl_2793_, v_value_2794_, v_a_2796_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(lean_object* v_pu_2801_, lean_object* v_decl_2802_, lean_object* v_value_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
uint8_t v_pu_boxed_2809_; lean_object* v_res_2810_; 
v_pu_boxed_2809_ = lean_unbox(v_pu_2801_);
v_res_2810_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(v_pu_boxed_2809_, v_decl_2802_, v_value_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t v_pu_2811_, lean_object* v_decl_2812_, lean_object* v_type_2813_, lean_object* v_params_2814_, lean_object* v_value_2815_, lean_object* v_a_2816_){
_start:
{
lean_object* v_fvarId_2818_; lean_object* v_binderName_2819_; lean_object* v_params_2820_; lean_object* v_type_2821_; lean_object* v_value_2822_; uint8_t v___y_2839_; size_t v___x_2844_; size_t v___x_2845_; uint8_t v___x_2846_; 
v_fvarId_2818_ = lean_ctor_get(v_decl_2812_, 0);
v_binderName_2819_ = lean_ctor_get(v_decl_2812_, 1);
v_params_2820_ = lean_ctor_get(v_decl_2812_, 2);
v_type_2821_ = lean_ctor_get(v_decl_2812_, 3);
v_value_2822_ = lean_ctor_get(v_decl_2812_, 4);
v___x_2844_ = lean_ptr_addr(v_type_2813_);
v___x_2845_ = lean_ptr_addr(v_type_2821_);
v___x_2846_ = lean_usize_dec_eq(v___x_2844_, v___x_2845_);
if (v___x_2846_ == 0)
{
v___y_2839_ = v___x_2846_;
goto v___jp_2838_;
}
else
{
size_t v___x_2847_; size_t v___x_2848_; uint8_t v___x_2849_; 
v___x_2847_ = lean_ptr_addr(v_params_2814_);
v___x_2848_ = lean_ptr_addr(v_params_2820_);
v___x_2849_ = lean_usize_dec_eq(v___x_2847_, v___x_2848_);
v___y_2839_ = v___x_2849_;
goto v___jp_2838_;
}
v___jp_2823_:
{
lean_object* v___x_2824_; lean_object* v_lctx_2825_; lean_object* v_nextIdx_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2837_; 
v___x_2824_ = lean_st_ref_take(v_a_2816_);
v_lctx_2825_ = lean_ctor_get(v___x_2824_, 0);
v_nextIdx_2826_ = lean_ctor_get(v___x_2824_, 1);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2828_ = v___x_2824_;
v_isShared_2829_ = v_isSharedCheck_2837_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_nextIdx_2826_);
lean_inc(v_lctx_2825_);
lean_dec(v___x_2824_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2837_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v_decl_2830_; lean_object* v___x_2831_; lean_object* v___x_2833_; 
v_decl_2830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_decl_2830_, 0, v_fvarId_2818_);
lean_ctor_set(v_decl_2830_, 1, v_binderName_2819_);
lean_ctor_set(v_decl_2830_, 2, v_params_2814_);
lean_ctor_set(v_decl_2830_, 3, v_type_2813_);
lean_ctor_set(v_decl_2830_, 4, v_value_2815_);
lean_inc_ref(v_decl_2830_);
v___x_2831_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2811_, v_lctx_2825_, v_decl_2830_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v___x_2831_);
v___x_2833_ = v___x_2828_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2831_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_nextIdx_2826_);
v___x_2833_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_st_ref_set(v_a_2816_, v___x_2833_);
v___x_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2835_, 0, v_decl_2830_);
return v___x_2835_;
}
}
}
v___jp_2838_:
{
if (v___y_2839_ == 0)
{
lean_inc(v_binderName_2819_);
lean_inc(v_fvarId_2818_);
lean_dec_ref(v_decl_2812_);
goto v___jp_2823_;
}
else
{
size_t v___x_2840_; size_t v___x_2841_; uint8_t v___x_2842_; 
v___x_2840_ = lean_ptr_addr(v_value_2815_);
v___x_2841_ = lean_ptr_addr(v_value_2822_);
v___x_2842_ = lean_usize_dec_eq(v___x_2840_, v___x_2841_);
if (v___x_2842_ == 0)
{
lean_inc(v_binderName_2819_);
lean_inc(v_fvarId_2818_);
lean_dec_ref(v_decl_2812_);
goto v___jp_2823_;
}
else
{
lean_object* v___x_2843_; 
lean_dec_ref(v_value_2815_);
lean_dec_ref(v_params_2814_);
lean_dec_ref(v_type_2813_);
v___x_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2843_, 0, v_decl_2812_);
return v___x_2843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(lean_object* v_pu_2850_, lean_object* v_decl_2851_, lean_object* v_type_2852_, lean_object* v_params_2853_, lean_object* v_value_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
uint8_t v_pu_boxed_2857_; lean_object* v_res_2858_; 
v_pu_boxed_2857_ = lean_unbox(v_pu_2850_);
v_res_2858_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_boxed_2857_, v_decl_2851_, v_type_2852_, v_params_2853_, v_value_2854_, v_a_2855_);
lean_dec(v_a_2855_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(uint8_t v_pu_2859_, lean_object* v_decl_2860_, lean_object* v_type_2861_, lean_object* v_params_2862_, lean_object* v_value_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2859_, v_decl_2860_, v_type_2861_, v_params_2862_, v_value_2863_, v_a_2865_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object* v_pu_2870_, lean_object* v_decl_2871_, lean_object* v_type_2872_, lean_object* v_params_2873_, lean_object* v_value_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_){
_start:
{
uint8_t v_pu_boxed_2880_; lean_object* v_res_2881_; 
v_pu_boxed_2880_ = lean_unbox(v_pu_2870_);
v_res_2881_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(v_pu_boxed_2880_, v_decl_2871_, v_type_2872_, v_params_2873_, v_value_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_);
lean_dec(v_a_2878_);
lean_dec_ref(v_a_2877_);
lean_dec(v_a_2876_);
lean_dec_ref(v_a_2875_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(uint8_t v_pu_2882_, lean_object* v_decl_2883_, lean_object* v_type_2884_, lean_object* v_value_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v_params_2888_; lean_object* v___x_2889_; 
v_params_2888_ = lean_ctor_get(v_decl_2883_, 2);
lean_inc_ref(v_params_2888_);
v___x_2889_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2882_, v_decl_2883_, v_type_2884_, v_params_2888_, v_value_2885_, v_a_2886_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(lean_object* v_pu_2890_, lean_object* v_decl_2891_, lean_object* v_type_2892_, lean_object* v_value_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
uint8_t v_pu_boxed_2896_; lean_object* v_res_2897_; 
v_pu_boxed_2896_ = lean_unbox(v_pu_2890_);
v_res_2897_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(v_pu_boxed_2896_, v_decl_2891_, v_type_2892_, v_value_2893_, v_a_2894_);
lean_dec(v_a_2894_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27(uint8_t v_pu_2898_, lean_object* v_decl_2899_, lean_object* v_type_2900_, lean_object* v_value_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v_params_2907_; lean_object* v___x_2908_; 
v_params_2907_ = lean_ctor_get(v_decl_2899_, 2);
lean_inc_ref(v_params_2907_);
v___x_2908_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2898_, v_decl_2899_, v_type_2900_, v_params_2907_, v_value_2901_, v_a_2903_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(lean_object* v_pu_2909_, lean_object* v_decl_2910_, lean_object* v_type_2911_, lean_object* v_value_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
uint8_t v_pu_boxed_2918_; lean_object* v_res_2919_; 
v_pu_boxed_2918_ = lean_unbox(v_pu_2909_);
v_res_2919_ = l_Lean_Compiler_LCNF_FunDecl_update_x27(v_pu_boxed_2918_, v_decl_2910_, v_type_2911_, v_value_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(uint8_t v_pu_2920_, lean_object* v_decl_2921_, lean_object* v_value_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v_params_2925_; lean_object* v_type_2926_; lean_object* v___x_2927_; 
v_params_2925_ = lean_ctor_get(v_decl_2921_, 2);
lean_inc_ref(v_params_2925_);
v_type_2926_ = lean_ctor_get(v_decl_2921_, 3);
lean_inc_ref(v_type_2926_);
v___x_2927_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2920_, v_decl_2921_, v_type_2926_, v_params_2925_, v_value_2922_, v_a_2923_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(lean_object* v_pu_2928_, lean_object* v_decl_2929_, lean_object* v_value_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_){
_start:
{
uint8_t v_pu_boxed_2933_; lean_object* v_res_2934_; 
v_pu_boxed_2933_ = lean_unbox(v_pu_2928_);
v_res_2934_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(v_pu_boxed_2933_, v_decl_2929_, v_value_2930_, v_a_2931_);
lean_dec(v_a_2931_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue(uint8_t v_pu_2935_, lean_object* v_decl_2936_, lean_object* v_value_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v_params_2943_; lean_object* v_type_2944_; lean_object* v___x_2945_; 
v_params_2943_ = lean_ctor_get(v_decl_2936_, 2);
lean_inc_ref(v_params_2943_);
v_type_2944_ = lean_ctor_get(v_decl_2936_, 3);
lean_inc_ref(v_type_2944_);
v___x_2945_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2935_, v_decl_2936_, v_type_2944_, v_params_2943_, v_value_2937_, v_a_2939_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(lean_object* v_pu_2946_, lean_object* v_decl_2947_, lean_object* v_value_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_){
_start:
{
uint8_t v_pu_boxed_2954_; lean_object* v_res_2955_; 
v_pu_boxed_2954_ = lean_unbox(v_pu_2946_);
v_res_2955_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(v_pu_boxed_2954_, v_decl_2947_, v_value_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0(uint8_t v_pu_2956_, lean_object* v_p_2957_, lean_object* v_inst_2958_, lean_object* v_____do__lift_2959_){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = lean_box(v_pu_2956_);
v___x_2961_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_2961_, 0, v___x_2960_);
lean_closure_set(v___x_2961_, 1, v_p_2957_);
lean_closure_set(v___x_2961_, 2, v_____do__lift_2959_);
v___x_2962_ = lean_apply_2(v_inst_2958_, lean_box(0), v___x_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(lean_object* v_pu_2963_, lean_object* v_p_2964_, lean_object* v_inst_2965_, lean_object* v_____do__lift_2966_){
_start:
{
uint8_t v_pu_boxed_2967_; lean_object* v_res_2968_; 
v_pu_boxed_2967_ = lean_unbox(v_pu_2963_);
v_res_2968_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__0(v_pu_boxed_2967_, v_p_2964_, v_inst_2965_, v_____do__lift_2966_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1(uint8_t v_pu_2969_, uint8_t v_t_2970_, lean_object* v_type_2971_, lean_object* v_toPure_2972_, lean_object* v_____do__lift_2973_){
_start:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2974_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2969_, v_____do__lift_2973_, v_t_2970_, v_type_2971_);
v___x_2975_ = lean_apply_2(v_toPure_2972_, lean_box(0), v___x_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(lean_object* v_pu_2976_, lean_object* v_t_2977_, lean_object* v_type_2978_, lean_object* v_toPure_2979_, lean_object* v_____do__lift_2980_){
_start:
{
uint8_t v_pu_boxed_2981_; uint8_t v_t_boxed_2982_; lean_object* v_res_2983_; 
v_pu_boxed_2981_ = lean_unbox(v_pu_2976_);
v_t_boxed_2982_ = lean_unbox(v_t_2977_);
v_res_2983_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(v_pu_boxed_2981_, v_t_boxed_2982_, v_type_2978_, v_toPure_2979_, v_____do__lift_2980_);
lean_dec_ref(v_____do__lift_2980_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg(uint8_t v_pu_2984_, uint8_t v_t_2985_, lean_object* v_inst_2986_, lean_object* v_inst_2987_, lean_object* v_inst_2988_, lean_object* v_p_2989_){
_start:
{
lean_object* v_toApplicative_2990_; lean_object* v_toBind_2991_; lean_object* v_type_2992_; lean_object* v_toPure_2993_; lean_object* v___x_2994_; lean_object* v___f_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___f_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v_toApplicative_2990_ = lean_ctor_get(v_inst_2987_, 0);
lean_inc_ref(v_toApplicative_2990_);
v_toBind_2991_ = lean_ctor_get(v_inst_2987_, 1);
lean_inc_n(v_toBind_2991_, 2);
lean_dec_ref(v_inst_2987_);
v_type_2992_ = lean_ctor_get(v_p_2989_, 2);
lean_inc_ref(v_type_2992_);
v_toPure_2993_ = lean_ctor_get(v_toApplicative_2990_, 1);
lean_inc(v_toPure_2993_);
lean_dec_ref(v_toApplicative_2990_);
v___x_2994_ = lean_box(v_pu_2984_);
v___f_2995_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2995_, 0, v___x_2994_);
lean_closure_set(v___f_2995_, 1, v_p_2989_);
lean_closure_set(v___f_2995_, 2, v_inst_2986_);
v___x_2996_ = lean_box(v_pu_2984_);
v___x_2997_ = lean_box(v_t_2985_);
v___f_2998_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2998_, 0, v___x_2996_);
lean_closure_set(v___f_2998_, 1, v___x_2997_);
lean_closure_set(v___f_2998_, 2, v_type_2992_);
lean_closure_set(v___f_2998_, 3, v_toPure_2993_);
v___x_2999_ = lean_apply_4(v_toBind_2991_, lean_box(0), lean_box(0), v_inst_2988_, v___f_2998_);
v___x_3000_ = lean_apply_4(v_toBind_2991_, lean_box(0), lean_box(0), v___x_2999_, v___f_2995_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___boxed(lean_object* v_pu_3001_, lean_object* v_t_3002_, lean_object* v_inst_3003_, lean_object* v_inst_3004_, lean_object* v_inst_3005_, lean_object* v_p_3006_){
_start:
{
uint8_t v_pu_boxed_3007_; uint8_t v_t_boxed_3008_; lean_object* v_res_3009_; 
v_pu_boxed_3007_ = lean_unbox(v_pu_3001_);
v_t_boxed_3008_ = lean_unbox(v_t_3002_);
v_res_3009_ = l_Lean_Compiler_LCNF_normParam___redArg(v_pu_boxed_3007_, v_t_boxed_3008_, v_inst_3003_, v_inst_3004_, v_inst_3005_, v_p_3006_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam(lean_object* v_m_3010_, uint8_t v_pu_3011_, uint8_t v_t_3012_, lean_object* v_inst_3013_, lean_object* v_inst_3014_, lean_object* v_inst_3015_, lean_object* v_p_3016_){
_start:
{
lean_object* v_toApplicative_3017_; lean_object* v_toBind_3018_; lean_object* v_type_3019_; lean_object* v_toPure_3020_; lean_object* v___x_3021_; lean_object* v___f_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___f_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v_toApplicative_3017_ = lean_ctor_get(v_inst_3014_, 0);
lean_inc_ref(v_toApplicative_3017_);
v_toBind_3018_ = lean_ctor_get(v_inst_3014_, 1);
lean_inc_n(v_toBind_3018_, 2);
lean_dec_ref(v_inst_3014_);
v_type_3019_ = lean_ctor_get(v_p_3016_, 2);
lean_inc_ref(v_type_3019_);
v_toPure_3020_ = lean_ctor_get(v_toApplicative_3017_, 1);
lean_inc(v_toPure_3020_);
lean_dec_ref(v_toApplicative_3017_);
v___x_3021_ = lean_box(v_pu_3011_);
v___f_3022_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3022_, 0, v___x_3021_);
lean_closure_set(v___f_3022_, 1, v_p_3016_);
lean_closure_set(v___f_3022_, 2, v_inst_3013_);
v___x_3023_ = lean_box(v_pu_3011_);
v___x_3024_ = lean_box(v_t_3012_);
v___f_3025_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3025_, 0, v___x_3023_);
lean_closure_set(v___f_3025_, 1, v___x_3024_);
lean_closure_set(v___f_3025_, 2, v_type_3019_);
lean_closure_set(v___f_3025_, 3, v_toPure_3020_);
v___x_3026_ = lean_apply_4(v_toBind_3018_, lean_box(0), lean_box(0), v_inst_3015_, v___f_3025_);
v___x_3027_ = lean_apply_4(v_toBind_3018_, lean_box(0), lean_box(0), v___x_3026_, v___f_3022_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___boxed(lean_object* v_m_3028_, lean_object* v_pu_3029_, lean_object* v_t_3030_, lean_object* v_inst_3031_, lean_object* v_inst_3032_, lean_object* v_inst_3033_, lean_object* v_p_3034_){
_start:
{
uint8_t v_pu_boxed_3035_; uint8_t v_t_boxed_3036_; lean_object* v_res_3037_; 
v_pu_boxed_3035_ = lean_unbox(v_pu_3029_);
v_t_boxed_3036_ = lean_unbox(v_t_3030_);
v_res_3037_ = l_Lean_Compiler_LCNF_normParam(v_m_3028_, v_pu_boxed_3035_, v_t_boxed_3036_, v_inst_3031_, v_inst_3032_, v_inst_3033_, v_p_3034_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg(uint8_t v_pu_3038_, uint8_t v_t_3039_, lean_object* v_inst_3040_, lean_object* v_inst_3041_, lean_object* v_inst_3042_, lean_object* v_ps_3043_){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3044_ = lean_box(v_pu_3038_);
v___x_3045_ = lean_box(v_t_3039_);
lean_inc_ref(v_inst_3041_);
v___x_3046_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___boxed), 7, 6);
lean_closure_set(v___x_3046_, 0, lean_box(0));
lean_closure_set(v___x_3046_, 1, v___x_3044_);
lean_closure_set(v___x_3046_, 2, v___x_3045_);
lean_closure_set(v___x_3046_, 3, v_inst_3040_);
lean_closure_set(v___x_3046_, 4, v_inst_3041_);
lean_closure_set(v___x_3046_, 5, v_inst_3042_);
v___x_3047_ = lean_unsigned_to_nat(0u);
v___x_3048_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_3041_, v___x_3046_, v___x_3047_, v_ps_3043_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg___boxed(lean_object* v_pu_3049_, lean_object* v_t_3050_, lean_object* v_inst_3051_, lean_object* v_inst_3052_, lean_object* v_inst_3053_, lean_object* v_ps_3054_){
_start:
{
uint8_t v_pu_boxed_3055_; uint8_t v_t_boxed_3056_; lean_object* v_res_3057_; 
v_pu_boxed_3055_ = lean_unbox(v_pu_3049_);
v_t_boxed_3056_ = lean_unbox(v_t_3050_);
v_res_3057_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_boxed_3055_, v_t_boxed_3056_, v_inst_3051_, v_inst_3052_, v_inst_3053_, v_ps_3054_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams(lean_object* v_m_3058_, uint8_t v_pu_3059_, uint8_t v_t_3060_, lean_object* v_inst_3061_, lean_object* v_inst_3062_, lean_object* v_inst_3063_, lean_object* v_ps_3064_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_3059_, v_t_3060_, v_inst_3061_, v_inst_3062_, v_inst_3063_, v_ps_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___boxed(lean_object* v_m_3066_, lean_object* v_pu_3067_, lean_object* v_t_3068_, lean_object* v_inst_3069_, lean_object* v_inst_3070_, lean_object* v_inst_3071_, lean_object* v_ps_3072_){
_start:
{
uint8_t v_pu_boxed_3073_; uint8_t v_t_boxed_3074_; lean_object* v_res_3075_; 
v_pu_boxed_3073_ = lean_unbox(v_pu_3067_);
v_t_boxed_3074_ = lean_unbox(v_t_3068_);
v_res_3075_ = l_Lean_Compiler_LCNF_normParams(v_m_3066_, v_pu_boxed_3073_, v_t_boxed_3074_, v_inst_3069_, v_inst_3070_, v_inst_3071_, v_ps_3072_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(uint8_t v_pu_3076_, lean_object* v_decl_3077_, lean_object* v_____do__lift_3078_, lean_object* v_inst_3079_, lean_object* v_____do__lift_3080_){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3081_ = lean_box(v_pu_3076_);
v___x_3082_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_3082_, 0, v___x_3081_);
lean_closure_set(v___x_3082_, 1, v_decl_3077_);
lean_closure_set(v___x_3082_, 2, v_____do__lift_3078_);
lean_closure_set(v___x_3082_, 3, v_____do__lift_3080_);
v___x_3083_ = lean_apply_2(v_inst_3079_, lean_box(0), v___x_3082_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(lean_object* v_pu_3084_, lean_object* v_decl_3085_, lean_object* v_____do__lift_3086_, lean_object* v_inst_3087_, lean_object* v_____do__lift_3088_){
_start:
{
uint8_t v_pu_boxed_3089_; lean_object* v_res_3090_; 
v_pu_boxed_3089_ = lean_unbox(v_pu_3084_);
v_res_3090_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(v_pu_boxed_3089_, v_decl_3085_, v_____do__lift_3086_, v_inst_3087_, v_____do__lift_3088_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(uint8_t v_pu_3091_, lean_object* v_value_3092_, uint8_t v_t_3093_, lean_object* v_toPure_3094_, lean_object* v_____do__lift_3095_){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3091_, v_____do__lift_3095_, v_value_3092_, v_t_3093_);
v___x_3097_ = lean_apply_2(v_toPure_3094_, lean_box(0), v___x_3096_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(lean_object* v_pu_3098_, lean_object* v_value_3099_, lean_object* v_t_3100_, lean_object* v_toPure_3101_, lean_object* v_____do__lift_3102_){
_start:
{
uint8_t v_pu_boxed_3103_; uint8_t v_t_boxed_3104_; lean_object* v_res_3105_; 
v_pu_boxed_3103_ = lean_unbox(v_pu_3098_);
v_t_boxed_3104_ = lean_unbox(v_t_3100_);
v_res_3105_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(v_pu_boxed_3103_, v_value_3099_, v_t_boxed_3104_, v_toPure_3101_, v_____do__lift_3102_);
lean_dec_ref(v_____do__lift_3102_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(uint8_t v_pu_3106_, lean_object* v_decl_3107_, lean_object* v_inst_3108_, lean_object* v_value_3109_, uint8_t v_t_3110_, lean_object* v_toPure_3111_, lean_object* v_toBind_3112_, lean_object* v_inst_3113_, lean_object* v_____do__lift_3114_){
_start:
{
lean_object* v___x_3115_; lean_object* v___f_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___f_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3115_ = lean_box(v_pu_3106_);
v___f_3116_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3116_, 0, v___x_3115_);
lean_closure_set(v___f_3116_, 1, v_decl_3107_);
lean_closure_set(v___f_3116_, 2, v_____do__lift_3114_);
lean_closure_set(v___f_3116_, 3, v_inst_3108_);
v___x_3117_ = lean_box(v_pu_3106_);
v___x_3118_ = lean_box(v_t_3110_);
v___f_3119_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3119_, 0, v___x_3117_);
lean_closure_set(v___f_3119_, 1, v_value_3109_);
lean_closure_set(v___f_3119_, 2, v___x_3118_);
lean_closure_set(v___f_3119_, 3, v_toPure_3111_);
lean_inc(v_toBind_3112_);
v___x_3120_ = lean_apply_4(v_toBind_3112_, lean_box(0), lean_box(0), v_inst_3113_, v___f_3119_);
v___x_3121_ = lean_apply_4(v_toBind_3112_, lean_box(0), lean_box(0), v___x_3120_, v___f_3116_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(lean_object* v_pu_3122_, lean_object* v_decl_3123_, lean_object* v_inst_3124_, lean_object* v_value_3125_, lean_object* v_t_3126_, lean_object* v_toPure_3127_, lean_object* v_toBind_3128_, lean_object* v_inst_3129_, lean_object* v_____do__lift_3130_){
_start:
{
uint8_t v_pu_boxed_3131_; uint8_t v_t_boxed_3132_; lean_object* v_res_3133_; 
v_pu_boxed_3131_ = lean_unbox(v_pu_3122_);
v_t_boxed_3132_ = lean_unbox(v_t_3126_);
v_res_3133_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(v_pu_boxed_3131_, v_decl_3123_, v_inst_3124_, v_value_3125_, v_t_boxed_3132_, v_toPure_3127_, v_toBind_3128_, v_inst_3129_, v_____do__lift_3130_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg(uint8_t v_pu_3134_, uint8_t v_t_3135_, lean_object* v_inst_3136_, lean_object* v_inst_3137_, lean_object* v_inst_3138_, lean_object* v_decl_3139_){
_start:
{
lean_object* v_toApplicative_3140_; lean_object* v_toBind_3141_; lean_object* v_type_3142_; lean_object* v_value_3143_; lean_object* v_toPure_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___f_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___f_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v_toApplicative_3140_ = lean_ctor_get(v_inst_3137_, 0);
lean_inc_ref(v_toApplicative_3140_);
v_toBind_3141_ = lean_ctor_get(v_inst_3137_, 1);
lean_inc_n(v_toBind_3141_, 3);
lean_dec_ref(v_inst_3137_);
v_type_3142_ = lean_ctor_get(v_decl_3139_, 2);
lean_inc_ref(v_type_3142_);
v_value_3143_ = lean_ctor_get(v_decl_3139_, 3);
lean_inc(v_value_3143_);
v_toPure_3144_ = lean_ctor_get(v_toApplicative_3140_, 1);
lean_inc_n(v_toPure_3144_, 2);
lean_dec_ref(v_toApplicative_3140_);
v___x_3145_ = lean_box(v_pu_3134_);
v___x_3146_ = lean_box(v_t_3135_);
lean_inc(v_inst_3138_);
v___f_3147_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_3147_, 0, v___x_3145_);
lean_closure_set(v___f_3147_, 1, v_decl_3139_);
lean_closure_set(v___f_3147_, 2, v_inst_3136_);
lean_closure_set(v___f_3147_, 3, v_value_3143_);
lean_closure_set(v___f_3147_, 4, v___x_3146_);
lean_closure_set(v___f_3147_, 5, v_toPure_3144_);
lean_closure_set(v___f_3147_, 6, v_toBind_3141_);
lean_closure_set(v___f_3147_, 7, v_inst_3138_);
v___x_3148_ = lean_box(v_pu_3134_);
v___x_3149_ = lean_box(v_t_3135_);
v___f_3150_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3150_, 0, v___x_3148_);
lean_closure_set(v___f_3150_, 1, v___x_3149_);
lean_closure_set(v___f_3150_, 2, v_type_3142_);
lean_closure_set(v___f_3150_, 3, v_toPure_3144_);
v___x_3151_ = lean_apply_4(v_toBind_3141_, lean_box(0), lean_box(0), v_inst_3138_, v___f_3150_);
v___x_3152_ = lean_apply_4(v_toBind_3141_, lean_box(0), lean_box(0), v___x_3151_, v___f_3147_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(lean_object* v_pu_3153_, lean_object* v_t_3154_, lean_object* v_inst_3155_, lean_object* v_inst_3156_, lean_object* v_inst_3157_, lean_object* v_decl_3158_){
_start:
{
uint8_t v_pu_boxed_3159_; uint8_t v_t_boxed_3160_; lean_object* v_res_3161_; 
v_pu_boxed_3159_ = lean_unbox(v_pu_3153_);
v_t_boxed_3160_ = lean_unbox(v_t_3154_);
v_res_3161_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_boxed_3159_, v_t_boxed_3160_, v_inst_3155_, v_inst_3156_, v_inst_3157_, v_decl_3158_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl(lean_object* v_m_3162_, uint8_t v_pu_3163_, uint8_t v_t_3164_, lean_object* v_inst_3165_, lean_object* v_inst_3166_, lean_object* v_inst_3167_, lean_object* v_decl_3168_){
_start:
{
lean_object* v___x_3169_; 
v___x_3169_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_3163_, v_t_3164_, v_inst_3165_, v_inst_3166_, v_inst_3167_, v_decl_3168_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___boxed(lean_object* v_m_3170_, lean_object* v_pu_3171_, lean_object* v_t_3172_, lean_object* v_inst_3173_, lean_object* v_inst_3174_, lean_object* v_inst_3175_, lean_object* v_decl_3176_){
_start:
{
uint8_t v_pu_boxed_3177_; uint8_t v_t_boxed_3178_; lean_object* v_res_3179_; 
v_pu_boxed_3177_ = lean_unbox(v_pu_3171_);
v_t_boxed_3178_ = lean_unbox(v_t_3172_);
v_res_3179_ = l_Lean_Compiler_LCNF_normLetDecl(v_m_3170_, v_pu_boxed_3177_, v_t_boxed_3178_, v_inst_3173_, v_inst_3174_, v_inst_3175_, v_decl_3176_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(uint8_t v_pu_3180_, uint8_t v_t_3181_){
_start:
{
lean_object* v___x_3182_; lean_object* v_toApplicative_3183_; lean_object* v_toFunctor_3184_; lean_object* v_toSeq_3185_; lean_object* v_toSeqLeft_3186_; lean_object* v_toSeqRight_3187_; lean_object* v___f_3188_; lean_object* v___f_3189_; lean_object* v___f_3190_; lean_object* v___f_3191_; lean_object* v___x_3192_; lean_object* v___f_3193_; lean_object* v___f_3194_; lean_object* v___f_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v_toApplicative_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3227_; 
v___x_3182_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_3183_ = lean_ctor_get(v___x_3182_, 0);
v_toFunctor_3184_ = lean_ctor_get(v_toApplicative_3183_, 0);
v_toSeq_3185_ = lean_ctor_get(v_toApplicative_3183_, 2);
v_toSeqLeft_3186_ = lean_ctor_get(v_toApplicative_3183_, 3);
v_toSeqRight_3187_ = lean_ctor_get(v_toApplicative_3183_, 4);
v___f_3188_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_3189_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_3184_, 2);
v___f_3190_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3190_, 0, v_toFunctor_3184_);
v___f_3191_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3191_, 0, v_toFunctor_3184_);
v___x_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___f_3190_);
lean_ctor_set(v___x_3192_, 1, v___f_3191_);
lean_inc(v_toSeqRight_3187_);
v___f_3193_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3193_, 0, v_toSeqRight_3187_);
lean_inc(v_toSeqLeft_3186_);
v___f_3194_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3194_, 0, v_toSeqLeft_3186_);
lean_inc(v_toSeq_3185_);
v___f_3195_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3195_, 0, v_toSeq_3185_);
v___x_3196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3192_);
lean_ctor_set(v___x_3196_, 1, v___f_3188_);
lean_ctor_set(v___x_3196_, 2, v___f_3195_);
lean_ctor_set(v___x_3196_, 3, v___f_3194_);
lean_ctor_set(v___x_3196_, 4, v___f_3193_);
v___x_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
lean_ctor_set(v___x_3197_, 1, v___f_3189_);
v___x_3198_ = l_StateRefT_x27_instMonad___redArg(v___x_3197_);
v_toApplicative_3199_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3227_ == 0)
{
lean_object* v_unused_3228_; 
v_unused_3228_ = lean_ctor_get(v___x_3198_, 1);
lean_dec(v_unused_3228_);
v___x_3201_ = v___x_3198_;
v_isShared_3202_ = v_isSharedCheck_3227_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_toApplicative_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3227_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v_toFunctor_3203_; lean_object* v_toSeq_3204_; lean_object* v_toSeqLeft_3205_; lean_object* v_toSeqRight_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3225_; 
v_toFunctor_3203_ = lean_ctor_get(v_toApplicative_3199_, 0);
v_toSeq_3204_ = lean_ctor_get(v_toApplicative_3199_, 2);
v_toSeqLeft_3205_ = lean_ctor_get(v_toApplicative_3199_, 3);
v_toSeqRight_3206_ = lean_ctor_get(v_toApplicative_3199_, 4);
v_isSharedCheck_3225_ = !lean_is_exclusive(v_toApplicative_3199_);
if (v_isSharedCheck_3225_ == 0)
{
lean_object* v_unused_3226_; 
v_unused_3226_ = lean_ctor_get(v_toApplicative_3199_, 1);
lean_dec(v_unused_3226_);
v___x_3208_ = v_toApplicative_3199_;
v_isShared_3209_ = v_isSharedCheck_3225_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_toSeqRight_3206_);
lean_inc(v_toSeqLeft_3205_);
lean_inc(v_toSeq_3204_);
lean_inc(v_toFunctor_3203_);
lean_dec(v_toApplicative_3199_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3225_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___f_3210_; lean_object* v___f_3211_; lean_object* v___f_3212_; lean_object* v___f_3213_; lean_object* v___x_3214_; lean_object* v___f_3215_; lean_object* v___f_3216_; lean_object* v___f_3217_; lean_object* v___x_3219_; 
v___f_3210_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_3211_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_3203_);
v___f_3212_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3212_, 0, v_toFunctor_3203_);
v___f_3213_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3213_, 0, v_toFunctor_3203_);
v___x_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___f_3212_);
lean_ctor_set(v___x_3214_, 1, v___f_3213_);
v___f_3215_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3215_, 0, v_toSeqRight_3206_);
v___f_3216_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3216_, 0, v_toSeqLeft_3205_);
v___f_3217_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3217_, 0, v_toSeq_3204_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 4, v___f_3215_);
lean_ctor_set(v___x_3208_, 3, v___f_3216_);
lean_ctor_set(v___x_3208_, 2, v___f_3217_);
lean_ctor_set(v___x_3208_, 1, v___f_3210_);
lean_ctor_set(v___x_3208_, 0, v___x_3214_);
v___x_3219_ = v___x_3208_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v___f_3210_);
lean_ctor_set(v_reuseFailAlloc_3224_, 2, v___f_3217_);
lean_ctor_set(v_reuseFailAlloc_3224_, 3, v___f_3216_);
lean_ctor_set(v_reuseFailAlloc_3224_, 4, v___f_3215_);
v___x_3219_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3221_; 
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 1, v___f_3211_);
lean_ctor_set(v___x_3201_, 0, v___x_3219_);
v___x_3221_ = v___x_3201_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3223_, 1, v___f_3211_);
v___x_3221_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3222_; 
v___x_3222_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_3222_, 0, lean_box(0));
lean_closure_set(v___x_3222_, 1, lean_box(0));
lean_closure_set(v___x_3222_, 2, v___x_3221_);
return v___x_3222_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(lean_object* v_pu_3229_, lean_object* v_t_3230_){
_start:
{
uint8_t v_pu_boxed_3231_; uint8_t v_t_boxed_3232_; lean_object* v_res_3233_; 
v_pu_boxed_3231_ = lean_unbox(v_pu_3229_);
v_t_boxed_3232_ = lean_unbox(v_t_3230_);
v_res_3233_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_boxed_3231_, v_t_boxed_3232_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg(uint8_t v_pu_3234_, lean_object* v_inst_3235_, lean_object* v_result_3236_, lean_object* v_x_3237_){
_start:
{
if (lean_obj_tag(v_result_3236_) == 0)
{
lean_object* v_fvarId_3238_; lean_object* v___x_3239_; 
lean_dec(v_inst_3235_);
v_fvarId_3238_ = lean_ctor_get(v_result_3236_, 0);
lean_inc(v_fvarId_3238_);
lean_dec_ref_known(v_result_3236_, 1);
v___x_3239_ = lean_apply_1(v_x_3237_, v_fvarId_3238_);
return v___x_3239_;
}
else
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
lean_dec(v_x_3237_);
v___x_3240_ = lean_box(v_pu_3234_);
v___x_3241_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3241_, 0, v___x_3240_);
v___x_3242_ = lean_apply_2(v_inst_3235_, lean_box(0), v___x_3241_);
return v___x_3242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(lean_object* v_pu_3243_, lean_object* v_inst_3244_, lean_object* v_result_3245_, lean_object* v_x_3246_){
_start:
{
uint8_t v_pu_boxed_3247_; lean_object* v_res_3248_; 
v_pu_boxed_3247_ = lean_unbox(v_pu_3243_);
v_res_3248_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(v_pu_boxed_3247_, v_inst_3244_, v_result_3245_, v_x_3246_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult(lean_object* v_m_3249_, uint8_t v_pu_3250_, lean_object* v_inst_3251_, lean_object* v_inst_3252_, lean_object* v_result_3253_, lean_object* v_x_3254_){
_start:
{
if (lean_obj_tag(v_result_3253_) == 0)
{
lean_object* v_fvarId_3255_; lean_object* v___x_3256_; 
lean_dec(v_inst_3251_);
v_fvarId_3255_ = lean_ctor_get(v_result_3253_, 0);
lean_inc(v_fvarId_3255_);
lean_dec_ref_known(v_result_3253_, 1);
v___x_3256_ = lean_apply_1(v_x_3254_, v_fvarId_3255_);
return v___x_3256_;
}
else
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
lean_dec(v_x_3254_);
v___x_3257_ = lean_box(v_pu_3250_);
v___x_3258_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3258_, 0, v___x_3257_);
v___x_3259_ = lean_apply_2(v_inst_3251_, lean_box(0), v___x_3258_);
return v___x_3259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___boxed(lean_object* v_m_3260_, lean_object* v_pu_3261_, lean_object* v_inst_3262_, lean_object* v_inst_3263_, lean_object* v_result_3264_, lean_object* v_x_3265_){
_start:
{
uint8_t v_pu_boxed_3266_; lean_object* v_res_3267_; 
v_pu_boxed_3266_ = lean_unbox(v_pu_3261_);
v_res_3267_ = l_Lean_Compiler_LCNF_withNormFVarResult(v_m_3260_, v_pu_boxed_3266_, v_inst_3262_, v_inst_3263_, v_result_3264_, v_x_3265_);
lean_dec_ref(v_inst_3263_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(uint8_t v_pu_3268_, uint8_t v_t_3269_, lean_object* v_args_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_3268_, v___y_3271_, v_args_3270_, v_t_3269_);
v___x_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(lean_object* v_pu_3275_, lean_object* v_t_3276_, lean_object* v_args_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
uint8_t v_pu_boxed_3280_; uint8_t v_t_boxed_3281_; lean_object* v_res_3282_; 
v_pu_boxed_3280_ = lean_unbox(v_pu_3275_);
v_t_boxed_3281_ = lean_unbox(v_t_3276_);
v_res_3282_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_boxed_3280_, v_t_boxed_3281_, v_args_3277_, v___y_3278_);
lean_dec_ref(v___y_3278_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(uint8_t v_pu_3283_, uint8_t v_t_3284_, lean_object* v_i_3285_, lean_object* v_as_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v___x_3290_; uint8_t v___x_3291_; 
v___x_3290_ = lean_array_get_size(v_as_3286_);
v___x_3291_ = lean_nat_dec_lt(v_i_3285_, v___x_3290_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3292_; 
lean_dec(v_i_3285_);
v___x_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3292_, 0, v_as_3286_);
return v___x_3292_;
}
else
{
lean_object* v_a_3293_; lean_object* v_type_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v_a_3293_ = lean_array_fget_borrowed(v_as_3286_, v_i_3285_);
v_type_3294_ = lean_ctor_get(v_a_3293_, 2);
lean_inc_ref(v_type_3294_);
v___x_3295_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3283_, v___y_3287_, v_t_3284_, v_type_3294_);
lean_inc(v_a_3293_);
v___x_3296_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_3283_, v_a_3293_, v___x_3295_, v___y_3288_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; size_t v___x_3298_; size_t v___x_3299_; uint8_t v___x_3300_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3296_, 1);
v___x_3298_ = lean_ptr_addr(v_a_3293_);
v___x_3299_ = lean_ptr_addr(v_a_3297_);
v___x_3300_ = lean_usize_dec_eq(v___x_3298_, v___x_3299_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3301_ = lean_unsigned_to_nat(1u);
v___x_3302_ = lean_nat_add(v_i_3285_, v___x_3301_);
v___x_3303_ = lean_array_fset(v_as_3286_, v_i_3285_, v_a_3297_);
lean_dec(v_i_3285_);
v_i_3285_ = v___x_3302_;
v_as_3286_ = v___x_3303_;
goto _start;
}
else
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
lean_dec(v_a_3297_);
v___x_3305_ = lean_unsigned_to_nat(1u);
v___x_3306_ = lean_nat_add(v_i_3285_, v___x_3305_);
lean_dec(v_i_3285_);
v_i_3285_ = v___x_3306_;
goto _start;
}
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
lean_dec_ref(v_as_3286_);
lean_dec(v_i_3285_);
v_a_3308_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3296_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3296_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(lean_object* v_pu_3316_, lean_object* v_t_3317_, lean_object* v_i_3318_, lean_object* v_as_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
uint8_t v_pu_boxed_3323_; uint8_t v_t_boxed_3324_; lean_object* v_res_3325_; 
v_pu_boxed_3323_ = lean_unbox(v_pu_3316_);
v_t_boxed_3324_ = lean_unbox(v_t_3317_);
v_res_3325_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_boxed_3323_, v_t_boxed_3324_, v_i_3318_, v_as_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(uint8_t v_pu_3326_, uint8_t v_t_3327_, lean_object* v_ps_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = lean_unsigned_to_nat(0u);
v___x_3336_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_3326_, v_t_3327_, v___x_3335_, v_ps_3328_, v___y_3329_, v___y_3331_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(lean_object* v_pu_3337_, lean_object* v_t_3338_, lean_object* v_ps_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
uint8_t v_pu_boxed_3346_; uint8_t v_t_boxed_3347_; lean_object* v_res_3348_; 
v_pu_boxed_3346_ = lean_unbox(v_pu_3337_);
v_t_boxed_3347_ = lean_unbox(v_t_3338_);
v_res_3348_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_boxed_3346_, v_t_boxed_3347_, v_ps_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec_ref(v___y_3340_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(uint8_t v_pu_3349_, uint8_t v_t_3350_, lean_object* v_decl_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v_type_3355_; lean_object* v_value_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v_type_3355_ = lean_ctor_get(v_decl_3351_, 2);
v_value_3356_ = lean_ctor_get(v_decl_3351_, 3);
lean_inc_ref(v_type_3355_);
v___x_3357_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3349_, v___y_3352_, v_t_3350_, v_type_3355_);
lean_inc(v_value_3356_);
v___x_3358_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3349_, v___y_3352_, v_value_3356_, v_t_3350_);
v___x_3359_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_3349_, v_decl_3351_, v___x_3357_, v___x_3358_, v___y_3353_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(lean_object* v_pu_3360_, lean_object* v_t_3361_, lean_object* v_decl_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
uint8_t v_pu_boxed_3366_; uint8_t v_t_boxed_3367_; lean_object* v_res_3368_; 
v_pu_boxed_3366_ = lean_unbox(v_pu_3360_);
v_t_boxed_3367_ = lean_unbox(v_t_3361_);
v_res_3368_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_boxed_3366_, v_t_boxed_3367_, v_decl_3362_, v___y_3363_, v___y_3364_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(uint8_t v_pu_3369_, uint8_t v_t_3370_, lean_object* v_i_3371_, lean_object* v_as_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v___x_3379_; uint8_t v___x_3380_; 
v___x_3379_ = lean_array_get_size(v_as_3372_);
v___x_3380_ = lean_nat_dec_lt(v_i_3371_, v___x_3379_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; 
lean_dec(v_i_3371_);
v___x_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3381_, 0, v_as_3372_);
return v___x_3381_;
}
else
{
lean_object* v_a_3382_; lean_object* v_a_3384_; 
v_a_3382_ = lean_array_fget_borrowed(v_as_3372_, v_i_3371_);
switch(lean_obj_tag(v_a_3382_))
{
case 0:
{
lean_object* v_params_3395_; lean_object* v_code_3396_; lean_object* v___x_3397_; 
v_params_3395_ = lean_ctor_get(v_a_3382_, 1);
v_code_3396_ = lean_ctor_get(v_a_3382_, 2);
lean_inc_ref(v_params_3395_);
v___x_3397_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_3369_, v_t_3370_, v_params_3395_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v___x_3399_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3398_);
lean_dec_ref_known(v___x_3397_, 1);
lean_inc_ref(v_code_3396_);
v___x_3399_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3369_, v_t_3370_, v_code_3396_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v___x_3401_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3399_, 1);
lean_inc_ref(v_a_3382_);
v___x_3401_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_3369_, v_a_3382_, v_a_3398_, v_a_3400_);
v_a_3384_ = v___x_3401_;
goto v___jp_3383_;
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec(v_a_3398_);
lean_dec_ref(v_as_3372_);
lean_dec(v_i_3371_);
v_a_3402_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3399_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3399_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec_ref(v_as_3372_);
lean_dec(v_i_3371_);
v_a_3410_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3397_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3397_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
case 1:
{
lean_object* v_code_3418_; lean_object* v___x_3419_; 
v_code_3418_ = lean_ctor_get(v_a_3382_, 1);
lean_inc_ref(v_code_3418_);
v___x_3419_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3369_, v_t_3370_, v_code_3418_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3421_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_a_3420_);
lean_dec_ref_known(v___x_3419_, 1);
lean_inc_ref(v_a_3382_);
v___x_3421_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3382_, v_a_3420_);
v_a_3384_ = v___x_3421_;
goto v___jp_3383_;
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
lean_dec_ref(v_as_3372_);
lean_dec(v_i_3371_);
v_a_3422_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3419_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3419_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
default: 
{
lean_object* v_code_3430_; lean_object* v___x_3431_; 
v_code_3430_ = lean_ctor_get(v_a_3382_, 0);
lean_inc_ref(v_code_3430_);
v___x_3431_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3369_, v_t_3370_, v_code_3430_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3433_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref_known(v___x_3431_, 1);
lean_inc_ref(v_a_3382_);
v___x_3433_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3382_, v_a_3432_);
v_a_3384_ = v___x_3433_;
goto v___jp_3383_;
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec_ref(v_as_3372_);
lean_dec(v_i_3371_);
v_a_3434_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3431_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3431_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
v___jp_3383_:
{
size_t v___x_3385_; size_t v___x_3386_; uint8_t v___x_3387_; 
v___x_3385_ = lean_ptr_addr(v_a_3382_);
v___x_3386_ = lean_ptr_addr(v_a_3384_);
v___x_3387_ = lean_usize_dec_eq(v___x_3385_, v___x_3386_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3388_ = lean_unsigned_to_nat(1u);
v___x_3389_ = lean_nat_add(v_i_3371_, v___x_3388_);
v___x_3390_ = lean_array_fset(v_as_3372_, v_i_3371_, v_a_3384_);
lean_dec(v_i_3371_);
v_i_3371_ = v___x_3389_;
v_as_3372_ = v___x_3390_;
goto _start;
}
else
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
lean_dec_ref(v_a_3384_);
v___x_3392_ = lean_unsigned_to_nat(1u);
v___x_3393_ = lean_nat_add(v_i_3371_, v___x_3392_);
lean_dec(v_i_3371_);
v_i_3371_ = v___x_3393_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t v_pu_3442_, uint8_t v_t_3443_, lean_object* v_code_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
switch(lean_obj_tag(v_code_3444_))
{
case 0:
{
lean_object* v_decl_3451_; lean_object* v_k_3452_; lean_object* v___x_3453_; 
v_decl_3451_ = lean_ctor_get(v_code_3444_, 0);
v_k_3452_ = lean_ctor_get(v_code_3444_, 1);
lean_inc_ref(v_decl_3451_);
v___x_3453_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_3442_, v_t_3443_, v_decl_3451_, v_a_3445_, v_a_3447_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3455_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
lean_inc_ref(v_k_3452_);
v___x_3455_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3442_, v_t_3443_, v_k_3452_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3483_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3458_ = v___x_3455_;
v_isShared_3459_ = v_isSharedCheck_3483_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3455_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3483_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
uint8_t v___y_3461_; size_t v___x_3477_; size_t v___x_3478_; uint8_t v___x_3479_; 
v___x_3477_ = lean_ptr_addr(v_k_3452_);
v___x_3478_ = lean_ptr_addr(v_a_3456_);
v___x_3479_ = lean_usize_dec_eq(v___x_3477_, v___x_3478_);
if (v___x_3479_ == 0)
{
v___y_3461_ = v___x_3479_;
goto v___jp_3460_;
}
else
{
size_t v___x_3480_; size_t v___x_3481_; uint8_t v___x_3482_; 
v___x_3480_ = lean_ptr_addr(v_decl_3451_);
v___x_3481_ = lean_ptr_addr(v_a_3454_);
v___x_3482_ = lean_usize_dec_eq(v___x_3480_, v___x_3481_);
v___y_3461_ = v___x_3482_;
goto v___jp_3460_;
}
v___jp_3460_:
{
if (v___y_3461_ == 0)
{
lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3471_; 
v_isSharedCheck_3471_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3471_ == 0)
{
lean_object* v_unused_3472_; lean_object* v_unused_3473_; 
v_unused_3472_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_3472_);
v_unused_3473_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3473_);
v___x_3463_ = v_code_3444_;
v_isShared_3464_ = v_isSharedCheck_3471_;
goto v_resetjp_3462_;
}
else
{
lean_dec(v_code_3444_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3471_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 1, v_a_3456_);
lean_ctor_set(v___x_3463_, 0, v_a_3454_);
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3454_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_a_3456_);
v___x_3466_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3468_; 
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v___x_3466_);
v___x_3468_ = v___x_3458_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3466_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
else
{
lean_object* v___x_3475_; 
lean_dec(v_a_3456_);
lean_dec(v_a_3454_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v_code_3444_);
v___x_3475_ = v___x_3458_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_code_3444_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
}
else
{
lean_dec(v_a_3454_);
lean_dec_ref_known(v_code_3444_, 2);
return v___x_3455_;
}
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
lean_dec_ref_known(v_code_3444_, 2);
v_a_3484_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3453_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3453_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
case 1:
{
lean_object* v_decl_3492_; lean_object* v_k_3493_; lean_object* v___x_3494_; 
v_decl_3492_ = lean_ctor_get(v_code_3444_, 0);
v_k_3493_ = lean_ctor_get(v_code_3444_, 1);
lean_inc_ref(v_decl_3492_);
v___x_3494_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3442_, v_t_3443_, v_decl_3492_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3496_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3495_);
lean_dec_ref_known(v___x_3494_, 1);
lean_inc_ref(v_k_3493_);
v___x_3496_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3442_, v_t_3443_, v_k_3493_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3524_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3499_ = v___x_3496_;
v_isShared_3500_ = v_isSharedCheck_3524_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3524_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
uint8_t v___y_3502_; size_t v___x_3518_; size_t v___x_3519_; uint8_t v___x_3520_; 
v___x_3518_ = lean_ptr_addr(v_k_3493_);
v___x_3519_ = lean_ptr_addr(v_a_3497_);
v___x_3520_ = lean_usize_dec_eq(v___x_3518_, v___x_3519_);
if (v___x_3520_ == 0)
{
v___y_3502_ = v___x_3520_;
goto v___jp_3501_;
}
else
{
size_t v___x_3521_; size_t v___x_3522_; uint8_t v___x_3523_; 
v___x_3521_ = lean_ptr_addr(v_decl_3492_);
v___x_3522_ = lean_ptr_addr(v_a_3495_);
v___x_3523_ = lean_usize_dec_eq(v___x_3521_, v___x_3522_);
v___y_3502_ = v___x_3523_;
goto v___jp_3501_;
}
v___jp_3501_:
{
if (v___y_3502_ == 0)
{
lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3512_; 
v_isSharedCheck_3512_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3512_ == 0)
{
lean_object* v_unused_3513_; lean_object* v_unused_3514_; 
v_unused_3513_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_3513_);
v_unused_3514_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3514_);
v___x_3504_ = v_code_3444_;
v_isShared_3505_ = v_isSharedCheck_3512_;
goto v_resetjp_3503_;
}
else
{
lean_dec(v_code_3444_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3512_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 1, v_a_3497_);
lean_ctor_set(v___x_3504_, 0, v_a_3495_);
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3495_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_a_3497_);
v___x_3507_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
lean_object* v___x_3509_; 
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v___x_3507_);
v___x_3509_ = v___x_3499_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3507_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
else
{
lean_object* v___x_3516_; 
lean_dec(v_a_3497_);
lean_dec(v_a_3495_);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v_code_3444_);
v___x_3516_ = v___x_3499_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_code_3444_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
}
else
{
lean_dec(v_a_3495_);
lean_dec_ref_known(v_code_3444_, 2);
return v___x_3496_;
}
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
lean_dec_ref_known(v_code_3444_, 2);
v_a_3525_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3494_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3494_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
case 2:
{
lean_object* v_decl_3533_; lean_object* v_k_3534_; lean_object* v___x_3535_; 
v_decl_3533_ = lean_ctor_get(v_code_3444_, 0);
v_k_3534_ = lean_ctor_get(v_code_3444_, 1);
lean_inc_ref(v_decl_3533_);
v___x_3535_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3442_, v_t_3443_, v_decl_3533_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v___x_3537_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3536_);
lean_dec_ref_known(v___x_3535_, 1);
lean_inc_ref(v_k_3534_);
v___x_3537_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3442_, v_t_3443_, v_k_3534_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3565_; 
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3540_ = v___x_3537_;
v_isShared_3541_ = v_isSharedCheck_3565_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3537_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3565_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
uint8_t v___y_3543_; size_t v___x_3559_; size_t v___x_3560_; uint8_t v___x_3561_; 
v___x_3559_ = lean_ptr_addr(v_k_3534_);
v___x_3560_ = lean_ptr_addr(v_a_3538_);
v___x_3561_ = lean_usize_dec_eq(v___x_3559_, v___x_3560_);
if (v___x_3561_ == 0)
{
v___y_3543_ = v___x_3561_;
goto v___jp_3542_;
}
else
{
size_t v___x_3562_; size_t v___x_3563_; uint8_t v___x_3564_; 
v___x_3562_ = lean_ptr_addr(v_decl_3533_);
v___x_3563_ = lean_ptr_addr(v_a_3536_);
v___x_3564_ = lean_usize_dec_eq(v___x_3562_, v___x_3563_);
v___y_3543_ = v___x_3564_;
goto v___jp_3542_;
}
v___jp_3542_:
{
if (v___y_3543_ == 0)
{
lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3553_; 
v_isSharedCheck_3553_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3553_ == 0)
{
lean_object* v_unused_3554_; lean_object* v_unused_3555_; 
v_unused_3554_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_3554_);
v_unused_3555_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3555_);
v___x_3545_ = v_code_3444_;
v_isShared_3546_ = v_isSharedCheck_3553_;
goto v_resetjp_3544_;
}
else
{
lean_dec(v_code_3444_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3553_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 1, v_a_3538_);
lean_ctor_set(v___x_3545_, 0, v_a_3536_);
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3536_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_a_3538_);
v___x_3548_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
lean_object* v___x_3550_; 
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 0, v___x_3548_);
v___x_3550_ = v___x_3540_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3548_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
else
{
lean_object* v___x_3557_; 
lean_dec(v_a_3538_);
lean_dec(v_a_3536_);
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 0, v_code_3444_);
v___x_3557_ = v___x_3540_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_code_3444_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
}
}
else
{
lean_dec(v_a_3536_);
lean_dec_ref_known(v_code_3444_, 2);
return v___x_3537_;
}
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
lean_dec_ref_known(v_code_3444_, 2);
v_a_3566_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3535_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3535_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3574_; lean_object* v_args_3575_; lean_object* v___x_3576_; 
v_fvarId_3574_ = lean_ctor_get(v_code_3444_, 0);
v_args_3575_ = lean_ctor_get(v_code_3444_, 1);
lean_inc(v_fvarId_3574_);
v___x_3576_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3445_, v_fvarId_3574_, v_t_3443_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_fvarId_3577_; lean_object* v___x_3578_; 
v_fvarId_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_fvarId_3577_);
lean_dec_ref_known(v___x_3576_, 1);
lean_inc_ref(v_args_3575_);
v___x_3578_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_3442_, v_t_3443_, v_args_3575_, v_a_3445_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3604_; 
v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3581_ = v___x_3578_;
v_isShared_3582_ = v_isSharedCheck_3604_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3578_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3604_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
uint8_t v___y_3584_; uint8_t v___x_3600_; 
v___x_3600_ = l_Lean_instBEqFVarId_beq(v_fvarId_3574_, v_fvarId_3577_);
if (v___x_3600_ == 0)
{
v___y_3584_ = v___x_3600_;
goto v___jp_3583_;
}
else
{
size_t v___x_3601_; size_t v___x_3602_; uint8_t v___x_3603_; 
v___x_3601_ = lean_ptr_addr(v_args_3575_);
v___x_3602_ = lean_ptr_addr(v_a_3579_);
v___x_3603_ = lean_usize_dec_eq(v___x_3601_, v___x_3602_);
v___y_3584_ = v___x_3603_;
goto v___jp_3583_;
}
v___jp_3583_:
{
if (v___y_3584_ == 0)
{
lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3594_; 
v_isSharedCheck_3594_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3594_ == 0)
{
lean_object* v_unused_3595_; lean_object* v_unused_3596_; 
v_unused_3595_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_3595_);
v_unused_3596_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3596_);
v___x_3586_ = v_code_3444_;
v_isShared_3587_ = v_isSharedCheck_3594_;
goto v_resetjp_3585_;
}
else
{
lean_dec(v_code_3444_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3594_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 1, v_a_3579_);
lean_ctor_set(v___x_3586_, 0, v_fvarId_3577_);
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_fvarId_3577_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v_a_3579_);
v___x_3589_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3591_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 0, v___x_3589_);
v___x_3591_ = v___x_3581_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3589_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
else
{
lean_object* v___x_3598_; 
lean_dec(v_a_3579_);
lean_dec(v_fvarId_3577_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 0, v_code_3444_);
v___x_3598_ = v___x_3581_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_code_3444_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
}
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
lean_dec(v_fvarId_3577_);
lean_dec_ref_known(v_code_3444_, 2);
v_a_3605_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3607_ = v___x_3578_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3578_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3605_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
else
{
lean_object* v___x_3613_; 
lean_dec_ref_known(v_code_3444_, 2);
v___x_3613_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3442_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_3613_;
}
}
case 4:
{
lean_object* v_cases_3614_; lean_object* v_typeName_3615_; lean_object* v_resultType_3616_; lean_object* v_discr_3617_; lean_object* v_alts_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3665_; 
v_cases_3614_ = lean_ctor_get(v_code_3444_, 0);
lean_inc_ref(v_cases_3614_);
v_typeName_3615_ = lean_ctor_get(v_cases_3614_, 0);
v_resultType_3616_ = lean_ctor_get(v_cases_3614_, 1);
v_discr_3617_ = lean_ctor_get(v_cases_3614_, 2);
v_alts_3618_ = lean_ctor_get(v_cases_3614_, 3);
v_isSharedCheck_3665_ = !lean_is_exclusive(v_cases_3614_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3620_ = v_cases_3614_;
v_isShared_3621_ = v_isSharedCheck_3665_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_alts_3618_);
lean_inc(v_discr_3617_);
lean_inc(v_resultType_3616_);
lean_inc(v_typeName_3615_);
lean_dec(v_cases_3614_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3665_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; 
lean_inc_ref(v_resultType_3616_);
v___x_3622_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3442_, v_a_3445_, v_t_3443_, v_resultType_3616_);
lean_inc(v_discr_3617_);
v___x_3623_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3445_, v_discr_3617_, v_t_3443_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_fvarId_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3663_; 
v_fvarId_3624_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3626_ = v___x_3623_;
v_isShared_3627_ = v_isSharedCheck_3663_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_fvarId_3624_);
lean_dec(v___x_3623_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3663_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3628_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3618_);
v___x_3629_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_3442_, v_t_3443_, v___x_3628_, v_alts_3618_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3654_; 
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3632_ = v___x_3629_;
v_isShared_3633_ = v_isSharedCheck_3654_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3629_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3654_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
uint8_t v___y_3645_; size_t v___x_3648_; size_t v___x_3649_; uint8_t v___x_3650_; 
v___x_3648_ = lean_ptr_addr(v_alts_3618_);
lean_dec_ref(v_alts_3618_);
v___x_3649_ = lean_ptr_addr(v_a_3630_);
v___x_3650_ = lean_usize_dec_eq(v___x_3648_, v___x_3649_);
if (v___x_3650_ == 0)
{
lean_dec_ref(v_resultType_3616_);
v___y_3645_ = v___x_3650_;
goto v___jp_3644_;
}
else
{
size_t v___x_3651_; size_t v___x_3652_; uint8_t v___x_3653_; 
v___x_3651_ = lean_ptr_addr(v_resultType_3616_);
lean_dec_ref(v_resultType_3616_);
v___x_3652_ = lean_ptr_addr(v___x_3622_);
v___x_3653_ = lean_usize_dec_eq(v___x_3651_, v___x_3652_);
v___y_3645_ = v___x_3653_;
goto v___jp_3644_;
}
v___jp_3634_:
{
lean_object* v___x_3636_; 
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 3, v_a_3630_);
lean_ctor_set(v___x_3620_, 2, v_fvarId_3624_);
lean_ctor_set(v___x_3620_, 1, v___x_3622_);
v___x_3636_ = v___x_3620_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_typeName_3615_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v___x_3622_);
lean_ctor_set(v_reuseFailAlloc_3643_, 2, v_fvarId_3624_);
lean_ctor_set(v_reuseFailAlloc_3643_, 3, v_a_3630_);
v___x_3636_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
lean_object* v___x_3638_; 
if (v_isShared_3627_ == 0)
{
lean_ctor_set_tag(v___x_3626_, 4);
lean_ctor_set(v___x_3626_, 0, v___x_3636_);
v___x_3638_ = v___x_3626_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3636_);
v___x_3638_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3640_; 
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 0, v___x_3638_);
v___x_3640_ = v___x_3632_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3638_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
v___jp_3644_:
{
if (v___y_3645_ == 0)
{
lean_dec(v_discr_3617_);
lean_dec_ref_known(v_code_3444_, 1);
goto v___jp_3634_;
}
else
{
uint8_t v___x_3646_; 
v___x_3646_ = l_Lean_instBEqFVarId_beq(v_discr_3617_, v_fvarId_3624_);
lean_dec(v_discr_3617_);
if (v___x_3646_ == 0)
{
lean_dec_ref_known(v_code_3444_, 1);
goto v___jp_3634_;
}
else
{
lean_object* v___x_3647_; 
lean_del_object(v___x_3632_);
lean_dec(v_a_3630_);
lean_del_object(v___x_3626_);
lean_dec(v_fvarId_3624_);
lean_dec_ref(v___x_3622_);
lean_del_object(v___x_3620_);
lean_dec(v_typeName_3615_);
v___x_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3647_, 0, v_code_3444_);
return v___x_3647_;
}
}
}
}
}
else
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
lean_del_object(v___x_3626_);
lean_dec(v_fvarId_3624_);
lean_dec_ref(v___x_3622_);
lean_del_object(v___x_3620_);
lean_dec_ref(v_alts_3618_);
lean_dec(v_discr_3617_);
lean_dec_ref(v_resultType_3616_);
lean_dec(v_typeName_3615_);
lean_dec_ref_known(v_code_3444_, 1);
v_a_3655_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3629_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3629_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
}
else
{
lean_object* v___x_3664_; 
lean_dec_ref(v___x_3622_);
lean_del_object(v___x_3620_);
lean_dec_ref(v_alts_3618_);
lean_dec(v_discr_3617_);
lean_dec_ref(v_resultType_3616_);
lean_dec(v_typeName_3615_);
lean_dec_ref_known(v_code_3444_, 1);
v___x_3664_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3442_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_3664_;
}
}
}
case 5:
{
lean_object* v_fvarId_3666_; lean_object* v___x_3667_; 
v_fvarId_3666_ = lean_ctor_get(v_code_3444_, 0);
lean_inc(v_fvarId_3666_);
v___x_3667_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3445_, v_fvarId_3666_, v_t_3443_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_fvarId_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3687_; 
v_fvarId_3668_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3670_ = v___x_3667_;
v_isShared_3671_ = v_isSharedCheck_3687_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_fvarId_3668_);
lean_dec(v___x_3667_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3687_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
uint8_t v___x_3672_; 
v___x_3672_ = l_Lean_instBEqFVarId_beq(v_fvarId_3666_, v_fvarId_3668_);
if (v___x_3672_ == 0)
{
lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3682_; 
v_isSharedCheck_3682_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3682_ == 0)
{
lean_object* v_unused_3683_; 
v_unused_3683_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3683_);
v___x_3674_ = v_code_3444_;
v_isShared_3675_ = v_isSharedCheck_3682_;
goto v_resetjp_3673_;
}
else
{
lean_dec(v_code_3444_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3682_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 0, v_fvarId_3668_);
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_fvarId_3668_);
v___x_3677_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
lean_object* v___x_3679_; 
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v___x_3677_);
v___x_3679_ = v___x_3670_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3677_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
else
{
lean_object* v___x_3685_; 
lean_dec(v_fvarId_3668_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v_code_3444_);
v___x_3685_ = v___x_3670_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_code_3444_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
else
{
lean_object* v___x_3688_; 
lean_dec_ref_known(v_code_3444_, 1);
v___x_3688_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3442_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_3688_;
}
}
case 6:
{
lean_object* v_type_3689_; lean_object* v___x_3690_; size_t v___x_3691_; size_t v___x_3692_; uint8_t v___x_3693_; 
v_type_3689_ = lean_ctor_get(v_code_3444_, 0);
lean_inc_ref(v_type_3689_);
v___x_3690_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3442_, v_a_3445_, v_t_3443_, v_type_3689_);
v___x_3691_ = lean_ptr_addr(v_type_3689_);
v___x_3692_ = lean_ptr_addr(v___x_3690_);
v___x_3693_ = lean_usize_dec_eq(v___x_3691_, v___x_3692_);
if (v___x_3693_ == 0)
{
lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3701_; 
v_isSharedCheck_3701_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3701_ == 0)
{
lean_object* v_unused_3702_; 
v_unused_3702_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3702_);
v___x_3695_ = v_code_3444_;
v_isShared_3696_ = v_isSharedCheck_3701_;
goto v_resetjp_3694_;
}
else
{
lean_dec(v_code_3444_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3701_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 0, v___x_3690_);
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3690_);
v___x_3698_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
lean_object* v___x_3699_; 
v___x_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
return v___x_3699_;
}
}
}
else
{
lean_object* v___x_3703_; 
lean_dec_ref(v___x_3690_);
v___x_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3703_, 0, v_code_3444_);
return v___x_3703_;
}
}
case 7:
{
lean_object* v_fvarId_3704_; lean_object* v_i_3705_; lean_object* v_y_3706_; lean_object* v_k_3707_; lean_object* v___x_3708_; 
v_fvarId_3704_ = lean_ctor_get(v_code_3444_, 0);
v_i_3705_ = lean_ctor_get(v_code_3444_, 1);
v_y_3706_ = lean_ctor_get(v_code_3444_, 2);
v_k_3707_ = lean_ctor_get(v_code_3444_, 3);
lean_inc(v_fvarId_3704_);
v___x_3708_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3445_, v_fvarId_3704_, v_t_3443_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_fvarId_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v_fvarId_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_fvarId_3709_);
lean_dec_ref_known(v___x_3708_, 1);
lean_inc(v_y_3706_);
v___x_3710_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_3442_, v_a_3445_, v_y_3706_, v_t_3443_);
lean_inc_ref(v_k_3707_);
v___x_3711_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3442_, v_t_3443_, v_k_3707_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3773_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3714_ = v___x_3711_;
v_isShared_3715_ = v_isSharedCheck_3773_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3711_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3773_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
uint8_t v___y_3717_; size_t v___x_3769_; size_t v___x_3770_; uint8_t v___x_3771_; 
v___x_3769_ = lean_ptr_addr(v_fvarId_3704_);
v___x_3770_ = lean_ptr_addr(v_fvarId_3709_);
v___x_3771_ = lean_usize_dec_eq(v___x_3769_, v___x_3770_);
if (v___x_3771_ == 0)
{
v___y_3717_ = v___x_3771_;
goto v___jp_3716_;
}
else
{
uint8_t v___x_3772_; 
v___x_3772_ = lean_nat_dec_eq(v_i_3705_, v_i_3705_);
v___y_3717_ = v___x_3772_;
goto v___jp_3716_;
}
v___jp_3716_:
{
if (v___y_3717_ == 0)
{
lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3727_; 
lean_inc(v_i_3705_);
v_isSharedCheck_3727_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3727_ == 0)
{
lean_object* v_unused_3728_; lean_object* v_unused_3729_; lean_object* v_unused_3730_; lean_object* v_unused_3731_; 
v_unused_3728_ = lean_ctor_get(v_code_3444_, 3);
lean_dec(v_unused_3728_);
v_unused_3729_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_3729_);
v_unused_3730_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_3730_);
v_unused_3731_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3731_);
v___x_3719_ = v_code_3444_;
v_isShared_3720_ = v_isSharedCheck_3727_;
goto v_resetjp_3718_;
}
else
{
lean_dec(v_code_3444_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3727_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 3, v_a_3712_);
lean_ctor_set(v___x_3719_, 2, v___x_3710_);
lean_ctor_set(v___x_3719_, 0, v_fvarId_3709_);
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_fvarId_3709_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v_i_3705_);
lean_ctor_set(v_reuseFailAlloc_3726_, 2, v___x_3710_);
lean_ctor_set(v_reuseFailAlloc_3726_, 3, v_a_3712_);
v___x_3722_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
lean_object* v___x_3724_; 
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 0, v___x_3722_);
v___x_3724_ = v___x_3714_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3722_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
else
{
size_t v___x_3732_; size_t v___x_3733_; uint8_t v___x_3734_; 
v___x_3732_ = lean_ptr_addr(v_y_3706_);
v___x_3733_ = lean_ptr_addr(v___x_3710_);
v___x_3734_ = lean_usize_dec_eq(v___x_3732_, v___x_3733_);
if (v___x_3734_ == 0)
{
lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3744_; 
lean_inc(v_i_3705_);
v_isSharedCheck_3744_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3744_ == 0)
{
lean_object* v_unused_3745_; lean_object* v_unused_3746_; lean_object* v_unused_3747_; lean_object* v_unused_3748_; 
v_unused_3745_ = lean_ctor_get(v_code_3444_, 3);
lean_dec(v_unused_3745_);
v_unused_3746_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_3746_);
v_unused_3747_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_3747_);
v_unused_3748_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3748_);
v___x_3736_ = v_code_3444_;
v_isShared_3737_ = v_isSharedCheck_3744_;
goto v_resetjp_3735_;
}
else
{
lean_dec(v_code_3444_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3744_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 3, v_a_3712_);
lean_ctor_set(v___x_3736_, 2, v___x_3710_);
lean_ctor_set(v___x_3736_, 0, v_fvarId_3709_);
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_fvarId_3709_);
lean_ctor_set(v_reuseFailAlloc_3743_, 1, v_i_3705_);
lean_ctor_set(v_reuseFailAlloc_3743_, 2, v___x_3710_);
lean_ctor_set(v_reuseFailAlloc_3743_, 3, v_a_3712_);
v___x_3739_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
lean_object* v___x_3741_; 
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 0, v___x_3739_);
v___x_3741_ = v___x_3714_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3739_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
else
{
size_t v___x_3749_; size_t v___x_3750_; uint8_t v___x_3751_; 
v___x_3749_ = lean_ptr_addr(v_k_3707_);
v___x_3750_ = lean_ptr_addr(v_a_3712_);
v___x_3751_ = lean_usize_dec_eq(v___x_3749_, v___x_3750_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3761_; 
lean_inc(v_i_3705_);
v_isSharedCheck_3761_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3761_ == 0)
{
lean_object* v_unused_3762_; lean_object* v_unused_3763_; lean_object* v_unused_3764_; lean_object* v_unused_3765_; 
v_unused_3762_ = lean_ctor_get(v_code_3444_, 3);
lean_dec(v_unused_3762_);
v_unused_3763_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_3763_);
v_unused_3764_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_3764_);
v_unused_3765_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3765_);
v___x_3753_ = v_code_3444_;
v_isShared_3754_ = v_isSharedCheck_3761_;
goto v_resetjp_3752_;
}
else
{
lean_dec(v_code_3444_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3761_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 3, v_a_3712_);
lean_ctor_set(v___x_3753_, 2, v___x_3710_);
lean_ctor_set(v___x_3753_, 0, v_fvarId_3709_);
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_fvarId_3709_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v_i_3705_);
lean_ctor_set(v_reuseFailAlloc_3760_, 2, v___x_3710_);
lean_ctor_set(v_reuseFailAlloc_3760_, 3, v_a_3712_);
v___x_3756_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3758_; 
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 0, v___x_3756_);
v___x_3758_ = v___x_3714_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
else
{
lean_object* v___x_3767_; 
lean_dec(v_a_3712_);
lean_dec(v___x_3710_);
lean_dec(v_fvarId_3709_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 0, v_code_3444_);
v___x_3767_ = v___x_3714_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_code_3444_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3710_);
lean_dec(v_fvarId_3709_);
lean_dec_ref_known(v_code_3444_, 4);
return v___x_3711_;
}
}
else
{
lean_object* v___x_3774_; 
lean_dec_ref_known(v_code_3444_, 4);
v___x_3774_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3442_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_3774_;
}
}
case 8:
{
lean_object* v_fvarId_3775_; lean_object* v_i_3776_; lean_object* v_y_3777_; lean_object* v_k_3778_; lean_object* v___x_3779_; 
v_fvarId_3775_ = lean_ctor_get(v_code_3444_, 0);
v_i_3776_ = lean_ctor_get(v_code_3444_, 1);
v_y_3777_ = lean_ctor_get(v_code_3444_, 2);
v_k_3778_ = lean_ctor_get(v_code_3444_, 3);
lean_inc(v_fvarId_3775_);
v___x_3779_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3445_, v_fvarId_3775_, v_t_3443_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_fvarId_3780_; lean_object* v___x_3781_; 
v_fvarId_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_fvarId_3780_);
lean_dec_ref_known(v___x_3779_, 1);
lean_inc(v_y_3777_);
v___x_3781_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3445_, v_y_3777_, v_t_3443_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_fvarId_3782_; lean_object* v___x_3783_; 
v_fvarId_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_fvarId_3782_);
lean_dec_ref_known(v___x_3781_, 1);
lean_inc_ref(v_k_3778_);
v___x_3783_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3442_, v_t_3443_, v_k_3778_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3845_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3786_ = v___x_3783_;
v_isShared_3787_ = v_isSharedCheck_3845_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3783_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3845_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
uint8_t v___y_3789_; size_t v___x_3841_; size_t v___x_3842_; uint8_t v___x_3843_; 
v___x_3841_ = lean_ptr_addr(v_fvarId_3775_);
v___x_3842_ = lean_ptr_addr(v_fvarId_3780_);
v___x_3843_ = lean_usize_dec_eq(v___x_3841_, v___x_3842_);
if (v___x_3843_ == 0)
{
v___y_3789_ = v___x_3843_;
goto v___jp_3788_;
}
else
{
uint8_t v___x_3844_; 
v___x_3844_ = lean_nat_dec_eq(v_i_3776_, v_i_3776_);
v___y_3789_ = v___x_3844_;
goto v___jp_3788_;
}
v___jp_3788_:
{
if (v___y_3789_ == 0)
{
lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3799_; 
lean_inc(v_i_3776_);
v_isSharedCheck_3799_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3799_ == 0)
{
lean_object* v_unused_3800_; lean_object* v_unused_3801_; lean_object* v_unused_3802_; lean_object* v_unused_3803_; 
v_unused_3800_ = lean_ctor_get(v_code_3444_, 3);
lean_dec(v_unused_3800_);
v_unused_3801_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_3801_);
v_unused_3802_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_3802_);
v_unused_3803_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3803_);
v___x_3791_ = v_code_3444_;
v_isShared_3792_ = v_isSharedCheck_3799_;
goto v_resetjp_3790_;
}
else
{
lean_dec(v_code_3444_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3799_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 3, v_a_3784_);
lean_ctor_set(v___x_3791_, 2, v_fvarId_3782_);
lean_ctor_set(v___x_3791_, 0, v_fvarId_3780_);
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_fvarId_3780_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_i_3776_);
lean_ctor_set(v_reuseFailAlloc_3798_, 2, v_fvarId_3782_);
lean_ctor_set(v_reuseFailAlloc_3798_, 3, v_a_3784_);
v___x_3794_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
lean_object* v___x_3796_; 
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 0, v___x_3794_);
v___x_3796_ = v___x_3786_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3794_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
else
{
size_t v___x_3804_; size_t v___x_3805_; uint8_t v___x_3806_; 
v___x_3804_ = lean_ptr_addr(v_y_3777_);
v___x_3805_ = lean_ptr_addr(v_fvarId_3782_);
v___x_3806_ = lean_usize_dec_eq(v___x_3804_, v___x_3805_);
if (v___x_3806_ == 0)
{
lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3816_; 
lean_inc(v_i_3776_);
v_isSharedCheck_3816_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3816_ == 0)
{
lean_object* v_unused_3817_; lean_object* v_unused_3818_; lean_object* v_unused_3819_; lean_object* v_unused_3820_; 
v_unused_3817_ = lean_ctor_get(v_code_3444_, 3);
lean_dec(v_unused_3817_);
v_unused_3818_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_3818_);
v_unused_3819_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_3819_);
v_unused_3820_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3820_);
v___x_3808_ = v_code_3444_;
v_isShared_3809_ = v_isSharedCheck_3816_;
goto v_resetjp_3807_;
}
else
{
lean_dec(v_code_3444_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3816_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 3, v_a_3784_);
lean_ctor_set(v___x_3808_, 2, v_fvarId_3782_);
lean_ctor_set(v___x_3808_, 0, v_fvarId_3780_);
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_fvarId_3780_);
lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_i_3776_);
lean_ctor_set(v_reuseFailAlloc_3815_, 2, v_fvarId_3782_);
lean_ctor_set(v_reuseFailAlloc_3815_, 3, v_a_3784_);
v___x_3811_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
lean_object* v___x_3813_; 
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 0, v___x_3811_);
v___x_3813_ = v___x_3786_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3811_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
else
{
size_t v___x_3821_; size_t v___x_3822_; uint8_t v___x_3823_; 
v___x_3821_ = lean_ptr_addr(v_k_3778_);
v___x_3822_ = lean_ptr_addr(v_a_3784_);
v___x_3823_ = lean_usize_dec_eq(v___x_3821_, v___x_3822_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3833_; 
lean_inc(v_i_3776_);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3833_ == 0)
{
lean_object* v_unused_3834_; lean_object* v_unused_3835_; lean_object* v_unused_3836_; lean_object* v_unused_3837_; 
v_unused_3834_ = lean_ctor_get(v_code_3444_, 3);
lean_dec(v_unused_3834_);
v_unused_3835_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_3835_);
v_unused_3836_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_3836_);
v_unused_3837_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3837_);
v___x_3825_ = v_code_3444_;
v_isShared_3826_ = v_isSharedCheck_3833_;
goto v_resetjp_3824_;
}
else
{
lean_dec(v_code_3444_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3833_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 3, v_a_3784_);
lean_ctor_set(v___x_3825_, 2, v_fvarId_3782_);
lean_ctor_set(v___x_3825_, 0, v_fvarId_3780_);
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_fvarId_3780_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_i_3776_);
lean_ctor_set(v_reuseFailAlloc_3832_, 2, v_fvarId_3782_);
lean_ctor_set(v_reuseFailAlloc_3832_, 3, v_a_3784_);
v___x_3828_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
lean_object* v___x_3830_; 
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 0, v___x_3828_);
v___x_3830_ = v___x_3786_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
else
{
lean_object* v___x_3839_; 
lean_dec(v_a_3784_);
lean_dec(v_fvarId_3782_);
lean_dec(v_fvarId_3780_);
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 0, v_code_3444_);
v___x_3839_ = v___x_3786_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_code_3444_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_3782_);
lean_dec(v_fvarId_3780_);
lean_dec_ref_known(v_code_3444_, 4);
return v___x_3783_;
}
}
else
{
lean_object* v___x_3846_; 
lean_dec(v_fvarId_3780_);
lean_dec_ref_known(v_code_3444_, 4);
v___x_3846_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3442_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_3846_;
}
}
else
{
lean_object* v___x_3847_; 
lean_dec_ref_known(v_code_3444_, 4);
v___x_3847_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3442_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_3847_;
}
}
case 9:
{
lean_object* v_fvarId_3848_; lean_object* v_i_3849_; lean_object* v_offset_3850_; lean_object* v_y_3851_; lean_object* v_ty_3852_; lean_object* v_k_3853_; lean_object* v___x_3854_; 
v_fvarId_3848_ = lean_ctor_get(v_code_3444_, 0);
v_i_3849_ = lean_ctor_get(v_code_3444_, 1);
v_offset_3850_ = lean_ctor_get(v_code_3444_, 2);
v_y_3851_ = lean_ctor_get(v_code_3444_, 3);
v_ty_3852_ = lean_ctor_get(v_code_3444_, 4);
v_k_3853_ = lean_ctor_get(v_code_3444_, 5);
lean_inc(v_fvarId_3848_);
v___x_3854_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3445_, v_fvarId_3848_, v_t_3443_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_fvarId_3855_; lean_object* v___x_3856_; 
v_fvarId_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_fvarId_3855_);
lean_dec_ref_known(v___x_3854_, 1);
lean_inc(v_y_3851_);
v___x_3856_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3445_, v_y_3851_, v_t_3443_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_fvarId_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v_fvarId_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_fvarId_3857_);
lean_dec_ref_known(v___x_3856_, 1);
lean_inc_ref(v_ty_3852_);
v___x_3858_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3442_, v_a_3445_, v_t_3443_, v_ty_3852_);
lean_inc_ref(v_k_3853_);
v___x_3859_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3442_, v_t_3443_, v_k_3853_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3963_; 
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3862_ = v___x_3859_;
v_isShared_3863_ = v_isSharedCheck_3963_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3859_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3963_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
uint8_t v___y_3865_; size_t v___x_3959_; size_t v___x_3960_; uint8_t v___x_3961_; 
v___x_3959_ = lean_ptr_addr(v_fvarId_3848_);
v___x_3960_ = lean_ptr_addr(v_fvarId_3855_);
v___x_3961_ = lean_usize_dec_eq(v___x_3959_, v___x_3960_);
if (v___x_3961_ == 0)
{
v___y_3865_ = v___x_3961_;
goto v___jp_3864_;
}
else
{
uint8_t v___x_3962_; 
v___x_3962_ = lean_nat_dec_eq(v_i_3849_, v_i_3849_);
v___y_3865_ = v___x_3962_;
goto v___jp_3864_;
}
v___jp_3864_:
{
if (v___y_3865_ == 0)
{
lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3875_; 
lean_inc(v_offset_3850_);
lean_inc(v_i_3849_);
v_isSharedCheck_3875_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3875_ == 0)
{
lean_object* v_unused_3876_; lean_object* v_unused_3877_; lean_object* v_unused_3878_; lean_object* v_unused_3879_; lean_object* v_unused_3880_; lean_object* v_unused_3881_; 
v_unused_3876_ = lean_ctor_get(v_code_3444_, 5);
lean_dec(v_unused_3876_);
v_unused_3877_ = lean_ctor_get(v_code_3444_, 4);
lean_dec(v_unused_3877_);
v_unused_3878_ = lean_ctor_get(v_code_3444_, 3);
lean_dec(v_unused_3878_);
v_unused_3879_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_3879_);
v_unused_3880_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_3880_);
v_unused_3881_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3881_);
v___x_3867_ = v_code_3444_;
v_isShared_3868_ = v_isSharedCheck_3875_;
goto v_resetjp_3866_;
}
else
{
lean_dec(v_code_3444_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3875_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
lean_ctor_set(v___x_3867_, 5, v_a_3860_);
lean_ctor_set(v___x_3867_, 4, v___x_3858_);
lean_ctor_set(v___x_3867_, 3, v_fvarId_3857_);
lean_ctor_set(v___x_3867_, 0, v_fvarId_3855_);
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_fvarId_3855_);
lean_ctor_set(v_reuseFailAlloc_3874_, 1, v_i_3849_);
lean_ctor_set(v_reuseFailAlloc_3874_, 2, v_offset_3850_);
lean_ctor_set(v_reuseFailAlloc_3874_, 3, v_fvarId_3857_);
lean_ctor_set(v_reuseFailAlloc_3874_, 4, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3874_, 5, v_a_3860_);
v___x_3870_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
lean_object* v___x_3872_; 
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 0, v___x_3870_);
v___x_3872_ = v___x_3862_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3870_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
else
{
uint8_t v___x_3882_; 
v___x_3882_ = lean_nat_dec_eq(v_offset_3850_, v_offset_3850_);
if (v___x_3882_ == 0)
{
lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3892_; 
lean_inc(v_offset_3850_);
lean_inc(v_i_3849_);
v_isSharedCheck_3892_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3892_ == 0)
{
lean_object* v_unused_3893_; lean_object* v_unused_3894_; lean_object* v_unused_3895_; lean_object* v_unused_3896_; lean_object* v_unused_3897_; lean_object* v_unused_3898_; 
v_unused_3893_ = lean_ctor_get(v_code_3444_, 5);
lean_dec(v_unused_3893_);
v_unused_3894_ = lean_ctor_get(v_code_3444_, 4);
lean_dec(v_unused_3894_);
v_unused_3895_ = lean_ctor_get(v_code_3444_, 3);
lean_dec(v_unused_3895_);
v_unused_3896_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_3896_);
v_unused_3897_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_3897_);
v_unused_3898_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3898_);
v___x_3884_ = v_code_3444_;
v_isShared_3885_ = v_isSharedCheck_3892_;
goto v_resetjp_3883_;
}
else
{
lean_dec(v_code_3444_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3892_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 5, v_a_3860_);
lean_ctor_set(v___x_3884_, 4, v___x_3858_);
lean_ctor_set(v___x_3884_, 3, v_fvarId_3857_);
lean_ctor_set(v___x_3884_, 0, v_fvarId_3855_);
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_fvarId_3855_);
lean_ctor_set(v_reuseFailAlloc_3891_, 1, v_i_3849_);
lean_ctor_set(v_reuseFailAlloc_3891_, 2, v_offset_3850_);
lean_ctor_set(v_reuseFailAlloc_3891_, 3, v_fvarId_3857_);
lean_ctor_set(v_reuseFailAlloc_3891_, 4, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3891_, 5, v_a_3860_);
v___x_3887_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
lean_object* v___x_3889_; 
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 0, v___x_3887_);
v___x_3889_ = v___x_3862_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3887_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
else
{
size_t v___x_3899_; size_t v___x_3900_; uint8_t v___x_3901_; 
v___x_3899_ = lean_ptr_addr(v_y_3851_);
v___x_3900_ = lean_ptr_addr(v_fvarId_3857_);
v___x_3901_ = lean_usize_dec_eq(v___x_3899_, v___x_3900_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3911_; 
lean_inc(v_offset_3850_);
lean_inc(v_i_3849_);
v_isSharedCheck_3911_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3911_ == 0)
{
lean_object* v_unused_3912_; lean_object* v_unused_3913_; lean_object* v_unused_3914_; lean_object* v_unused_3915_; lean_object* v_unused_3916_; lean_object* v_unused_3917_; 
v_unused_3912_ = lean_ctor_get(v_code_3444_, 5);
lean_dec(v_unused_3912_);
v_unused_3913_ = lean_ctor_get(v_code_3444_, 4);
lean_dec(v_unused_3913_);
v_unused_3914_ = lean_ctor_get(v_code_3444_, 3);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_3916_);
v_unused_3917_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3917_);
v___x_3903_ = v_code_3444_;
v_isShared_3904_ = v_isSharedCheck_3911_;
goto v_resetjp_3902_;
}
else
{
lean_dec(v_code_3444_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3911_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 5, v_a_3860_);
lean_ctor_set(v___x_3903_, 4, v___x_3858_);
lean_ctor_set(v___x_3903_, 3, v_fvarId_3857_);
lean_ctor_set(v___x_3903_, 0, v_fvarId_3855_);
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_fvarId_3855_);
lean_ctor_set(v_reuseFailAlloc_3910_, 1, v_i_3849_);
lean_ctor_set(v_reuseFailAlloc_3910_, 2, v_offset_3850_);
lean_ctor_set(v_reuseFailAlloc_3910_, 3, v_fvarId_3857_);
lean_ctor_set(v_reuseFailAlloc_3910_, 4, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3910_, 5, v_a_3860_);
v___x_3906_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
lean_object* v___x_3908_; 
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 0, v___x_3906_);
v___x_3908_ = v___x_3862_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3906_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
else
{
size_t v___x_3918_; size_t v___x_3919_; uint8_t v___x_3920_; 
v___x_3918_ = lean_ptr_addr(v_ty_3852_);
v___x_3919_ = lean_ptr_addr(v___x_3858_);
v___x_3920_ = lean_usize_dec_eq(v___x_3918_, v___x_3919_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3930_; 
lean_inc(v_offset_3850_);
lean_inc(v_i_3849_);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3930_ == 0)
{
lean_object* v_unused_3931_; lean_object* v_unused_3932_; lean_object* v_unused_3933_; lean_object* v_unused_3934_; lean_object* v_unused_3935_; lean_object* v_unused_3936_; 
v_unused_3931_ = lean_ctor_get(v_code_3444_, 5);
lean_dec(v_unused_3931_);
v_unused_3932_ = lean_ctor_get(v_code_3444_, 4);
lean_dec(v_unused_3932_);
v_unused_3933_ = lean_ctor_get(v_code_3444_, 3);
lean_dec(v_unused_3933_);
v_unused_3934_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_3934_);
v_unused_3935_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_3935_);
v_unused_3936_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3936_);
v___x_3922_ = v_code_3444_;
v_isShared_3923_ = v_isSharedCheck_3930_;
goto v_resetjp_3921_;
}
else
{
lean_dec(v_code_3444_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3930_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
lean_ctor_set(v___x_3922_, 5, v_a_3860_);
lean_ctor_set(v___x_3922_, 4, v___x_3858_);
lean_ctor_set(v___x_3922_, 3, v_fvarId_3857_);
lean_ctor_set(v___x_3922_, 0, v_fvarId_3855_);
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_fvarId_3855_);
lean_ctor_set(v_reuseFailAlloc_3929_, 1, v_i_3849_);
lean_ctor_set(v_reuseFailAlloc_3929_, 2, v_offset_3850_);
lean_ctor_set(v_reuseFailAlloc_3929_, 3, v_fvarId_3857_);
lean_ctor_set(v_reuseFailAlloc_3929_, 4, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3929_, 5, v_a_3860_);
v___x_3925_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
lean_object* v___x_3927_; 
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 0, v___x_3925_);
v___x_3927_ = v___x_3862_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3925_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
else
{
size_t v___x_3937_; size_t v___x_3938_; uint8_t v___x_3939_; 
v___x_3937_ = lean_ptr_addr(v_k_3853_);
v___x_3938_ = lean_ptr_addr(v_a_3860_);
v___x_3939_ = lean_usize_dec_eq(v___x_3937_, v___x_3938_);
if (v___x_3939_ == 0)
{
lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3949_; 
lean_inc(v_offset_3850_);
lean_inc(v_i_3849_);
v_isSharedCheck_3949_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3949_ == 0)
{
lean_object* v_unused_3950_; lean_object* v_unused_3951_; lean_object* v_unused_3952_; lean_object* v_unused_3953_; lean_object* v_unused_3954_; lean_object* v_unused_3955_; 
v_unused_3950_ = lean_ctor_get(v_code_3444_, 5);
lean_dec(v_unused_3950_);
v_unused_3951_ = lean_ctor_get(v_code_3444_, 4);
lean_dec(v_unused_3951_);
v_unused_3952_ = lean_ctor_get(v_code_3444_, 3);
lean_dec(v_unused_3952_);
v_unused_3953_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_3953_);
v_unused_3954_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_3954_);
v_unused_3955_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3955_);
v___x_3941_ = v_code_3444_;
v_isShared_3942_ = v_isSharedCheck_3949_;
goto v_resetjp_3940_;
}
else
{
lean_dec(v_code_3444_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3949_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3944_; 
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 5, v_a_3860_);
lean_ctor_set(v___x_3941_, 4, v___x_3858_);
lean_ctor_set(v___x_3941_, 3, v_fvarId_3857_);
lean_ctor_set(v___x_3941_, 0, v_fvarId_3855_);
v___x_3944_ = v___x_3941_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_fvarId_3855_);
lean_ctor_set(v_reuseFailAlloc_3948_, 1, v_i_3849_);
lean_ctor_set(v_reuseFailAlloc_3948_, 2, v_offset_3850_);
lean_ctor_set(v_reuseFailAlloc_3948_, 3, v_fvarId_3857_);
lean_ctor_set(v_reuseFailAlloc_3948_, 4, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3948_, 5, v_a_3860_);
v___x_3944_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
lean_object* v___x_3946_; 
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 0, v___x_3944_);
v___x_3946_ = v___x_3862_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3944_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
else
{
lean_object* v___x_3957_; 
lean_dec(v_a_3860_);
lean_dec_ref(v___x_3858_);
lean_dec(v_fvarId_3857_);
lean_dec(v_fvarId_3855_);
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 0, v_code_3444_);
v___x_3957_ = v___x_3862_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v_code_3444_);
v___x_3957_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
return v___x_3957_;
}
}
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3858_);
lean_dec(v_fvarId_3857_);
lean_dec(v_fvarId_3855_);
lean_dec_ref_known(v_code_3444_, 6);
return v___x_3859_;
}
}
else
{
lean_object* v___x_3964_; 
lean_dec(v_fvarId_3855_);
lean_dec_ref_known(v_code_3444_, 6);
v___x_3964_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3442_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_3964_;
}
}
else
{
lean_object* v___x_3965_; 
lean_dec_ref_known(v_code_3444_, 6);
v___x_3965_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3442_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_3965_;
}
}
case 10:
{
lean_object* v_fvarId_3966_; lean_object* v_cidx_3967_; lean_object* v_k_3968_; lean_object* v___x_3969_; 
v_fvarId_3966_ = lean_ctor_get(v_code_3444_, 0);
v_cidx_3967_ = lean_ctor_get(v_code_3444_, 1);
v_k_3968_ = lean_ctor_get(v_code_3444_, 2);
lean_inc(v_fvarId_3966_);
v___x_3969_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3445_, v_fvarId_3966_, v_t_3443_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_fvarId_3970_; lean_object* v___x_3971_; 
v_fvarId_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_fvarId_3970_);
lean_dec_ref_known(v___x_3969_, 1);
lean_inc_ref(v_k_3968_);
v___x_3971_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3442_, v_t_3443_, v_k_3968_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_4014_; 
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_3974_ = v___x_3971_;
v_isShared_3975_ = v_isSharedCheck_4014_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3971_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_4014_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
uint8_t v___y_3977_; size_t v___x_4010_; size_t v___x_4011_; uint8_t v___x_4012_; 
v___x_4010_ = lean_ptr_addr(v_fvarId_3966_);
v___x_4011_ = lean_ptr_addr(v_fvarId_3970_);
v___x_4012_ = lean_usize_dec_eq(v___x_4010_, v___x_4011_);
if (v___x_4012_ == 0)
{
v___y_3977_ = v___x_4012_;
goto v___jp_3976_;
}
else
{
uint8_t v___x_4013_; 
v___x_4013_ = lean_nat_dec_eq(v_cidx_3967_, v_cidx_3967_);
v___y_3977_ = v___x_4013_;
goto v___jp_3976_;
}
v___jp_3976_:
{
if (v___y_3977_ == 0)
{
lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3987_; 
lean_inc(v_cidx_3967_);
v_isSharedCheck_3987_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_3987_ == 0)
{
lean_object* v_unused_3988_; lean_object* v_unused_3989_; lean_object* v_unused_3990_; 
v_unused_3988_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_3988_);
v_unused_3989_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_3989_);
v_unused_3990_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_3990_);
v___x_3979_ = v_code_3444_;
v_isShared_3980_ = v_isSharedCheck_3987_;
goto v_resetjp_3978_;
}
else
{
lean_dec(v_code_3444_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3987_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 2, v_a_3972_);
lean_ctor_set(v___x_3979_, 0, v_fvarId_3970_);
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_fvarId_3970_);
lean_ctor_set(v_reuseFailAlloc_3986_, 1, v_cidx_3967_);
lean_ctor_set(v_reuseFailAlloc_3986_, 2, v_a_3972_);
v___x_3982_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
lean_object* v___x_3984_; 
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 0, v___x_3982_);
v___x_3984_ = v___x_3974_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3982_);
v___x_3984_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
return v___x_3984_;
}
}
}
}
else
{
size_t v___x_3991_; size_t v___x_3992_; uint8_t v___x_3993_; 
v___x_3991_ = lean_ptr_addr(v_k_3968_);
v___x_3992_ = lean_ptr_addr(v_a_3972_);
v___x_3993_ = lean_usize_dec_eq(v___x_3991_, v___x_3992_);
if (v___x_3993_ == 0)
{
lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4003_; 
lean_inc(v_cidx_3967_);
v_isSharedCheck_4003_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_4003_ == 0)
{
lean_object* v_unused_4004_; lean_object* v_unused_4005_; lean_object* v_unused_4006_; 
v_unused_4004_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_4004_);
v_unused_4005_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_4005_);
v_unused_4006_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_4006_);
v___x_3995_ = v_code_3444_;
v_isShared_3996_ = v_isSharedCheck_4003_;
goto v_resetjp_3994_;
}
else
{
lean_dec(v_code_3444_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4003_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 2, v_a_3972_);
lean_ctor_set(v___x_3995_, 0, v_fvarId_3970_);
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_fvarId_3970_);
lean_ctor_set(v_reuseFailAlloc_4002_, 1, v_cidx_3967_);
lean_ctor_set(v_reuseFailAlloc_4002_, 2, v_a_3972_);
v___x_3998_ = v_reuseFailAlloc_4002_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
lean_object* v___x_4000_; 
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 0, v___x_3998_);
v___x_4000_ = v___x_3974_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v___x_3998_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
}
else
{
lean_object* v___x_4008_; 
lean_dec(v_a_3972_);
lean_dec(v_fvarId_3970_);
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 0, v_code_3444_);
v___x_4008_ = v___x_3974_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_code_3444_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_3970_);
lean_dec_ref_known(v_code_3444_, 3);
return v___x_3971_;
}
}
else
{
lean_object* v___x_4015_; 
lean_dec_ref_known(v_code_3444_, 3);
v___x_4015_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3442_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_4015_;
}
}
case 11:
{
lean_object* v_fvarId_4016_; lean_object* v_n_4017_; uint8_t v_check_4018_; uint8_t v_persistent_4019_; lean_object* v_k_4020_; lean_object* v___x_4021_; 
v_fvarId_4016_ = lean_ctor_get(v_code_3444_, 0);
v_n_4017_ = lean_ctor_get(v_code_3444_, 1);
v_check_4018_ = lean_ctor_get_uint8(v_code_3444_, sizeof(void*)*3);
v_persistent_4019_ = lean_ctor_get_uint8(v_code_3444_, sizeof(void*)*3 + 1);
v_k_4020_ = lean_ctor_get(v_code_3444_, 2);
lean_inc(v_fvarId_4016_);
v___x_4021_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3445_, v_fvarId_4016_, v_t_3443_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_fvarId_4022_; lean_object* v___x_4023_; 
v_fvarId_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_fvarId_4022_);
lean_dec_ref_known(v___x_4021_, 1);
lean_inc_ref(v_k_4020_);
v___x_4023_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3442_, v_t_3443_, v_k_4020_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4066_; 
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4026_ = v___x_4023_;
v_isShared_4027_ = v_isSharedCheck_4066_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_4023_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4066_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
uint8_t v___y_4029_; size_t v___x_4062_; size_t v___x_4063_; uint8_t v___x_4064_; 
v___x_4062_ = lean_ptr_addr(v_fvarId_4016_);
v___x_4063_ = lean_ptr_addr(v_fvarId_4022_);
v___x_4064_ = lean_usize_dec_eq(v___x_4062_, v___x_4063_);
if (v___x_4064_ == 0)
{
v___y_4029_ = v___x_4064_;
goto v___jp_4028_;
}
else
{
uint8_t v___x_4065_; 
v___x_4065_ = lean_nat_dec_eq(v_n_4017_, v_n_4017_);
v___y_4029_ = v___x_4065_;
goto v___jp_4028_;
}
v___jp_4028_:
{
if (v___y_4029_ == 0)
{
lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4039_; 
lean_inc(v_n_4017_);
v_isSharedCheck_4039_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_4039_ == 0)
{
lean_object* v_unused_4040_; lean_object* v_unused_4041_; lean_object* v_unused_4042_; 
v_unused_4040_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_4040_);
v_unused_4041_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_4041_);
v_unused_4042_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_4042_);
v___x_4031_ = v_code_3444_;
v_isShared_4032_ = v_isSharedCheck_4039_;
goto v_resetjp_4030_;
}
else
{
lean_dec(v_code_3444_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4039_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 2, v_a_4024_);
lean_ctor_set(v___x_4031_, 0, v_fvarId_4022_);
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_fvarId_4022_);
lean_ctor_set(v_reuseFailAlloc_4038_, 1, v_n_4017_);
lean_ctor_set(v_reuseFailAlloc_4038_, 2, v_a_4024_);
lean_ctor_set_uint8(v_reuseFailAlloc_4038_, sizeof(void*)*3, v_check_4018_);
lean_ctor_set_uint8(v_reuseFailAlloc_4038_, sizeof(void*)*3 + 1, v_persistent_4019_);
v___x_4034_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
lean_object* v___x_4036_; 
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 0, v___x_4034_);
v___x_4036_ = v___x_4026_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v___x_4034_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
else
{
size_t v___x_4043_; size_t v___x_4044_; uint8_t v___x_4045_; 
v___x_4043_ = lean_ptr_addr(v_k_4020_);
v___x_4044_ = lean_ptr_addr(v_a_4024_);
v___x_4045_ = lean_usize_dec_eq(v___x_4043_, v___x_4044_);
if (v___x_4045_ == 0)
{
lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4055_; 
lean_inc(v_n_4017_);
v_isSharedCheck_4055_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_4055_ == 0)
{
lean_object* v_unused_4056_; lean_object* v_unused_4057_; lean_object* v_unused_4058_; 
v_unused_4056_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_4056_);
v_unused_4057_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_4057_);
v_unused_4058_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_4058_);
v___x_4047_ = v_code_3444_;
v_isShared_4048_ = v_isSharedCheck_4055_;
goto v_resetjp_4046_;
}
else
{
lean_dec(v_code_3444_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4055_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 2, v_a_4024_);
lean_ctor_set(v___x_4047_, 0, v_fvarId_4022_);
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_fvarId_4022_);
lean_ctor_set(v_reuseFailAlloc_4054_, 1, v_n_4017_);
lean_ctor_set(v_reuseFailAlloc_4054_, 2, v_a_4024_);
lean_ctor_set_uint8(v_reuseFailAlloc_4054_, sizeof(void*)*3, v_check_4018_);
lean_ctor_set_uint8(v_reuseFailAlloc_4054_, sizeof(void*)*3 + 1, v_persistent_4019_);
v___x_4050_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
lean_object* v___x_4052_; 
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 0, v___x_4050_);
v___x_4052_ = v___x_4026_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_4050_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
else
{
lean_object* v___x_4060_; 
lean_dec(v_a_4024_);
lean_dec(v_fvarId_4022_);
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 0, v_code_3444_);
v___x_4060_ = v___x_4026_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_code_3444_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4022_);
lean_dec_ref_known(v_code_3444_, 3);
return v___x_4023_;
}
}
else
{
lean_object* v___x_4067_; 
lean_dec_ref_known(v_code_3444_, 3);
v___x_4067_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3442_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_4067_;
}
}
case 12:
{
lean_object* v_fvarId_4068_; lean_object* v_n_4069_; uint8_t v_check_4070_; uint8_t v_persistent_4071_; lean_object* v_objs_x3f_4072_; lean_object* v_k_4073_; lean_object* v___x_4074_; 
v_fvarId_4068_ = lean_ctor_get(v_code_3444_, 0);
v_n_4069_ = lean_ctor_get(v_code_3444_, 1);
v_check_4070_ = lean_ctor_get_uint8(v_code_3444_, sizeof(void*)*4);
v_persistent_4071_ = lean_ctor_get_uint8(v_code_3444_, sizeof(void*)*4 + 1);
v_objs_x3f_4072_ = lean_ctor_get(v_code_3444_, 2);
v_k_4073_ = lean_ctor_get(v_code_3444_, 3);
lean_inc(v_fvarId_4068_);
v___x_4074_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3445_, v_fvarId_4068_, v_t_3443_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_fvarId_4075_; lean_object* v___x_4076_; 
v_fvarId_4075_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_fvarId_4075_);
lean_dec_ref_known(v___x_4074_, 1);
lean_inc_ref(v_k_4073_);
v___x_4076_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3442_, v_t_3443_, v_k_4073_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4137_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4079_ = v___x_4076_;
v_isShared_4080_ = v_isSharedCheck_4137_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_a_4077_);
lean_dec(v___x_4076_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4137_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
uint8_t v___y_4082_; size_t v___x_4133_; size_t v___x_4134_; uint8_t v___x_4135_; 
v___x_4133_ = lean_ptr_addr(v_fvarId_4068_);
v___x_4134_ = lean_ptr_addr(v_fvarId_4075_);
v___x_4135_ = lean_usize_dec_eq(v___x_4133_, v___x_4134_);
if (v___x_4135_ == 0)
{
v___y_4082_ = v___x_4135_;
goto v___jp_4081_;
}
else
{
uint8_t v___x_4136_; 
v___x_4136_ = lean_nat_dec_eq(v_n_4069_, v_n_4069_);
v___y_4082_ = v___x_4136_;
goto v___jp_4081_;
}
v___jp_4081_:
{
if (v___y_4082_ == 0)
{
lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4092_; 
lean_inc(v_objs_x3f_4072_);
lean_inc(v_n_4069_);
v_isSharedCheck_4092_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_4092_ == 0)
{
lean_object* v_unused_4093_; lean_object* v_unused_4094_; lean_object* v_unused_4095_; lean_object* v_unused_4096_; 
v_unused_4093_ = lean_ctor_get(v_code_3444_, 3);
lean_dec(v_unused_4093_);
v_unused_4094_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_4094_);
v_unused_4095_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_4095_);
v_unused_4096_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_4096_);
v___x_4084_ = v_code_3444_;
v_isShared_4085_ = v_isSharedCheck_4092_;
goto v_resetjp_4083_;
}
else
{
lean_dec(v_code_3444_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4092_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 3, v_a_4077_);
lean_ctor_set(v___x_4084_, 0, v_fvarId_4075_);
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_fvarId_4075_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v_n_4069_);
lean_ctor_set(v_reuseFailAlloc_4091_, 2, v_objs_x3f_4072_);
lean_ctor_set(v_reuseFailAlloc_4091_, 3, v_a_4077_);
lean_ctor_set_uint8(v_reuseFailAlloc_4091_, sizeof(void*)*4, v_check_4070_);
lean_ctor_set_uint8(v_reuseFailAlloc_4091_, sizeof(void*)*4 + 1, v_persistent_4071_);
v___x_4087_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
lean_object* v___x_4089_; 
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 0, v___x_4087_);
v___x_4089_ = v___x_4079_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4087_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
else
{
size_t v___x_4097_; uint8_t v___x_4098_; 
v___x_4097_ = lean_ptr_addr(v_objs_x3f_4072_);
v___x_4098_ = lean_usize_dec_eq(v___x_4097_, v___x_4097_);
if (v___x_4098_ == 0)
{
lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4108_; 
lean_inc(v_objs_x3f_4072_);
lean_inc(v_n_4069_);
v_isSharedCheck_4108_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_4108_ == 0)
{
lean_object* v_unused_4109_; lean_object* v_unused_4110_; lean_object* v_unused_4111_; lean_object* v_unused_4112_; 
v_unused_4109_ = lean_ctor_get(v_code_3444_, 3);
lean_dec(v_unused_4109_);
v_unused_4110_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_4110_);
v_unused_4111_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_4111_);
v_unused_4112_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_4112_);
v___x_4100_ = v_code_3444_;
v_isShared_4101_ = v_isSharedCheck_4108_;
goto v_resetjp_4099_;
}
else
{
lean_dec(v_code_3444_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4108_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 3, v_a_4077_);
lean_ctor_set(v___x_4100_, 0, v_fvarId_4075_);
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_fvarId_4075_);
lean_ctor_set(v_reuseFailAlloc_4107_, 1, v_n_4069_);
lean_ctor_set(v_reuseFailAlloc_4107_, 2, v_objs_x3f_4072_);
lean_ctor_set(v_reuseFailAlloc_4107_, 3, v_a_4077_);
lean_ctor_set_uint8(v_reuseFailAlloc_4107_, sizeof(void*)*4, v_check_4070_);
lean_ctor_set_uint8(v_reuseFailAlloc_4107_, sizeof(void*)*4 + 1, v_persistent_4071_);
v___x_4103_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
lean_object* v___x_4105_; 
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 0, v___x_4103_);
v___x_4105_ = v___x_4079_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___x_4103_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
else
{
size_t v___x_4113_; size_t v___x_4114_; uint8_t v___x_4115_; 
v___x_4113_ = lean_ptr_addr(v_k_4073_);
v___x_4114_ = lean_ptr_addr(v_a_4077_);
v___x_4115_ = lean_usize_dec_eq(v___x_4113_, v___x_4114_);
if (v___x_4115_ == 0)
{
lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4125_; 
lean_inc(v_objs_x3f_4072_);
lean_inc(v_n_4069_);
v_isSharedCheck_4125_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_4125_ == 0)
{
lean_object* v_unused_4126_; lean_object* v_unused_4127_; lean_object* v_unused_4128_; lean_object* v_unused_4129_; 
v_unused_4126_ = lean_ctor_get(v_code_3444_, 3);
lean_dec(v_unused_4126_);
v_unused_4127_ = lean_ctor_get(v_code_3444_, 2);
lean_dec(v_unused_4127_);
v_unused_4128_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_4128_);
v_unused_4129_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_4129_);
v___x_4117_ = v_code_3444_;
v_isShared_4118_ = v_isSharedCheck_4125_;
goto v_resetjp_4116_;
}
else
{
lean_dec(v_code_3444_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4125_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
lean_ctor_set(v___x_4117_, 3, v_a_4077_);
lean_ctor_set(v___x_4117_, 0, v_fvarId_4075_);
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_fvarId_4075_);
lean_ctor_set(v_reuseFailAlloc_4124_, 1, v_n_4069_);
lean_ctor_set(v_reuseFailAlloc_4124_, 2, v_objs_x3f_4072_);
lean_ctor_set(v_reuseFailAlloc_4124_, 3, v_a_4077_);
lean_ctor_set_uint8(v_reuseFailAlloc_4124_, sizeof(void*)*4, v_check_4070_);
lean_ctor_set_uint8(v_reuseFailAlloc_4124_, sizeof(void*)*4 + 1, v_persistent_4071_);
v___x_4120_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
lean_object* v___x_4122_; 
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 0, v___x_4120_);
v___x_4122_ = v___x_4079_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4120_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
else
{
lean_object* v___x_4131_; 
lean_dec(v_a_4077_);
lean_dec(v_fvarId_4075_);
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 0, v_code_3444_);
v___x_4131_ = v___x_4079_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_code_3444_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4075_);
lean_dec_ref_known(v_code_3444_, 4);
return v___x_4076_;
}
}
else
{
lean_object* v___x_4138_; 
lean_dec_ref_known(v_code_3444_, 4);
v___x_4138_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3442_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_4138_;
}
}
default: 
{
lean_object* v_fvarId_4139_; lean_object* v_k_4140_; lean_object* v___x_4141_; 
v_fvarId_4139_ = lean_ctor_get(v_code_3444_, 0);
v_k_4140_ = lean_ctor_get(v_code_3444_, 1);
lean_inc(v_fvarId_4139_);
v___x_4141_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3445_, v_fvarId_4139_, v_t_3443_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_fvarId_4142_; lean_object* v___x_4143_; 
v_fvarId_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_fvarId_4142_);
lean_dec_ref_known(v___x_4141_, 1);
lean_inc_ref(v_k_4140_);
v___x_4143_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3442_, v_t_3443_, v_k_4140_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4171_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4146_ = v___x_4143_;
v_isShared_4147_ = v_isSharedCheck_4171_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4143_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4171_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
uint8_t v___y_4149_; size_t v___x_4165_; size_t v___x_4166_; uint8_t v___x_4167_; 
v___x_4165_ = lean_ptr_addr(v_fvarId_4139_);
v___x_4166_ = lean_ptr_addr(v_fvarId_4142_);
v___x_4167_ = lean_usize_dec_eq(v___x_4165_, v___x_4166_);
if (v___x_4167_ == 0)
{
v___y_4149_ = v___x_4167_;
goto v___jp_4148_;
}
else
{
size_t v___x_4168_; size_t v___x_4169_; uint8_t v___x_4170_; 
v___x_4168_ = lean_ptr_addr(v_k_4140_);
v___x_4169_ = lean_ptr_addr(v_a_4144_);
v___x_4170_ = lean_usize_dec_eq(v___x_4168_, v___x_4169_);
v___y_4149_ = v___x_4170_;
goto v___jp_4148_;
}
v___jp_4148_:
{
if (v___y_4149_ == 0)
{
lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4159_; 
v_isSharedCheck_4159_ = !lean_is_exclusive(v_code_3444_);
if (v_isSharedCheck_4159_ == 0)
{
lean_object* v_unused_4160_; lean_object* v_unused_4161_; 
v_unused_4160_ = lean_ctor_get(v_code_3444_, 1);
lean_dec(v_unused_4160_);
v_unused_4161_ = lean_ctor_get(v_code_3444_, 0);
lean_dec(v_unused_4161_);
v___x_4151_ = v_code_3444_;
v_isShared_4152_ = v_isSharedCheck_4159_;
goto v_resetjp_4150_;
}
else
{
lean_dec(v_code_3444_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4159_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 1, v_a_4144_);
lean_ctor_set(v___x_4151_, 0, v_fvarId_4142_);
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_fvarId_4142_);
lean_ctor_set(v_reuseFailAlloc_4158_, 1, v_a_4144_);
v___x_4154_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
lean_object* v___x_4156_; 
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 0, v___x_4154_);
v___x_4156_ = v___x_4146_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v___x_4154_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
}
}
else
{
lean_object* v___x_4163_; 
lean_dec(v_a_4144_);
lean_dec(v_fvarId_4142_);
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 0, v_code_3444_);
v___x_4163_ = v___x_4146_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_code_3444_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_4142_);
lean_dec_ref_known(v_code_3444_, 2);
return v___x_4143_;
}
}
else
{
lean_object* v___x_4172_; 
lean_dec_ref_known(v_code_3444_, 2);
v___x_4172_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3442_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_4172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t v_pu_4173_, uint8_t v_t_4174_, lean_object* v_decl_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_){
_start:
{
lean_object* v_params_4182_; lean_object* v_type_4183_; lean_object* v_value_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v_params_4182_ = lean_ctor_get(v_decl_4175_, 2);
v_type_4183_ = lean_ctor_get(v_decl_4175_, 3);
v_value_4184_ = lean_ctor_get(v_decl_4175_, 4);
lean_inc_ref(v_type_4183_);
v___x_4185_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4173_, v_a_4176_, v_t_4174_, v_type_4183_);
lean_inc_ref(v_params_4182_);
v___x_4186_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4173_, v_t_4174_, v_params_4182_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; lean_object* v___x_4188_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
lean_inc(v_a_4187_);
lean_dec_ref_known(v___x_4186_, 1);
lean_inc_ref(v_value_4184_);
v___x_4188_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4173_, v_t_4174_, v_value_4184_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_);
if (lean_obj_tag(v___x_4188_) == 0)
{
lean_object* v_a_4189_; lean_object* v___x_4190_; 
v_a_4189_ = lean_ctor_get(v___x_4188_, 0);
lean_inc(v_a_4189_);
lean_dec_ref_known(v___x_4188_, 1);
v___x_4190_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_4173_, v_decl_4175_, v___x_4185_, v_a_4187_, v_a_4189_, v_a_4178_);
return v___x_4190_;
}
else
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4198_; 
lean_dec(v_a_4187_);
lean_dec_ref(v___x_4185_);
lean_dec_ref(v_decl_4175_);
v_a_4191_ = lean_ctor_get(v___x_4188_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4188_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4193_ = v___x_4188_;
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4188_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
if (v_isShared_4194_ == 0)
{
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_a_4191_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
}
}
}
}
else
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
lean_dec_ref(v___x_4185_);
lean_dec_ref(v_decl_4175_);
v_a_4199_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v___x_4186_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v___x_4186_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4199_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp___boxed(lean_object* v_pu_4207_, lean_object* v_t_4208_, lean_object* v_decl_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_){
_start:
{
uint8_t v_pu_boxed_4216_; uint8_t v_t_boxed_4217_; lean_object* v_res_4218_; 
v_pu_boxed_4216_ = lean_unbox(v_pu_4207_);
v_t_boxed_4217_ = lean_unbox(v_t_4208_);
v_res_4218_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_boxed_4216_, v_t_boxed_4217_, v_decl_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
lean_dec_ref(v_a_4210_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(lean_object* v_pu_4219_, lean_object* v_t_4220_, lean_object* v_i_4221_, lean_object* v_as_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
uint8_t v_pu_boxed_4229_; uint8_t v_t_boxed_4230_; lean_object* v_res_4231_; 
v_pu_boxed_4229_ = lean_unbox(v_pu_4219_);
v_t_boxed_4230_ = lean_unbox(v_t_4220_);
v_res_4231_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_boxed_4229_, v_t_boxed_4230_, v_i_4221_, v_as_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec_ref(v___y_4223_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp___boxed(lean_object* v_pu_4232_, lean_object* v_t_4233_, lean_object* v_code_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_){
_start:
{
uint8_t v_pu_boxed_4241_; uint8_t v_t_boxed_4242_; lean_object* v_res_4243_; 
v_pu_boxed_4241_ = lean_unbox(v_pu_4232_);
v_t_boxed_4242_ = lean_unbox(v_t_4233_);
v_res_4243_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_boxed_4241_, v_t_boxed_4242_, v_code_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
lean_dec(v_a_4239_);
lean_dec_ref(v_a_4238_);
lean_dec(v_a_4237_);
lean_dec_ref(v_a_4236_);
lean_dec_ref(v_a_4235_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(uint8_t v_pu_4244_, uint8_t v_t_4245_, uint8_t v_pu_4246_, uint8_t v_t_4247_, lean_object* v_decl_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
lean_object* v___x_4255_; 
v___x_4255_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_4246_, v_t_4247_, v_decl_4248_, v___y_4249_, v___y_4251_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(lean_object* v_pu_4256_, lean_object* v_t_4257_, lean_object* v_pu_4258_, lean_object* v_t_4259_, lean_object* v_decl_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
uint8_t v_pu_boxed_4267_; uint8_t v_t_boxed_4268_; uint8_t v_pu_boxed_4269_; uint8_t v_t_boxed_4270_; lean_object* v_res_4271_; 
v_pu_boxed_4267_ = lean_unbox(v_pu_4256_);
v_t_boxed_4268_ = lean_unbox(v_t_4257_);
v_pu_boxed_4269_ = lean_unbox(v_pu_4258_);
v_t_boxed_4270_ = lean_unbox(v_t_4259_);
v_res_4271_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(v_pu_boxed_4267_, v_t_boxed_4268_, v_pu_boxed_4269_, v_t_boxed_4270_, v_decl_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec_ref(v___y_4261_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(uint8_t v_pu_4272_, uint8_t v_t_4273_, uint8_t v_pu_4274_, uint8_t v_t_4275_, lean_object* v_args_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_4274_, v_t_4275_, v_args_4276_, v___y_4277_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(lean_object* v_pu_4284_, lean_object* v_t_4285_, lean_object* v_pu_4286_, lean_object* v_t_4287_, lean_object* v_args_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_){
_start:
{
uint8_t v_pu_boxed_4295_; uint8_t v_t_boxed_4296_; uint8_t v_pu_boxed_4297_; uint8_t v_t_boxed_4298_; lean_object* v_res_4299_; 
v_pu_boxed_4295_ = lean_unbox(v_pu_4284_);
v_t_boxed_4296_ = lean_unbox(v_t_4285_);
v_pu_boxed_4297_ = lean_unbox(v_pu_4286_);
v_t_boxed_4298_ = lean_unbox(v_t_4287_);
v_res_4299_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(v_pu_boxed_4295_, v_t_boxed_4296_, v_pu_boxed_4297_, v_t_boxed_4298_, v_args_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec_ref(v___y_4289_);
return v_res_4299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(uint8_t v_pu_4300_, uint8_t v_t_4301_, uint8_t v_pu_4302_, uint8_t v_t_4303_, lean_object* v_ps_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_){
_start:
{
lean_object* v___x_4311_; 
v___x_4311_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4302_, v_t_4303_, v_ps_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
return v___x_4311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(lean_object* v_pu_4312_, lean_object* v_t_4313_, lean_object* v_pu_4314_, lean_object* v_t_4315_, lean_object* v_ps_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
uint8_t v_pu_boxed_4323_; uint8_t v_t_boxed_4324_; uint8_t v_pu_boxed_4325_; uint8_t v_t_boxed_4326_; lean_object* v_res_4327_; 
v_pu_boxed_4323_ = lean_unbox(v_pu_4312_);
v_t_boxed_4324_ = lean_unbox(v_t_4313_);
v_pu_boxed_4325_ = lean_unbox(v_pu_4314_);
v_t_boxed_4326_ = lean_unbox(v_t_4315_);
v_res_4327_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(v_pu_boxed_4323_, v_t_boxed_4324_, v_pu_boxed_4325_, v_t_boxed_4326_, v_ps_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
lean_dec_ref(v___y_4317_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(uint8_t v_pu_4328_, uint8_t v_t_4329_, lean_object* v_i_4330_, lean_object* v_as_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_){
_start:
{
lean_object* v___x_4338_; 
v___x_4338_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_4328_, v_t_4329_, v_i_4330_, v_as_4331_, v___y_4332_, v___y_4334_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(lean_object* v_pu_4339_, lean_object* v_t_4340_, lean_object* v_i_4341_, lean_object* v_as_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_){
_start:
{
uint8_t v_pu_boxed_4349_; uint8_t v_t_boxed_4350_; lean_object* v_res_4351_; 
v_pu_boxed_4349_ = lean_unbox(v_pu_4339_);
v_t_boxed_4350_ = lean_unbox(v_t_4340_);
v_res_4351_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_boxed_4349_, v_t_boxed_4350_, v_i_4341_, v_as_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
lean_dec(v___y_4347_);
lean_dec_ref(v___y_4346_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
lean_dec_ref(v___y_4343_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(uint8_t v_pu_4352_, uint8_t v_t_4353_, lean_object* v_decl_4354_, lean_object* v_inst_4355_, lean_object* v_____do__lift_4356_){
_start:
{
lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4357_ = lean_box(v_pu_4352_);
v___x_4358_ = lean_box(v_t_4353_);
v___x_4359_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDeclImp___boxed), 9, 4);
lean_closure_set(v___x_4359_, 0, v___x_4357_);
lean_closure_set(v___x_4359_, 1, v___x_4358_);
lean_closure_set(v___x_4359_, 2, v_decl_4354_);
lean_closure_set(v___x_4359_, 3, v_____do__lift_4356_);
v___x_4360_ = lean_apply_2(v_inst_4355_, lean_box(0), v___x_4359_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(lean_object* v_pu_4361_, lean_object* v_t_4362_, lean_object* v_decl_4363_, lean_object* v_inst_4364_, lean_object* v_____do__lift_4365_){
_start:
{
uint8_t v_pu_boxed_4366_; uint8_t v_t_boxed_4367_; lean_object* v_res_4368_; 
v_pu_boxed_4366_ = lean_unbox(v_pu_4361_);
v_t_boxed_4367_ = lean_unbox(v_t_4362_);
v_res_4368_ = l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(v_pu_boxed_4366_, v_t_boxed_4367_, v_decl_4363_, v_inst_4364_, v_____do__lift_4365_);
return v_res_4368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg(uint8_t v_pu_4369_, uint8_t v_t_4370_, lean_object* v_inst_4371_, lean_object* v_inst_4372_, lean_object* v_inst_4373_, lean_object* v_decl_4374_){
_start:
{
lean_object* v_toBind_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___f_4378_; lean_object* v___x_4379_; 
v_toBind_4375_ = lean_ctor_get(v_inst_4372_, 1);
lean_inc(v_toBind_4375_);
lean_dec_ref(v_inst_4372_);
v___x_4376_ = lean_box(v_pu_4369_);
v___x_4377_ = lean_box(v_t_4370_);
v___f_4378_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4378_, 0, v___x_4376_);
lean_closure_set(v___f_4378_, 1, v___x_4377_);
lean_closure_set(v___f_4378_, 2, v_decl_4374_);
lean_closure_set(v___f_4378_, 3, v_inst_4371_);
v___x_4379_ = lean_apply_4(v_toBind_4375_, lean_box(0), lean_box(0), v_inst_4373_, v___f_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(lean_object* v_pu_4380_, lean_object* v_t_4381_, lean_object* v_inst_4382_, lean_object* v_inst_4383_, lean_object* v_inst_4384_, lean_object* v_decl_4385_){
_start:
{
uint8_t v_pu_boxed_4386_; uint8_t v_t_boxed_4387_; lean_object* v_res_4388_; 
v_pu_boxed_4386_ = lean_unbox(v_pu_4380_);
v_t_boxed_4387_ = lean_unbox(v_t_4381_);
v_res_4388_ = l_Lean_Compiler_LCNF_normFunDecl___redArg(v_pu_boxed_4386_, v_t_boxed_4387_, v_inst_4382_, v_inst_4383_, v_inst_4384_, v_decl_4385_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl(lean_object* v_m_4389_, uint8_t v_pu_4390_, uint8_t v_t_4391_, lean_object* v_inst_4392_, lean_object* v_inst_4393_, lean_object* v_inst_4394_, lean_object* v_decl_4395_){
_start:
{
lean_object* v_toBind_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___f_4399_; lean_object* v___x_4400_; 
v_toBind_4396_ = lean_ctor_get(v_inst_4393_, 1);
lean_inc(v_toBind_4396_);
lean_dec_ref(v_inst_4393_);
v___x_4397_ = lean_box(v_pu_4390_);
v___x_4398_ = lean_box(v_t_4391_);
v___f_4399_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4399_, 0, v___x_4397_);
lean_closure_set(v___f_4399_, 1, v___x_4398_);
lean_closure_set(v___f_4399_, 2, v_decl_4395_);
lean_closure_set(v___f_4399_, 3, v_inst_4392_);
v___x_4400_ = lean_apply_4(v_toBind_4396_, lean_box(0), lean_box(0), v_inst_4394_, v___f_4399_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___boxed(lean_object* v_m_4401_, lean_object* v_pu_4402_, lean_object* v_t_4403_, lean_object* v_inst_4404_, lean_object* v_inst_4405_, lean_object* v_inst_4406_, lean_object* v_decl_4407_){
_start:
{
uint8_t v_pu_boxed_4408_; uint8_t v_t_boxed_4409_; lean_object* v_res_4410_; 
v_pu_boxed_4408_ = lean_unbox(v_pu_4402_);
v_t_boxed_4409_ = lean_unbox(v_t_4403_);
v_res_4410_ = l_Lean_Compiler_LCNF_normFunDecl(v_m_4401_, v_pu_boxed_4408_, v_t_boxed_4409_, v_inst_4404_, v_inst_4405_, v_inst_4406_, v_decl_4407_);
return v_res_4410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0(uint8_t v_pu_4411_, uint8_t v_t_4412_, lean_object* v_code_4413_, lean_object* v_inst_4414_, lean_object* v_____do__lift_4415_){
_start:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4416_ = lean_box(v_pu_4411_);
v___x_4417_ = lean_box(v_t_4412_);
v___x_4418_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCodeImp___boxed), 9, 4);
lean_closure_set(v___x_4418_, 0, v___x_4416_);
lean_closure_set(v___x_4418_, 1, v___x_4417_);
lean_closure_set(v___x_4418_, 2, v_code_4413_);
lean_closure_set(v___x_4418_, 3, v_____do__lift_4415_);
v___x_4419_ = lean_apply_2(v_inst_4414_, lean_box(0), v___x_4418_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(lean_object* v_pu_4420_, lean_object* v_t_4421_, lean_object* v_code_4422_, lean_object* v_inst_4423_, lean_object* v_____do__lift_4424_){
_start:
{
uint8_t v_pu_boxed_4425_; uint8_t v_t_boxed_4426_; lean_object* v_res_4427_; 
v_pu_boxed_4425_ = lean_unbox(v_pu_4420_);
v_t_boxed_4426_ = lean_unbox(v_t_4421_);
v_res_4427_ = l_Lean_Compiler_LCNF_normCode___redArg___lam__0(v_pu_boxed_4425_, v_t_boxed_4426_, v_code_4422_, v_inst_4423_, v_____do__lift_4424_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg(uint8_t v_pu_4428_, uint8_t v_t_4429_, lean_object* v_inst_4430_, lean_object* v_inst_4431_, lean_object* v_inst_4432_, lean_object* v_code_4433_){
_start:
{
lean_object* v_toBind_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___f_4437_; lean_object* v___x_4438_; 
v_toBind_4434_ = lean_ctor_get(v_inst_4431_, 1);
lean_inc(v_toBind_4434_);
lean_dec_ref(v_inst_4431_);
v___x_4435_ = lean_box(v_pu_4428_);
v___x_4436_ = lean_box(v_t_4429_);
v___f_4437_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4437_, 0, v___x_4435_);
lean_closure_set(v___f_4437_, 1, v___x_4436_);
lean_closure_set(v___f_4437_, 2, v_code_4433_);
lean_closure_set(v___f_4437_, 3, v_inst_4430_);
v___x_4438_ = lean_apply_4(v_toBind_4434_, lean_box(0), lean_box(0), v_inst_4432_, v___f_4437_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___boxed(lean_object* v_pu_4439_, lean_object* v_t_4440_, lean_object* v_inst_4441_, lean_object* v_inst_4442_, lean_object* v_inst_4443_, lean_object* v_code_4444_){
_start:
{
uint8_t v_pu_boxed_4445_; uint8_t v_t_boxed_4446_; lean_object* v_res_4447_; 
v_pu_boxed_4445_ = lean_unbox(v_pu_4439_);
v_t_boxed_4446_ = lean_unbox(v_t_4440_);
v_res_4447_ = l_Lean_Compiler_LCNF_normCode___redArg(v_pu_boxed_4445_, v_t_boxed_4446_, v_inst_4441_, v_inst_4442_, v_inst_4443_, v_code_4444_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode(lean_object* v_m_4448_, uint8_t v_pu_4449_, uint8_t v_t_4450_, lean_object* v_inst_4451_, lean_object* v_inst_4452_, lean_object* v_inst_4453_, lean_object* v_code_4454_){
_start:
{
lean_object* v_toBind_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___f_4458_; lean_object* v___x_4459_; 
v_toBind_4455_ = lean_ctor_get(v_inst_4452_, 1);
lean_inc(v_toBind_4455_);
lean_dec_ref(v_inst_4452_);
v___x_4456_ = lean_box(v_pu_4449_);
v___x_4457_ = lean_box(v_t_4450_);
v___f_4458_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4458_, 0, v___x_4456_);
lean_closure_set(v___f_4458_, 1, v___x_4457_);
lean_closure_set(v___f_4458_, 2, v_code_4454_);
lean_closure_set(v___f_4458_, 3, v_inst_4451_);
v___x_4459_ = lean_apply_4(v_toBind_4455_, lean_box(0), lean_box(0), v_inst_4453_, v___f_4458_);
return v___x_4459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___boxed(lean_object* v_m_4460_, lean_object* v_pu_4461_, lean_object* v_t_4462_, lean_object* v_inst_4463_, lean_object* v_inst_4464_, lean_object* v_inst_4465_, lean_object* v_code_4466_){
_start:
{
uint8_t v_pu_boxed_4467_; uint8_t v_t_boxed_4468_; lean_object* v_res_4469_; 
v_pu_boxed_4467_ = lean_unbox(v_pu_4461_);
v_t_boxed_4468_ = lean_unbox(v_t_4462_);
v_res_4469_ = l_Lean_Compiler_LCNF_normCode(v_m_4460_, v_pu_boxed_4467_, v_t_boxed_4468_, v_inst_4463_, v_inst_4464_, v_inst_4465_, v_code_4466_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t v_pu_4470_, lean_object* v_e_4471_, lean_object* v_s_4472_, uint8_t v_translator_4473_){
_start:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4475_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4470_, v_s_4472_, v_translator_4473_, v_e_4471_);
v___x_4476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4476_, 0, v___x_4475_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(lean_object* v_pu_4477_, lean_object* v_e_4478_, lean_object* v_s_4479_, lean_object* v_translator_4480_, lean_object* v_a_4481_){
_start:
{
uint8_t v_pu_boxed_4482_; uint8_t v_translator_boxed_4483_; lean_object* v_res_4484_; 
v_pu_boxed_4482_ = lean_unbox(v_pu_4477_);
v_translator_boxed_4483_ = lean_unbox(v_translator_4480_);
v_res_4484_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_boxed_4482_, v_e_4478_, v_s_4479_, v_translator_boxed_4483_);
lean_dec_ref(v_s_4479_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(uint8_t v_pu_4485_, lean_object* v_e_4486_, lean_object* v_s_4487_, uint8_t v_translator_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_){
_start:
{
lean_object* v___x_4494_; 
v___x_4494_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_4485_, v_e_4486_, v_s_4487_, v_translator_4488_);
return v___x_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___boxed(lean_object* v_pu_4495_, lean_object* v_e_4496_, lean_object* v_s_4497_, lean_object* v_translator_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_){
_start:
{
uint8_t v_pu_boxed_4504_; uint8_t v_translator_boxed_4505_; lean_object* v_res_4506_; 
v_pu_boxed_4504_ = lean_unbox(v_pu_4495_);
v_translator_boxed_4505_ = lean_unbox(v_translator_4498_);
v_res_4506_ = l_Lean_Compiler_LCNF_replaceExprFVars(v_pu_boxed_4504_, v_e_4496_, v_s_4497_, v_translator_boxed_4505_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_);
lean_dec(v_a_4502_);
lean_dec_ref(v_a_4501_);
lean_dec(v_a_4500_);
lean_dec_ref(v_a_4499_);
lean_dec_ref(v_s_4497_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t v_pu_4507_, lean_object* v_code_4508_, lean_object* v_s_4509_, uint8_t v_translator_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_){
_start:
{
lean_object* v___x_4516_; 
v___x_4516_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4507_, v_translator_4510_, v_code_4508_, v_s_4509_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_);
return v___x_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars___boxed(lean_object* v_pu_4517_, lean_object* v_code_4518_, lean_object* v_s_4519_, lean_object* v_translator_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_){
_start:
{
uint8_t v_pu_boxed_4526_; uint8_t v_translator_boxed_4527_; lean_object* v_res_4528_; 
v_pu_boxed_4526_ = lean_unbox(v_pu_4517_);
v_translator_boxed_4527_ = lean_unbox(v_translator_4520_);
v_res_4528_ = l_Lean_Compiler_LCNF_replaceFVars(v_pu_boxed_4526_, v_code_4518_, v_s_4519_, v_translator_boxed_4527_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_);
lean_dec(v_a_4524_);
lean_dec_ref(v_a_4523_);
lean_dec(v_a_4522_);
lean_dec_ref(v_a_4521_);
lean_dec_ref(v_s_4519_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object* v_a_4532_){
_start:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; 
v___x_4534_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1));
v___x_4535_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4534_, v_a_4532_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(lean_object* v_a_4536_, lean_object* v_a_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4536_);
lean_dec(v_a_4536_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_){
_start:
{
lean_object* v___x_4544_; 
v___x_4544_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4540_);
return v___x_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___boxed(lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_);
lean_dec(v_a_4548_);
lean_dec_ref(v_a_4547_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t v_pu_4551_, lean_object* v_type_4552_, uint8_t v_borrow_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_){
_start:
{
lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v_a_4561_; lean_object* v___x_4562_; 
v___x_4559_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_4560_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4559_, v_a_4555_);
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
lean_inc(v_a_4561_);
lean_dec_ref(v___x_4560_);
v___x_4562_ = l_Lean_Compiler_LCNF_mkParam(v_pu_4551_, v_a_4561_, v_type_4552_, v_borrow_4553_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_);
return v___x_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam___boxed(lean_object* v_pu_4563_, lean_object* v_type_4564_, lean_object* v_borrow_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_){
_start:
{
uint8_t v_pu_boxed_4571_; uint8_t v_borrow_boxed_4572_; lean_object* v_res_4573_; 
v_pu_boxed_4571_ = lean_unbox(v_pu_4563_);
v_borrow_boxed_4572_ = lean_unbox(v_borrow_4565_);
v_res_4573_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_boxed_4571_, v_type_4564_, v_borrow_boxed_4572_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_);
lean_dec(v_a_4569_);
lean_dec_ref(v_a_4568_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
return v_res_4573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object* v_a_4574_){
_start:
{
lean_object* v_config_4576_; lean_object* v___x_4577_; 
v_config_4576_ = lean_ctor_get(v_a_4574_, 0);
lean_inc_ref(v_config_4576_);
v___x_4577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4577_, 0, v_config_4576_);
return v___x_4577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg___boxed(lean_object* v_a_4578_, lean_object* v_a_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4578_);
lean_dec_ref(v_a_4578_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_){
_start:
{
lean_object* v___x_4586_; 
v___x_4586_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4581_);
return v___x_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___boxed(lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l_Lean_Compiler_LCNF_getConfig(v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
lean_dec(v_a_4590_);
lean_dec_ref(v_a_4589_);
lean_dec(v_a_4588_);
lean_dec_ref(v_a_4587_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object* v_x_4593_, lean_object* v_s_4594_, uint8_t v_phase_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_){
_start:
{
lean_object* v___x_4599_; lean_object* v_options_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4599_ = lean_st_mk_ref(v_s_4594_);
v_options_4600_ = lean_ctor_get(v_a_4596_, 2);
v___x_4601_ = l_Lean_Compiler_LCNF_toConfigOptions(v_options_4600_);
v___x_4602_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4602_, 0, v___x_4601_);
lean_ctor_set_uint8(v___x_4602_, sizeof(void*)*1, v_phase_4595_);
lean_inc(v_a_4597_);
lean_inc_ref(v_a_4596_);
lean_inc(v___x_4599_);
v___x_4603_ = lean_apply_5(v_x_4593_, v___x_4602_, v___x_4599_, v_a_4596_, v_a_4597_, lean_box(0));
if (lean_obj_tag(v___x_4603_) == 0)
{
lean_object* v_a_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4612_; 
v_a_4604_ = lean_ctor_get(v___x_4603_, 0);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4606_ = v___x_4603_;
v_isShared_4607_ = v_isSharedCheck_4612_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_a_4604_);
lean_dec(v___x_4603_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4612_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4608_; lean_object* v___x_4610_; 
v___x_4608_ = lean_st_ref_get(v___x_4599_);
lean_dec(v___x_4599_);
lean_dec(v___x_4608_);
if (v_isShared_4607_ == 0)
{
v___x_4610_ = v___x_4606_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4604_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
return v___x_4610_;
}
}
}
else
{
lean_dec(v___x_4599_);
return v___x_4603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(lean_object* v_x_4613_, lean_object* v_s_4614_, lean_object* v_phase_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_){
_start:
{
uint8_t v_phase_boxed_4619_; lean_object* v_res_4620_; 
v_phase_boxed_4619_ = lean_unbox(v_phase_4615_);
v_res_4620_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4613_, v_s_4614_, v_phase_boxed_4619_, v_a_4616_, v_a_4617_);
lean_dec(v_a_4617_);
lean_dec_ref(v_a_4616_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run(lean_object* v_00_u03b1_4621_, lean_object* v_x_4622_, lean_object* v_s_4623_, uint8_t v_phase_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_){
_start:
{
lean_object* v___x_4628_; 
v___x_4628_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4622_, v_s_4623_, v_phase_4624_, v_a_4625_, v_a_4626_);
return v___x_4628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object* v_00_u03b1_4629_, lean_object* v_x_4630_, lean_object* v_s_4631_, lean_object* v_phase_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_){
_start:
{
uint8_t v_phase_boxed_4636_; lean_object* v_res_4637_; 
v_phase_boxed_4636_ = lean_unbox(v_phase_4632_);
v_res_4637_ = l_Lean_Compiler_LCNF_CompilerM_run(v_00_u03b1_4629_, v_x_4630_, v_s_4631_, v_phase_boxed_4636_, v_a_4633_, v_a_4634_);
lean_dec(v_a_4634_);
lean_dec_ref(v_a_4633_);
return v_res_4637_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0(void){
_start:
{
lean_object* v___x_4638_; 
v___x_4638_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object* v_00_u03b1_4639_, lean_object* v_00_u03b2_4640_, lean_object* v_inst_4641_, lean_object* v_inst_4642_){
_start:
{
lean_object* v___x_4643_; 
v___x_4643_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object* v_00_u03b1_4644_, lean_object* v_00_u03b2_4645_, lean_object* v_inst_4646_, lean_object* v_inst_4647_){
_start:
{
lean_object* v_res_4648_; 
v_res_4648_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(v_00_u03b1_4644_, v_00_u03b2_4645_, v_inst_4646_, v_inst_4647_);
lean_dec_ref(v_inst_4647_);
lean_dec_ref(v_inst_4646_);
return v_res_4648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension(lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_){
_start:
{
lean_object* v___x_4653_; 
v___x_4653_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_){
_start:
{
lean_object* v_res_4658_; 
v_res_4658_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension(v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_);
lean_dec_ref(v_a_4657_);
lean_dec_ref(v_a_4656_);
return v_res_4658_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4662_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2));
v___x_4663_ = lean_unsigned_to_nat(14u);
v___x_4664_ = lean_unsigned_to_nat(178u);
v___x_4665_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1));
v___x_4666_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0));
v___x_4667_ = l_mkPanicMessageWithDecl(v___x_4666_, v___x_4665_, v___x_4664_, v___x_4663_, v___x_4662_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(lean_object* v_inst_4668_, lean_object* v_inst_4669_, lean_object* v_snd_4670_, lean_object* v_inst_4671_, lean_object* v_s_4672_, lean_object* v_e_4673_){
_start:
{
lean_object* v_fst_4674_; lean_object* v_snd_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4690_; 
v_fst_4674_ = lean_ctor_get(v_s_4672_, 0);
v_snd_4675_ = lean_ctor_get(v_s_4672_, 1);
v_isSharedCheck_4690_ = !lean_is_exclusive(v_s_4672_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4677_ = v_s_4672_;
v_isShared_4678_ = v_isSharedCheck_4690_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_snd_4675_);
lean_inc(v_fst_4674_);
lean_dec(v_s_4672_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4690_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
lean_object* v___x_4679_; lean_object* v___y_4681_; lean_object* v___x_4686_; 
lean_inc_n(v_e_4673_, 2);
v___x_4679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4679_, 0, v_e_4673_);
lean_ctor_set(v___x_4679_, 1, v_fst_4674_);
lean_inc_ref(v_inst_4669_);
lean_inc_ref(v_inst_4668_);
v___x_4686_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4668_, v_inst_4669_, v_snd_4670_, v_e_4673_);
if (lean_obj_tag(v___x_4686_) == 0)
{
lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4687_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3);
v___x_4688_ = l_panic___redArg(v_inst_4671_, v___x_4687_);
v___y_4681_ = v___x_4688_;
goto v___jp_4680_;
}
else
{
lean_object* v_val_4689_; 
v_val_4689_ = lean_ctor_get(v___x_4686_, 0);
lean_inc(v_val_4689_);
lean_dec_ref_known(v___x_4686_, 1);
v___y_4681_ = v_val_4689_;
goto v___jp_4680_;
}
v___jp_4680_:
{
lean_object* v___x_4682_; lean_object* v___x_4684_; 
v___x_4682_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4668_, v_inst_4669_, v_snd_4675_, v_e_4673_, v___y_4681_);
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 1, v___x_4682_);
lean_ctor_set(v___x_4677_, 0, v___x_4679_);
v___x_4684_ = v___x_4677_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v___x_4679_);
lean_ctor_set(v_reuseFailAlloc_4685_, 1, v___x_4682_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed(lean_object* v_inst_4691_, lean_object* v_inst_4692_, lean_object* v_snd_4693_, lean_object* v_inst_4694_, lean_object* v_s_4695_, lean_object* v_e_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(v_inst_4691_, v_inst_4692_, v_snd_4693_, v_inst_4694_, v_s_4695_, v_e_4696_);
lean_dec(v_inst_4694_);
lean_dec(v_snd_4693_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object* v_inst_4700_, lean_object* v_inst_4701_, lean_object* v_inst_4702_, lean_object* v_oldState_4703_, lean_object* v_newState_4704_, lean_object* v_x_4705_, lean_object* v_s_4706_){
_start:
{
lean_object* v_fst_4707_; lean_object* v_snd_4708_; lean_object* v_fst_4709_; lean_object* v___f_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v_newEntries_4715_; lean_object* v___x_4716_; 
v_fst_4707_ = lean_ctor_get(v_newState_4704_, 0);
lean_inc_n(v_fst_4707_, 2);
v_snd_4708_ = lean_ctor_get(v_newState_4704_, 1);
lean_inc(v_snd_4708_);
lean_dec_ref(v_newState_4704_);
v_fst_4709_ = lean_ctor_get(v_oldState_4703_, 0);
v___f_4710_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_4710_, 0, v_inst_4700_);
lean_closure_set(v___f_4710_, 1, v_inst_4701_);
lean_closure_set(v___f_4710_, 2, v_snd_4708_);
lean_closure_set(v___f_4710_, 3, v_inst_4702_);
v___x_4711_ = l_List_lengthTR___redArg(v_fst_4707_);
v___x_4712_ = l_List_lengthTR___redArg(v_fst_4709_);
v___x_4713_ = lean_nat_sub(v___x_4711_, v___x_4712_);
lean_dec(v___x_4712_);
lean_dec(v___x_4711_);
v___x_4714_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0));
v_newEntries_4715_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fst_4707_, v_fst_4707_, v___x_4713_, v___x_4714_);
lean_dec(v_fst_4707_);
v___x_4716_ = l_List_foldl___redArg(v___f_4710_, v_s_4706_, v_newEntries_4715_);
return v___x_4716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object* v_inst_4717_, lean_object* v_inst_4718_, lean_object* v_inst_4719_, lean_object* v_oldState_4720_, lean_object* v_newState_4721_, lean_object* v_x_4722_, lean_object* v_s_4723_){
_start:
{
lean_object* v_res_4724_; 
v_res_4724_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(v_inst_4717_, v_inst_4718_, v_inst_4719_, v_oldState_4720_, v_newState_4721_, v_x_4722_, v_s_4723_);
lean_dec(v_x_4722_);
lean_dec_ref(v_oldState_4720_);
return v_res_4724_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0(void){
_start:
{
lean_object* v___x_4725_; 
v___x_4725_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4725_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1(void){
_start:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4726_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0);
v___x_4727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4727_, 0, v___x_4726_);
return v___x_4727_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2(void){
_start:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; 
v___x_4728_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1);
v___x_4729_ = lean_box(0);
v___x_4730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4730_, 0, v___x_4729_);
lean_ctor_set(v___x_4730_, 1, v___x_4728_);
return v___x_4730_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3(void){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; 
v___x_4731_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2);
v___x_4732_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_4732_, 0, lean_box(0));
lean_closure_set(v___x_4732_, 1, lean_box(0));
lean_closure_set(v___x_4732_, 2, v___x_4731_);
return v___x_4732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object* v_inst_4733_, lean_object* v_inst_4734_, lean_object* v_inst_4735_){
_start:
{
lean_object* v___f_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v___f_4737_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4737_, 0, v_inst_4733_);
lean_closure_set(v___f_4737_, 1, v_inst_4734_);
lean_closure_set(v___f_4737_, 2, v_inst_4735_);
v___x_4738_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3);
v___x_4739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4739_, 0, v___f_4737_);
v___x_4740_ = lean_box(0);
v___x_4741_ = l_Lean_registerEnvExtension___redArg(v___x_4738_, v___x_4739_, v___x_4740_);
if (lean_obj_tag(v___x_4741_) == 0)
{
lean_object* v_a_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4749_; 
v_a_4742_ = lean_ctor_get(v___x_4741_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4744_ = v___x_4741_;
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_a_4742_);
lean_dec(v___x_4741_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v___x_4747_; 
if (v_isShared_4745_ == 0)
{
v___x_4747_ = v___x_4744_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_a_4742_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
else
{
lean_object* v_a_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4757_; 
v_a_4750_ = lean_ctor_get(v___x_4741_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4752_ = v___x_4741_;
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v___x_4741_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v___x_4755_; 
if (v_isShared_4753_ == 0)
{
v___x_4755_ = v___x_4752_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_a_4750_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object* v_inst_4758_, lean_object* v_inst_4759_, lean_object* v_inst_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4758_, v_inst_4759_, v_inst_4760_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object* v_00_u03b1_4763_, lean_object* v_00_u03b2_4764_, lean_object* v_inst_4765_, lean_object* v_inst_4766_, lean_object* v_inst_4767_){
_start:
{
lean_object* v___x_4769_; 
v___x_4769_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4765_, v_inst_4766_, v_inst_4767_);
return v___x_4769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object* v_00_u03b1_4770_, lean_object* v_00_u03b2_4771_, lean_object* v_inst_4772_, lean_object* v_inst_4773_, lean_object* v_inst_4774_, lean_object* v_a_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l_Lean_Compiler_LCNF_CacheExtension_register(v_00_u03b1_4770_, v_00_u03b2_4771_, v_inst_4772_, v_inst_4773_, v_inst_4774_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object* v_a_4777_, lean_object* v_inst_4778_, lean_object* v_inst_4779_, lean_object* v_b_4780_, lean_object* v_x_4781_){
_start:
{
lean_object* v_fst_4782_; lean_object* v_snd_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4792_; 
v_fst_4782_ = lean_ctor_get(v_x_4781_, 0);
v_snd_4783_ = lean_ctor_get(v_x_4781_, 1);
v_isSharedCheck_4792_ = !lean_is_exclusive(v_x_4781_);
if (v_isSharedCheck_4792_ == 0)
{
v___x_4785_ = v_x_4781_;
v_isShared_4786_ = v_isSharedCheck_4792_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_snd_4783_);
lean_inc(v_fst_4782_);
lean_dec(v_x_4781_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4792_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4790_; 
lean_inc(v_a_4777_);
v___x_4787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4787_, 0, v_a_4777_);
lean_ctor_set(v___x_4787_, 1, v_fst_4782_);
v___x_4788_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4778_, v_inst_4779_, v_snd_4783_, v_a_4777_, v_b_4780_);
if (v_isShared_4786_ == 0)
{
lean_ctor_set(v___x_4785_, 1, v___x_4788_);
lean_ctor_set(v___x_4785_, 0, v___x_4787_);
v___x_4790_ = v___x_4785_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v___x_4787_);
lean_ctor_set(v_reuseFailAlloc_4791_, 1, v___x_4788_);
v___x_4790_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
return v___x_4790_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_4793_; 
v___x_4793_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4793_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4794_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0);
v___x_4795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4795_, 0, v___x_4794_);
return v___x_4795_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2(void){
_start:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4796_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1);
v___x_4797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4796_);
lean_ctor_set(v___x_4797_, 1, v___x_4796_);
return v___x_4797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object* v_inst_4798_, lean_object* v_inst_4799_, lean_object* v_ext_4800_, lean_object* v_a_4801_, lean_object* v_b_4802_, lean_object* v_a_4803_){
_start:
{
lean_object* v___x_4805_; lean_object* v_env_4806_; lean_object* v_nextMacroScope_4807_; lean_object* v_ngen_4808_; lean_object* v_auxDeclNGen_4809_; lean_object* v_traceState_4810_; lean_object* v_messages_4811_; lean_object* v_infoState_4812_; lean_object* v_snapshotTasks_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4828_; 
v___x_4805_ = lean_st_ref_take(v_a_4803_);
v_env_4806_ = lean_ctor_get(v___x_4805_, 0);
v_nextMacroScope_4807_ = lean_ctor_get(v___x_4805_, 1);
v_ngen_4808_ = lean_ctor_get(v___x_4805_, 2);
v_auxDeclNGen_4809_ = lean_ctor_get(v___x_4805_, 3);
v_traceState_4810_ = lean_ctor_get(v___x_4805_, 4);
v_messages_4811_ = lean_ctor_get(v___x_4805_, 6);
v_infoState_4812_ = lean_ctor_get(v___x_4805_, 7);
v_snapshotTasks_4813_ = lean_ctor_get(v___x_4805_, 8);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4805_);
if (v_isSharedCheck_4828_ == 0)
{
lean_object* v_unused_4829_; 
v_unused_4829_ = lean_ctor_get(v___x_4805_, 5);
lean_dec(v_unused_4829_);
v___x_4815_ = v___x_4805_;
v_isShared_4816_ = v_isSharedCheck_4828_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_snapshotTasks_4813_);
lean_inc(v_infoState_4812_);
lean_inc(v_messages_4811_);
lean_inc(v_traceState_4810_);
lean_inc(v_auxDeclNGen_4809_);
lean_inc(v_ngen_4808_);
lean_inc(v_nextMacroScope_4807_);
lean_inc(v_env_4806_);
lean_dec(v___x_4805_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4828_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v_asyncMode_4817_; lean_object* v___f_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4823_; 
v_asyncMode_4817_ = lean_ctor_get(v_ext_4800_, 2);
lean_inc(v_asyncMode_4817_);
v___f_4818_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4818_, 0, v_a_4801_);
lean_closure_set(v___f_4818_, 1, v_inst_4798_);
lean_closure_set(v___f_4818_, 2, v_inst_4799_);
lean_closure_set(v___f_4818_, 3, v_b_4802_);
v___x_4819_ = lean_box(0);
v___x_4820_ = l_Lean_EnvExtension_modifyState___redArg(v_ext_4800_, v_env_4806_, v___f_4818_, v_asyncMode_4817_, v___x_4819_);
lean_dec(v_asyncMode_4817_);
v___x_4821_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2);
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 5, v___x_4821_);
lean_ctor_set(v___x_4815_, 0, v___x_4820_);
v___x_4823_ = v___x_4815_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v___x_4820_);
lean_ctor_set(v_reuseFailAlloc_4827_, 1, v_nextMacroScope_4807_);
lean_ctor_set(v_reuseFailAlloc_4827_, 2, v_ngen_4808_);
lean_ctor_set(v_reuseFailAlloc_4827_, 3, v_auxDeclNGen_4809_);
lean_ctor_set(v_reuseFailAlloc_4827_, 4, v_traceState_4810_);
lean_ctor_set(v_reuseFailAlloc_4827_, 5, v___x_4821_);
lean_ctor_set(v_reuseFailAlloc_4827_, 6, v_messages_4811_);
lean_ctor_set(v_reuseFailAlloc_4827_, 7, v_infoState_4812_);
lean_ctor_set(v_reuseFailAlloc_4827_, 8, v_snapshotTasks_4813_);
v___x_4823_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4824_ = lean_st_ref_set(v_a_4803_, v___x_4823_);
v___x_4825_ = lean_box(0);
v___x_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4825_);
return v___x_4826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object* v_inst_4830_, lean_object* v_inst_4831_, lean_object* v_ext_4832_, lean_object* v_a_4833_, lean_object* v_b_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_){
_start:
{
lean_object* v_res_4837_; 
v_res_4837_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4830_, v_inst_4831_, v_ext_4832_, v_a_4833_, v_b_4834_, v_a_4835_);
lean_dec(v_a_4835_);
return v_res_4837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object* v_00_u03b1_4838_, lean_object* v_00_u03b2_4839_, lean_object* v_inst_4840_, lean_object* v_inst_4841_, lean_object* v_inst_4842_, lean_object* v_ext_4843_, lean_object* v_a_4844_, lean_object* v_b_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_){
_start:
{
lean_object* v___x_4849_; 
v___x_4849_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4840_, v_inst_4841_, v_ext_4843_, v_a_4844_, v_b_4845_, v_a_4847_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object* v_00_u03b1_4850_, lean_object* v_00_u03b2_4851_, lean_object* v_inst_4852_, lean_object* v_inst_4853_, lean_object* v_inst_4854_, lean_object* v_ext_4855_, lean_object* v_a_4856_, lean_object* v_b_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_){
_start:
{
lean_object* v_res_4861_; 
v_res_4861_ = l_Lean_Compiler_LCNF_CacheExtension_insert(v_00_u03b1_4850_, v_00_u03b2_4851_, v_inst_4852_, v_inst_4853_, v_inst_4854_, v_ext_4855_, v_a_4856_, v_b_4857_, v_a_4858_, v_a_4859_);
lean_dec(v_a_4859_);
lean_dec_ref(v_a_4858_);
lean_dec(v_inst_4854_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object* v_inst_4862_, lean_object* v_inst_4863_, lean_object* v_ext_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_){
_start:
{
lean_object* v___x_4868_; lean_object* v_env_4869_; lean_object* v_asyncMode_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v_snd_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4868_ = lean_st_ref_get(v_a_4866_);
v_env_4869_ = lean_ctor_get(v___x_4868_, 0);
lean_inc_ref(v_env_4869_);
lean_dec(v___x_4868_);
v_asyncMode_4870_ = lean_ctor_get(v_ext_4864_, 2);
v___x_4871_ = lean_box(0);
v___x_4872_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v_inst_4862_, v_inst_4863_);
v___x_4873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4871_);
lean_ctor_set(v___x_4873_, 1, v___x_4872_);
v___x_4874_ = lean_box(0);
v___x_4875_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4873_, v_ext_4864_, v_env_4869_, v_asyncMode_4870_, v___x_4874_);
lean_dec_ref_known(v___x_4873_, 2);
v_snd_4876_ = lean_ctor_get(v___x_4875_, 1);
lean_inc(v_snd_4876_);
lean_dec(v___x_4875_);
v___x_4877_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4862_, v_inst_4863_, v_snd_4876_, v_a_4865_);
lean_dec(v_snd_4876_);
v___x_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object* v_inst_4879_, lean_object* v_inst_4880_, lean_object* v_ext_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_){
_start:
{
lean_object* v_res_4885_; 
v_res_4885_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4879_, v_inst_4880_, v_ext_4881_, v_a_4882_, v_a_4883_);
lean_dec(v_a_4883_);
lean_dec_ref(v_ext_4881_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object* v_00_u03b1_4886_, lean_object* v_00_u03b2_4887_, lean_object* v_inst_4888_, lean_object* v_inst_4889_, lean_object* v_inst_4890_, lean_object* v_ext_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_){
_start:
{
lean_object* v___x_4896_; 
v___x_4896_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4888_, v_inst_4889_, v_ext_4891_, v_a_4892_, v_a_4894_);
return v___x_4896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object* v_00_u03b1_4897_, lean_object* v_00_u03b2_4898_, lean_object* v_inst_4899_, lean_object* v_inst_4900_, lean_object* v_inst_4901_, lean_object* v_ext_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_){
_start:
{
lean_object* v_res_4907_; 
v_res_4907_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(v_00_u03b1_4897_, v_00_u03b2_4898_, v_inst_4899_, v_inst_4900_, v_inst_4901_, v_ext_4902_, v_a_4903_, v_a_4904_, v_a_4905_);
lean_dec(v_a_4905_);
lean_dec_ref(v_a_4904_);
lean_dec_ref(v_ext_4902_);
lean_dec(v_inst_4901_);
return v_res_4907_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_LCtx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ConfigOptions(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InductiveOverride(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_LCtx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ConfigOptions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_InductiveOverride(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_instInhabitedPhase_default = _init_l_Lean_Compiler_LCNF_instInhabitedPhase_default();
l_Lean_Compiler_LCNF_instInhabitedPhase = _init_l_Lean_Compiler_LCNF_instInhabitedPhase();
l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default = _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default();
lean_mark_persistent(l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default);
l_Lean_Compiler_LCNF_CompilerM_instInhabitedState = _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState();
lean_mark_persistent(l_Lean_Compiler_LCNF_CompilerM_instInhabitedState);
l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default = _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default();
lean_mark_persistent(l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default);
l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext = _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext();
lean_mark_persistent(l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext);
l_Lean_Compiler_LCNF_instMonadCompilerM = _init_l_Lean_Compiler_LCNF_instMonadCompilerM();
lean_mark_persistent(l_Lean_Compiler_LCNF_instMonadCompilerM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_LCtx(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ConfigOptions(uint8_t builtin);
lean_object* initialize_Lean_Compiler_InductiveOverride(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_LCtx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ConfigOptions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InductiveOverride(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_CompilerM(builtin);
}
#ifdef __cplusplus
}
#endif
