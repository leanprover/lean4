// Lean compiler output
// Module: Lean.Compiler.LCNF.CompilerM
// Imports: public import Lean.Compiler.LCNF.LCtx public import Lean.Compiler.LCNF.ConfigOptions
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_Compiler_LCNF_Phase_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg(lean_object* v_base_23_){
_start:
{
lean_inc(v_base_23_);
return v_base_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg___boxed(lean_object* v_base_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Compiler_LCNF_Phase_base_elim___redArg(v_base_24_);
lean_dec(v_base_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_base_29_){
_start:
{
lean_inc(v_base_29_);
return v_base_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_base_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_Compiler_LCNF_Phase_base_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_base_33_);
lean_dec(v_base_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(lean_object* v_mono_36_){
_start:
{
lean_inc(v_mono_36_);
return v_mono_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg___boxed(lean_object* v_mono_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(v_mono_37_);
lean_dec(v_mono_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_mono_42_){
_start:
{
lean_inc(v_mono_42_);
return v_mono_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_mono_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_Compiler_LCNF_Phase_mono_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_mono_46_);
lean_dec(v_mono_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(lean_object* v_impure_49_){
_start:
{
lean_inc(v_impure_49_);
return v_impure_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg___boxed(lean_object* v_impure_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(v_impure_50_);
lean_dec(v_impure_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_impure_55_){
_start:
{
lean_inc(v_impure_55_);
return v_impure_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_impure_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_Compiler_LCNF_Phase_impure_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_impure_59_);
lean_dec(v_impure_59_);
return v_res_61_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_instInhabitedPhase_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_instInhabitedPhase(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Phase_ofNat(lean_object* v_n_64_){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = lean_nat_dec_le(v_n_64_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(1u);
v___x_68_ = lean_nat_dec_le(v_n_64_, v___x_67_);
if (v___x_68_ == 0)
{
uint8_t v___x_69_; 
v___x_69_ = 2;
return v___x_69_;
}
else
{
uint8_t v___x_70_; 
v___x_70_ = 1;
return v___x_70_;
}
}
else
{
uint8_t v___x_71_; 
v___x_71_ = 0;
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ofNat___boxed(lean_object* v_n_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Lean_Compiler_LCNF_Phase_ofNat(v_n_72_);
lean_dec(v_n_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableEqPhase(uint8_t v_x_75_, uint8_t v_y_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_77_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_x_75_);
v___x_78_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_y_76_);
v___x_79_ = lean_nat_dec_eq(v___x_77_, v___x_78_);
lean_dec(v___x_78_);
lean_dec(v___x_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableEqPhase___boxed(lean_object* v_x_80_, lean_object* v_y_81_){
_start:
{
uint8_t v_x_13__boxed_82_; uint8_t v_y_14__boxed_83_; uint8_t v_res_84_; lean_object* v_r_85_; 
v_x_13__boxed_82_ = lean_unbox(v_x_80_);
v_y_14__boxed_83_ = lean_unbox(v_y_81_);
v_res_84_ = l_Lean_Compiler_LCNF_instDecidableEqPhase(v_x_13__boxed_82_, v_y_14__boxed_83_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t v_x_86_){
_start:
{
if (v_x_86_ == 2)
{
uint8_t v___x_87_; 
v___x_87_ = 1;
return v___x_87_;
}
else
{
uint8_t v___x_88_; 
v___x_88_ = 0;
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toPurity___boxed(lean_object* v_x_89_){
_start:
{
uint8_t v_x_23__boxed_90_; uint8_t v_res_91_; lean_object* v_r_92_; 
v_x_23__boxed_90_ = lean_unbox(v_x_89_);
v_res_91_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_x_23__boxed_90_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_box(0);
v___x_94_ = lean_unsigned_to_nat(16u);
v___x_95_ = lean_mk_array(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1);
v___x_100_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
lean_ctor_set(v___x_100_, 2, v___x_99_);
lean_ctor_set(v___x_100_, 3, v___x_99_);
lean_ctor_set(v___x_100_, 4, v___x_99_);
lean_ctor_set(v___x_100_, 5, v___x_99_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_101_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default(void){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState(void){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default;
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0(void){
_start:
{
lean_object* v___x_106_; uint8_t v___x_107_; lean_object* v___x_108_; 
v___x_106_ = l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default;
v___x_107_ = 0;
v___x_108_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*1, v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default(void){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default;
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(lean_object* v_00_u03b1_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___y_112_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object* v_00_u03b1_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(v_00_u03b1_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object* v_00_u03b1_127_, lean_object* v_00_u03b2_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___x_136_; 
lean_inc(v___y_134_);
lean_inc_ref(v___y_133_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
v___x_136_ = lean_apply_5(v___y_129_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, lean_box(0));
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; lean_object* v___x_138_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_137_);
lean_dec_ref_known(v___x_136_, 1);
lean_inc(v___y_134_);
lean_inc_ref(v___y_133_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
v___x_138_ = lean_apply_6(v___y_130_, v_a_137_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, lean_box(0));
return v___x_138_;
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec_ref(v___y_130_);
v_a_139_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_136_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_136_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object* v_00_u03b1_147_, lean_object* v_00_u03b2_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(v_00_u03b1_147_, v_00_u03b2_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
return v_res_156_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0(void){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_instMonadEIO(lean_box(0));
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0);
v___x_159_ = l_StateRefT_x27_instMonad___redArg(v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM(void){
_start:
{
lean_object* v___x_164_; lean_object* v_toApplicative_165_; lean_object* v_toFunctor_166_; lean_object* v_toSeq_167_; lean_object* v_toSeqLeft_168_; lean_object* v_toSeqRight_169_; lean_object* v___f_170_; lean_object* v___f_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___x_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___f_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v_toApplicative_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_208_; 
v___x_164_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_165_ = lean_ctor_get(v___x_164_, 0);
v_toFunctor_166_ = lean_ctor_get(v_toApplicative_165_, 0);
v_toSeq_167_ = lean_ctor_get(v_toApplicative_165_, 2);
v_toSeqLeft_168_ = lean_ctor_get(v_toApplicative_165_, 3);
v_toSeqRight_169_ = lean_ctor_get(v_toApplicative_165_, 4);
v___f_170_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_171_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_166_, 2);
v___f_172_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_172_, 0, v_toFunctor_166_);
v___f_173_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_173_, 0, v_toFunctor_166_);
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v___f_172_);
lean_ctor_set(v___x_174_, 1, v___f_173_);
lean_inc(v_toSeqRight_169_);
v___f_175_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_175_, 0, v_toSeqRight_169_);
lean_inc(v_toSeqLeft_168_);
v___f_176_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_176_, 0, v_toSeqLeft_168_);
lean_inc(v_toSeq_167_);
v___f_177_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_177_, 0, v_toSeq_167_);
v___x_178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_178_, 0, v___x_174_);
lean_ctor_set(v___x_178_, 1, v___f_170_);
lean_ctor_set(v___x_178_, 2, v___f_177_);
lean_ctor_set(v___x_178_, 3, v___f_176_);
lean_ctor_set(v___x_178_, 4, v___f_175_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___f_171_);
v___x_180_ = l_StateRefT_x27_instMonad___redArg(v___x_179_);
v_toApplicative_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; 
v_unused_209_ = lean_ctor_get(v___x_180_, 1);
lean_dec(v_unused_209_);
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_208_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_toApplicative_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_208_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v_toFunctor_185_; lean_object* v_toSeq_186_; lean_object* v_toSeqLeft_187_; lean_object* v_toSeqRight_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_206_; 
v_toFunctor_185_ = lean_ctor_get(v_toApplicative_181_, 0);
v_toSeq_186_ = lean_ctor_get(v_toApplicative_181_, 2);
v_toSeqLeft_187_ = lean_ctor_get(v_toApplicative_181_, 3);
v_toSeqRight_188_ = lean_ctor_get(v_toApplicative_181_, 4);
v_isSharedCheck_206_ = !lean_is_exclusive(v_toApplicative_181_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; 
v_unused_207_ = lean_ctor_get(v_toApplicative_181_, 1);
lean_dec(v_unused_207_);
v___x_190_ = v_toApplicative_181_;
v_isShared_191_ = v_isSharedCheck_206_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_toSeqRight_188_);
lean_inc(v_toSeqLeft_187_);
lean_inc(v_toSeq_186_);
lean_inc(v_toFunctor_185_);
lean_dec(v_toApplicative_181_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_206_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___f_192_; lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___x_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___x_201_; 
v___f_192_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_193_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_185_);
v___f_194_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_194_, 0, v_toFunctor_185_);
v___f_195_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_195_, 0, v_toFunctor_185_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___f_194_);
lean_ctor_set(v___x_196_, 1, v___f_195_);
v___f_197_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_197_, 0, v_toSeqRight_188_);
v___f_198_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_198_, 0, v_toSeqLeft_187_);
v___f_199_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_199_, 0, v_toSeq_186_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 4, v___f_197_);
lean_ctor_set(v___x_190_, 3, v___f_198_);
lean_ctor_set(v___x_190_, 2, v___f_199_);
lean_ctor_set(v___x_190_, 1, v___f_192_);
lean_ctor_set(v___x_190_, 0, v___x_196_);
v___x_201_ = v___x_190_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___f_192_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v___f_199_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v___f_198_);
lean_ctor_set(v_reuseFailAlloc_205_, 4, v___f_197_);
v___x_201_ = v_reuseFailAlloc_205_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_203_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v___f_193_);
lean_ctor_set(v___x_183_, 0, v___x_201_);
v___x_203_ = v___x_183_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v___f_193_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg(uint8_t v_phase_210_, lean_object* v_x_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_config_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_config_217_ = lean_ctor_get(v_a_212_, 0);
lean_inc_ref(v_config_217_);
v___x_218_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_218_, 0, v_config_217_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*1, v_phase_210_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
v___x_219_ = lean_apply_5(v_x_211_, v___x_218_, v_a_213_, v_a_214_, v_a_215_, lean_box(0));
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg___boxed(lean_object* v_phase_220_, lean_object* v_x_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
uint8_t v_phase_boxed_227_; lean_object* v_res_228_; 
v_phase_boxed_227_ = lean_unbox(v_phase_220_);
v_res_228_ = l_Lean_Compiler_LCNF_withPhase___redArg(v_phase_boxed_227_, v_x_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase(lean_object* v_00_u03b1_229_, uint8_t v_phase_230_, lean_object* v_x_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_config_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_config_237_ = lean_ctor_get(v_a_232_, 0);
lean_inc_ref(v_config_237_);
v___x_238_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_238_, 0, v_config_237_);
lean_ctor_set_uint8(v___x_238_, sizeof(void*)*1, v_phase_230_);
lean_inc(v_a_235_);
lean_inc_ref(v_a_234_);
lean_inc(v_a_233_);
v___x_239_ = lean_apply_5(v_x_231_, v___x_238_, v_a_233_, v_a_234_, v_a_235_, lean_box(0));
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___boxed(lean_object* v_00_u03b1_240_, lean_object* v_phase_241_, lean_object* v_x_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
uint8_t v_phase_boxed_248_; lean_object* v_res_249_; 
v_phase_boxed_248_ = lean_unbox(v_phase_241_);
v_res_249_ = l_Lean_Compiler_LCNF_withPhase(v_00_u03b1_240_, v_phase_boxed_248_, v_x_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object* v_a_250_){
_start:
{
uint8_t v_phase_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_phase_252_ = lean_ctor_get_uint8(v_a_250_, sizeof(void*)*1);
v___x_253_ = lean_box(v_phase_252_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg___boxed(lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_255_);
lean_dec_ref(v_a_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase(lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_258_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___boxed(lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Compiler_LCNF_getPhase(v_a_264_, v_a_265_, v_a_266_, v_a_267_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object* v_a_270_){
_start:
{
lean_object* v___x_272_; lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_283_; 
v___x_272_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_270_);
v_a_273_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_283_ == 0)
{
v___x_275_ = v___x_272_;
v_isShared_276_ = v_isSharedCheck_283_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_283_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
uint8_t v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_277_ = lean_unbox(v_a_273_);
lean_dec(v_a_273_);
v___x_278_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_277_);
v___x_279_ = lean_box(v___x_278_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_279_);
v___x_281_ = v___x_275_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg___boxed(lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_284_);
lean_dec_ref(v_a_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity(lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_287_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___boxed(lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Compiler_LCNF_getPurity(v_a_293_, v_a_294_, v_a_295_, v_a_296_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg(lean_object* v_a_299_){
_start:
{
lean_object* v___x_301_; lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_317_; 
v___x_301_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_299_);
v_a_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_317_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_317_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_317_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
uint8_t v___x_306_; 
v___x_306_ = lean_unbox(v_a_302_);
lean_dec(v_a_302_);
if (v___x_306_ == 0)
{
uint8_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_307_ = 1;
v___x_308_ = lean_box(v___x_307_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_308_);
v___x_310_ = v___x_304_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
else
{
uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_312_ = 0;
v___x_313_ = lean_box(v___x_312_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_313_);
v___x_315_ = v___x_304_;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg___boxed(lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_318_);
lean_dec_ref(v_a_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase(lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_321_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___boxed(lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_Compiler_LCNF_inBasePhase(v_a_327_, v_a_328_, v_a_329_, v_a_330_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
return v_res_332_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0(void){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_333_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
lean_ctor_set(v___x_338_, 2, v___x_337_);
lean_ctor_set(v___x_338_, 3, v___x_337_);
lean_ctor_set(v___x_338_, 4, v___x_336_);
lean_ctor_set(v___x_338_, 5, v___x_336_);
lean_ctor_set(v___x_338_, 6, v___x_336_);
lean_ctor_set(v___x_338_, 7, v___x_336_);
lean_ctor_set(v___x_338_, 8, v___x_336_);
lean_ctor_set(v___x_338_, 9, v___x_336_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(lean_object* v_msgData_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_st_ref_get(v___y_343_);
v___x_346_ = lean_st_ref_get(v___y_341_);
v___x_347_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_340_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_370_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_370_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_370_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_370_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v_env_352_; lean_object* v_lctx_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_368_; 
v_env_352_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_env_352_);
lean_dec(v___x_345_);
v_lctx_353_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; 
v_unused_369_ = lean_ctor_get(v___x_346_, 1);
lean_dec(v_unused_369_);
v___x_355_ = v___x_346_;
v_isShared_356_ = v_isSharedCheck_368_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_lctx_353_);
lean_dec(v___x_346_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_368_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v_options_357_; uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v_options_357_ = lean_ctor_get(v___y_342_, 2);
v___x_358_ = lean_unbox(v_a_348_);
lean_dec(v_a_348_);
v___x_359_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_353_, v___x_358_);
lean_dec_ref(v_lctx_353_);
v___x_360_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_357_);
v___x_361_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_361_, 0, v_env_352_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
lean_ctor_set(v___x_361_, 2, v___x_359_);
lean_ctor_set(v___x_361_, 3, v_options_357_);
if (v_isShared_356_ == 0)
{
lean_ctor_set_tag(v___x_355_, 3);
lean_ctor_set(v___x_355_, 1, v_msgData_339_);
lean_ctor_set(v___x_355_, 0, v___x_361_);
v___x_363_ = v___x_355_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_msgData_339_);
v___x_363_ = v_reuseFailAlloc_367_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_363_);
v___x_365_ = v___x_350_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec(v___x_346_);
lean_dec(v___x_345_);
lean_dec_ref(v_msgData_339_);
v_a_371_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_347_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_347_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed(lean_object* v_msgData_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(v_msgData_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(lean_object* v_msg_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_options_394_; lean_object* v_ref_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_options_394_ = lean_ctor_get(v___y_391_, 2);
v_ref_395_ = lean_ctor_get(v___y_391_, 5);
v___x_396_ = lean_st_ref_get(v___y_392_);
v___x_397_ = lean_st_ref_get(v___y_390_);
v___x_398_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_389_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_421_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_421_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_421_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_421_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v_env_403_; lean_object* v_lctx_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_419_; 
v_env_403_ = lean_ctor_get(v___x_396_, 0);
lean_inc_ref(v_env_403_);
lean_dec(v___x_396_);
v_lctx_404_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v___x_397_, 1);
lean_dec(v_unused_420_);
v___x_406_ = v___x_397_;
v_isShared_407_ = v_isSharedCheck_419_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_lctx_404_);
lean_dec(v___x_397_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_419_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_408_ = lean_unbox(v_a_399_);
lean_dec(v_a_399_);
v___x_409_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_404_, v___x_408_);
lean_dec_ref(v_lctx_404_);
v___x_410_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
lean_inc_ref(v_options_394_);
v___x_411_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_411_, 0, v_env_403_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
lean_ctor_set(v___x_411_, 2, v___x_409_);
lean_ctor_set(v___x_411_, 3, v_options_394_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 3);
lean_ctor_set(v___x_406_, 1, v_msg_388_);
lean_ctor_set(v___x_406_, 0, v___x_411_);
v___x_413_ = v___x_406_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_msg_388_);
v___x_413_ = v_reuseFailAlloc_418_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
lean_inc(v_ref_395_);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v_ref_395_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
if (v_isShared_402_ == 0)
{
lean_ctor_set_tag(v___x_401_, 1);
lean_ctor_set(v___x_401_, 0, v___x_414_);
v___x_416_ = v___x_401_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec(v___x_397_);
lean_dec(v___x_396_);
lean_dec_ref(v_msg_388_);
v_a_422_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_398_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_398_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg___boxed(lean_object* v_msg_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(lean_object* v_00_u03b1_437_, lean_object* v_msg_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___boxed(lean_object* v_00_u03b1_445_, lean_object* v_msg_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(v_00_u03b1_445_, v_msg_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(lean_object* v_a_453_, lean_object* v_x_454_){
_start:
{
if (lean_obj_tag(v_x_454_) == 0)
{
lean_object* v___x_455_; 
v___x_455_ = lean_box(0);
return v___x_455_;
}
else
{
lean_object* v_key_456_; lean_object* v_value_457_; lean_object* v_tail_458_; uint8_t v___x_459_; 
v_key_456_ = lean_ctor_get(v_x_454_, 0);
v_value_457_ = lean_ctor_get(v_x_454_, 1);
v_tail_458_ = lean_ctor_get(v_x_454_, 2);
v___x_459_ = l_Lean_instBEqFVarId_beq(v_key_456_, v_a_453_);
if (v___x_459_ == 0)
{
v_x_454_ = v_tail_458_;
goto _start;
}
else
{
lean_object* v___x_461_; 
lean_inc(v_value_457_);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v_value_457_);
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg___boxed(lean_object* v_a_462_, lean_object* v_x_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_462_, v_x_463_);
lean_dec(v_x_463_);
lean_dec(v_a_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object* v_m_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_buckets_467_; lean_object* v___x_468_; uint64_t v___x_469_; uint64_t v___x_470_; uint64_t v___x_471_; uint64_t v_fold_472_; uint64_t v___x_473_; uint64_t v___x_474_; uint64_t v___x_475_; size_t v___x_476_; size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v_buckets_467_ = lean_ctor_get(v_m_465_, 1);
v___x_468_ = lean_array_get_size(v_buckets_467_);
v___x_469_ = l_Lean_instHashableFVarId_hash(v_a_466_);
v___x_470_ = 32ULL;
v___x_471_ = lean_uint64_shift_right(v___x_469_, v___x_470_);
v_fold_472_ = lean_uint64_xor(v___x_469_, v___x_471_);
v___x_473_ = 16ULL;
v___x_474_ = lean_uint64_shift_right(v_fold_472_, v___x_473_);
v___x_475_ = lean_uint64_xor(v_fold_472_, v___x_474_);
v___x_476_ = lean_uint64_to_usize(v___x_475_);
v___x_477_ = lean_usize_of_nat(v___x_468_);
v___x_478_ = ((size_t)1ULL);
v___x_479_ = lean_usize_sub(v___x_477_, v___x_478_);
v___x_480_ = lean_usize_land(v___x_476_, v___x_479_);
v___x_481_ = lean_array_uget_borrowed(v_buckets_467_, v___x_480_);
v___x_482_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_466_, v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg___boxed(lean_object* v_m_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_483_, v_a_484_);
lean_dec(v_a_484_);
lean_dec_ref(v_m_483_);
return v_res_485_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getType___closed__1(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l_Lean_Compiler_LCNF_getType___closed__0));
v___x_488_ = l_Lean_stringToMessageData(v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType(lean_object* v_fvarId_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_st_ref_get(v_a_491_);
v___x_496_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_490_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_547_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_547_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_547_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_547_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___y_502_; lean_object* v_lctx_513_; lean_object* v___y_515_; lean_object* v___y_530_; uint8_t v___x_544_; 
v_lctx_513_ = lean_ctor_get(v___x_495_, 0);
lean_inc_ref(v_lctx_513_);
lean_dec(v___x_495_);
v___x_544_ = lean_unbox(v_a_497_);
if (v___x_544_ == 0)
{
lean_object* v_letDeclsPure_545_; 
v_letDeclsPure_545_ = lean_ctor_get(v_lctx_513_, 2);
lean_inc_ref(v_letDeclsPure_545_);
v___y_530_ = v_letDeclsPure_545_;
goto v___jp_529_;
}
else
{
lean_object* v_letDeclsImpure_546_; 
v_letDeclsImpure_546_ = lean_ctor_get(v_lctx_513_, 3);
lean_inc_ref(v_letDeclsImpure_546_);
v___y_530_ = v_letDeclsImpure_546_;
goto v___jp_529_;
}
v___jp_501_:
{
lean_object* v___x_503_; 
v___x_503_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_502_, v_fvarId_489_);
lean_dec_ref(v___y_502_);
if (lean_obj_tag(v___x_503_) == 1)
{
lean_object* v_val_504_; lean_object* v_type_505_; lean_object* v___x_507_; 
lean_dec(v_fvarId_489_);
v_val_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_val_504_);
lean_dec_ref_known(v___x_503_, 1);
v_type_505_ = lean_ctor_get(v_val_504_, 3);
lean_inc_ref(v_type_505_);
lean_dec(v_val_504_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v_type_505_);
v___x_507_ = v___x_499_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_type_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v___x_503_);
lean_del_object(v___x_499_);
v___x_509_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_510_ = l_Lean_MessageData_ofName(v_fvarId_489_);
v___x_511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_509_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_511_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
return v___x_512_;
}
}
v___jp_514_:
{
lean_object* v___x_516_; 
v___x_516_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_515_, v_fvarId_489_);
lean_dec_ref(v___y_515_);
if (lean_obj_tag(v___x_516_) == 1)
{
lean_object* v_val_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v_lctx_513_);
lean_del_object(v___x_499_);
lean_dec(v_a_497_);
lean_dec(v_fvarId_489_);
v_val_517_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_525_ == 0)
{
v___x_519_ = v___x_516_;
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_val_517_);
lean_dec(v___x_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_type_521_; lean_object* v___x_523_; 
v_type_521_ = lean_ctor_get(v_val_517_, 2);
lean_inc_ref(v_type_521_);
lean_dec(v_val_517_);
if (v_isShared_520_ == 0)
{
lean_ctor_set_tag(v___x_519_, 0);
lean_ctor_set(v___x_519_, 0, v_type_521_);
v___x_523_ = v___x_519_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_type_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
else
{
uint8_t v___x_526_; 
lean_dec(v___x_516_);
v___x_526_ = lean_unbox(v_a_497_);
lean_dec(v_a_497_);
if (v___x_526_ == 0)
{
lean_object* v_funDeclsPure_527_; 
v_funDeclsPure_527_ = lean_ctor_get(v_lctx_513_, 4);
lean_inc_ref(v_funDeclsPure_527_);
lean_dec_ref(v_lctx_513_);
v___y_502_ = v_funDeclsPure_527_;
goto v___jp_501_;
}
else
{
lean_object* v_funDeclsImpure_528_; 
v_funDeclsImpure_528_ = lean_ctor_get(v_lctx_513_, 5);
lean_inc_ref(v_funDeclsImpure_528_);
lean_dec_ref(v_lctx_513_);
v___y_502_ = v_funDeclsImpure_528_;
goto v___jp_501_;
}
}
}
v___jp_529_:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_530_, v_fvarId_489_);
lean_dec_ref(v___y_530_);
if (lean_obj_tag(v___x_531_) == 1)
{
lean_object* v_val_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_540_; 
lean_dec_ref(v_lctx_513_);
lean_del_object(v___x_499_);
lean_dec(v_a_497_);
lean_dec(v_fvarId_489_);
v_val_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_540_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_540_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_val_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_540_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v_type_536_; lean_object* v___x_538_; 
v_type_536_ = lean_ctor_get(v_val_532_, 2);
lean_inc_ref(v_type_536_);
lean_dec(v_val_532_);
if (v_isShared_535_ == 0)
{
lean_ctor_set_tag(v___x_534_, 0);
lean_ctor_set(v___x_534_, 0, v_type_536_);
v___x_538_ = v___x_534_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_type_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
else
{
uint8_t v___x_541_; 
lean_dec(v___x_531_);
v___x_541_ = lean_unbox(v_a_497_);
if (v___x_541_ == 0)
{
lean_object* v_paramsPure_542_; 
v_paramsPure_542_ = lean_ctor_get(v_lctx_513_, 0);
lean_inc_ref(v_paramsPure_542_);
v___y_515_ = v_paramsPure_542_;
goto v___jp_514_;
}
else
{
lean_object* v_paramsImpure_543_; 
v_paramsImpure_543_ = lean_ctor_get(v_lctx_513_, 1);
lean_inc_ref(v_paramsImpure_543_);
v___y_515_ = v_paramsImpure_543_;
goto v___jp_514_;
}
}
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec(v___x_495_);
lean_dec(v_fvarId_489_);
v_a_548_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_496_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_496_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType___boxed(lean_object* v_fvarId_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Compiler_LCNF_getType(v_fvarId_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(lean_object* v_00_u03b2_563_, lean_object* v_m_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_564_, v_a_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(lean_object* v_00_u03b2_567_, lean_object* v_m_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(v_00_u03b2_567_, v_m_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_m_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(lean_object* v_00_u03b2_571_, lean_object* v_a_572_, lean_object* v_x_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_572_, v_x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_575_, lean_object* v_a_576_, lean_object* v_x_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(v_00_u03b2_575_, v_a_576_, v_x_577_);
lean_dec(v_x_577_);
lean_dec(v_a_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object* v_fvarId_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = lean_st_ref_get(v_a_581_);
v___x_586_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_580_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_637_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_637_ == 0)
{
v___x_589_ = v___x_586_;
v_isShared_590_ = v_isSharedCheck_637_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_637_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___y_592_; lean_object* v_lctx_603_; lean_object* v___y_605_; lean_object* v___y_620_; uint8_t v___x_634_; 
v_lctx_603_ = lean_ctor_get(v___x_585_, 0);
lean_inc_ref(v_lctx_603_);
lean_dec(v___x_585_);
v___x_634_ = lean_unbox(v_a_587_);
if (v___x_634_ == 0)
{
lean_object* v_letDeclsPure_635_; 
v_letDeclsPure_635_ = lean_ctor_get(v_lctx_603_, 2);
lean_inc_ref(v_letDeclsPure_635_);
v___y_620_ = v_letDeclsPure_635_;
goto v___jp_619_;
}
else
{
lean_object* v_letDeclsImpure_636_; 
v_letDeclsImpure_636_ = lean_ctor_get(v_lctx_603_, 3);
lean_inc_ref(v_letDeclsImpure_636_);
v___y_620_ = v_letDeclsImpure_636_;
goto v___jp_619_;
}
v___jp_591_:
{
lean_object* v___x_593_; 
v___x_593_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_592_, v_fvarId_579_);
lean_dec_ref(v___y_592_);
if (lean_obj_tag(v___x_593_) == 1)
{
lean_object* v_val_594_; lean_object* v_binderName_595_; lean_object* v___x_597_; 
lean_dec(v_fvarId_579_);
v_val_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_val_594_);
lean_dec_ref_known(v___x_593_, 1);
v_binderName_595_ = lean_ctor_get(v_val_594_, 1);
lean_inc(v_binderName_595_);
lean_dec(v_val_594_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v_binderName_595_);
v___x_597_ = v___x_589_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_binderName_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v___x_593_);
lean_del_object(v___x_589_);
v___x_599_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_600_ = l_Lean_MessageData_ofName(v_fvarId_579_);
v___x_601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_601_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
return v___x_602_;
}
}
v___jp_604_:
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_605_, v_fvarId_579_);
lean_dec_ref(v___y_605_);
if (lean_obj_tag(v___x_606_) == 1)
{
lean_object* v_val_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v_lctx_603_);
lean_del_object(v___x_589_);
lean_dec(v_a_587_);
lean_dec(v_fvarId_579_);
v_val_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_615_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_val_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v_binderName_611_; lean_object* v___x_613_; 
v_binderName_611_ = lean_ctor_get(v_val_607_, 1);
lean_inc(v_binderName_611_);
lean_dec(v_val_607_);
if (v_isShared_610_ == 0)
{
lean_ctor_set_tag(v___x_609_, 0);
lean_ctor_set(v___x_609_, 0, v_binderName_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_binderName_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
else
{
uint8_t v___x_616_; 
lean_dec(v___x_606_);
v___x_616_ = lean_unbox(v_a_587_);
lean_dec(v_a_587_);
if (v___x_616_ == 0)
{
lean_object* v_funDeclsPure_617_; 
v_funDeclsPure_617_ = lean_ctor_get(v_lctx_603_, 4);
lean_inc_ref(v_funDeclsPure_617_);
lean_dec_ref(v_lctx_603_);
v___y_592_ = v_funDeclsPure_617_;
goto v___jp_591_;
}
else
{
lean_object* v_funDeclsImpure_618_; 
v_funDeclsImpure_618_ = lean_ctor_get(v_lctx_603_, 5);
lean_inc_ref(v_funDeclsImpure_618_);
lean_dec_ref(v_lctx_603_);
v___y_592_ = v_funDeclsImpure_618_;
goto v___jp_591_;
}
}
}
v___jp_619_:
{
lean_object* v___x_621_; 
v___x_621_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_620_, v_fvarId_579_);
lean_dec_ref(v___y_620_);
if (lean_obj_tag(v___x_621_) == 1)
{
lean_object* v_val_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v_lctx_603_);
lean_del_object(v___x_589_);
lean_dec(v_a_587_);
lean_dec(v_fvarId_579_);
v_val_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_630_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_630_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_val_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_630_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v_binderName_626_; lean_object* v___x_628_; 
v_binderName_626_ = lean_ctor_get(v_val_622_, 1);
lean_inc(v_binderName_626_);
lean_dec(v_val_622_);
if (v_isShared_625_ == 0)
{
lean_ctor_set_tag(v___x_624_, 0);
lean_ctor_set(v___x_624_, 0, v_binderName_626_);
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_binderName_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
else
{
uint8_t v___x_631_; 
lean_dec(v___x_621_);
v___x_631_ = lean_unbox(v_a_587_);
if (v___x_631_ == 0)
{
lean_object* v_paramsPure_632_; 
v_paramsPure_632_ = lean_ctor_get(v_lctx_603_, 0);
lean_inc_ref(v_paramsPure_632_);
v___y_605_ = v_paramsPure_632_;
goto v___jp_604_;
}
else
{
lean_object* v_paramsImpure_633_; 
v_paramsImpure_633_ = lean_ctor_get(v_lctx_603_, 1);
lean_inc_ref(v_paramsImpure_633_);
v___y_605_ = v_paramsImpure_633_;
goto v___jp_604_;
}
}
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec(v___x_585_);
lean_dec(v_fvarId_579_);
v_a_638_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_586_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_586_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName___boxed(lean_object* v_fvarId_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t v_pu_653_, lean_object* v_fvarId_654_, lean_object* v_a_655_){
_start:
{
lean_object* v___x_657_; lean_object* v___y_659_; 
v___x_657_ = lean_st_ref_get(v_a_655_);
if (v_pu_653_ == 0)
{
lean_object* v_lctx_662_; lean_object* v_paramsPure_663_; 
v_lctx_662_ = lean_ctor_get(v___x_657_, 0);
lean_inc_ref(v_lctx_662_);
lean_dec(v___x_657_);
v_paramsPure_663_ = lean_ctor_get(v_lctx_662_, 0);
lean_inc_ref(v_paramsPure_663_);
lean_dec_ref(v_lctx_662_);
v___y_659_ = v_paramsPure_663_;
goto v___jp_658_;
}
else
{
lean_object* v_lctx_664_; lean_object* v_paramsImpure_665_; 
v_lctx_664_ = lean_ctor_get(v___x_657_, 0);
lean_inc_ref(v_lctx_664_);
lean_dec(v___x_657_);
v_paramsImpure_665_ = lean_ctor_get(v_lctx_664_, 1);
lean_inc_ref(v_paramsImpure_665_);
lean_dec_ref(v_lctx_664_);
v___y_659_ = v_paramsImpure_665_;
goto v___jp_658_;
}
v___jp_658_:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_659_, v_fvarId_654_);
lean_dec_ref(v___y_659_);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(lean_object* v_pu_666_, lean_object* v_fvarId_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
uint8_t v_pu_boxed_670_; lean_object* v_res_671_; 
v_pu_boxed_670_ = lean_unbox(v_pu_666_);
v_res_671_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_boxed_670_, v_fvarId_667_, v_a_668_);
lean_dec(v_a_668_);
lean_dec(v_fvarId_667_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f(uint8_t v_pu_672_, lean_object* v_fvarId_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_672_, v_fvarId_673_, v_a_675_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___boxed(lean_object* v_pu_680_, lean_object* v_fvarId_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
uint8_t v_pu_boxed_687_; lean_object* v_res_688_; 
v_pu_boxed_687_ = lean_unbox(v_pu_680_);
v_res_688_ = l_Lean_Compiler_LCNF_findParam_x3f(v_pu_boxed_687_, v_fvarId_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_fvarId_681_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t v_pu_689_, lean_object* v_fvarId_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___x_693_; lean_object* v___y_695_; 
v___x_693_ = lean_st_ref_get(v_a_691_);
if (v_pu_689_ == 0)
{
lean_object* v_lctx_698_; lean_object* v_letDeclsPure_699_; 
v_lctx_698_ = lean_ctor_get(v___x_693_, 0);
lean_inc_ref(v_lctx_698_);
lean_dec(v___x_693_);
v_letDeclsPure_699_ = lean_ctor_get(v_lctx_698_, 2);
lean_inc_ref(v_letDeclsPure_699_);
lean_dec_ref(v_lctx_698_);
v___y_695_ = v_letDeclsPure_699_;
goto v___jp_694_;
}
else
{
lean_object* v_lctx_700_; lean_object* v_letDeclsImpure_701_; 
v_lctx_700_ = lean_ctor_get(v___x_693_, 0);
lean_inc_ref(v_lctx_700_);
lean_dec(v___x_693_);
v_letDeclsImpure_701_ = lean_ctor_get(v_lctx_700_, 3);
lean_inc_ref(v_letDeclsImpure_701_);
lean_dec_ref(v_lctx_700_);
v___y_695_ = v_letDeclsImpure_701_;
goto v___jp_694_;
}
v___jp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_695_, v_fvarId_690_);
lean_dec_ref(v___y_695_);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(lean_object* v_pu_702_, lean_object* v_fvarId_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
uint8_t v_pu_boxed_706_; lean_object* v_res_707_; 
v_pu_boxed_706_ = lean_unbox(v_pu_702_);
v_res_707_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_boxed_706_, v_fvarId_703_, v_a_704_);
lean_dec(v_a_704_);
lean_dec(v_fvarId_703_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(uint8_t v_pu_708_, lean_object* v_fvarId_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_708_, v_fvarId_709_, v_a_711_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(lean_object* v_pu_716_, lean_object* v_fvarId_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
uint8_t v_pu_boxed_723_; lean_object* v_res_724_; 
v_pu_boxed_723_ = lean_unbox(v_pu_716_);
v_res_724_ = l_Lean_Compiler_LCNF_findLetDecl_x3f(v_pu_boxed_723_, v_fvarId_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_fvarId_717_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t v_pu_725_, lean_object* v_fvarId_726_, lean_object* v_a_727_){
_start:
{
lean_object* v___x_729_; lean_object* v___y_731_; 
v___x_729_ = lean_st_ref_get(v_a_727_);
if (v_pu_725_ == 0)
{
lean_object* v_lctx_734_; lean_object* v_funDeclsPure_735_; 
v_lctx_734_ = lean_ctor_get(v___x_729_, 0);
lean_inc_ref(v_lctx_734_);
lean_dec(v___x_729_);
v_funDeclsPure_735_ = lean_ctor_get(v_lctx_734_, 4);
lean_inc_ref(v_funDeclsPure_735_);
lean_dec_ref(v_lctx_734_);
v___y_731_ = v_funDeclsPure_735_;
goto v___jp_730_;
}
else
{
lean_object* v_lctx_736_; lean_object* v_funDeclsImpure_737_; 
v_lctx_736_ = lean_ctor_get(v___x_729_, 0);
lean_inc_ref(v_lctx_736_);
lean_dec(v___x_729_);
v_funDeclsImpure_737_ = lean_ctor_get(v_lctx_736_, 5);
lean_inc_ref(v_funDeclsImpure_737_);
lean_dec_ref(v_lctx_736_);
v___y_731_ = v_funDeclsImpure_737_;
goto v___jp_730_;
}
v___jp_730_:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_731_, v_fvarId_726_);
lean_dec_ref(v___y_731_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(lean_object* v_pu_738_, lean_object* v_fvarId_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
uint8_t v_pu_boxed_742_; lean_object* v_res_743_; 
v_pu_boxed_742_ = lean_unbox(v_pu_738_);
v_res_743_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_boxed_742_, v_fvarId_739_, v_a_740_);
lean_dec(v_a_740_);
lean_dec(v_fvarId_739_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(uint8_t v_pu_744_, lean_object* v_fvarId_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_744_, v_fvarId_745_, v_a_747_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(lean_object* v_pu_752_, lean_object* v_fvarId_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
uint8_t v_pu_boxed_759_; lean_object* v_res_760_; 
v_pu_boxed_759_ = lean_unbox(v_pu_752_);
v_res_760_ = l_Lean_Compiler_LCNF_findFunDecl_x3f(v_pu_boxed_759_, v_fvarId_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_fvarId_753_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t v_pu_761_, lean_object* v_fvarId_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_765_; lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_786_; 
v___x_765_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_761_, v_fvarId_762_, v_a_763_);
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_786_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_786_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_786_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
if (lean_obj_tag(v_a_766_) == 1)
{
lean_object* v_val_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_781_; 
v_val_770_ = lean_ctor_get(v_a_766_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v_a_766_);
if (v_isSharedCheck_781_ == 0)
{
v___x_772_ = v_a_766_;
v_isShared_773_ = v_isSharedCheck_781_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_val_770_);
lean_dec(v_a_766_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_781_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_value_774_; lean_object* v___x_776_; 
v_value_774_ = lean_ctor_get(v_val_770_, 3);
lean_inc(v_value_774_);
lean_dec(v_val_770_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v_value_774_);
v___x_776_ = v___x_772_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_value_774_);
v___x_776_ = v_reuseFailAlloc_780_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_778_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_776_);
v___x_778_ = v___x_768_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v___x_782_; lean_object* v___x_784_; 
lean_dec(v_a_766_);
v___x_782_ = lean_box(0);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_782_);
v___x_784_ = v___x_768_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg___boxed(lean_object* v_pu_787_, lean_object* v_fvarId_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
uint8_t v_pu_boxed_791_; lean_object* v_res_792_; 
v_pu_boxed_791_ = lean_unbox(v_pu_787_);
v_res_792_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_boxed_791_, v_fvarId_788_, v_a_789_);
lean_dec(v_a_789_);
lean_dec(v_fvarId_788_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f(uint8_t v_pu_793_, lean_object* v_fvarId_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_793_, v_fvarId_794_, v_a_796_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(lean_object* v_pu_801_, lean_object* v_fvarId_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
uint8_t v_pu_boxed_808_; lean_object* v_res_809_; 
v_pu_boxed_808_ = lean_unbox(v_pu_801_);
v_res_809_ = l_Lean_Compiler_LCNF_findLetValue_x3f(v_pu_boxed_808_, v_fvarId_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_fvarId_802_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg(lean_object* v_fvarId_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
uint8_t v___x_814_; lean_object* v___x_815_; 
v___x_814_ = 0;
v___x_815_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_814_, v_fvarId_810_, v_a_811_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_859_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_859_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_859_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_859_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
if (lean_obj_tag(v_a_816_) == 1)
{
lean_object* v_val_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_858_; 
v_val_826_ = lean_ctor_get(v_a_816_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v_a_816_);
if (v_isSharedCheck_858_ == 0)
{
v___x_828_ = v_a_816_;
v_isShared_829_ = v_isSharedCheck_858_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_val_826_);
lean_dec(v_a_816_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_858_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
if (lean_obj_tag(v_val_826_) == 3)
{
lean_object* v_declName_830_; lean_object* v___x_831_; lean_object* v_env_832_; uint8_t v___x_833_; lean_object* v___x_834_; 
lean_del_object(v___x_818_);
v_declName_830_ = lean_ctor_get(v_val_826_, 0);
lean_inc(v_declName_830_);
lean_dec_ref_known(v_val_826_, 3);
v___x_831_ = lean_st_ref_get(v_a_812_);
v_env_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc_ref(v_env_832_);
lean_dec(v___x_831_);
v___x_833_ = 0;
v___x_834_ = l_Lean_Environment_find_x3f(v_env_832_, v_declName_830_, v___x_833_);
if (lean_obj_tag(v___x_834_) == 1)
{
lean_object* v_val_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_853_; 
lean_del_object(v___x_828_);
v_val_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_853_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_853_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_val_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_853_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
if (lean_obj_tag(v_val_835_) == 6)
{
lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_847_; 
lean_del_object(v___x_837_);
v_isSharedCheck_847_ = !lean_is_exclusive(v_val_835_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; 
v_unused_848_ = lean_ctor_get(v_val_835_, 0);
lean_dec(v_unused_848_);
v___x_840_ = v_val_835_;
v_isShared_841_ = v_isSharedCheck_847_;
goto v_resetjp_839_;
}
else
{
lean_dec(v_val_835_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_847_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
uint8_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_842_ = 1;
v___x_843_ = lean_box(v___x_842_);
if (v_isShared_841_ == 0)
{
lean_ctor_set_tag(v___x_840_, 0);
lean_ctor_set(v___x_840_, 0, v___x_843_);
v___x_845_ = v___x_840_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
else
{
lean_object* v___x_849_; lean_object* v___x_851_; 
lean_dec(v_val_835_);
v___x_849_ = lean_box(v___x_833_);
if (v_isShared_838_ == 0)
{
lean_ctor_set_tag(v___x_837_, 0);
lean_ctor_set(v___x_837_, 0, v___x_849_);
v___x_851_ = v___x_837_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
else
{
lean_object* v___x_854_; lean_object* v___x_856_; 
lean_dec(v___x_834_);
v___x_854_ = lean_box(v___x_833_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 0);
lean_ctor_set(v___x_828_, 0, v___x_854_);
v___x_856_ = v___x_828_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
else
{
lean_del_object(v___x_828_);
lean_dec(v_val_826_);
goto v___jp_820_;
}
}
}
else
{
lean_dec(v_a_816_);
goto v___jp_820_;
}
v___jp_820_:
{
uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_821_ = 0;
v___x_822_ = lean_box(v___x_821_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_822_);
v___x_824_ = v___x_818_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
v_a_860_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_815_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_815_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg___boxed(lean_object* v_fvarId_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_868_, v_a_869_, v_a_870_);
lean_dec(v_a_870_);
lean_dec(v_a_869_);
lean_dec(v_fvarId_868_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp(lean_object* v_fvarId_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_873_, v_a_875_, v_a_877_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___boxed(lean_object* v_fvarId_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_Compiler_LCNF_isConstructorApp(v_fvarId_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_fvarId_880_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object* v_arg_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
if (lean_obj_tag(v_arg_887_) == 1)
{
lean_object* v_fvarId_891_; lean_object* v___x_892_; 
v_fvarId_891_ = lean_ctor_get(v_arg_887_, 0);
v___x_892_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_891_, v_a_888_, v_a_889_);
return v___x_892_;
}
else
{
uint8_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = 0;
v___x_894_ = lean_box(v___x_893_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(lean_object* v_arg_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_896_, v_a_897_, v_a_898_);
lean_dec(v_a_898_);
lean_dec(v_a_897_);
lean_dec(v_arg_896_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp(uint8_t v_pu_901_, lean_object* v_arg_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_902_, v_a_904_, v_a_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(lean_object* v_pu_909_, lean_object* v_arg_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
uint8_t v_pu_boxed_916_; lean_object* v_res_917_; 
v_pu_boxed_916_ = lean_unbox(v_pu_909_);
v_res_917_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp(v_pu_boxed_916_, v_arg_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_arg_910_);
return v_res_917_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getParam___closed__1(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParam___closed__0));
v___x_920_ = l_Lean_stringToMessageData(v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam(uint8_t v_pu_921_, lean_object* v_fvarId_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_928_; lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_941_; 
v___x_928_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_921_, v_fvarId_922_, v_a_924_);
v_a_929_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_941_ == 0)
{
v___x_931_ = v___x_928_;
v_isShared_932_ = v_isSharedCheck_941_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_928_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_941_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
if (lean_obj_tag(v_a_929_) == 1)
{
lean_object* v_val_933_; lean_object* v___x_935_; 
lean_dec(v_fvarId_922_);
v_val_933_ = lean_ctor_get(v_a_929_, 0);
lean_inc(v_val_933_);
lean_dec_ref_known(v_a_929_, 1);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v_val_933_);
v___x_935_ = v___x_931_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_val_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
lean_del_object(v___x_931_);
lean_dec(v_a_929_);
v___x_937_ = lean_obj_once(&l_Lean_Compiler_LCNF_getParam___closed__1, &l_Lean_Compiler_LCNF_getParam___closed__1_once, _init_l_Lean_Compiler_LCNF_getParam___closed__1);
v___x_938_ = l_Lean_MessageData_ofName(v_fvarId_922_);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_939_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
return v___x_940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam___boxed(lean_object* v_pu_942_, lean_object* v_fvarId_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
uint8_t v_pu_boxed_949_; lean_object* v_res_950_; 
v_pu_boxed_949_ = lean_unbox(v_pu_942_);
v_res_950_ = l_Lean_Compiler_LCNF_getParam(v_pu_boxed_949_, v_fvarId_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
return v_res_950_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l_Lean_Compiler_LCNF_getLetDecl___closed__0));
v___x_953_ = l_Lean_stringToMessageData(v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl(uint8_t v_pu_954_, lean_object* v_fvarId_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v___x_961_; lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_974_; 
v___x_961_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_954_, v_fvarId_955_, v_a_957_);
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_974_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_974_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_974_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
if (lean_obj_tag(v_a_962_) == 1)
{
lean_object* v_val_966_; lean_object* v___x_968_; 
lean_dec(v_fvarId_955_);
v_val_966_ = lean_ctor_get(v_a_962_, 0);
lean_inc(v_val_966_);
lean_dec_ref_known(v_a_962_, 1);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v_val_966_);
v___x_968_ = v___x_964_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_val_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
lean_del_object(v___x_964_);
lean_dec(v_a_962_);
v___x_970_ = lean_obj_once(&l_Lean_Compiler_LCNF_getLetDecl___closed__1, &l_Lean_Compiler_LCNF_getLetDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1);
v___x_971_ = l_Lean_MessageData_ofName(v_fvarId_955_);
v___x_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_972_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
return v___x_973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl___boxed(lean_object* v_pu_975_, lean_object* v_fvarId_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
uint8_t v_pu_boxed_982_; lean_object* v_res_983_; 
v_pu_boxed_982_ = lean_unbox(v_pu_975_);
v_res_983_ = l_Lean_Compiler_LCNF_getLetDecl(v_pu_boxed_982_, v_fvarId_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
return v_res_983_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l_Lean_Compiler_LCNF_getFunDecl___closed__0));
v___x_986_ = l_Lean_stringToMessageData(v___x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t v_pu_987_, lean_object* v_fvarId_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v___x_994_; lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1007_; 
v___x_994_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_987_, v_fvarId_988_, v_a_990_);
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1007_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1007_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
if (lean_obj_tag(v_a_995_) == 1)
{
lean_object* v_val_999_; lean_object* v___x_1001_; 
lean_dec(v_fvarId_988_);
v_val_999_ = lean_ctor_get(v_a_995_, 0);
lean_inc(v_val_999_);
lean_dec_ref_known(v_a_995_, 1);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v_val_999_);
v___x_1001_ = v___x_997_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_val_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_del_object(v___x_997_);
lean_dec(v_a_995_);
v___x_1003_ = lean_obj_once(&l_Lean_Compiler_LCNF_getFunDecl___closed__1, &l_Lean_Compiler_LCNF_getFunDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1);
v___x_1004_ = l_Lean_MessageData_ofName(v_fvarId_988_);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_1005_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
return v___x_1006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl___boxed(lean_object* v_pu_1008_, lean_object* v_fvarId_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
uint8_t v_pu_boxed_1015_; lean_object* v_res_1016_; 
v_pu_boxed_1015_ = lean_unbox(v_pu_1008_);
v_res_1016_ = l_Lean_Compiler_LCNF_getFunDecl(v_pu_boxed_1015_, v_fvarId_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg(lean_object* v_f_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v___x_1020_; lean_object* v_lctx_1021_; lean_object* v_nextIdx_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1033_; 
v___x_1020_ = lean_st_ref_take(v_a_1018_);
v_lctx_1021_ = lean_ctor_get(v___x_1020_, 0);
v_nextIdx_1022_ = lean_ctor_get(v___x_1020_, 1);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1024_ = v___x_1020_;
v_isShared_1025_ = v_isSharedCheck_1033_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_nextIdx_1022_);
lean_inc(v_lctx_1021_);
lean_dec(v___x_1020_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1033_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = lean_apply_1(v_f_1017_, v_lctx_1021_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1026_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_nextIdx_1022_);
v___x_1028_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = lean_st_ref_set(v_a_1018_, v___x_1028_);
v___x_1030_ = lean_box(0);
v___x_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
return v___x_1031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(lean_object* v_f_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Compiler_LCNF_modifyLCtx___redArg(v_f_1034_, v_a_1035_);
lean_dec(v_a_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx(lean_object* v_f_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v___x_1044_; lean_object* v_lctx_1045_; lean_object* v_nextIdx_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1057_; 
v___x_1044_ = lean_st_ref_take(v_a_1040_);
v_lctx_1045_ = lean_ctor_get(v___x_1044_, 0);
v_nextIdx_1046_ = lean_ctor_get(v___x_1044_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1048_ = v___x_1044_;
v_isShared_1049_ = v_isSharedCheck_1057_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_nextIdx_1046_);
lean_inc(v_lctx_1045_);
lean_dec(v___x_1044_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1057_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1050_ = lean_apply_1(v_f_1038_, v_lctx_1045_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1050_);
v___x_1052_ = v___x_1048_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_nextIdx_1046_);
v___x_1052_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1053_ = lean_st_ref_set(v_a_1040_, v___x_1052_);
v___x_1054_ = lean_box(0);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___boxed(lean_object* v_f_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_Compiler_LCNF_modifyLCtx(v_f_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t v_pu_1065_, lean_object* v_decl_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v___x_1069_; lean_object* v_lctx_1070_; lean_object* v_nextIdx_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1082_; 
v___x_1069_ = lean_st_ref_take(v_a_1067_);
v_lctx_1070_ = lean_ctor_get(v___x_1069_, 0);
v_nextIdx_1071_ = lean_ctor_get(v___x_1069_, 1);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1073_ = v___x_1069_;
v_isShared_1074_ = v_isSharedCheck_1082_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_nextIdx_1071_);
lean_inc(v_lctx_1070_);
lean_dec(v___x_1069_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1082_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1075_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_1065_, v_lctx_1070_, v_decl_1066_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1075_);
v___x_1077_ = v___x_1073_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_nextIdx_1071_);
v___x_1077_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = lean_st_ref_set(v_a_1067_, v___x_1077_);
v___x_1079_ = lean_box(0);
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(lean_object* v_pu_1083_, lean_object* v_decl_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
uint8_t v_pu_boxed_1087_; lean_object* v_res_1088_; 
v_pu_boxed_1087_ = lean_unbox(v_pu_1083_);
v_res_1088_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_boxed_1087_, v_decl_1084_, v_a_1085_);
lean_dec(v_a_1085_);
lean_dec_ref(v_decl_1084_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(uint8_t v_pu_1089_, lean_object* v_decl_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1089_, v_decl_1090_, v_a_1092_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___boxed(lean_object* v_pu_1097_, lean_object* v_decl_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_){
_start:
{
uint8_t v_pu_boxed_1104_; lean_object* v_res_1105_; 
v_pu_boxed_1104_ = lean_unbox(v_pu_1097_);
v_res_1105_ = l_Lean_Compiler_LCNF_eraseLetDecl(v_pu_boxed_1104_, v_decl_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec_ref(v_decl_1098_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t v_pu_1106_, lean_object* v_decl_1107_, uint8_t v_recursive_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v___x_1111_; lean_object* v_lctx_1112_; lean_object* v_nextIdx_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1124_; 
v___x_1111_ = lean_st_ref_take(v_a_1109_);
v_lctx_1112_ = lean_ctor_get(v___x_1111_, 0);
v_nextIdx_1113_ = lean_ctor_get(v___x_1111_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1115_ = v___x_1111_;
v_isShared_1116_ = v_isSharedCheck_1124_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_nextIdx_1113_);
lean_inc(v_lctx_1112_);
lean_dec(v___x_1111_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1124_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1117_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_1106_, v_lctx_1112_, v_decl_1107_, v_recursive_1108_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1117_);
v___x_1119_ = v___x_1115_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_nextIdx_1113_);
v___x_1119_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = lean_st_ref_set(v_a_1109_, v___x_1119_);
v___x_1121_ = lean_box(0);
v___x_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
return v___x_1122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(lean_object* v_pu_1125_, lean_object* v_decl_1126_, lean_object* v_recursive_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
uint8_t v_pu_boxed_1130_; uint8_t v_recursive_boxed_1131_; lean_object* v_res_1132_; 
v_pu_boxed_1130_ = lean_unbox(v_pu_1125_);
v_recursive_boxed_1131_ = lean_unbox(v_recursive_1127_);
v_res_1132_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_boxed_1130_, v_decl_1126_, v_recursive_boxed_1131_, v_a_1128_);
lean_dec(v_a_1128_);
lean_dec_ref(v_decl_1126_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(uint8_t v_pu_1133_, lean_object* v_decl_1134_, uint8_t v_recursive_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1133_, v_decl_1134_, v_recursive_1135_, v_a_1137_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___boxed(lean_object* v_pu_1142_, lean_object* v_decl_1143_, lean_object* v_recursive_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
uint8_t v_pu_boxed_1150_; uint8_t v_recursive_boxed_1151_; lean_object* v_res_1152_; 
v_pu_boxed_1150_ = lean_unbox(v_pu_1142_);
v_recursive_boxed_1151_ = lean_unbox(v_recursive_1144_);
v_res_1152_ = l_Lean_Compiler_LCNF_eraseFunDecl(v_pu_boxed_1150_, v_decl_1143_, v_recursive_boxed_1151_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec_ref(v_decl_1143_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t v_pu_1153_, lean_object* v_code_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___x_1157_; lean_object* v_lctx_1158_; lean_object* v_nextIdx_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1170_; 
v___x_1157_ = lean_st_ref_take(v_a_1155_);
v_lctx_1158_ = lean_ctor_get(v___x_1157_, 0);
v_nextIdx_1159_ = lean_ctor_get(v___x_1157_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1161_ = v___x_1157_;
v_isShared_1162_ = v_isSharedCheck_1170_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_nextIdx_1159_);
lean_inc(v_lctx_1158_);
lean_dec(v___x_1157_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1170_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1163_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1153_, v_code_1154_, v_lctx_1158_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1163_);
v___x_1165_ = v___x_1161_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_nextIdx_1159_);
v___x_1165_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = lean_st_ref_set(v_a_1155_, v___x_1165_);
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(lean_object* v_pu_1171_, lean_object* v_code_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
uint8_t v_pu_boxed_1175_; lean_object* v_res_1176_; 
v_pu_boxed_1175_ = lean_unbox(v_pu_1171_);
v_res_1176_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_boxed_1175_, v_code_1172_, v_a_1173_);
lean_dec(v_a_1173_);
lean_dec_ref(v_code_1172_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode(uint8_t v_pu_1177_, lean_object* v_code_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_1177_, v_code_1178_, v_a_1180_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___boxed(lean_object* v_pu_1185_, lean_object* v_code_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
uint8_t v_pu_boxed_1192_; lean_object* v_res_1193_; 
v_pu_boxed_1192_ = lean_unbox(v_pu_1185_);
v_res_1193_ = l_Lean_Compiler_LCNF_eraseCode(v_pu_boxed_1192_, v_code_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec_ref(v_code_1186_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t v_pu_1194_, lean_object* v_param_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v___x_1198_; lean_object* v_lctx_1199_; lean_object* v_nextIdx_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1211_; 
v___x_1198_ = lean_st_ref_take(v_a_1196_);
v_lctx_1199_ = lean_ctor_get(v___x_1198_, 0);
v_nextIdx_1200_ = lean_ctor_get(v___x_1198_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1202_ = v___x_1198_;
v_isShared_1203_ = v_isSharedCheck_1211_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_nextIdx_1200_);
lean_inc(v_lctx_1199_);
lean_dec(v___x_1198_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1211_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1204_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_1194_, v_lctx_1199_, v_param_1195_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1204_);
v___x_1206_ = v___x_1202_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_nextIdx_1200_);
v___x_1206_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = lean_st_ref_set(v_a_1196_, v___x_1206_);
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(lean_object* v_pu_1212_, lean_object* v_param_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
uint8_t v_pu_boxed_1216_; lean_object* v_res_1217_; 
v_pu_boxed_1216_ = lean_unbox(v_pu_1212_);
v_res_1217_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_boxed_1216_, v_param_1213_, v_a_1214_);
lean_dec(v_a_1214_);
lean_dec_ref(v_param_1213_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam(uint8_t v_pu_1218_, lean_object* v_param_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_1218_, v_param_1219_, v_a_1221_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___boxed(lean_object* v_pu_1226_, lean_object* v_param_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
uint8_t v_pu_boxed_1233_; lean_object* v_res_1234_; 
v_pu_boxed_1233_ = lean_unbox(v_pu_1226_);
v_res_1234_ = l_Lean_Compiler_LCNF_eraseParam(v_pu_boxed_1233_, v_param_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec_ref(v_param_1227_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t v_pu_1235_, lean_object* v_params_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v___x_1239_; lean_object* v_lctx_1240_; lean_object* v_nextIdx_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1252_; 
v___x_1239_ = lean_st_ref_take(v_a_1237_);
v_lctx_1240_ = lean_ctor_get(v___x_1239_, 0);
v_nextIdx_1241_ = lean_ctor_get(v___x_1239_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1243_ = v___x_1239_;
v_isShared_1244_ = v_isSharedCheck_1252_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_nextIdx_1241_);
lean_inc(v_lctx_1240_);
lean_dec(v___x_1239_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1252_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1245_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_1235_, v_lctx_1240_, v_params_1236_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1245_);
v___x_1247_ = v___x_1243_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1245_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_nextIdx_1241_);
v___x_1247_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = lean_st_ref_set(v_a_1237_, v___x_1247_);
v___x_1249_ = lean_box(0);
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(lean_object* v_pu_1253_, lean_object* v_params_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_){
_start:
{
uint8_t v_pu_boxed_1257_; lean_object* v_res_1258_; 
v_pu_boxed_1257_ = lean_unbox(v_pu_1253_);
v_res_1258_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_boxed_1257_, v_params_1254_, v_a_1255_);
lean_dec(v_a_1255_);
lean_dec_ref(v_params_1254_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams(uint8_t v_pu_1259_, lean_object* v_params_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1259_, v_params_1260_, v_a_1262_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___boxed(lean_object* v_pu_1267_, lean_object* v_params_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
uint8_t v_pu_boxed_1274_; lean_object* v_res_1275_; 
v_pu_boxed_1274_ = lean_unbox(v_pu_1267_);
v_res_1275_ = l_Lean_Compiler_LCNF_eraseParams(v_pu_boxed_1274_, v_params_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec_ref(v_params_1268_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t v_pu_1276_, lean_object* v_decl_1277_, lean_object* v_a_1278_){
_start:
{
switch(lean_obj_tag(v_decl_1277_))
{
case 0:
{
lean_object* v_decl_1280_; lean_object* v___x_1281_; 
v_decl_1280_ = lean_ctor_get(v_decl_1277_, 0);
v___x_1281_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1276_, v_decl_1280_, v_a_1278_);
return v___x_1281_;
}
case 1:
{
lean_object* v_decl_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; 
v_decl_1282_ = lean_ctor_get(v_decl_1277_, 0);
v___x_1283_ = 1;
v___x_1284_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1276_, v_decl_1282_, v___x_1283_, v_a_1278_);
return v___x_1284_;
}
case 2:
{
lean_object* v_decl_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; 
v_decl_1285_ = lean_ctor_get(v_decl_1277_, 0);
v___x_1286_ = 1;
v___x_1287_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1276_, v_decl_1285_, v___x_1286_, v_a_1278_);
return v___x_1287_;
}
default: 
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_box(0);
v___x_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
return v___x_1289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(lean_object* v_pu_1290_, lean_object* v_decl_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
uint8_t v_pu_boxed_1294_; lean_object* v_res_1295_; 
v_pu_boxed_1294_ = lean_unbox(v_pu_1290_);
v_res_1295_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_boxed_1294_, v_decl_1291_, v_a_1292_);
lean_dec(v_a_1292_);
lean_dec_ref(v_decl_1291_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(uint8_t v_pu_1296_, lean_object* v_decl_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1296_, v_decl_1297_, v_a_1299_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(lean_object* v_pu_1304_, lean_object* v_decl_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
uint8_t v_pu_boxed_1311_; lean_object* v_res_1312_; 
v_pu_boxed_1311_ = lean_unbox(v_pu_1304_);
v_res_1312_ = l_Lean_Compiler_LCNF_eraseCodeDecl(v_pu_boxed_1311_, v_decl_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec_ref(v_decl_1305_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(uint8_t v_pu_1313_, lean_object* v_as_1314_, size_t v_i_1315_, size_t v_stop_1316_, lean_object* v_b_1317_, lean_object* v___y_1318_){
_start:
{
uint8_t v___x_1320_; 
v___x_1320_ = lean_usize_dec_eq(v_i_1315_, v_stop_1316_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = lean_array_uget_borrowed(v_as_1314_, v_i_1315_);
v___x_1322_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1313_, v___x_1321_, v___y_1318_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; size_t v___x_1324_; size_t v___x_1325_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
lean_dec_ref_known(v___x_1322_, 1);
v___x_1324_ = ((size_t)1ULL);
v___x_1325_ = lean_usize_add(v_i_1315_, v___x_1324_);
v_i_1315_ = v___x_1325_;
v_b_1317_ = v_a_1323_;
goto _start;
}
else
{
return v___x_1322_;
}
}
else
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1327_, 0, v_b_1317_);
return v___x_1327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(lean_object* v_pu_1328_, lean_object* v_as_1329_, lean_object* v_i_1330_, lean_object* v_stop_1331_, lean_object* v_b_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
uint8_t v_pu_boxed_1335_; size_t v_i_boxed_1336_; size_t v_stop_boxed_1337_; lean_object* v_res_1338_; 
v_pu_boxed_1335_ = lean_unbox(v_pu_1328_);
v_i_boxed_1336_ = lean_unbox_usize(v_i_1330_);
lean_dec(v_i_1330_);
v_stop_boxed_1337_ = lean_unbox_usize(v_stop_1331_);
lean_dec(v_stop_1331_);
v_res_1338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_boxed_1335_, v_as_1329_, v_i_boxed_1336_, v_stop_boxed_1337_, v_b_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v_as_1329_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(uint8_t v_pu_1339_, lean_object* v_decls_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1346_ = lean_unsigned_to_nat(0u);
v___x_1347_ = lean_array_get_size(v_decls_1340_);
v___x_1348_ = lean_box(0);
v___x_1349_ = lean_nat_dec_lt(v___x_1346_, v___x_1347_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
return v___x_1350_;
}
else
{
uint8_t v___x_1351_; 
v___x_1351_ = lean_nat_dec_le(v___x_1347_, v___x_1347_);
if (v___x_1351_ == 0)
{
if (v___x_1349_ == 0)
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1348_);
return v___x_1352_;
}
else
{
size_t v___x_1353_; size_t v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = ((size_t)0ULL);
v___x_1354_ = lean_usize_of_nat(v___x_1347_);
v___x_1355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1339_, v_decls_1340_, v___x_1353_, v___x_1354_, v___x_1348_, v_a_1342_);
return v___x_1355_;
}
}
else
{
size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = ((size_t)0ULL);
v___x_1357_ = lean_usize_of_nat(v___x_1347_);
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1339_, v_decls_1340_, v___x_1356_, v___x_1357_, v___x_1348_, v_a_1342_);
return v___x_1358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(lean_object* v_pu_1359_, lean_object* v_decls_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
uint8_t v_pu_boxed_1366_; lean_object* v_res_1367_; 
v_pu_boxed_1366_ = lean_unbox(v_pu_1359_);
v_res_1367_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v_pu_boxed_1366_, v_decls_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec_ref(v_decls_1360_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(uint8_t v_pu_1368_, lean_object* v_as_1369_, size_t v_i_1370_, size_t v_stop_1371_, lean_object* v_b_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1368_, v_as_1369_, v_i_1370_, v_stop_1371_, v_b_1372_, v___y_1374_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(lean_object* v_pu_1379_, lean_object* v_as_1380_, lean_object* v_i_1381_, lean_object* v_stop_1382_, lean_object* v_b_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
uint8_t v_pu_boxed_1389_; size_t v_i_boxed_1390_; size_t v_stop_boxed_1391_; lean_object* v_res_1392_; 
v_pu_boxed_1389_ = lean_unbox(v_pu_1379_);
v_i_boxed_1390_ = lean_unbox_usize(v_i_1381_);
lean_dec(v_i_1381_);
v_stop_boxed_1391_ = lean_unbox_usize(v_stop_1382_);
lean_dec(v_stop_1382_);
v_res_1392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(v_pu_boxed_1389_, v_as_1380_, v_i_boxed_1390_, v_stop_boxed_1391_, v_b_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec_ref(v_as_1380_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(lean_object* v_f_1393_, lean_object* v_v_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
if (lean_obj_tag(v_v_1394_) == 0)
{
lean_object* v_code_1400_; lean_object* v___x_1401_; 
v_code_1400_ = lean_ctor_get(v_v_1394_, 0);
lean_inc_ref(v_code_1400_);
lean_dec_ref_known(v_v_1394_, 1);
lean_inc(v___y_1398_);
lean_inc_ref(v___y_1397_);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
v___x_1401_ = lean_apply_6(v_f_1393_, v_code_1400_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, lean_box(0));
return v___x_1401_;
}
else
{
lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1409_; 
lean_dec_ref(v_f_1393_);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_v_1394_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; 
v_unused_1410_ = lean_ctor_get(v_v_1394_, 0);
lean_dec(v_unused_1410_);
v___x_1403_ = v_v_1394_;
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
else
{
lean_dec(v_v_1394_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1405_ = lean_box(0);
if (v_isShared_1404_ == 0)
{
lean_ctor_set_tag(v___x_1403_, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1405_);
v___x_1407_ = v___x_1403_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg___boxed(lean_object* v_f_1411_, lean_object* v_v_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1411_, v_v_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(uint8_t v_pu_1419_, lean_object* v_f_1420_, lean_object* v_v_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1420_, v_v_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(lean_object* v_pu_1428_, lean_object* v_f_1429_, lean_object* v_v_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
uint8_t v_pu_boxed_1436_; lean_object* v_res_1437_; 
v_pu_boxed_1436_ = lean_unbox(v_pu_1428_);
v_res_1437_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(v_pu_boxed_1436_, v_f_1429_, v_v_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t v_pu_1438_, lean_object* v_decl_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v_toSignature_1445_; lean_object* v_value_1446_; lean_object* v_params_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v_toSignature_1445_ = lean_ctor_get(v_decl_1439_, 0);
lean_inc_ref(v_toSignature_1445_);
v_value_1446_ = lean_ctor_get(v_decl_1439_, 1);
lean_inc_ref(v_value_1446_);
lean_dec_ref(v_decl_1439_);
v_params_1447_ = lean_ctor_get(v_toSignature_1445_, 3);
lean_inc_ref(v_params_1447_);
lean_dec_ref(v_toSignature_1445_);
v___x_1448_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1438_, v_params_1447_, v_a_1441_);
lean_dec_ref(v_params_1447_);
lean_dec_ref(v___x_1448_);
v___x_1449_ = lean_box(v_pu_1438_);
v___x_1450_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_eraseCode___boxed), 7, 1);
lean_closure_set(v___x_1450_, 0, v___x_1449_);
v___x_1451_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v___x_1450_, v_value_1446_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl___boxed(lean_object* v_pu_1452_, lean_object* v_decl_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_){
_start:
{
uint8_t v_pu_boxed_1459_; lean_object* v_res_1460_; 
v_pu_boxed_1459_ = lean_unbox(v_pu_1452_);
v_res_1460_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_boxed_1459_, v_decl_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase(uint8_t v_pu_1461_, lean_object* v_decl_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_1461_, v_decl_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase___boxed(lean_object* v_pu_1469_, lean_object* v_decl_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
uint8_t v_pu_boxed_1476_; lean_object* v_res_1477_; 
v_pu_boxed_1476_ = lean_unbox(v_pu_1469_);
v_res_1477_ = l_Lean_Compiler_LCNF_Decl_erase(v_pu_boxed_1476_, v_decl_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(lean_object* v_msg_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = l_Lean_instInhabitedExpr;
v___x_1480_ = lean_panic_fn_borrowed(v___x_1479_, v_msg_1478_);
return v___x_1480_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1484_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2));
v___x_1485_ = lean_unsigned_to_nat(20u);
v___x_1486_ = lean_unsigned_to_nat(215u);
v___x_1487_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1));
v___x_1488_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0));
v___x_1489_ = l_mkPanicMessageWithDecl(v___x_1488_, v___x_1487_, v___x_1486_, v___x_1485_, v___x_1484_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t v_pu_1490_, lean_object* v_s_1491_, uint8_t v_translator_1492_, lean_object* v_e_1493_){
_start:
{
uint8_t v___x_1494_; 
v___x_1494_ = l_Lean_Expr_hasFVar(v_e_1493_);
if (v___x_1494_ == 0)
{
return v_e_1493_;
}
else
{
switch(lean_obj_tag(v_e_1493_))
{
case 1:
{
lean_object* v_fvarId_1495_; lean_object* v___x_1496_; 
v_fvarId_1495_ = lean_ctor_get(v_e_1493_, 0);
v___x_1496_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1491_, v_fvarId_1495_);
if (lean_obj_tag(v___x_1496_) == 0)
{
return v_e_1493_;
}
else
{
lean_object* v_val_1497_; 
lean_dec_ref_known(v_e_1493_, 1);
v_val_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_val_1497_);
lean_dec_ref_known(v___x_1496_, 1);
switch(lean_obj_tag(v_val_1497_))
{
case 0:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Lean_Compiler_LCNF_erasedExpr;
return v___x_1498_;
}
case 1:
{
if (v_translator_1492_ == 0)
{
lean_object* v_fvarId_1499_; lean_object* v___x_1500_; 
v_fvarId_1499_ = lean_ctor_get(v_val_1497_, 0);
lean_inc(v_fvarId_1499_);
lean_dec_ref_known(v_val_1497_, 1);
v___x_1500_ = l_Lean_Expr_fvar___override(v_fvarId_1499_);
v_e_1493_ = v___x_1500_;
goto _start;
}
else
{
lean_object* v_fvarId_1502_; lean_object* v___x_1503_; 
v_fvarId_1502_ = lean_ctor_get(v_val_1497_, 0);
lean_inc(v_fvarId_1502_);
lean_dec_ref_known(v_val_1497_, 1);
v___x_1503_ = l_Lean_Expr_fvar___override(v_fvarId_1502_);
return v___x_1503_;
}
}
default: 
{
if (v_translator_1492_ == 0)
{
lean_object* v_expr_1504_; 
v_expr_1504_ = lean_ctor_get(v_val_1497_, 0);
lean_inc_ref(v_expr_1504_);
lean_dec_ref_known(v_val_1497_, 1);
v_e_1493_ = v_expr_1504_;
goto _start;
}
else
{
lean_object* v_expr_1506_; 
v_expr_1506_ = lean_ctor_get(v_val_1497_, 0);
lean_inc_ref(v_expr_1506_);
lean_dec_ref_known(v_val_1497_, 1);
return v_expr_1506_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_1507_; lean_object* v_arg_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___y_1512_; size_t v___x_1516_; size_t v___x_1517_; uint8_t v___x_1518_; 
v_fn_1507_ = lean_ctor_get(v_e_1493_, 0);
v_arg_1508_ = lean_ctor_get(v_e_1493_, 1);
lean_inc_ref(v_fn_1507_);
v___x_1509_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1490_, v_s_1491_, v_translator_1492_, v_fn_1507_);
lean_inc_ref(v_arg_1508_);
v___x_1510_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1490_, v_s_1491_, v_translator_1492_, v_arg_1508_);
v___x_1516_ = lean_ptr_addr(v_fn_1507_);
v___x_1517_ = lean_ptr_addr(v___x_1509_);
v___x_1518_ = lean_usize_dec_eq(v___x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
v___y_1512_ = v___x_1518_;
goto v___jp_1511_;
}
else
{
size_t v___x_1519_; size_t v___x_1520_; uint8_t v___x_1521_; 
v___x_1519_ = lean_ptr_addr(v_arg_1508_);
v___x_1520_ = lean_ptr_addr(v___x_1510_);
v___x_1521_ = lean_usize_dec_eq(v___x_1519_, v___x_1520_);
v___y_1512_ = v___x_1521_;
goto v___jp_1511_;
}
v___jp_1511_:
{
if (v___y_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec_ref_known(v_e_1493_, 2);
v___x_1513_ = l_Lean_Expr_app___override(v___x_1509_, v___x_1510_);
v___x_1514_ = l_Lean_Expr_headBeta(v___x_1513_);
return v___x_1514_;
}
else
{
lean_object* v___x_1515_; 
lean_dec_ref(v___x_1510_);
lean_dec_ref(v___x_1509_);
v___x_1515_ = l_Lean_Expr_headBeta(v_e_1493_);
return v___x_1515_;
}
}
}
case 6:
{
lean_object* v_binderName_1522_; lean_object* v_binderType_1523_; lean_object* v_body_1524_; uint8_t v_binderInfo_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___y_1529_; size_t v___x_1533_; size_t v___x_1534_; uint8_t v___x_1535_; 
v_binderName_1522_ = lean_ctor_get(v_e_1493_, 0);
v_binderType_1523_ = lean_ctor_get(v_e_1493_, 1);
v_body_1524_ = lean_ctor_get(v_e_1493_, 2);
v_binderInfo_1525_ = lean_ctor_get_uint8(v_e_1493_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1523_);
v___x_1526_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1490_, v_s_1491_, v_translator_1492_, v_binderType_1523_);
lean_inc_ref(v_body_1524_);
v___x_1527_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1490_, v_s_1491_, v_translator_1492_, v_body_1524_);
v___x_1533_ = lean_ptr_addr(v_binderType_1523_);
v___x_1534_ = lean_ptr_addr(v___x_1526_);
v___x_1535_ = lean_usize_dec_eq(v___x_1533_, v___x_1534_);
if (v___x_1535_ == 0)
{
v___y_1529_ = v___x_1535_;
goto v___jp_1528_;
}
else
{
size_t v___x_1536_; size_t v___x_1537_; uint8_t v___x_1538_; 
v___x_1536_ = lean_ptr_addr(v_body_1524_);
v___x_1537_ = lean_ptr_addr(v___x_1527_);
v___x_1538_ = lean_usize_dec_eq(v___x_1536_, v___x_1537_);
v___y_1529_ = v___x_1538_;
goto v___jp_1528_;
}
v___jp_1528_:
{
if (v___y_1529_ == 0)
{
lean_object* v___x_1530_; 
lean_inc(v_binderName_1522_);
lean_dec_ref_known(v_e_1493_, 3);
v___x_1530_ = l_Lean_Expr_lam___override(v_binderName_1522_, v___x_1526_, v___x_1527_, v_binderInfo_1525_);
return v___x_1530_;
}
else
{
uint8_t v___x_1531_; 
v___x_1531_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1525_, v_binderInfo_1525_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; 
lean_inc(v_binderName_1522_);
lean_dec_ref_known(v_e_1493_, 3);
v___x_1532_ = l_Lean_Expr_lam___override(v_binderName_1522_, v___x_1526_, v___x_1527_, v_binderInfo_1525_);
return v___x_1532_;
}
else
{
lean_dec_ref(v___x_1527_);
lean_dec_ref(v___x_1526_);
return v_e_1493_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1539_; lean_object* v_binderType_1540_; lean_object* v_body_1541_; uint8_t v_binderInfo_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___y_1546_; size_t v___x_1550_; size_t v___x_1551_; uint8_t v___x_1552_; 
v_binderName_1539_ = lean_ctor_get(v_e_1493_, 0);
v_binderType_1540_ = lean_ctor_get(v_e_1493_, 1);
v_body_1541_ = lean_ctor_get(v_e_1493_, 2);
v_binderInfo_1542_ = lean_ctor_get_uint8(v_e_1493_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1540_);
v___x_1543_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1490_, v_s_1491_, v_translator_1492_, v_binderType_1540_);
lean_inc_ref(v_body_1541_);
v___x_1544_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1490_, v_s_1491_, v_translator_1492_, v_body_1541_);
v___x_1550_ = lean_ptr_addr(v_binderType_1540_);
v___x_1551_ = lean_ptr_addr(v___x_1543_);
v___x_1552_ = lean_usize_dec_eq(v___x_1550_, v___x_1551_);
if (v___x_1552_ == 0)
{
v___y_1546_ = v___x_1552_;
goto v___jp_1545_;
}
else
{
size_t v___x_1553_; size_t v___x_1554_; uint8_t v___x_1555_; 
v___x_1553_ = lean_ptr_addr(v_body_1541_);
v___x_1554_ = lean_ptr_addr(v___x_1544_);
v___x_1555_ = lean_usize_dec_eq(v___x_1553_, v___x_1554_);
v___y_1546_ = v___x_1555_;
goto v___jp_1545_;
}
v___jp_1545_:
{
if (v___y_1546_ == 0)
{
lean_object* v___x_1547_; 
lean_inc(v_binderName_1539_);
lean_dec_ref_known(v_e_1493_, 3);
v___x_1547_ = l_Lean_Expr_forallE___override(v_binderName_1539_, v___x_1543_, v___x_1544_, v_binderInfo_1542_);
return v___x_1547_;
}
else
{
uint8_t v___x_1548_; 
v___x_1548_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1542_, v_binderInfo_1542_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
lean_inc(v_binderName_1539_);
lean_dec_ref_known(v_e_1493_, 3);
v___x_1549_ = l_Lean_Expr_forallE___override(v_binderName_1539_, v___x_1543_, v___x_1544_, v_binderInfo_1542_);
return v___x_1549_;
}
else
{
lean_dec_ref(v___x_1544_);
lean_dec_ref(v___x_1543_);
return v_e_1493_;
}
}
}
}
case 8:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec_ref_known(v_e_1493_, 4);
v___x_1556_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3, &l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
v___x_1557_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_1556_);
return v___x_1557_;
}
case 10:
{
lean_object* v_data_1558_; lean_object* v_expr_1559_; lean_object* v___x_1560_; size_t v___x_1561_; size_t v___x_1562_; uint8_t v___x_1563_; 
v_data_1558_ = lean_ctor_get(v_e_1493_, 0);
v_expr_1559_ = lean_ctor_get(v_e_1493_, 1);
lean_inc_ref(v_expr_1559_);
v___x_1560_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1490_, v_s_1491_, v_translator_1492_, v_expr_1559_);
v___x_1561_ = lean_ptr_addr(v_expr_1559_);
v___x_1562_ = lean_ptr_addr(v___x_1560_);
v___x_1563_ = lean_usize_dec_eq(v___x_1561_, v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; 
lean_inc(v_data_1558_);
lean_dec_ref_known(v_e_1493_, 2);
v___x_1564_ = l_Lean_Expr_mdata___override(v_data_1558_, v___x_1560_);
return v___x_1564_;
}
else
{
lean_dec_ref(v___x_1560_);
return v_e_1493_;
}
}
case 11:
{
lean_object* v_typeName_1565_; lean_object* v_idx_1566_; lean_object* v_struct_1567_; lean_object* v___x_1568_; size_t v___x_1569_; size_t v___x_1570_; uint8_t v___x_1571_; 
v_typeName_1565_ = lean_ctor_get(v_e_1493_, 0);
v_idx_1566_ = lean_ctor_get(v_e_1493_, 1);
v_struct_1567_ = lean_ctor_get(v_e_1493_, 2);
lean_inc_ref(v_struct_1567_);
v___x_1568_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1490_, v_s_1491_, v_translator_1492_, v_struct_1567_);
v___x_1569_ = lean_ptr_addr(v_struct_1567_);
v___x_1570_ = lean_ptr_addr(v___x_1568_);
v___x_1571_ = lean_usize_dec_eq(v___x_1569_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; 
lean_inc(v_idx_1566_);
lean_inc(v_typeName_1565_);
lean_dec_ref_known(v_e_1493_, 3);
v___x_1572_ = l_Lean_Expr_proj___override(v_typeName_1565_, v_idx_1566_, v___x_1568_);
return v___x_1572_;
}
else
{
lean_dec_ref(v___x_1568_);
return v_e_1493_;
}
}
default: 
{
return v_e_1493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t v_pu_1573_, lean_object* v_s_1574_, uint8_t v_translator_1575_, lean_object* v_e_1576_){
_start:
{
if (lean_obj_tag(v_e_1576_) == 5)
{
lean_object* v_fn_1577_; lean_object* v_arg_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___y_1582_; size_t v___x_1584_; size_t v___x_1585_; uint8_t v___x_1586_; 
v_fn_1577_ = lean_ctor_get(v_e_1576_, 0);
v_arg_1578_ = lean_ctor_get(v_e_1576_, 1);
lean_inc_ref(v_fn_1577_);
v___x_1579_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1573_, v_s_1574_, v_translator_1575_, v_fn_1577_);
lean_inc_ref(v_arg_1578_);
v___x_1580_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1573_, v_s_1574_, v_translator_1575_, v_arg_1578_);
v___x_1584_ = lean_ptr_addr(v_fn_1577_);
v___x_1585_ = lean_ptr_addr(v___x_1579_);
v___x_1586_ = lean_usize_dec_eq(v___x_1584_, v___x_1585_);
if (v___x_1586_ == 0)
{
v___y_1582_ = v___x_1586_;
goto v___jp_1581_;
}
else
{
size_t v___x_1587_; size_t v___x_1588_; uint8_t v___x_1589_; 
v___x_1587_ = lean_ptr_addr(v_arg_1578_);
v___x_1588_ = lean_ptr_addr(v___x_1580_);
v___x_1589_ = lean_usize_dec_eq(v___x_1587_, v___x_1588_);
v___y_1582_ = v___x_1589_;
goto v___jp_1581_;
}
v___jp_1581_:
{
if (v___y_1582_ == 0)
{
lean_object* v___x_1583_; 
lean_dec_ref_known(v_e_1576_, 2);
v___x_1583_ = l_Lean_Expr_app___override(v___x_1579_, v___x_1580_);
return v___x_1583_;
}
else
{
lean_dec_ref(v___x_1580_);
lean_dec_ref(v___x_1579_);
return v_e_1576_;
}
}
}
else
{
lean_object* v___x_1590_; 
v___x_1590_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1573_, v_s_1574_, v_translator_1575_, v_e_1576_);
return v___x_1590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object* v_pu_1591_, lean_object* v_s_1592_, lean_object* v_translator_1593_, lean_object* v_e_1594_){
_start:
{
uint8_t v_pu_boxed_1595_; uint8_t v_translator_boxed_1596_; lean_object* v_res_1597_; 
v_pu_boxed_1595_ = lean_unbox(v_pu_1591_);
v_translator_boxed_1596_ = lean_unbox(v_translator_1593_);
v_res_1597_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_boxed_1595_, v_s_1592_, v_translator_boxed_1596_, v_e_1594_);
lean_dec_ref(v_s_1592_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object* v_pu_1598_, lean_object* v_s_1599_, lean_object* v_translator_1600_, lean_object* v_e_1601_){
_start:
{
uint8_t v_pu_boxed_1602_; uint8_t v_translator_boxed_1603_; lean_object* v_res_1604_; 
v_pu_boxed_1602_ = lean_unbox(v_pu_1598_);
v_translator_boxed_1603_ = lean_unbox(v_translator_1600_);
v_res_1604_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_boxed_1602_, v_s_1599_, v_translator_boxed_1603_, v_e_1601_);
lean_dec_ref(v_s_1599_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t v_pu_1605_, lean_object* v_s_1606_, lean_object* v_e_1607_, uint8_t v_translator_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1605_, v_s_1606_, v_translator_1608_, v_e_1607_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object* v_pu_1610_, lean_object* v_s_1611_, lean_object* v_e_1612_, lean_object* v_translator_1613_){
_start:
{
uint8_t v_pu_boxed_1614_; uint8_t v_translator_boxed_1615_; lean_object* v_res_1616_; 
v_pu_boxed_1614_ = lean_unbox(v_pu_1610_);
v_translator_boxed_1615_ = lean_unbox(v_translator_1613_);
v_res_1616_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(v_pu_boxed_1614_, v_s_1611_, v_e_1612_, v_translator_boxed_1615_);
lean_dec_ref(v_s_1611_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(lean_object* v_x_1617_){
_start:
{
if (lean_obj_tag(v_x_1617_) == 0)
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_unsigned_to_nat(0u);
return v___x_1618_;
}
else
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_unsigned_to_nat(1u);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___boxed(lean_object* v_x_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(v_x_1620_);
lean_dec(v_x_1620_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(lean_object* v_t_1622_, lean_object* v_k_1623_){
_start:
{
if (lean_obj_tag(v_t_1622_) == 0)
{
lean_object* v_fvarId_1624_; lean_object* v___x_1625_; 
v_fvarId_1624_ = lean_ctor_get(v_t_1622_, 0);
lean_inc(v_fvarId_1624_);
lean_dec_ref_known(v_t_1622_, 1);
v___x_1625_ = lean_apply_1(v_k_1623_, v_fvarId_1624_);
return v___x_1625_;
}
else
{
return v_k_1623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(lean_object* v_motive_1626_, lean_object* v_ctorIdx_1627_, lean_object* v_t_1628_, lean_object* v_h_1629_, lean_object* v_k_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1628_, v_k_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(lean_object* v_motive_1632_, lean_object* v_ctorIdx_1633_, lean_object* v_t_1634_, lean_object* v_h_1635_, lean_object* v_k_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(v_motive_1632_, v_ctorIdx_1633_, v_t_1634_, v_h_1635_, v_k_1636_);
lean_dec(v_ctorIdx_1633_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(lean_object* v_t_1638_, lean_object* v_fvar_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1638_, v_fvar_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(lean_object* v_motive_1641_, lean_object* v_t_1642_, lean_object* v_h_1643_, lean_object* v_fvar_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1642_, v_fvar_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(lean_object* v_t_1646_, lean_object* v_erased_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1646_, v_erased_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(lean_object* v_motive_1649_, lean_object* v_t_1650_, lean_object* v_h_1651_, lean_object* v_erased_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1650_, v_erased_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object* v_s_1658_, lean_object* v_fvarId_1659_, uint8_t v_translator_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1658_, v_fvarId_1659_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1662_, 0, v_fvarId_1659_);
return v___x_1662_;
}
else
{
lean_object* v_val_1663_; 
lean_dec(v_fvarId_1659_);
v_val_1663_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_val_1663_);
lean_dec_ref_known(v___x_1661_, 1);
if (lean_obj_tag(v_val_1663_) == 1)
{
if (v_translator_1660_ == 0)
{
lean_object* v_fvarId_1664_; 
v_fvarId_1664_ = lean_ctor_get(v_val_1663_, 0);
lean_inc(v_fvarId_1664_);
lean_dec_ref_known(v_val_1663_, 1);
v_fvarId_1659_ = v_fvarId_1664_;
goto _start;
}
else
{
lean_object* v_fvarId_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
v_fvarId_1666_ = lean_ctor_get(v_val_1663_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_val_1663_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v_val_1663_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_fvarId_1666_);
lean_dec(v_val_1663_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
lean_ctor_set_tag(v___x_1668_, 0);
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_fvarId_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v___x_1674_; 
lean_dec(v_val_1663_);
v___x_1674_ = lean_box(1);
return v___x_1674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg___boxed(lean_object* v_s_1675_, lean_object* v_fvarId_1676_, lean_object* v_translator_1677_){
_start:
{
uint8_t v_translator_boxed_1678_; lean_object* v_res_1679_; 
v_translator_boxed_1678_ = lean_unbox(v_translator_1677_);
v_res_1679_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1675_, v_fvarId_1676_, v_translator_boxed_1678_);
lean_dec_ref(v_s_1675_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp(uint8_t v_pu_1680_, lean_object* v_s_1681_, lean_object* v_fvarId_1682_, uint8_t v_translator_1683_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1681_, v_fvarId_1682_, v_translator_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___boxed(lean_object* v_pu_1685_, lean_object* v_s_1686_, lean_object* v_fvarId_1687_, lean_object* v_translator_1688_){
_start:
{
uint8_t v_pu_boxed_1689_; uint8_t v_translator_boxed_1690_; lean_object* v_res_1691_; 
v_pu_boxed_1689_ = lean_unbox(v_pu_1685_);
v_translator_boxed_1690_ = lean_unbox(v_translator_1688_);
v_res_1691_ = l_Lean_Compiler_LCNF_normFVarImp(v_pu_boxed_1689_, v_s_1686_, v_fvarId_1687_, v_translator_boxed_1690_);
lean_dec_ref(v_s_1686_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t v_pu_1692_, lean_object* v_s_1693_, lean_object* v_arg_1694_, uint8_t v_translator_1695_){
_start:
{
switch(lean_obj_tag(v_arg_1694_))
{
case 0:
{
return v_arg_1694_;
}
case 1:
{
lean_object* v_fvarId_1696_; lean_object* v___x_1697_; 
v_fvarId_1696_ = lean_ctor_get(v_arg_1694_, 0);
v___x_1697_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1693_, v_fvarId_1696_);
if (lean_obj_tag(v___x_1697_) == 0)
{
return v_arg_1694_;
}
else
{
lean_object* v_val_1698_; 
lean_dec_ref_known(v_arg_1694_, 1);
v_val_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_val_1698_);
lean_dec_ref_known(v___x_1697_, 1);
switch(lean_obj_tag(v_val_1698_))
{
case 0:
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_box(0);
return v___x_1699_;
}
case 1:
{
lean_object* v_fvarId_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1708_; 
v_fvarId_1700_ = lean_ctor_get(v_val_1698_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_val_1698_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1702_ = v_val_1698_;
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_fvarId_1700_);
lean_dec(v_val_1698_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_fvarId_1700_);
v___x_1705_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
if (v_translator_1695_ == 0)
{
v_arg_1694_ = v___x_1705_;
goto _start;
}
else
{
return v___x_1705_;
}
}
}
}
default: 
{
lean_object* v_expr_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
v_expr_1709_ = lean_ctor_get(v_val_1698_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_val_1698_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v_val_1698_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_expr_1709_);
lean_dec(v_val_1698_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_expr_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
}
default: 
{
lean_object* v_expr_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_expr_1717_ = lean_ctor_get(v_arg_1694_, 0);
lean_inc_ref(v_expr_1717_);
v___x_1718_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1692_, v_s_1693_, v_translator_1695_, v_expr_1717_);
v___x_1719_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1692_, v_arg_1694_, v___x_1718_);
return v___x_1719_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp___boxed(lean_object* v_pu_1720_, lean_object* v_s_1721_, lean_object* v_arg_1722_, lean_object* v_translator_1723_){
_start:
{
uint8_t v_pu_boxed_1724_; uint8_t v_translator_boxed_1725_; lean_object* v_res_1726_; 
v_pu_boxed_1724_ = lean_unbox(v_pu_1720_);
v_translator_boxed_1725_ = lean_unbox(v_translator_1723_);
v_res_1726_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_boxed_1724_, v_s_1721_, v_arg_1722_, v_translator_boxed_1725_);
lean_dec_ref(v_s_1721_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(uint8_t v_pu_1727_, lean_object* v_s_1728_, uint8_t v_translator_1729_, lean_object* v_i_1730_, lean_object* v_as_1731_){
_start:
{
lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = lean_array_get_size(v_as_1731_);
v___x_1733_ = lean_nat_dec_lt(v_i_1730_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_dec(v_i_1730_);
return v_as_1731_;
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1735_; size_t v___x_1736_; size_t v___x_1737_; uint8_t v___x_1738_; 
v_a_1734_ = lean_array_fget_borrowed(v_as_1731_, v_i_1730_);
lean_inc(v_a_1734_);
v___x_1735_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1727_, v_s_1728_, v_a_1734_, v_translator_1729_);
v___x_1736_ = lean_ptr_addr(v_a_1734_);
v___x_1737_ = lean_ptr_addr(v___x_1735_);
v___x_1738_ = lean_usize_dec_eq(v___x_1736_, v___x_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1739_ = lean_unsigned_to_nat(1u);
v___x_1740_ = lean_nat_add(v_i_1730_, v___x_1739_);
v___x_1741_ = lean_array_fset(v_as_1731_, v_i_1730_, v___x_1735_);
lean_dec(v_i_1730_);
v_i_1730_ = v___x_1740_;
v_as_1731_ = v___x_1741_;
goto _start;
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec(v___x_1735_);
v___x_1743_ = lean_unsigned_to_nat(1u);
v___x_1744_ = lean_nat_add(v_i_1730_, v___x_1743_);
lean_dec(v_i_1730_);
v_i_1730_ = v___x_1744_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0___boxed(lean_object* v_pu_1746_, lean_object* v_s_1747_, lean_object* v_translator_1748_, lean_object* v_i_1749_, lean_object* v_as_1750_){
_start:
{
uint8_t v_pu_boxed_1751_; uint8_t v_translator_boxed_1752_; lean_object* v_res_1753_; 
v_pu_boxed_1751_ = lean_unbox(v_pu_1746_);
v_translator_boxed_1752_ = lean_unbox(v_translator_1748_);
v_res_1753_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_boxed_1751_, v_s_1747_, v_translator_boxed_1752_, v_i_1749_, v_as_1750_);
lean_dec_ref(v_s_1747_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t v_pu_1754_, lean_object* v_s_1755_, lean_object* v_args_1756_, uint8_t v_translator_1757_){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_1754_, v_s_1755_, v_translator_1757_, v___x_1758_, v_args_1756_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(lean_object* v_pu_1760_, lean_object* v_s_1761_, lean_object* v_args_1762_, lean_object* v_translator_1763_){
_start:
{
uint8_t v_pu_boxed_1764_; uint8_t v_translator_boxed_1765_; lean_object* v_res_1766_; 
v_pu_boxed_1764_ = lean_unbox(v_pu_1760_);
v_translator_boxed_1765_ = lean_unbox(v_translator_1763_);
v_res_1766_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_boxed_1764_, v_s_1761_, v_args_1762_, v_translator_boxed_1765_);
lean_dec_ref(v_s_1761_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t v_pu_1767_, lean_object* v_s_1768_, lean_object* v_e_1769_, uint8_t v_translator_1770_){
_start:
{
lean_object* v_fvarId_1772_; lean_object* v_args_1778_; 
switch(lean_obj_tag(v_e_1769_))
{
case 2:
{
lean_object* v_struct_1781_; lean_object* v___x_1782_; 
v_struct_1781_ = lean_ctor_get(v_e_1769_, 2);
lean_inc(v_struct_1781_);
v___x_1782_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1768_, v_struct_1781_, v_translator_1770_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_fvarId_1783_; lean_object* v___x_1784_; 
v_fvarId_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_fvarId_1783_);
lean_dec_ref_known(v___x_1782_, 1);
v___x_1784_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1767_, v_e_1769_, v_fvarId_1783_);
return v___x_1784_;
}
else
{
lean_object* v___x_1785_; 
lean_dec_ref_known(v_e_1769_, 3);
v___x_1785_ = lean_box(1);
return v___x_1785_;
}
}
case 3:
{
lean_object* v_args_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_args_1786_ = lean_ctor_get(v_e_1769_, 2);
lean_inc_ref(v_args_1786_);
v___x_1787_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1767_, v_s_1768_, v_args_1786_, v_translator_1770_);
v___x_1788_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1767_, v_e_1769_, v___x_1787_);
return v___x_1788_;
}
case 4:
{
lean_object* v_fvarId_1789_; lean_object* v_args_1790_; lean_object* v___x_1791_; 
v_fvarId_1789_ = lean_ctor_get(v_e_1769_, 0);
v_args_1790_ = lean_ctor_get(v_e_1769_, 1);
lean_inc(v_fvarId_1789_);
v___x_1791_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1768_, v_fvarId_1789_, v_translator_1770_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_fvarId_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v_fvarId_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_fvarId_1792_);
lean_dec_ref_known(v___x_1791_, 1);
lean_inc_ref(v_args_1790_);
v___x_1793_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1767_, v_s_1768_, v_args_1790_, v_translator_1770_);
v___x_1794_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_1767_, v_e_1769_, v_fvarId_1792_, v___x_1793_);
lean_dec_ref_known(v_e_1769_, 2);
return v___x_1794_;
}
else
{
lean_object* v___x_1795_; 
lean_dec_ref_known(v_e_1769_, 2);
v___x_1795_ = lean_box(1);
return v___x_1795_;
}
}
case 5:
{
lean_object* v_args_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v_args_1796_ = lean_ctor_get(v_e_1769_, 1);
lean_inc_ref(v_args_1796_);
v___x_1797_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1767_, v_s_1768_, v_args_1796_, v_translator_1770_);
v___x_1798_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1767_, v_e_1769_, v___x_1797_);
return v___x_1798_;
}
case 6:
{
lean_object* v_var_1799_; 
v_var_1799_ = lean_ctor_get(v_e_1769_, 1);
lean_inc(v_var_1799_);
v_fvarId_1772_ = v_var_1799_;
goto v___jp_1771_;
}
case 7:
{
lean_object* v_var_1800_; 
v_var_1800_ = lean_ctor_get(v_e_1769_, 1);
lean_inc(v_var_1800_);
v_fvarId_1772_ = v_var_1800_;
goto v___jp_1771_;
}
case 8:
{
lean_object* v_var_1801_; lean_object* v___x_1802_; 
v_var_1801_ = lean_ctor_get(v_e_1769_, 2);
lean_inc(v_var_1801_);
v___x_1802_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1768_, v_var_1801_, v_translator_1770_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_fvarId_1803_; lean_object* v___x_1804_; 
v_fvarId_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_fvarId_1803_);
lean_dec_ref_known(v___x_1802_, 1);
v___x_1804_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1767_, v_e_1769_, v_fvarId_1803_);
return v___x_1804_;
}
else
{
lean_object* v___x_1805_; 
lean_dec_ref_known(v_e_1769_, 3);
v___x_1805_ = lean_box(1);
return v___x_1805_;
}
}
case 9:
{
lean_object* v_args_1806_; 
v_args_1806_ = lean_ctor_get(v_e_1769_, 1);
lean_inc_ref(v_args_1806_);
v_args_1778_ = v_args_1806_;
goto v___jp_1777_;
}
case 10:
{
lean_object* v_args_1807_; 
v_args_1807_ = lean_ctor_get(v_e_1769_, 1);
lean_inc_ref(v_args_1807_);
v_args_1778_ = v_args_1807_;
goto v___jp_1777_;
}
case 11:
{
lean_object* v_n_1808_; lean_object* v_var_1809_; lean_object* v___x_1810_; 
v_n_1808_ = lean_ctor_get(v_e_1769_, 0);
lean_inc(v_n_1808_);
v_var_1809_ = lean_ctor_get(v_e_1769_, 1);
lean_inc(v_var_1809_);
v___x_1810_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1768_, v_var_1809_, v_translator_1770_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_fvarId_1811_; lean_object* v___x_1812_; 
v_fvarId_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_fvarId_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v___x_1812_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_1767_, v_e_1769_, v_n_1808_, v_fvarId_1811_);
lean_dec_ref_known(v_e_1769_, 2);
return v___x_1812_;
}
else
{
lean_object* v___x_1813_; 
lean_dec_ref_known(v_e_1769_, 2);
lean_dec(v_n_1808_);
v___x_1813_ = lean_box(1);
return v___x_1813_;
}
}
case 12:
{
lean_object* v_var_1814_; lean_object* v_i_1815_; uint8_t v_updateHeader_1816_; lean_object* v_args_1817_; lean_object* v___x_1818_; 
v_var_1814_ = lean_ctor_get(v_e_1769_, 0);
v_i_1815_ = lean_ctor_get(v_e_1769_, 1);
lean_inc_ref(v_i_1815_);
v_updateHeader_1816_ = lean_ctor_get_uint8(v_e_1769_, sizeof(void*)*3);
v_args_1817_ = lean_ctor_get(v_e_1769_, 2);
lean_inc(v_var_1814_);
v___x_1818_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1768_, v_var_1814_, v_translator_1770_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_fvarId_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v_fvarId_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_fvarId_1819_);
lean_dec_ref_known(v___x_1818_, 1);
lean_inc_ref(v_args_1817_);
v___x_1820_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1767_, v_s_1768_, v_args_1817_, v_translator_1770_);
v___x_1821_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_1767_, v_e_1769_, v_fvarId_1819_, v_i_1815_, v_updateHeader_1816_, v___x_1820_);
return v___x_1821_;
}
else
{
lean_object* v___x_1822_; 
lean_dec_ref(v_i_1815_);
lean_dec_ref_known(v_e_1769_, 3);
v___x_1822_ = lean_box(1);
return v___x_1822_;
}
}
case 13:
{
lean_object* v_ty_1823_; lean_object* v_fvarId_1824_; lean_object* v___x_1825_; 
v_ty_1823_ = lean_ctor_get(v_e_1769_, 0);
lean_inc_ref(v_ty_1823_);
v_fvarId_1824_ = lean_ctor_get(v_e_1769_, 1);
lean_inc(v_fvarId_1824_);
v___x_1825_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1768_, v_fvarId_1824_, v_translator_1770_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_fvarId_1826_; lean_object* v___x_1827_; 
v_fvarId_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_fvarId_1826_);
lean_dec_ref_known(v___x_1825_, 1);
v___x_1827_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_1767_, v_e_1769_, v_ty_1823_, v_fvarId_1826_);
lean_dec_ref_known(v_e_1769_, 2);
return v___x_1827_;
}
else
{
lean_object* v___x_1828_; 
lean_dec_ref_known(v_e_1769_, 2);
lean_dec_ref(v_ty_1823_);
v___x_1828_ = lean_box(1);
return v___x_1828_;
}
}
case 14:
{
lean_object* v_fvarId_1829_; lean_object* v___x_1830_; 
v_fvarId_1829_ = lean_ctor_get(v_e_1769_, 0);
lean_inc(v_fvarId_1829_);
v___x_1830_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1768_, v_fvarId_1829_, v_translator_1770_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_fvarId_1831_; lean_object* v___x_1832_; 
v_fvarId_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_fvarId_1831_);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1832_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_1767_, v_e_1769_, v_fvarId_1831_);
return v___x_1832_;
}
else
{
lean_object* v___x_1833_; 
lean_dec_ref_known(v_e_1769_, 1);
v___x_1833_ = lean_box(1);
return v___x_1833_;
}
}
case 15:
{
lean_object* v_fvarId_1834_; lean_object* v___x_1835_; 
v_fvarId_1834_ = lean_ctor_get(v_e_1769_, 0);
lean_inc(v_fvarId_1834_);
v___x_1835_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1768_, v_fvarId_1834_, v_translator_1770_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_fvarId_1836_; lean_object* v___x_1837_; 
v_fvarId_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_fvarId_1836_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_1767_, v_e_1769_, v_fvarId_1836_);
return v___x_1837_;
}
else
{
lean_object* v___x_1838_; 
lean_dec_ref_known(v_e_1769_, 1);
v___x_1838_ = lean_box(1);
return v___x_1838_;
}
}
default: 
{
return v_e_1769_;
}
}
v___jp_1771_:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1768_, v_fvarId_1772_, v_translator_1770_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_fvarId_1774_; lean_object* v___x_1775_; 
v_fvarId_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_fvarId_1774_);
lean_dec_ref_known(v___x_1773_, 1);
v___x_1775_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1767_, v_e_1769_, v_fvarId_1774_);
return v___x_1775_;
}
else
{
lean_object* v___x_1776_; 
lean_dec(v_e_1769_);
v___x_1776_ = lean_box(1);
return v___x_1776_;
}
}
v___jp_1777_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1767_, v_s_1768_, v_args_1778_, v_translator_1770_);
v___x_1780_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_1767_, v_e_1769_, v___x_1779_);
return v___x_1780_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp___boxed(lean_object* v_pu_1839_, lean_object* v_s_1840_, lean_object* v_e_1841_, lean_object* v_translator_1842_){
_start:
{
uint8_t v_pu_boxed_1843_; uint8_t v_translator_boxed_1844_; lean_object* v_res_1845_; 
v_pu_boxed_1843_ = lean_unbox(v_pu_1839_);
v_translator_boxed_1844_ = lean_unbox(v_translator_1842_);
v_res_1845_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_boxed_1843_, v_s_1840_, v_e_1841_, v_translator_boxed_1844_);
lean_dec_ref(v_s_1840_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(lean_object* v_inst_1846_, lean_object* v_inst_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_apply_2(v_inst_1846_, lean_box(0), v_inst_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(uint8_t v_pu_1849_, uint8_t v_t_1850_, lean_object* v_m_1851_, lean_object* v_n_1852_, lean_object* v_inst_1853_, lean_object* v_inst_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_apply_2(v_inst_1853_, lean_box(0), v_inst_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(lean_object* v_pu_1856_, lean_object* v_t_1857_, lean_object* v_m_1858_, lean_object* v_n_1859_, lean_object* v_inst_1860_, lean_object* v_inst_1861_){
_start:
{
uint8_t v_pu_boxed_1862_; uint8_t v_t_boxed_1863_; lean_object* v_res_1864_; 
v_pu_boxed_1862_ = lean_unbox(v_pu_1856_);
v_t_boxed_1863_ = lean_unbox(v_t_1857_);
v_res_1864_ = l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(v_pu_boxed_1862_, v_t_boxed_1863_, v_m_1858_, v_n_1859_, v_inst_1860_, v_inst_1861_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0(lean_object* v_inst_1865_, lean_object* v_inst_1866_, lean_object* v_f_1867_){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = lean_apply_1(v_inst_1865_, v_f_1867_);
v___x_1869_ = lean_apply_2(v_inst_1866_, lean_box(0), v___x_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(lean_object* v_inst_1870_, lean_object* v_inst_1871_){
_start:
{
lean_object* v___f_1872_; 
v___f_1872_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1872_, 0, v_inst_1871_);
lean_closure_set(v___f_1872_, 1, v_inst_1870_);
return v___f_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(uint8_t v_pu_1873_, lean_object* v_m_1874_, lean_object* v_n_1875_, lean_object* v_inst_1876_, lean_object* v_inst_1877_){
_start:
{
lean_object* v___f_1878_; 
v___f_1878_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1878_, 0, v_inst_1877_);
lean_closure_set(v___f_1878_, 1, v_inst_1876_);
return v___f_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(lean_object* v_pu_1879_, lean_object* v_m_1880_, lean_object* v_n_1881_, lean_object* v_inst_1882_, lean_object* v_inst_1883_){
_start:
{
uint8_t v_pu_boxed_1884_; lean_object* v_res_1885_; 
v_pu_boxed_1884_ = lean_unbox(v_pu_1879_);
v_res_1885_ = l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(v_pu_boxed_1884_, v_m_1880_, v_n_1881_, v_inst_1882_, v_inst_1883_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___lam__0(lean_object* v___x_1886_, lean_object* v___x_1887_, lean_object* v_fvarId_1888_, lean_object* v_arg_1889_, lean_object* v_s_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1886_, v___x_1887_, v_s_1890_, v_fvarId_1888_, v_arg_1889_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg(lean_object* v_inst_1894_, lean_object* v_fvarId_1895_, lean_object* v_arg_1896_){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___f_1899_; lean_object* v___x_1900_; 
v___x_1897_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1898_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1899_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1899_, 0, v___x_1897_);
lean_closure_set(v___f_1899_, 1, v___x_1898_);
lean_closure_set(v___f_1899_, 2, v_fvarId_1895_);
lean_closure_set(v___f_1899_, 3, v_arg_1896_);
v___x_1900_ = lean_apply_1(v_inst_1894_, v___f_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst(lean_object* v_m_1901_, uint8_t v_pu_1902_, lean_object* v_inst_1903_, lean_object* v_fvarId_1904_, lean_object* v_arg_1905_){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___f_1908_; lean_object* v___x_1909_; 
v___x_1906_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1907_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1908_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1908_, 0, v___x_1906_);
lean_closure_set(v___f_1908_, 1, v___x_1907_);
lean_closure_set(v___f_1908_, 2, v_fvarId_1904_);
lean_closure_set(v___f_1908_, 3, v_arg_1905_);
v___x_1909_ = lean_apply_1(v_inst_1903_, v___f_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___boxed(lean_object* v_m_1910_, lean_object* v_pu_1911_, lean_object* v_inst_1912_, lean_object* v_fvarId_1913_, lean_object* v_arg_1914_){
_start:
{
uint8_t v_pu_boxed_1915_; lean_object* v_res_1916_; 
v_pu_boxed_1915_ = lean_unbox(v_pu_1911_);
v_res_1916_ = l_Lean_Compiler_LCNF_addSubst(v_m_1910_, v_pu_boxed_1915_, v_inst_1912_, v_fvarId_1913_, v_arg_1914_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0(lean_object* v_fvarId_x27_1917_, lean_object* v___x_1918_, lean_object* v___x_1919_, lean_object* v_fvarId_1920_, lean_object* v_s_1921_){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1922_, 0, v_fvarId_x27_1917_);
v___x_1923_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1918_, v___x_1919_, v_s_1921_, v_fvarId_1920_, v___x_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg(lean_object* v_inst_1924_, lean_object* v_fvarId_1925_, lean_object* v_fvarId_x27_1926_){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___f_1929_; lean_object* v___x_1930_; 
v___x_1927_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1928_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1929_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1929_, 0, v_fvarId_x27_1926_);
lean_closure_set(v___f_1929_, 1, v___x_1927_);
lean_closure_set(v___f_1929_, 2, v___x_1928_);
lean_closure_set(v___f_1929_, 3, v_fvarId_1925_);
v___x_1930_ = lean_apply_1(v_inst_1924_, v___f_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst(lean_object* v_m_1931_, uint8_t v_ph_1932_, lean_object* v_inst_1933_, lean_object* v_fvarId_1934_, lean_object* v_fvarId_x27_1935_){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___f_1938_; lean_object* v___x_1939_; 
v___x_1936_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1937_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1938_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1938_, 0, v_fvarId_x27_1935_);
lean_closure_set(v___f_1938_, 1, v___x_1936_);
lean_closure_set(v___f_1938_, 2, v___x_1937_);
lean_closure_set(v___f_1938_, 3, v_fvarId_1934_);
v___x_1939_ = lean_apply_1(v_inst_1933_, v___f_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___boxed(lean_object* v_m_1940_, lean_object* v_ph_1941_, lean_object* v_inst_1942_, lean_object* v_fvarId_1943_, lean_object* v_fvarId_x27_1944_){
_start:
{
uint8_t v_ph_boxed_1945_; lean_object* v_res_1946_; 
v_ph_boxed_1945_ = lean_unbox(v_ph_1941_);
v_res_1946_ = l_Lean_Compiler_LCNF_addFVarSubst(v_m_1940_, v_ph_boxed_1945_, v_inst_1942_, v_fvarId_1943_, v_fvarId_x27_1944_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(lean_object* v_fvarId_1947_, uint8_t v_t_1948_, lean_object* v_toPure_1949_, lean_object* v_____do__lift_1950_){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_____do__lift_1950_, v_fvarId_1947_, v_t_1948_);
v___x_1952_ = lean_apply_2(v_toPure_1949_, lean_box(0), v___x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(lean_object* v_fvarId_1953_, lean_object* v_t_1954_, lean_object* v_toPure_1955_, lean_object* v_____do__lift_1956_){
_start:
{
uint8_t v_t_boxed_1957_; lean_object* v_res_1958_; 
v_t_boxed_1957_ = lean_unbox(v_t_1954_);
v_res_1958_ = l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(v_fvarId_1953_, v_t_boxed_1957_, v_toPure_1955_, v_____do__lift_1956_);
lean_dec_ref(v_____do__lift_1956_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg(uint8_t v_t_1959_, lean_object* v_inst_1960_, lean_object* v_inst_1961_, lean_object* v_fvarId_1962_){
_start:
{
lean_object* v_toApplicative_1963_; lean_object* v_toBind_1964_; lean_object* v_toPure_1965_; lean_object* v___x_1966_; lean_object* v___f_1967_; lean_object* v___x_1968_; 
v_toApplicative_1963_ = lean_ctor_get(v_inst_1961_, 0);
lean_inc_ref(v_toApplicative_1963_);
v_toBind_1964_ = lean_ctor_get(v_inst_1961_, 1);
lean_inc(v_toBind_1964_);
lean_dec_ref(v_inst_1961_);
v_toPure_1965_ = lean_ctor_get(v_toApplicative_1963_, 1);
lean_inc(v_toPure_1965_);
lean_dec_ref(v_toApplicative_1963_);
v___x_1966_ = lean_box(v_t_1959_);
v___f_1967_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1967_, 0, v_fvarId_1962_);
lean_closure_set(v___f_1967_, 1, v___x_1966_);
lean_closure_set(v___f_1967_, 2, v_toPure_1965_);
v___x_1968_ = lean_apply_4(v_toBind_1964_, lean_box(0), lean_box(0), v_inst_1960_, v___f_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___boxed(lean_object* v_t_1969_, lean_object* v_inst_1970_, lean_object* v_inst_1971_, lean_object* v_fvarId_1972_){
_start:
{
uint8_t v_t_boxed_1973_; lean_object* v_res_1974_; 
v_t_boxed_1973_ = lean_unbox(v_t_1969_);
v_res_1974_ = l_Lean_Compiler_LCNF_normFVar___redArg(v_t_boxed_1973_, v_inst_1970_, v_inst_1971_, v_fvarId_1972_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar(lean_object* v_m_1975_, uint8_t v_pu_1976_, uint8_t v_t_1977_, lean_object* v_inst_1978_, lean_object* v_inst_1979_, lean_object* v_fvarId_1980_){
_start:
{
lean_object* v_toApplicative_1981_; lean_object* v_toBind_1982_; lean_object* v_toPure_1983_; lean_object* v___x_1984_; lean_object* v___f_1985_; lean_object* v___x_1986_; 
v_toApplicative_1981_ = lean_ctor_get(v_inst_1979_, 0);
lean_inc_ref(v_toApplicative_1981_);
v_toBind_1982_ = lean_ctor_get(v_inst_1979_, 1);
lean_inc(v_toBind_1982_);
lean_dec_ref(v_inst_1979_);
v_toPure_1983_ = lean_ctor_get(v_toApplicative_1981_, 1);
lean_inc(v_toPure_1983_);
lean_dec_ref(v_toApplicative_1981_);
v___x_1984_ = lean_box(v_t_1977_);
v___f_1985_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1985_, 0, v_fvarId_1980_);
lean_closure_set(v___f_1985_, 1, v___x_1984_);
lean_closure_set(v___f_1985_, 2, v_toPure_1983_);
v___x_1986_ = lean_apply_4(v_toBind_1982_, lean_box(0), lean_box(0), v_inst_1978_, v___f_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___boxed(lean_object* v_m_1987_, lean_object* v_pu_1988_, lean_object* v_t_1989_, lean_object* v_inst_1990_, lean_object* v_inst_1991_, lean_object* v_fvarId_1992_){
_start:
{
uint8_t v_pu_boxed_1993_; uint8_t v_t_boxed_1994_; lean_object* v_res_1995_; 
v_pu_boxed_1993_ = lean_unbox(v_pu_1988_);
v_t_boxed_1994_ = lean_unbox(v_t_1989_);
v_res_1995_ = l_Lean_Compiler_LCNF_normFVar(v_m_1987_, v_pu_boxed_1993_, v_t_boxed_1994_, v_inst_1990_, v_inst_1991_, v_fvarId_1992_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(uint8_t v_pu_1996_, uint8_t v_t_1997_, lean_object* v_e_1998_, lean_object* v_toPure_1999_, lean_object* v_____do__lift_2000_){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1996_, v_____do__lift_2000_, v_t_1997_, v_e_1998_);
v___x_2002_ = lean_apply_2(v_toPure_1999_, lean_box(0), v___x_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(lean_object* v_pu_2003_, lean_object* v_t_2004_, lean_object* v_e_2005_, lean_object* v_toPure_2006_, lean_object* v_____do__lift_2007_){
_start:
{
uint8_t v_pu_boxed_2008_; uint8_t v_t_boxed_2009_; lean_object* v_res_2010_; 
v_pu_boxed_2008_ = lean_unbox(v_pu_2003_);
v_t_boxed_2009_ = lean_unbox(v_t_2004_);
v_res_2010_ = l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(v_pu_boxed_2008_, v_t_boxed_2009_, v_e_2005_, v_toPure_2006_, v_____do__lift_2007_);
lean_dec_ref(v_____do__lift_2007_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg(uint8_t v_pu_2011_, uint8_t v_t_2012_, lean_object* v_inst_2013_, lean_object* v_inst_2014_, lean_object* v_e_2015_){
_start:
{
lean_object* v_toApplicative_2016_; lean_object* v_toBind_2017_; lean_object* v_toPure_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___f_2021_; lean_object* v___x_2022_; 
v_toApplicative_2016_ = lean_ctor_get(v_inst_2014_, 0);
lean_inc_ref(v_toApplicative_2016_);
v_toBind_2017_ = lean_ctor_get(v_inst_2014_, 1);
lean_inc(v_toBind_2017_);
lean_dec_ref(v_inst_2014_);
v_toPure_2018_ = lean_ctor_get(v_toApplicative_2016_, 1);
lean_inc(v_toPure_2018_);
lean_dec_ref(v_toApplicative_2016_);
v___x_2019_ = lean_box(v_pu_2011_);
v___x_2020_ = lean_box(v_t_2012_);
v___f_2021_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2021_, 0, v___x_2019_);
lean_closure_set(v___f_2021_, 1, v___x_2020_);
lean_closure_set(v___f_2021_, 2, v_e_2015_);
lean_closure_set(v___f_2021_, 3, v_toPure_2018_);
v___x_2022_ = lean_apply_4(v_toBind_2017_, lean_box(0), lean_box(0), v_inst_2013_, v___f_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___boxed(lean_object* v_pu_2023_, lean_object* v_t_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_e_2027_){
_start:
{
uint8_t v_pu_boxed_2028_; uint8_t v_t_boxed_2029_; lean_object* v_res_2030_; 
v_pu_boxed_2028_ = lean_unbox(v_pu_2023_);
v_t_boxed_2029_ = lean_unbox(v_t_2024_);
v_res_2030_ = l_Lean_Compiler_LCNF_normExpr___redArg(v_pu_boxed_2028_, v_t_boxed_2029_, v_inst_2025_, v_inst_2026_, v_e_2027_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr(lean_object* v_m_2031_, uint8_t v_pu_2032_, uint8_t v_t_2033_, lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v_e_2036_){
_start:
{
lean_object* v_toApplicative_2037_; lean_object* v_toBind_2038_; lean_object* v_toPure_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___f_2042_; lean_object* v___x_2043_; 
v_toApplicative_2037_ = lean_ctor_get(v_inst_2035_, 0);
lean_inc_ref(v_toApplicative_2037_);
v_toBind_2038_ = lean_ctor_get(v_inst_2035_, 1);
lean_inc(v_toBind_2038_);
lean_dec_ref(v_inst_2035_);
v_toPure_2039_ = lean_ctor_get(v_toApplicative_2037_, 1);
lean_inc(v_toPure_2039_);
lean_dec_ref(v_toApplicative_2037_);
v___x_2040_ = lean_box(v_pu_2032_);
v___x_2041_ = lean_box(v_t_2033_);
v___f_2042_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2042_, 0, v___x_2040_);
lean_closure_set(v___f_2042_, 1, v___x_2041_);
lean_closure_set(v___f_2042_, 2, v_e_2036_);
lean_closure_set(v___f_2042_, 3, v_toPure_2039_);
v___x_2043_ = lean_apply_4(v_toBind_2038_, lean_box(0), lean_box(0), v_inst_2034_, v___f_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___boxed(lean_object* v_m_2044_, lean_object* v_pu_2045_, lean_object* v_t_2046_, lean_object* v_inst_2047_, lean_object* v_inst_2048_, lean_object* v_e_2049_){
_start:
{
uint8_t v_pu_boxed_2050_; uint8_t v_t_boxed_2051_; lean_object* v_res_2052_; 
v_pu_boxed_2050_ = lean_unbox(v_pu_2045_);
v_t_boxed_2051_ = lean_unbox(v_t_2046_);
v_res_2052_ = l_Lean_Compiler_LCNF_normExpr(v_m_2044_, v_pu_boxed_2050_, v_t_boxed_2051_, v_inst_2047_, v_inst_2048_, v_e_2049_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0(uint8_t v_pu_2053_, lean_object* v_arg_2054_, uint8_t v_t_2055_, lean_object* v_toPure_2056_, lean_object* v_____do__lift_2057_){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2053_, v_____do__lift_2057_, v_arg_2054_, v_t_2055_);
v___x_2059_ = lean_apply_2(v_toPure_2056_, lean_box(0), v___x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(lean_object* v_pu_2060_, lean_object* v_arg_2061_, lean_object* v_t_2062_, lean_object* v_toPure_2063_, lean_object* v_____do__lift_2064_){
_start:
{
uint8_t v_pu_boxed_2065_; uint8_t v_t_boxed_2066_; lean_object* v_res_2067_; 
v_pu_boxed_2065_ = lean_unbox(v_pu_2060_);
v_t_boxed_2066_ = lean_unbox(v_t_2062_);
v_res_2067_ = l_Lean_Compiler_LCNF_normArg___redArg___lam__0(v_pu_boxed_2065_, v_arg_2061_, v_t_boxed_2066_, v_toPure_2063_, v_____do__lift_2064_);
lean_dec_ref(v_____do__lift_2064_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg(uint8_t v_pu_2068_, uint8_t v_t_2069_, lean_object* v_inst_2070_, lean_object* v_inst_2071_, lean_object* v_arg_2072_){
_start:
{
lean_object* v_toApplicative_2073_; lean_object* v_toBind_2074_; lean_object* v_toPure_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___f_2078_; lean_object* v___x_2079_; 
v_toApplicative_2073_ = lean_ctor_get(v_inst_2071_, 0);
lean_inc_ref(v_toApplicative_2073_);
v_toBind_2074_ = lean_ctor_get(v_inst_2071_, 1);
lean_inc(v_toBind_2074_);
lean_dec_ref(v_inst_2071_);
v_toPure_2075_ = lean_ctor_get(v_toApplicative_2073_, 1);
lean_inc(v_toPure_2075_);
lean_dec_ref(v_toApplicative_2073_);
v___x_2076_ = lean_box(v_pu_2068_);
v___x_2077_ = lean_box(v_t_2069_);
v___f_2078_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2078_, 0, v___x_2076_);
lean_closure_set(v___f_2078_, 1, v_arg_2072_);
lean_closure_set(v___f_2078_, 2, v___x_2077_);
lean_closure_set(v___f_2078_, 3, v_toPure_2075_);
v___x_2079_ = lean_apply_4(v_toBind_2074_, lean_box(0), lean_box(0), v_inst_2070_, v___f_2078_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___boxed(lean_object* v_pu_2080_, lean_object* v_t_2081_, lean_object* v_inst_2082_, lean_object* v_inst_2083_, lean_object* v_arg_2084_){
_start:
{
uint8_t v_pu_boxed_2085_; uint8_t v_t_boxed_2086_; lean_object* v_res_2087_; 
v_pu_boxed_2085_ = lean_unbox(v_pu_2080_);
v_t_boxed_2086_ = lean_unbox(v_t_2081_);
v_res_2087_ = l_Lean_Compiler_LCNF_normArg___redArg(v_pu_boxed_2085_, v_t_boxed_2086_, v_inst_2082_, v_inst_2083_, v_arg_2084_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg(lean_object* v_m_2088_, uint8_t v_pu_2089_, uint8_t v_t_2090_, lean_object* v_inst_2091_, lean_object* v_inst_2092_, lean_object* v_arg_2093_){
_start:
{
lean_object* v_toApplicative_2094_; lean_object* v_toBind_2095_; lean_object* v_toPure_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___f_2099_; lean_object* v___x_2100_; 
v_toApplicative_2094_ = lean_ctor_get(v_inst_2092_, 0);
lean_inc_ref(v_toApplicative_2094_);
v_toBind_2095_ = lean_ctor_get(v_inst_2092_, 1);
lean_inc(v_toBind_2095_);
lean_dec_ref(v_inst_2092_);
v_toPure_2096_ = lean_ctor_get(v_toApplicative_2094_, 1);
lean_inc(v_toPure_2096_);
lean_dec_ref(v_toApplicative_2094_);
v___x_2097_ = lean_box(v_pu_2089_);
v___x_2098_ = lean_box(v_t_2090_);
v___f_2099_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2099_, 0, v___x_2097_);
lean_closure_set(v___f_2099_, 1, v_arg_2093_);
lean_closure_set(v___f_2099_, 2, v___x_2098_);
lean_closure_set(v___f_2099_, 3, v_toPure_2096_);
v___x_2100_ = lean_apply_4(v_toBind_2095_, lean_box(0), lean_box(0), v_inst_2091_, v___f_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___boxed(lean_object* v_m_2101_, lean_object* v_pu_2102_, lean_object* v_t_2103_, lean_object* v_inst_2104_, lean_object* v_inst_2105_, lean_object* v_arg_2106_){
_start:
{
uint8_t v_pu_boxed_2107_; uint8_t v_t_boxed_2108_; lean_object* v_res_2109_; 
v_pu_boxed_2107_ = lean_unbox(v_pu_2102_);
v_t_boxed_2108_ = lean_unbox(v_t_2103_);
v_res_2109_ = l_Lean_Compiler_LCNF_normArg(v_m_2101_, v_pu_boxed_2107_, v_t_boxed_2108_, v_inst_2104_, v_inst_2105_, v_arg_2106_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(uint8_t v_pu_2110_, lean_object* v_e_2111_, uint8_t v_t_2112_, lean_object* v_toPure_2113_, lean_object* v_____do__lift_2114_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_2110_, v_____do__lift_2114_, v_e_2111_, v_t_2112_);
v___x_2116_ = lean_apply_2(v_toPure_2113_, lean_box(0), v___x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(lean_object* v_pu_2117_, lean_object* v_e_2118_, lean_object* v_t_2119_, lean_object* v_toPure_2120_, lean_object* v_____do__lift_2121_){
_start:
{
uint8_t v_pu_boxed_2122_; uint8_t v_t_boxed_2123_; lean_object* v_res_2124_; 
v_pu_boxed_2122_ = lean_unbox(v_pu_2117_);
v_t_boxed_2123_ = lean_unbox(v_t_2119_);
v_res_2124_ = l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(v_pu_boxed_2122_, v_e_2118_, v_t_boxed_2123_, v_toPure_2120_, v_____do__lift_2121_);
lean_dec_ref(v_____do__lift_2121_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg(uint8_t v_pu_2125_, uint8_t v_t_2126_, lean_object* v_inst_2127_, lean_object* v_inst_2128_, lean_object* v_e_2129_){
_start:
{
lean_object* v_toApplicative_2130_; lean_object* v_toBind_2131_; lean_object* v_toPure_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___f_2135_; lean_object* v___x_2136_; 
v_toApplicative_2130_ = lean_ctor_get(v_inst_2128_, 0);
lean_inc_ref(v_toApplicative_2130_);
v_toBind_2131_ = lean_ctor_get(v_inst_2128_, 1);
lean_inc(v_toBind_2131_);
lean_dec_ref(v_inst_2128_);
v_toPure_2132_ = lean_ctor_get(v_toApplicative_2130_, 1);
lean_inc(v_toPure_2132_);
lean_dec_ref(v_toApplicative_2130_);
v___x_2133_ = lean_box(v_pu_2125_);
v___x_2134_ = lean_box(v_t_2126_);
v___f_2135_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2135_, 0, v___x_2133_);
lean_closure_set(v___f_2135_, 1, v_e_2129_);
lean_closure_set(v___f_2135_, 2, v___x_2134_);
lean_closure_set(v___f_2135_, 3, v_toPure_2132_);
v___x_2136_ = lean_apply_4(v_toBind_2131_, lean_box(0), lean_box(0), v_inst_2127_, v___f_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(lean_object* v_pu_2137_, lean_object* v_t_2138_, lean_object* v_inst_2139_, lean_object* v_inst_2140_, lean_object* v_e_2141_){
_start:
{
uint8_t v_pu_boxed_2142_; uint8_t v_t_boxed_2143_; lean_object* v_res_2144_; 
v_pu_boxed_2142_ = lean_unbox(v_pu_2137_);
v_t_boxed_2143_ = lean_unbox(v_t_2138_);
v_res_2144_ = l_Lean_Compiler_LCNF_normLetValue___redArg(v_pu_boxed_2142_, v_t_boxed_2143_, v_inst_2139_, v_inst_2140_, v_e_2141_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue(lean_object* v_m_2145_, uint8_t v_pu_2146_, uint8_t v_t_2147_, lean_object* v_inst_2148_, lean_object* v_inst_2149_, lean_object* v_e_2150_){
_start:
{
lean_object* v_toApplicative_2151_; lean_object* v_toBind_2152_; lean_object* v_toPure_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___f_2156_; lean_object* v___x_2157_; 
v_toApplicative_2151_ = lean_ctor_get(v_inst_2149_, 0);
lean_inc_ref(v_toApplicative_2151_);
v_toBind_2152_ = lean_ctor_get(v_inst_2149_, 1);
lean_inc(v_toBind_2152_);
lean_dec_ref(v_inst_2149_);
v_toPure_2153_ = lean_ctor_get(v_toApplicative_2151_, 1);
lean_inc(v_toPure_2153_);
lean_dec_ref(v_toApplicative_2151_);
v___x_2154_ = lean_box(v_pu_2146_);
v___x_2155_ = lean_box(v_t_2147_);
v___f_2156_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2156_, 0, v___x_2154_);
lean_closure_set(v___f_2156_, 1, v_e_2150_);
lean_closure_set(v___f_2156_, 2, v___x_2155_);
lean_closure_set(v___f_2156_, 3, v_toPure_2153_);
v___x_2157_ = lean_apply_4(v_toBind_2152_, lean_box(0), lean_box(0), v_inst_2148_, v___f_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___boxed(lean_object* v_m_2158_, lean_object* v_pu_2159_, lean_object* v_t_2160_, lean_object* v_inst_2161_, lean_object* v_inst_2162_, lean_object* v_e_2163_){
_start:
{
uint8_t v_pu_boxed_2164_; uint8_t v_t_boxed_2165_; lean_object* v_res_2166_; 
v_pu_boxed_2164_ = lean_unbox(v_pu_2159_);
v_t_boxed_2165_ = lean_unbox(v_t_2160_);
v_res_2166_ = l_Lean_Compiler_LCNF_normLetValue(v_m_2158_, v_pu_boxed_2164_, v_t_boxed_2165_, v_inst_2161_, v_inst_2162_, v_e_2163_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore(uint8_t v_pu_2167_, lean_object* v_s_2168_, lean_object* v_e_2169_, uint8_t v_translator_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2167_, v_s_2168_, v_translator_2170_, v_e_2169_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore___boxed(lean_object* v_pu_2172_, lean_object* v_s_2173_, lean_object* v_e_2174_, lean_object* v_translator_2175_){
_start:
{
uint8_t v_pu_boxed_2176_; uint8_t v_translator_boxed_2177_; lean_object* v_res_2178_; 
v_pu_boxed_2176_ = lean_unbox(v_pu_2172_);
v_translator_boxed_2177_ = lean_unbox(v_translator_2175_);
v_res_2178_ = l_Lean_Compiler_LCNF_normExprCore(v_pu_boxed_2176_, v_s_2173_, v_e_2174_, v_translator_boxed_2177_);
lean_dec_ref(v_s_2173_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(uint8_t v_pu_2179_, lean_object* v_args_2180_, uint8_t v_t_2181_, lean_object* v_toPure_2182_, lean_object* v_____do__lift_2183_){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_2179_, v_____do__lift_2183_, v_args_2180_, v_t_2181_);
v___x_2185_ = lean_apply_2(v_toPure_2182_, lean_box(0), v___x_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(lean_object* v_pu_2186_, lean_object* v_args_2187_, lean_object* v_t_2188_, lean_object* v_toPure_2189_, lean_object* v_____do__lift_2190_){
_start:
{
uint8_t v_pu_boxed_2191_; uint8_t v_t_boxed_2192_; lean_object* v_res_2193_; 
v_pu_boxed_2191_ = lean_unbox(v_pu_2186_);
v_t_boxed_2192_ = lean_unbox(v_t_2188_);
v_res_2193_ = l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(v_pu_boxed_2191_, v_args_2187_, v_t_boxed_2192_, v_toPure_2189_, v_____do__lift_2190_);
lean_dec_ref(v_____do__lift_2190_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg(uint8_t v_pu_2194_, uint8_t v_t_2195_, lean_object* v_inst_2196_, lean_object* v_inst_2197_, lean_object* v_args_2198_){
_start:
{
lean_object* v_toApplicative_2199_; lean_object* v_toBind_2200_; lean_object* v_toPure_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___f_2204_; lean_object* v___x_2205_; 
v_toApplicative_2199_ = lean_ctor_get(v_inst_2197_, 0);
lean_inc_ref(v_toApplicative_2199_);
v_toBind_2200_ = lean_ctor_get(v_inst_2197_, 1);
lean_inc(v_toBind_2200_);
lean_dec_ref(v_inst_2197_);
v_toPure_2201_ = lean_ctor_get(v_toApplicative_2199_, 1);
lean_inc(v_toPure_2201_);
lean_dec_ref(v_toApplicative_2199_);
v___x_2202_ = lean_box(v_pu_2194_);
v___x_2203_ = lean_box(v_t_2195_);
v___f_2204_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2204_, 0, v___x_2202_);
lean_closure_set(v___f_2204_, 1, v_args_2198_);
lean_closure_set(v___f_2204_, 2, v___x_2203_);
lean_closure_set(v___f_2204_, 3, v_toPure_2201_);
v___x_2205_ = lean_apply_4(v_toBind_2200_, lean_box(0), lean_box(0), v_inst_2196_, v___f_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___boxed(lean_object* v_pu_2206_, lean_object* v_t_2207_, lean_object* v_inst_2208_, lean_object* v_inst_2209_, lean_object* v_args_2210_){
_start:
{
uint8_t v_pu_boxed_2211_; uint8_t v_t_boxed_2212_; lean_object* v_res_2213_; 
v_pu_boxed_2211_ = lean_unbox(v_pu_2206_);
v_t_boxed_2212_ = lean_unbox(v_t_2207_);
v_res_2213_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_boxed_2211_, v_t_boxed_2212_, v_inst_2208_, v_inst_2209_, v_args_2210_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs(lean_object* v_m_2214_, uint8_t v_pu_2215_, uint8_t v_t_2216_, lean_object* v_inst_2217_, lean_object* v_inst_2218_, lean_object* v_args_2219_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_2215_, v_t_2216_, v_inst_2217_, v_inst_2218_, v_args_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___boxed(lean_object* v_m_2221_, lean_object* v_pu_2222_, lean_object* v_t_2223_, lean_object* v_inst_2224_, lean_object* v_inst_2225_, lean_object* v_args_2226_){
_start:
{
uint8_t v_pu_boxed_2227_; uint8_t v_t_boxed_2228_; lean_object* v_res_2229_; 
v_pu_boxed_2227_ = lean_unbox(v_pu_2222_);
v_t_boxed_2228_ = lean_unbox(v_t_2223_);
v_res_2229_ = l_Lean_Compiler_LCNF_normArgs(v_m_2221_, v_pu_boxed_2227_, v_t_boxed_2228_, v_inst_2224_, v_inst_2225_, v_args_2226_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object* v_binderName_2230_, lean_object* v_a_2231_){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v_lctx_2235_; lean_object* v_nextIdx_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2249_; 
v___x_2233_ = lean_st_ref_get(v_a_2231_);
v___x_2234_ = lean_st_ref_take(v_a_2231_);
v_lctx_2235_ = lean_ctor_get(v___x_2234_, 0);
v_nextIdx_2236_ = lean_ctor_get(v___x_2234_, 1);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2238_ = v___x_2234_;
v_isShared_2239_ = v_isSharedCheck_2249_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_nextIdx_2236_);
lean_inc(v_lctx_2235_);
lean_dec(v___x_2234_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2249_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2243_; 
v___x_2240_ = lean_unsigned_to_nat(1u);
v___x_2241_ = lean_nat_add(v_nextIdx_2236_, v___x_2240_);
lean_dec(v_nextIdx_2236_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 1, v___x_2241_);
v___x_2243_ = v___x_2238_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_lctx_2235_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v___x_2241_);
v___x_2243_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
lean_object* v___x_2244_; lean_object* v_nextIdx_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2244_ = lean_st_ref_set(v_a_2231_, v___x_2243_);
v_nextIdx_2245_ = lean_ctor_get(v___x_2233_, 1);
lean_inc(v_nextIdx_2245_);
lean_dec(v___x_2233_);
v___x_2246_ = l_Lean_Name_num___override(v_binderName_2230_, v_nextIdx_2245_);
v___x_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
return v___x_2247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(lean_object* v_binderName_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2250_, v_a_2251_);
lean_dec(v_a_2251_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object* v_binderName_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2254_, v_a_2256_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(lean_object* v_binderName_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_Lean_Compiler_LCNF_mkFreshBinderName(v_binderName_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec_ref(v_a_2262_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(lean_object* v_binderName_2268_, lean_object* v_baseName_2269_, lean_object* v_a_2270_){
_start:
{
uint8_t v___x_2272_; 
v___x_2272_ = l_Lean_Name_isAnonymous(v_binderName_2268_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; 
lean_dec(v_baseName_2269_);
v___x_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2273_, 0, v_binderName_2268_);
return v___x_2273_;
}
else
{
lean_object* v___x_2274_; 
lean_dec(v_binderName_2268_);
v___x_2274_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_baseName_2269_, v_a_2270_);
return v___x_2274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(lean_object* v_binderName_2275_, lean_object* v_baseName_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2275_, v_baseName_2276_, v_a_2277_);
lean_dec(v_a_2277_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous(lean_object* v_binderName_2280_, lean_object* v_baseName_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2280_, v_baseName_2281_, v_a_2283_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(lean_object* v_binderName_2288_, lean_object* v_baseName_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_Compiler_LCNF_ensureNotAnonymous(v_binderName_2288_, v_baseName_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(lean_object* v___y_2296_){
_start:
{
lean_object* v___x_2298_; lean_object* v_ngen_2299_; lean_object* v_namePrefix_2300_; lean_object* v_idx_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2330_; 
v___x_2298_ = lean_st_ref_get(v___y_2296_);
v_ngen_2299_ = lean_ctor_get(v___x_2298_, 2);
lean_inc_ref(v_ngen_2299_);
lean_dec(v___x_2298_);
v_namePrefix_2300_ = lean_ctor_get(v_ngen_2299_, 0);
v_idx_2301_ = lean_ctor_get(v_ngen_2299_, 1);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_ngen_2299_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2303_ = v_ngen_2299_;
v_isShared_2304_ = v_isSharedCheck_2330_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_idx_2301_);
lean_inc(v_namePrefix_2300_);
lean_dec(v_ngen_2299_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2330_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2305_; lean_object* v_env_2306_; lean_object* v_nextMacroScope_2307_; lean_object* v_auxDeclNGen_2308_; lean_object* v_traceState_2309_; lean_object* v_cache_2310_; lean_object* v_messages_2311_; lean_object* v_infoState_2312_; lean_object* v_snapshotTasks_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2328_; 
v___x_2305_ = lean_st_ref_take(v___y_2296_);
v_env_2306_ = lean_ctor_get(v___x_2305_, 0);
v_nextMacroScope_2307_ = lean_ctor_get(v___x_2305_, 1);
v_auxDeclNGen_2308_ = lean_ctor_get(v___x_2305_, 3);
v_traceState_2309_ = lean_ctor_get(v___x_2305_, 4);
v_cache_2310_ = lean_ctor_get(v___x_2305_, 5);
v_messages_2311_ = lean_ctor_get(v___x_2305_, 6);
v_infoState_2312_ = lean_ctor_get(v___x_2305_, 7);
v_snapshotTasks_2313_ = lean_ctor_get(v___x_2305_, 8);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2328_ == 0)
{
lean_object* v_unused_2329_; 
v_unused_2329_ = lean_ctor_get(v___x_2305_, 2);
lean_dec(v_unused_2329_);
v___x_2315_ = v___x_2305_;
v_isShared_2316_ = v_isSharedCheck_2328_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_snapshotTasks_2313_);
lean_inc(v_infoState_2312_);
lean_inc(v_messages_2311_);
lean_inc(v_cache_2310_);
lean_inc(v_traceState_2309_);
lean_inc(v_auxDeclNGen_2308_);
lean_inc(v_nextMacroScope_2307_);
lean_inc(v_env_2306_);
lean_dec(v___x_2305_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2328_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v_r_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2321_; 
lean_inc(v_idx_2301_);
lean_inc(v_namePrefix_2300_);
v_r_2317_ = l_Lean_Name_num___override(v_namePrefix_2300_, v_idx_2301_);
v___x_2318_ = lean_unsigned_to_nat(1u);
v___x_2319_ = lean_nat_add(v_idx_2301_, v___x_2318_);
lean_dec(v_idx_2301_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 1, v___x_2319_);
v___x_2321_ = v___x_2303_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_namePrefix_2300_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
lean_object* v___x_2323_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 2, v___x_2321_);
v___x_2323_ = v___x_2315_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_env_2306_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_nextMacroScope_2307_);
lean_ctor_set(v_reuseFailAlloc_2326_, 2, v___x_2321_);
lean_ctor_set(v_reuseFailAlloc_2326_, 3, v_auxDeclNGen_2308_);
lean_ctor_set(v_reuseFailAlloc_2326_, 4, v_traceState_2309_);
lean_ctor_set(v_reuseFailAlloc_2326_, 5, v_cache_2310_);
lean_ctor_set(v_reuseFailAlloc_2326_, 6, v_messages_2311_);
lean_ctor_set(v_reuseFailAlloc_2326_, 7, v_infoState_2312_);
lean_ctor_set(v_reuseFailAlloc_2326_, 8, v_snapshotTasks_2313_);
v___x_2323_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_st_ref_set(v___y_2296_, v___x_2323_);
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v_r_2317_);
return v___x_2325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2331_);
lean_dec(v___y_2331_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
v___x_2339_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2337_);
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t v_pu_2357_, lean_object* v_binderName_2358_, lean_object* v_type_2359_, uint8_t v_borrow_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2390_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_2369_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2358_, v___x_2368_, v_a_2362_);
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2390_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2390_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v_lctx_2375_; lean_object* v_nextIdx_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2389_; 
v___x_2374_ = lean_st_ref_take(v_a_2362_);
v_lctx_2375_ = lean_ctor_get(v___x_2374_, 0);
v_nextIdx_2376_ = lean_ctor_get(v___x_2374_, 1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2378_ = v___x_2374_;
v_isShared_2379_ = v_isSharedCheck_2389_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_nextIdx_2376_);
lean_inc(v_lctx_2375_);
lean_dec(v___x_2374_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2389_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2380_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2380_, 0, v_a_2367_);
lean_ctor_set(v___x_2380_, 1, v_a_2370_);
lean_ctor_set(v___x_2380_, 2, v_type_2359_);
lean_ctor_set_uint8(v___x_2380_, sizeof(void*)*3, v_borrow_2360_);
lean_inc_ref(v___x_2380_);
v___x_2381_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2357_, v_lctx_2375_, v___x_2380_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2381_);
v___x_2383_ = v___x_2378_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_nextIdx_2376_);
v___x_2383_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2384_; lean_object* v___x_2386_; 
v___x_2384_ = lean_st_ref_set(v_a_2362_, v___x_2383_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2380_);
v___x_2386_ = v___x_2372_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2380_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec_ref(v_type_2359_);
lean_dec(v_binderName_2358_);
v_a_2391_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2366_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2366_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam___boxed(lean_object* v_pu_2399_, lean_object* v_binderName_2400_, lean_object* v_type_2401_, lean_object* v_borrow_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
uint8_t v_pu_boxed_2408_; uint8_t v_borrow_boxed_2409_; lean_object* v_res_2410_; 
v_pu_boxed_2408_ = lean_unbox(v_pu_2399_);
v_borrow_boxed_2409_ = lean_unbox(v_borrow_2402_);
v_res_2410_ = l_Lean_Compiler_LCNF_mkParam(v_pu_boxed_2408_, v_binderName_2400_, v_type_2401_, v_borrow_boxed_2409_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2414_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t v_pu_2426_, lean_object* v_binderName_2427_, lean_object* v_type_2428_, lean_object* v_value_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2459_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v___x_2437_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2438_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2427_, v___x_2437_, v_a_2431_);
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2441_ = v___x_2438_;
v_isShared_2442_ = v_isSharedCheck_2459_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2438_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2459_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; lean_object* v_lctx_2444_; lean_object* v_nextIdx_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2458_; 
v___x_2443_ = lean_st_ref_take(v_a_2431_);
v_lctx_2444_ = lean_ctor_get(v___x_2443_, 0);
v_nextIdx_2445_ = lean_ctor_get(v___x_2443_, 1);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2447_ = v___x_2443_;
v_isShared_2448_ = v_isSharedCheck_2458_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_nextIdx_2445_);
lean_inc(v_lctx_2444_);
lean_dec(v___x_2443_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2458_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2449_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2449_, 0, v_a_2436_);
lean_ctor_set(v___x_2449_, 1, v_a_2439_);
lean_ctor_set(v___x_2449_, 2, v_type_2428_);
lean_ctor_set(v___x_2449_, 3, v_value_2429_);
lean_inc_ref(v___x_2449_);
v___x_2450_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2426_, v_lctx_2444_, v___x_2449_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v___x_2450_);
v___x_2452_ = v___x_2447_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_nextIdx_2445_);
v___x_2452_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2453_ = lean_st_ref_set(v_a_2431_, v___x_2452_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 0, v___x_2449_);
v___x_2455_ = v___x_2441_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2449_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec(v_value_2429_);
lean_dec_ref(v_type_2428_);
lean_dec(v_binderName_2427_);
v_a_2460_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2435_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2435_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl___boxed(lean_object* v_pu_2468_, lean_object* v_binderName_2469_, lean_object* v_type_2470_, lean_object* v_value_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
uint8_t v_pu_boxed_2477_; lean_object* v_res_2478_; 
v_pu_boxed_2477_ = lean_unbox(v_pu_2468_);
v_res_2478_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_boxed_2477_, v_binderName_2469_, v_type_2470_, v_value_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t v_pu_2482_, lean_object* v_binderName_2483_, lean_object* v_type_2484_, lean_object* v_params_2485_, lean_object* v_value_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2516_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2492_, 1);
v___x_2494_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFunDecl___closed__1));
v___x_2495_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2483_, v___x_2494_, v_a_2488_);
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2516_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2516_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v_lctx_2501_; lean_object* v_nextIdx_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2515_; 
v___x_2500_ = lean_st_ref_take(v_a_2488_);
v_lctx_2501_ = lean_ctor_get(v___x_2500_, 0);
v_nextIdx_2502_ = lean_ctor_get(v___x_2500_, 1);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2504_ = v___x_2500_;
v_isShared_2505_ = v_isSharedCheck_2515_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_nextIdx_2502_);
lean_inc(v_lctx_2501_);
lean_dec(v___x_2500_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2515_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2506_, 0, v_a_2493_);
lean_ctor_set(v___x_2506_, 1, v_a_2496_);
lean_ctor_set(v___x_2506_, 2, v_params_2485_);
lean_ctor_set(v___x_2506_, 3, v_type_2484_);
lean_ctor_set(v___x_2506_, 4, v_value_2486_);
lean_inc_ref(v___x_2506_);
v___x_2507_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2482_, v_lctx_2501_, v___x_2506_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 0, v___x_2507_);
v___x_2509_ = v___x_2504_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_nextIdx_2502_);
v___x_2509_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2510_ = lean_st_ref_set(v_a_2488_, v___x_2509_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v___x_2506_);
v___x_2512_ = v___x_2498_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2506_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_dec_ref(v_value_2486_);
lean_dec_ref(v_params_2485_);
lean_dec_ref(v_type_2484_);
lean_dec(v_binderName_2483_);
v_a_2517_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2492_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2492_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl___boxed(lean_object* v_pu_2525_, lean_object* v_binderName_2526_, lean_object* v_type_2527_, lean_object* v_params_2528_, lean_object* v_value_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_){
_start:
{
uint8_t v_pu_boxed_2535_; lean_object* v_res_2536_; 
v_pu_boxed_2535_ = lean_unbox(v_pu_2525_);
v_res_2536_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_boxed_2535_, v_binderName_2526_, v_type_2527_, v_params_2528_, v_value_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t v_pu_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v_a_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2543_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2544_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2543_, v_a_2539_);
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref(v___x_2544_);
v___x_2546_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2547_ = lean_box(1);
v___x_2548_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2537_, v_a_2545_, v___x_2546_, v___x_2547_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(lean_object* v_pu_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
uint8_t v_pu_boxed_2555_; lean_object* v_res_2556_; 
v_pu_boxed_2555_ = lean_unbox(v_pu_2549_);
v_res_2556_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_boxed_2555_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t v_pu_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2574_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2566_ = v___x_2563_;
v_isShared_2567_ = v_isSharedCheck_2574_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2574_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v_fvarId_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2572_; 
v_fvarId_2568_ = lean_ctor_get(v_a_2564_, 0);
lean_inc(v_fvarId_2568_);
v___x_2569_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2569_, 0, v_fvarId_2568_);
v___x_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2570_, 0, v_a_2564_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2570_);
v___x_2572_ = v___x_2566_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
v_a_2575_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2563_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2563_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased___boxed(lean_object* v_pu_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
uint8_t v_pu_boxed_2589_; lean_object* v_res_2590_; 
v_pu_boxed_2589_ = lean_unbox(v_pu_2583_);
v_res_2590_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_boxed_2589_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t v_pu_2591_, lean_object* v_p_2592_, lean_object* v_type_2593_, lean_object* v_a_2594_){
_start:
{
lean_object* v_fvarId_2596_; lean_object* v_binderName_2597_; lean_object* v_type_2598_; uint8_t v_borrow_2599_; size_t v___x_2600_; size_t v___x_2601_; uint8_t v___x_2602_; 
v_fvarId_2596_ = lean_ctor_get(v_p_2592_, 0);
v_binderName_2597_ = lean_ctor_get(v_p_2592_, 1);
v_type_2598_ = lean_ctor_get(v_p_2592_, 2);
v_borrow_2599_ = lean_ctor_get_uint8(v_p_2592_, sizeof(void*)*3);
v___x_2600_ = lean_ptr_addr(v_type_2593_);
v___x_2601_ = lean_ptr_addr(v_type_2598_);
v___x_2602_ = lean_usize_dec_eq(v___x_2600_, v___x_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2622_; 
lean_inc(v_binderName_2597_);
lean_inc(v_fvarId_2596_);
v_isSharedCheck_2622_ = !lean_is_exclusive(v_p_2592_);
if (v_isSharedCheck_2622_ == 0)
{
lean_object* v_unused_2623_; lean_object* v_unused_2624_; lean_object* v_unused_2625_; 
v_unused_2623_ = lean_ctor_get(v_p_2592_, 2);
lean_dec(v_unused_2623_);
v_unused_2624_ = lean_ctor_get(v_p_2592_, 1);
lean_dec(v_unused_2624_);
v_unused_2625_ = lean_ctor_get(v_p_2592_, 0);
lean_dec(v_unused_2625_);
v___x_2604_ = v_p_2592_;
v_isShared_2605_ = v_isSharedCheck_2622_;
goto v_resetjp_2603_;
}
else
{
lean_dec(v_p_2592_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2622_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; lean_object* v_lctx_2607_; lean_object* v_nextIdx_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2621_; 
v___x_2606_ = lean_st_ref_take(v_a_2594_);
v_lctx_2607_ = lean_ctor_get(v___x_2606_, 0);
v_nextIdx_2608_ = lean_ctor_get(v___x_2606_, 1);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2610_ = v___x_2606_;
v_isShared_2611_ = v_isSharedCheck_2621_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_nextIdx_2608_);
lean_inc(v_lctx_2607_);
lean_dec(v___x_2606_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2621_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v_p_2613_; 
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 2, v_type_2593_);
v_p_2613_ = v___x_2604_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_fvarId_2596_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v_binderName_2597_);
lean_ctor_set(v_reuseFailAlloc_2620_, 2, v_type_2593_);
lean_ctor_set_uint8(v_reuseFailAlloc_2620_, sizeof(void*)*3, v_borrow_2599_);
v_p_2613_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2614_; lean_object* v___x_2616_; 
lean_inc_ref(v_p_2613_);
v___x_2614_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2591_, v_lctx_2607_, v_p_2613_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___x_2614_);
v___x_2616_ = v___x_2610_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2614_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_nextIdx_2608_);
v___x_2616_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2617_ = lean_st_ref_set(v_a_2594_, v___x_2616_);
v___x_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2618_, 0, v_p_2613_);
return v___x_2618_;
}
}
}
}
}
else
{
lean_object* v___x_2626_; 
lean_dec_ref(v_type_2593_);
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_p_2592_);
return v___x_2626_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(lean_object* v_pu_2627_, lean_object* v_p_2628_, lean_object* v_type_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
uint8_t v_pu_boxed_2632_; lean_object* v_res_2633_; 
v_pu_boxed_2632_ = lean_unbox(v_pu_2627_);
v_res_2633_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_boxed_2632_, v_p_2628_, v_type_2629_, v_a_2630_);
lean_dec(v_a_2630_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(uint8_t v_pu_2634_, lean_object* v_p_2635_, lean_object* v_type_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_2634_, v_p_2635_, v_type_2636_, v_a_2638_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object* v_pu_2643_, lean_object* v_p_2644_, lean_object* v_type_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
uint8_t v_pu_boxed_2651_; lean_object* v_res_2652_; 
v_pu_boxed_2651_ = lean_unbox(v_pu_2643_);
v_res_2652_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(v_pu_boxed_2651_, v_p_2644_, v_type_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
lean_dec(v_a_2649_);
lean_dec_ref(v_a_2648_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t v_pu_2653_, lean_object* v_p_2654_, uint8_t v_borrow_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v_fvarId_2658_; lean_object* v_binderName_2659_; lean_object* v_type_2660_; uint8_t v_borrow_2661_; 
v_fvarId_2658_ = lean_ctor_get(v_p_2654_, 0);
v_binderName_2659_ = lean_ctor_get(v_p_2654_, 1);
v_type_2660_ = lean_ctor_get(v_p_2654_, 2);
v_borrow_2661_ = lean_ctor_get_uint8(v_p_2654_, sizeof(void*)*3);
if (v_borrow_2655_ == 0)
{
if (v_borrow_2661_ == 0)
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2677_, 0, v_p_2654_);
return v___x_2677_;
}
else
{
lean_inc_ref(v_type_2660_);
lean_inc(v_binderName_2659_);
lean_inc(v_fvarId_2658_);
lean_dec_ref(v_p_2654_);
goto v___jp_2662_;
}
}
else
{
if (v_borrow_2661_ == 0)
{
lean_inc_ref(v_type_2660_);
lean_inc(v_binderName_2659_);
lean_inc(v_fvarId_2658_);
lean_dec_ref(v_p_2654_);
goto v___jp_2662_;
}
else
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v_p_2654_);
return v___x_2678_;
}
}
v___jp_2662_:
{
lean_object* v___x_2663_; lean_object* v_lctx_2664_; lean_object* v_nextIdx_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2676_; 
v___x_2663_ = lean_st_ref_take(v_a_2656_);
v_lctx_2664_ = lean_ctor_get(v___x_2663_, 0);
v_nextIdx_2665_ = lean_ctor_get(v___x_2663_, 1);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2667_ = v___x_2663_;
v_isShared_2668_ = v_isSharedCheck_2676_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_nextIdx_2665_);
lean_inc(v_lctx_2664_);
lean_dec(v___x_2663_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2676_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v_p_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
v_p_2669_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_p_2669_, 0, v_fvarId_2658_);
lean_ctor_set(v_p_2669_, 1, v_binderName_2659_);
lean_ctor_set(v_p_2669_, 2, v_type_2660_);
lean_ctor_set_uint8(v_p_2669_, sizeof(void*)*3, v_borrow_2655_);
lean_inc_ref(v_p_2669_);
v___x_2670_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2653_, v_lctx_2664_, v_p_2669_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v___x_2670_);
v___x_2672_ = v___x_2667_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_nextIdx_2665_);
v___x_2672_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = lean_st_ref_set(v_a_2656_, v___x_2672_);
v___x_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2674_, 0, v_p_2669_);
return v___x_2674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(lean_object* v_pu_2679_, lean_object* v_p_2680_, lean_object* v_borrow_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
uint8_t v_pu_boxed_2684_; uint8_t v_borrow_boxed_2685_; lean_object* v_res_2686_; 
v_pu_boxed_2684_ = lean_unbox(v_pu_2679_);
v_borrow_boxed_2685_ = lean_unbox(v_borrow_2681_);
v_res_2686_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_boxed_2684_, v_p_2680_, v_borrow_boxed_2685_, v_a_2682_);
lean_dec(v_a_2682_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(uint8_t v_pu_2687_, lean_object* v_p_2688_, uint8_t v_borrow_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_2687_, v_p_2688_, v_borrow_2689_, v_a_2691_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(lean_object* v_pu_2696_, lean_object* v_p_2697_, lean_object* v_borrow_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
uint8_t v_pu_boxed_2704_; uint8_t v_borrow_boxed_2705_; lean_object* v_res_2706_; 
v_pu_boxed_2704_ = lean_unbox(v_pu_2696_);
v_borrow_boxed_2705_ = lean_unbox(v_borrow_2698_);
v_res_2706_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(v_pu_boxed_2704_, v_p_2697_, v_borrow_boxed_2705_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
lean_dec(v_a_2702_);
lean_dec_ref(v_a_2701_);
lean_dec(v_a_2700_);
lean_dec_ref(v_a_2699_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t v_pu_2707_, lean_object* v_decl_2708_, lean_object* v_type_2709_, lean_object* v_value_2710_, lean_object* v_a_2711_){
_start:
{
lean_object* v_fvarId_2713_; lean_object* v_binderName_2714_; lean_object* v_type_2715_; lean_object* v_value_2716_; uint8_t v___y_2718_; size_t v___x_2744_; size_t v___x_2745_; uint8_t v___x_2746_; 
v_fvarId_2713_ = lean_ctor_get(v_decl_2708_, 0);
v_binderName_2714_ = lean_ctor_get(v_decl_2708_, 1);
v_type_2715_ = lean_ctor_get(v_decl_2708_, 2);
v_value_2716_ = lean_ctor_get(v_decl_2708_, 3);
v___x_2744_ = lean_ptr_addr(v_type_2709_);
v___x_2745_ = lean_ptr_addr(v_type_2715_);
v___x_2746_ = lean_usize_dec_eq(v___x_2744_, v___x_2745_);
if (v___x_2746_ == 0)
{
v___y_2718_ = v___x_2746_;
goto v___jp_2717_;
}
else
{
size_t v___x_2747_; size_t v___x_2748_; uint8_t v___x_2749_; 
v___x_2747_ = lean_ptr_addr(v_value_2710_);
v___x_2748_ = lean_ptr_addr(v_value_2716_);
v___x_2749_ = lean_usize_dec_eq(v___x_2747_, v___x_2748_);
v___y_2718_ = v___x_2749_;
goto v___jp_2717_;
}
v___jp_2717_:
{
if (v___y_2718_ == 0)
{
lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2738_; 
lean_inc(v_binderName_2714_);
lean_inc(v_fvarId_2713_);
v_isSharedCheck_2738_ = !lean_is_exclusive(v_decl_2708_);
if (v_isSharedCheck_2738_ == 0)
{
lean_object* v_unused_2739_; lean_object* v_unused_2740_; lean_object* v_unused_2741_; lean_object* v_unused_2742_; 
v_unused_2739_ = lean_ctor_get(v_decl_2708_, 3);
lean_dec(v_unused_2739_);
v_unused_2740_ = lean_ctor_get(v_decl_2708_, 2);
lean_dec(v_unused_2740_);
v_unused_2741_ = lean_ctor_get(v_decl_2708_, 1);
lean_dec(v_unused_2741_);
v_unused_2742_ = lean_ctor_get(v_decl_2708_, 0);
lean_dec(v_unused_2742_);
v___x_2720_ = v_decl_2708_;
v_isShared_2721_ = v_isSharedCheck_2738_;
goto v_resetjp_2719_;
}
else
{
lean_dec(v_decl_2708_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2738_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2722_; lean_object* v_lctx_2723_; lean_object* v_nextIdx_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2737_; 
v___x_2722_ = lean_st_ref_take(v_a_2711_);
v_lctx_2723_ = lean_ctor_get(v___x_2722_, 0);
v_nextIdx_2724_ = lean_ctor_get(v___x_2722_, 1);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2726_ = v___x_2722_;
v_isShared_2727_ = v_isSharedCheck_2737_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_nextIdx_2724_);
lean_inc(v_lctx_2723_);
lean_dec(v___x_2722_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2737_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v_decl_2729_; 
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 3, v_value_2710_);
lean_ctor_set(v___x_2720_, 2, v_type_2709_);
v_decl_2729_ = v___x_2720_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_fvarId_2713_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_binderName_2714_);
lean_ctor_set(v_reuseFailAlloc_2736_, 2, v_type_2709_);
lean_ctor_set(v_reuseFailAlloc_2736_, 3, v_value_2710_);
v_decl_2729_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
lean_object* v___x_2730_; lean_object* v___x_2732_; 
lean_inc_ref(v_decl_2729_);
v___x_2730_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2707_, v_lctx_2723_, v_decl_2729_);
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 0, v___x_2730_);
v___x_2732_ = v___x_2726_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2730_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_nextIdx_2724_);
v___x_2732_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = lean_st_ref_set(v_a_2711_, v___x_2732_);
v___x_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2734_, 0, v_decl_2729_);
return v___x_2734_;
}
}
}
}
}
else
{
lean_object* v___x_2743_; 
lean_dec(v_value_2710_);
lean_dec_ref(v_type_2709_);
v___x_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2743_, 0, v_decl_2708_);
return v___x_2743_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(lean_object* v_pu_2750_, lean_object* v_decl_2751_, lean_object* v_type_2752_, lean_object* v_value_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_){
_start:
{
uint8_t v_pu_boxed_2756_; lean_object* v_res_2757_; 
v_pu_boxed_2756_ = lean_unbox(v_pu_2750_);
v_res_2757_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_boxed_2756_, v_decl_2751_, v_type_2752_, v_value_2753_, v_a_2754_);
lean_dec(v_a_2754_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(uint8_t v_pu_2758_, lean_object* v_decl_2759_, lean_object* v_type_2760_, lean_object* v_value_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2758_, v_decl_2759_, v_type_2760_, v_value_2761_, v_a_2763_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object* v_pu_2768_, lean_object* v_decl_2769_, lean_object* v_type_2770_, lean_object* v_value_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
uint8_t v_pu_boxed_2777_; lean_object* v_res_2778_; 
v_pu_boxed_2777_ = lean_unbox(v_pu_2768_);
v_res_2778_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(v_pu_boxed_2777_, v_decl_2769_, v_type_2770_, v_value_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t v_pu_2779_, lean_object* v_decl_2780_, lean_object* v_value_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v_type_2784_; lean_object* v___x_2785_; 
v_type_2784_ = lean_ctor_get(v_decl_2780_, 2);
lean_inc_ref(v_type_2784_);
v___x_2785_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2779_, v_decl_2780_, v_type_2784_, v_value_2781_, v_a_2782_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(lean_object* v_pu_2786_, lean_object* v_decl_2787_, lean_object* v_value_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_){
_start:
{
uint8_t v_pu_boxed_2791_; lean_object* v_res_2792_; 
v_pu_boxed_2791_ = lean_unbox(v_pu_2786_);
v_res_2792_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_boxed_2791_, v_decl_2787_, v_value_2788_, v_a_2789_);
lean_dec(v_a_2789_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(uint8_t v_pu_2793_, lean_object* v_decl_2794_, lean_object* v_value_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_2793_, v_decl_2794_, v_value_2795_, v_a_2797_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(lean_object* v_pu_2802_, lean_object* v_decl_2803_, lean_object* v_value_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_){
_start:
{
uint8_t v_pu_boxed_2810_; lean_object* v_res_2811_; 
v_pu_boxed_2810_ = lean_unbox(v_pu_2802_);
v_res_2811_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(v_pu_boxed_2810_, v_decl_2803_, v_value_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_2807_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t v_pu_2812_, lean_object* v_decl_2813_, lean_object* v_type_2814_, lean_object* v_params_2815_, lean_object* v_value_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v_fvarId_2819_; lean_object* v_binderName_2820_; lean_object* v_params_2821_; lean_object* v_type_2822_; lean_object* v_value_2823_; uint8_t v___y_2840_; size_t v___x_2845_; size_t v___x_2846_; uint8_t v___x_2847_; 
v_fvarId_2819_ = lean_ctor_get(v_decl_2813_, 0);
v_binderName_2820_ = lean_ctor_get(v_decl_2813_, 1);
v_params_2821_ = lean_ctor_get(v_decl_2813_, 2);
v_type_2822_ = lean_ctor_get(v_decl_2813_, 3);
v_value_2823_ = lean_ctor_get(v_decl_2813_, 4);
v___x_2845_ = lean_ptr_addr(v_type_2814_);
v___x_2846_ = lean_ptr_addr(v_type_2822_);
v___x_2847_ = lean_usize_dec_eq(v___x_2845_, v___x_2846_);
if (v___x_2847_ == 0)
{
v___y_2840_ = v___x_2847_;
goto v___jp_2839_;
}
else
{
size_t v___x_2848_; size_t v___x_2849_; uint8_t v___x_2850_; 
v___x_2848_ = lean_ptr_addr(v_params_2815_);
v___x_2849_ = lean_ptr_addr(v_params_2821_);
v___x_2850_ = lean_usize_dec_eq(v___x_2848_, v___x_2849_);
v___y_2840_ = v___x_2850_;
goto v___jp_2839_;
}
v___jp_2824_:
{
lean_object* v___x_2825_; lean_object* v_lctx_2826_; lean_object* v_nextIdx_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2838_; 
v___x_2825_ = lean_st_ref_take(v_a_2817_);
v_lctx_2826_ = lean_ctor_get(v___x_2825_, 0);
v_nextIdx_2827_ = lean_ctor_get(v___x_2825_, 1);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2829_ = v___x_2825_;
v_isShared_2830_ = v_isSharedCheck_2838_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_nextIdx_2827_);
lean_inc(v_lctx_2826_);
lean_dec(v___x_2825_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2838_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v_decl_2831_; lean_object* v___x_2832_; lean_object* v___x_2834_; 
v_decl_2831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_decl_2831_, 0, v_fvarId_2819_);
lean_ctor_set(v_decl_2831_, 1, v_binderName_2820_);
lean_ctor_set(v_decl_2831_, 2, v_params_2815_);
lean_ctor_set(v_decl_2831_, 3, v_type_2814_);
lean_ctor_set(v_decl_2831_, 4, v_value_2816_);
lean_inc_ref(v_decl_2831_);
v___x_2832_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2812_, v_lctx_2826_, v_decl_2831_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v___x_2832_);
v___x_2834_ = v___x_2829_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_nextIdx_2827_);
v___x_2834_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = lean_st_ref_set(v_a_2817_, v___x_2834_);
v___x_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2836_, 0, v_decl_2831_);
return v___x_2836_;
}
}
}
v___jp_2839_:
{
if (v___y_2840_ == 0)
{
lean_inc(v_binderName_2820_);
lean_inc(v_fvarId_2819_);
lean_dec_ref(v_decl_2813_);
goto v___jp_2824_;
}
else
{
size_t v___x_2841_; size_t v___x_2842_; uint8_t v___x_2843_; 
v___x_2841_ = lean_ptr_addr(v_value_2816_);
v___x_2842_ = lean_ptr_addr(v_value_2823_);
v___x_2843_ = lean_usize_dec_eq(v___x_2841_, v___x_2842_);
if (v___x_2843_ == 0)
{
lean_inc(v_binderName_2820_);
lean_inc(v_fvarId_2819_);
lean_dec_ref(v_decl_2813_);
goto v___jp_2824_;
}
else
{
lean_object* v___x_2844_; 
lean_dec_ref(v_value_2816_);
lean_dec_ref(v_params_2815_);
lean_dec_ref(v_type_2814_);
v___x_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2844_, 0, v_decl_2813_);
return v___x_2844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(lean_object* v_pu_2851_, lean_object* v_decl_2852_, lean_object* v_type_2853_, lean_object* v_params_2854_, lean_object* v_value_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_){
_start:
{
uint8_t v_pu_boxed_2858_; lean_object* v_res_2859_; 
v_pu_boxed_2858_ = lean_unbox(v_pu_2851_);
v_res_2859_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_boxed_2858_, v_decl_2852_, v_type_2853_, v_params_2854_, v_value_2855_, v_a_2856_);
lean_dec(v_a_2856_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(uint8_t v_pu_2860_, lean_object* v_decl_2861_, lean_object* v_type_2862_, lean_object* v_params_2863_, lean_object* v_value_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2860_, v_decl_2861_, v_type_2862_, v_params_2863_, v_value_2864_, v_a_2866_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object* v_pu_2871_, lean_object* v_decl_2872_, lean_object* v_type_2873_, lean_object* v_params_2874_, lean_object* v_value_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_){
_start:
{
uint8_t v_pu_boxed_2881_; lean_object* v_res_2882_; 
v_pu_boxed_2881_ = lean_unbox(v_pu_2871_);
v_res_2882_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(v_pu_boxed_2881_, v_decl_2872_, v_type_2873_, v_params_2874_, v_value_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_);
lean_dec(v_a_2879_);
lean_dec_ref(v_a_2878_);
lean_dec(v_a_2877_);
lean_dec_ref(v_a_2876_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(uint8_t v_pu_2883_, lean_object* v_decl_2884_, lean_object* v_type_2885_, lean_object* v_value_2886_, lean_object* v_a_2887_){
_start:
{
lean_object* v_params_2889_; lean_object* v___x_2890_; 
v_params_2889_ = lean_ctor_get(v_decl_2884_, 2);
lean_inc_ref(v_params_2889_);
v___x_2890_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2883_, v_decl_2884_, v_type_2885_, v_params_2889_, v_value_2886_, v_a_2887_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(lean_object* v_pu_2891_, lean_object* v_decl_2892_, lean_object* v_type_2893_, lean_object* v_value_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
uint8_t v_pu_boxed_2897_; lean_object* v_res_2898_; 
v_pu_boxed_2897_ = lean_unbox(v_pu_2891_);
v_res_2898_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(v_pu_boxed_2897_, v_decl_2892_, v_type_2893_, v_value_2894_, v_a_2895_);
lean_dec(v_a_2895_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27(uint8_t v_pu_2899_, lean_object* v_decl_2900_, lean_object* v_type_2901_, lean_object* v_value_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v_params_2908_; lean_object* v___x_2909_; 
v_params_2908_ = lean_ctor_get(v_decl_2900_, 2);
lean_inc_ref(v_params_2908_);
v___x_2909_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2899_, v_decl_2900_, v_type_2901_, v_params_2908_, v_value_2902_, v_a_2904_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(lean_object* v_pu_2910_, lean_object* v_decl_2911_, lean_object* v_type_2912_, lean_object* v_value_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_){
_start:
{
uint8_t v_pu_boxed_2919_; lean_object* v_res_2920_; 
v_pu_boxed_2919_ = lean_unbox(v_pu_2910_);
v_res_2920_ = l_Lean_Compiler_LCNF_FunDecl_update_x27(v_pu_boxed_2919_, v_decl_2911_, v_type_2912_, v_value_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_);
lean_dec(v_a_2917_);
lean_dec_ref(v_a_2916_);
lean_dec(v_a_2915_);
lean_dec_ref(v_a_2914_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(uint8_t v_pu_2921_, lean_object* v_decl_2922_, lean_object* v_value_2923_, lean_object* v_a_2924_){
_start:
{
lean_object* v_params_2926_; lean_object* v_type_2927_; lean_object* v___x_2928_; 
v_params_2926_ = lean_ctor_get(v_decl_2922_, 2);
lean_inc_ref(v_params_2926_);
v_type_2927_ = lean_ctor_get(v_decl_2922_, 3);
lean_inc_ref(v_type_2927_);
v___x_2928_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2921_, v_decl_2922_, v_type_2927_, v_params_2926_, v_value_2923_, v_a_2924_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(lean_object* v_pu_2929_, lean_object* v_decl_2930_, lean_object* v_value_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_){
_start:
{
uint8_t v_pu_boxed_2934_; lean_object* v_res_2935_; 
v_pu_boxed_2934_ = lean_unbox(v_pu_2929_);
v_res_2935_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(v_pu_boxed_2934_, v_decl_2930_, v_value_2931_, v_a_2932_);
lean_dec(v_a_2932_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue(uint8_t v_pu_2936_, lean_object* v_decl_2937_, lean_object* v_value_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v_params_2944_; lean_object* v_type_2945_; lean_object* v___x_2946_; 
v_params_2944_ = lean_ctor_get(v_decl_2937_, 2);
lean_inc_ref(v_params_2944_);
v_type_2945_ = lean_ctor_get(v_decl_2937_, 3);
lean_inc_ref(v_type_2945_);
v___x_2946_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2936_, v_decl_2937_, v_type_2945_, v_params_2944_, v_value_2938_, v_a_2940_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(lean_object* v_pu_2947_, lean_object* v_decl_2948_, lean_object* v_value_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
uint8_t v_pu_boxed_2955_; lean_object* v_res_2956_; 
v_pu_boxed_2955_ = lean_unbox(v_pu_2947_);
v_res_2956_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(v_pu_boxed_2955_, v_decl_2948_, v_value_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_);
lean_dec(v_a_2953_);
lean_dec_ref(v_a_2952_);
lean_dec(v_a_2951_);
lean_dec_ref(v_a_2950_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0(uint8_t v_pu_2957_, lean_object* v_p_2958_, lean_object* v_inst_2959_, lean_object* v_____do__lift_2960_){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = lean_box(v_pu_2957_);
v___x_2962_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_2962_, 0, v___x_2961_);
lean_closure_set(v___x_2962_, 1, v_p_2958_);
lean_closure_set(v___x_2962_, 2, v_____do__lift_2960_);
v___x_2963_ = lean_apply_2(v_inst_2959_, lean_box(0), v___x_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(lean_object* v_pu_2964_, lean_object* v_p_2965_, lean_object* v_inst_2966_, lean_object* v_____do__lift_2967_){
_start:
{
uint8_t v_pu_boxed_2968_; lean_object* v_res_2969_; 
v_pu_boxed_2968_ = lean_unbox(v_pu_2964_);
v_res_2969_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__0(v_pu_boxed_2968_, v_p_2965_, v_inst_2966_, v_____do__lift_2967_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1(uint8_t v_pu_2970_, uint8_t v_t_2971_, lean_object* v_type_2972_, lean_object* v_toPure_2973_, lean_object* v_____do__lift_2974_){
_start:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2970_, v_____do__lift_2974_, v_t_2971_, v_type_2972_);
v___x_2976_ = lean_apply_2(v_toPure_2973_, lean_box(0), v___x_2975_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(lean_object* v_pu_2977_, lean_object* v_t_2978_, lean_object* v_type_2979_, lean_object* v_toPure_2980_, lean_object* v_____do__lift_2981_){
_start:
{
uint8_t v_pu_boxed_2982_; uint8_t v_t_boxed_2983_; lean_object* v_res_2984_; 
v_pu_boxed_2982_ = lean_unbox(v_pu_2977_);
v_t_boxed_2983_ = lean_unbox(v_t_2978_);
v_res_2984_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(v_pu_boxed_2982_, v_t_boxed_2983_, v_type_2979_, v_toPure_2980_, v_____do__lift_2981_);
lean_dec_ref(v_____do__lift_2981_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg(uint8_t v_pu_2985_, uint8_t v_t_2986_, lean_object* v_inst_2987_, lean_object* v_inst_2988_, lean_object* v_inst_2989_, lean_object* v_p_2990_){
_start:
{
lean_object* v_toApplicative_2991_; lean_object* v_toBind_2992_; lean_object* v_type_2993_; lean_object* v_toPure_2994_; lean_object* v___x_2995_; lean_object* v___f_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___f_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v_toApplicative_2991_ = lean_ctor_get(v_inst_2988_, 0);
lean_inc_ref(v_toApplicative_2991_);
v_toBind_2992_ = lean_ctor_get(v_inst_2988_, 1);
lean_inc_n(v_toBind_2992_, 2);
lean_dec_ref(v_inst_2988_);
v_type_2993_ = lean_ctor_get(v_p_2990_, 2);
lean_inc_ref(v_type_2993_);
v_toPure_2994_ = lean_ctor_get(v_toApplicative_2991_, 1);
lean_inc(v_toPure_2994_);
lean_dec_ref(v_toApplicative_2991_);
v___x_2995_ = lean_box(v_pu_2985_);
v___f_2996_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2996_, 0, v___x_2995_);
lean_closure_set(v___f_2996_, 1, v_p_2990_);
lean_closure_set(v___f_2996_, 2, v_inst_2987_);
v___x_2997_ = lean_box(v_pu_2985_);
v___x_2998_ = lean_box(v_t_2986_);
v___f_2999_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2999_, 0, v___x_2997_);
lean_closure_set(v___f_2999_, 1, v___x_2998_);
lean_closure_set(v___f_2999_, 2, v_type_2993_);
lean_closure_set(v___f_2999_, 3, v_toPure_2994_);
v___x_3000_ = lean_apply_4(v_toBind_2992_, lean_box(0), lean_box(0), v_inst_2989_, v___f_2999_);
v___x_3001_ = lean_apply_4(v_toBind_2992_, lean_box(0), lean_box(0), v___x_3000_, v___f_2996_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___boxed(lean_object* v_pu_3002_, lean_object* v_t_3003_, lean_object* v_inst_3004_, lean_object* v_inst_3005_, lean_object* v_inst_3006_, lean_object* v_p_3007_){
_start:
{
uint8_t v_pu_boxed_3008_; uint8_t v_t_boxed_3009_; lean_object* v_res_3010_; 
v_pu_boxed_3008_ = lean_unbox(v_pu_3002_);
v_t_boxed_3009_ = lean_unbox(v_t_3003_);
v_res_3010_ = l_Lean_Compiler_LCNF_normParam___redArg(v_pu_boxed_3008_, v_t_boxed_3009_, v_inst_3004_, v_inst_3005_, v_inst_3006_, v_p_3007_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam(lean_object* v_m_3011_, uint8_t v_pu_3012_, uint8_t v_t_3013_, lean_object* v_inst_3014_, lean_object* v_inst_3015_, lean_object* v_inst_3016_, lean_object* v_p_3017_){
_start:
{
lean_object* v_toApplicative_3018_; lean_object* v_toBind_3019_; lean_object* v_type_3020_; lean_object* v_toPure_3021_; lean_object* v___x_3022_; lean_object* v___f_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___f_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v_toApplicative_3018_ = lean_ctor_get(v_inst_3015_, 0);
lean_inc_ref(v_toApplicative_3018_);
v_toBind_3019_ = lean_ctor_get(v_inst_3015_, 1);
lean_inc_n(v_toBind_3019_, 2);
lean_dec_ref(v_inst_3015_);
v_type_3020_ = lean_ctor_get(v_p_3017_, 2);
lean_inc_ref(v_type_3020_);
v_toPure_3021_ = lean_ctor_get(v_toApplicative_3018_, 1);
lean_inc(v_toPure_3021_);
lean_dec_ref(v_toApplicative_3018_);
v___x_3022_ = lean_box(v_pu_3012_);
v___f_3023_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3023_, 0, v___x_3022_);
lean_closure_set(v___f_3023_, 1, v_p_3017_);
lean_closure_set(v___f_3023_, 2, v_inst_3014_);
v___x_3024_ = lean_box(v_pu_3012_);
v___x_3025_ = lean_box(v_t_3013_);
v___f_3026_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3026_, 0, v___x_3024_);
lean_closure_set(v___f_3026_, 1, v___x_3025_);
lean_closure_set(v___f_3026_, 2, v_type_3020_);
lean_closure_set(v___f_3026_, 3, v_toPure_3021_);
v___x_3027_ = lean_apply_4(v_toBind_3019_, lean_box(0), lean_box(0), v_inst_3016_, v___f_3026_);
v___x_3028_ = lean_apply_4(v_toBind_3019_, lean_box(0), lean_box(0), v___x_3027_, v___f_3023_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___boxed(lean_object* v_m_3029_, lean_object* v_pu_3030_, lean_object* v_t_3031_, lean_object* v_inst_3032_, lean_object* v_inst_3033_, lean_object* v_inst_3034_, lean_object* v_p_3035_){
_start:
{
uint8_t v_pu_boxed_3036_; uint8_t v_t_boxed_3037_; lean_object* v_res_3038_; 
v_pu_boxed_3036_ = lean_unbox(v_pu_3030_);
v_t_boxed_3037_ = lean_unbox(v_t_3031_);
v_res_3038_ = l_Lean_Compiler_LCNF_normParam(v_m_3029_, v_pu_boxed_3036_, v_t_boxed_3037_, v_inst_3032_, v_inst_3033_, v_inst_3034_, v_p_3035_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg(uint8_t v_pu_3039_, uint8_t v_t_3040_, lean_object* v_inst_3041_, lean_object* v_inst_3042_, lean_object* v_inst_3043_, lean_object* v_ps_3044_){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3045_ = lean_box(v_pu_3039_);
v___x_3046_ = lean_box(v_t_3040_);
lean_inc_ref(v_inst_3042_);
v___x_3047_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___boxed), 7, 6);
lean_closure_set(v___x_3047_, 0, lean_box(0));
lean_closure_set(v___x_3047_, 1, v___x_3045_);
lean_closure_set(v___x_3047_, 2, v___x_3046_);
lean_closure_set(v___x_3047_, 3, v_inst_3041_);
lean_closure_set(v___x_3047_, 4, v_inst_3042_);
lean_closure_set(v___x_3047_, 5, v_inst_3043_);
v___x_3048_ = lean_unsigned_to_nat(0u);
v___x_3049_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_3042_, v___x_3047_, v___x_3048_, v_ps_3044_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg___boxed(lean_object* v_pu_3050_, lean_object* v_t_3051_, lean_object* v_inst_3052_, lean_object* v_inst_3053_, lean_object* v_inst_3054_, lean_object* v_ps_3055_){
_start:
{
uint8_t v_pu_boxed_3056_; uint8_t v_t_boxed_3057_; lean_object* v_res_3058_; 
v_pu_boxed_3056_ = lean_unbox(v_pu_3050_);
v_t_boxed_3057_ = lean_unbox(v_t_3051_);
v_res_3058_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_boxed_3056_, v_t_boxed_3057_, v_inst_3052_, v_inst_3053_, v_inst_3054_, v_ps_3055_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams(lean_object* v_m_3059_, uint8_t v_pu_3060_, uint8_t v_t_3061_, lean_object* v_inst_3062_, lean_object* v_inst_3063_, lean_object* v_inst_3064_, lean_object* v_ps_3065_){
_start:
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_3060_, v_t_3061_, v_inst_3062_, v_inst_3063_, v_inst_3064_, v_ps_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___boxed(lean_object* v_m_3067_, lean_object* v_pu_3068_, lean_object* v_t_3069_, lean_object* v_inst_3070_, lean_object* v_inst_3071_, lean_object* v_inst_3072_, lean_object* v_ps_3073_){
_start:
{
uint8_t v_pu_boxed_3074_; uint8_t v_t_boxed_3075_; lean_object* v_res_3076_; 
v_pu_boxed_3074_ = lean_unbox(v_pu_3068_);
v_t_boxed_3075_ = lean_unbox(v_t_3069_);
v_res_3076_ = l_Lean_Compiler_LCNF_normParams(v_m_3067_, v_pu_boxed_3074_, v_t_boxed_3075_, v_inst_3070_, v_inst_3071_, v_inst_3072_, v_ps_3073_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(uint8_t v_pu_3077_, lean_object* v_decl_3078_, lean_object* v_____do__lift_3079_, lean_object* v_inst_3080_, lean_object* v_____do__lift_3081_){
_start:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3082_ = lean_box(v_pu_3077_);
v___x_3083_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_3083_, 0, v___x_3082_);
lean_closure_set(v___x_3083_, 1, v_decl_3078_);
lean_closure_set(v___x_3083_, 2, v_____do__lift_3079_);
lean_closure_set(v___x_3083_, 3, v_____do__lift_3081_);
v___x_3084_ = lean_apply_2(v_inst_3080_, lean_box(0), v___x_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(lean_object* v_pu_3085_, lean_object* v_decl_3086_, lean_object* v_____do__lift_3087_, lean_object* v_inst_3088_, lean_object* v_____do__lift_3089_){
_start:
{
uint8_t v_pu_boxed_3090_; lean_object* v_res_3091_; 
v_pu_boxed_3090_ = lean_unbox(v_pu_3085_);
v_res_3091_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(v_pu_boxed_3090_, v_decl_3086_, v_____do__lift_3087_, v_inst_3088_, v_____do__lift_3089_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(uint8_t v_pu_3092_, lean_object* v_value_3093_, uint8_t v_t_3094_, lean_object* v_toPure_3095_, lean_object* v_____do__lift_3096_){
_start:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3097_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3092_, v_____do__lift_3096_, v_value_3093_, v_t_3094_);
v___x_3098_ = lean_apply_2(v_toPure_3095_, lean_box(0), v___x_3097_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(lean_object* v_pu_3099_, lean_object* v_value_3100_, lean_object* v_t_3101_, lean_object* v_toPure_3102_, lean_object* v_____do__lift_3103_){
_start:
{
uint8_t v_pu_boxed_3104_; uint8_t v_t_boxed_3105_; lean_object* v_res_3106_; 
v_pu_boxed_3104_ = lean_unbox(v_pu_3099_);
v_t_boxed_3105_ = lean_unbox(v_t_3101_);
v_res_3106_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(v_pu_boxed_3104_, v_value_3100_, v_t_boxed_3105_, v_toPure_3102_, v_____do__lift_3103_);
lean_dec_ref(v_____do__lift_3103_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(uint8_t v_pu_3107_, lean_object* v_decl_3108_, lean_object* v_inst_3109_, lean_object* v_value_3110_, uint8_t v_t_3111_, lean_object* v_toPure_3112_, lean_object* v_toBind_3113_, lean_object* v_inst_3114_, lean_object* v_____do__lift_3115_){
_start:
{
lean_object* v___x_3116_; lean_object* v___f_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___f_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3116_ = lean_box(v_pu_3107_);
v___f_3117_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3117_, 0, v___x_3116_);
lean_closure_set(v___f_3117_, 1, v_decl_3108_);
lean_closure_set(v___f_3117_, 2, v_____do__lift_3115_);
lean_closure_set(v___f_3117_, 3, v_inst_3109_);
v___x_3118_ = lean_box(v_pu_3107_);
v___x_3119_ = lean_box(v_t_3111_);
v___f_3120_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3120_, 0, v___x_3118_);
lean_closure_set(v___f_3120_, 1, v_value_3110_);
lean_closure_set(v___f_3120_, 2, v___x_3119_);
lean_closure_set(v___f_3120_, 3, v_toPure_3112_);
lean_inc(v_toBind_3113_);
v___x_3121_ = lean_apply_4(v_toBind_3113_, lean_box(0), lean_box(0), v_inst_3114_, v___f_3120_);
v___x_3122_ = lean_apply_4(v_toBind_3113_, lean_box(0), lean_box(0), v___x_3121_, v___f_3117_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(lean_object* v_pu_3123_, lean_object* v_decl_3124_, lean_object* v_inst_3125_, lean_object* v_value_3126_, lean_object* v_t_3127_, lean_object* v_toPure_3128_, lean_object* v_toBind_3129_, lean_object* v_inst_3130_, lean_object* v_____do__lift_3131_){
_start:
{
uint8_t v_pu_boxed_3132_; uint8_t v_t_boxed_3133_; lean_object* v_res_3134_; 
v_pu_boxed_3132_ = lean_unbox(v_pu_3123_);
v_t_boxed_3133_ = lean_unbox(v_t_3127_);
v_res_3134_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(v_pu_boxed_3132_, v_decl_3124_, v_inst_3125_, v_value_3126_, v_t_boxed_3133_, v_toPure_3128_, v_toBind_3129_, v_inst_3130_, v_____do__lift_3131_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg(uint8_t v_pu_3135_, uint8_t v_t_3136_, lean_object* v_inst_3137_, lean_object* v_inst_3138_, lean_object* v_inst_3139_, lean_object* v_decl_3140_){
_start:
{
lean_object* v_toApplicative_3141_; lean_object* v_toBind_3142_; lean_object* v_type_3143_; lean_object* v_value_3144_; lean_object* v_toPure_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___f_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___f_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v_toApplicative_3141_ = lean_ctor_get(v_inst_3138_, 0);
lean_inc_ref(v_toApplicative_3141_);
v_toBind_3142_ = lean_ctor_get(v_inst_3138_, 1);
lean_inc_n(v_toBind_3142_, 3);
lean_dec_ref(v_inst_3138_);
v_type_3143_ = lean_ctor_get(v_decl_3140_, 2);
lean_inc_ref(v_type_3143_);
v_value_3144_ = lean_ctor_get(v_decl_3140_, 3);
lean_inc(v_value_3144_);
v_toPure_3145_ = lean_ctor_get(v_toApplicative_3141_, 1);
lean_inc_n(v_toPure_3145_, 2);
lean_dec_ref(v_toApplicative_3141_);
v___x_3146_ = lean_box(v_pu_3135_);
v___x_3147_ = lean_box(v_t_3136_);
lean_inc(v_inst_3139_);
v___f_3148_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_3148_, 0, v___x_3146_);
lean_closure_set(v___f_3148_, 1, v_decl_3140_);
lean_closure_set(v___f_3148_, 2, v_inst_3137_);
lean_closure_set(v___f_3148_, 3, v_value_3144_);
lean_closure_set(v___f_3148_, 4, v___x_3147_);
lean_closure_set(v___f_3148_, 5, v_toPure_3145_);
lean_closure_set(v___f_3148_, 6, v_toBind_3142_);
lean_closure_set(v___f_3148_, 7, v_inst_3139_);
v___x_3149_ = lean_box(v_pu_3135_);
v___x_3150_ = lean_box(v_t_3136_);
v___f_3151_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3151_, 0, v___x_3149_);
lean_closure_set(v___f_3151_, 1, v___x_3150_);
lean_closure_set(v___f_3151_, 2, v_type_3143_);
lean_closure_set(v___f_3151_, 3, v_toPure_3145_);
v___x_3152_ = lean_apply_4(v_toBind_3142_, lean_box(0), lean_box(0), v_inst_3139_, v___f_3151_);
v___x_3153_ = lean_apply_4(v_toBind_3142_, lean_box(0), lean_box(0), v___x_3152_, v___f_3148_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(lean_object* v_pu_3154_, lean_object* v_t_3155_, lean_object* v_inst_3156_, lean_object* v_inst_3157_, lean_object* v_inst_3158_, lean_object* v_decl_3159_){
_start:
{
uint8_t v_pu_boxed_3160_; uint8_t v_t_boxed_3161_; lean_object* v_res_3162_; 
v_pu_boxed_3160_ = lean_unbox(v_pu_3154_);
v_t_boxed_3161_ = lean_unbox(v_t_3155_);
v_res_3162_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_boxed_3160_, v_t_boxed_3161_, v_inst_3156_, v_inst_3157_, v_inst_3158_, v_decl_3159_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl(lean_object* v_m_3163_, uint8_t v_pu_3164_, uint8_t v_t_3165_, lean_object* v_inst_3166_, lean_object* v_inst_3167_, lean_object* v_inst_3168_, lean_object* v_decl_3169_){
_start:
{
lean_object* v___x_3170_; 
v___x_3170_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_3164_, v_t_3165_, v_inst_3166_, v_inst_3167_, v_inst_3168_, v_decl_3169_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___boxed(lean_object* v_m_3171_, lean_object* v_pu_3172_, lean_object* v_t_3173_, lean_object* v_inst_3174_, lean_object* v_inst_3175_, lean_object* v_inst_3176_, lean_object* v_decl_3177_){
_start:
{
uint8_t v_pu_boxed_3178_; uint8_t v_t_boxed_3179_; lean_object* v_res_3180_; 
v_pu_boxed_3178_ = lean_unbox(v_pu_3172_);
v_t_boxed_3179_ = lean_unbox(v_t_3173_);
v_res_3180_ = l_Lean_Compiler_LCNF_normLetDecl(v_m_3171_, v_pu_boxed_3178_, v_t_boxed_3179_, v_inst_3174_, v_inst_3175_, v_inst_3176_, v_decl_3177_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(uint8_t v_pu_3181_, uint8_t v_t_3182_){
_start:
{
lean_object* v___x_3183_; lean_object* v_toApplicative_3184_; lean_object* v_toFunctor_3185_; lean_object* v_toSeq_3186_; lean_object* v_toSeqLeft_3187_; lean_object* v_toSeqRight_3188_; lean_object* v___f_3189_; lean_object* v___f_3190_; lean_object* v___f_3191_; lean_object* v___f_3192_; lean_object* v___x_3193_; lean_object* v___f_3194_; lean_object* v___f_3195_; lean_object* v___f_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v_toApplicative_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3228_; 
v___x_3183_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_3184_ = lean_ctor_get(v___x_3183_, 0);
v_toFunctor_3185_ = lean_ctor_get(v_toApplicative_3184_, 0);
v_toSeq_3186_ = lean_ctor_get(v_toApplicative_3184_, 2);
v_toSeqLeft_3187_ = lean_ctor_get(v_toApplicative_3184_, 3);
v_toSeqRight_3188_ = lean_ctor_get(v_toApplicative_3184_, 4);
v___f_3189_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_3190_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_3185_, 2);
v___f_3191_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3191_, 0, v_toFunctor_3185_);
v___f_3192_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3192_, 0, v_toFunctor_3185_);
v___x_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3193_, 0, v___f_3191_);
lean_ctor_set(v___x_3193_, 1, v___f_3192_);
lean_inc(v_toSeqRight_3188_);
v___f_3194_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3194_, 0, v_toSeqRight_3188_);
lean_inc(v_toSeqLeft_3187_);
v___f_3195_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3195_, 0, v_toSeqLeft_3187_);
lean_inc(v_toSeq_3186_);
v___f_3196_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3196_, 0, v_toSeq_3186_);
v___x_3197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3193_);
lean_ctor_set(v___x_3197_, 1, v___f_3189_);
lean_ctor_set(v___x_3197_, 2, v___f_3196_);
lean_ctor_set(v___x_3197_, 3, v___f_3195_);
lean_ctor_set(v___x_3197_, 4, v___f_3194_);
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3197_);
lean_ctor_set(v___x_3198_, 1, v___f_3190_);
v___x_3199_ = l_StateRefT_x27_instMonad___redArg(v___x_3198_);
v_toApplicative_3200_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; 
v_unused_3229_ = lean_ctor_get(v___x_3199_, 1);
lean_dec(v_unused_3229_);
v___x_3202_ = v___x_3199_;
v_isShared_3203_ = v_isSharedCheck_3228_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_toApplicative_3200_);
lean_dec(v___x_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3228_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v_toFunctor_3204_; lean_object* v_toSeq_3205_; lean_object* v_toSeqLeft_3206_; lean_object* v_toSeqRight_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3226_; 
v_toFunctor_3204_ = lean_ctor_get(v_toApplicative_3200_, 0);
v_toSeq_3205_ = lean_ctor_get(v_toApplicative_3200_, 2);
v_toSeqLeft_3206_ = lean_ctor_get(v_toApplicative_3200_, 3);
v_toSeqRight_3207_ = lean_ctor_get(v_toApplicative_3200_, 4);
v_isSharedCheck_3226_ = !lean_is_exclusive(v_toApplicative_3200_);
if (v_isSharedCheck_3226_ == 0)
{
lean_object* v_unused_3227_; 
v_unused_3227_ = lean_ctor_get(v_toApplicative_3200_, 1);
lean_dec(v_unused_3227_);
v___x_3209_ = v_toApplicative_3200_;
v_isShared_3210_ = v_isSharedCheck_3226_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_toSeqRight_3207_);
lean_inc(v_toSeqLeft_3206_);
lean_inc(v_toSeq_3205_);
lean_inc(v_toFunctor_3204_);
lean_dec(v_toApplicative_3200_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3226_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___f_3211_; lean_object* v___f_3212_; lean_object* v___f_3213_; lean_object* v___f_3214_; lean_object* v___x_3215_; lean_object* v___f_3216_; lean_object* v___f_3217_; lean_object* v___f_3218_; lean_object* v___x_3220_; 
v___f_3211_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_3212_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_3204_);
v___f_3213_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3213_, 0, v_toFunctor_3204_);
v___f_3214_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3214_, 0, v_toFunctor_3204_);
v___x_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___f_3213_);
lean_ctor_set(v___x_3215_, 1, v___f_3214_);
v___f_3216_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3216_, 0, v_toSeqRight_3207_);
v___f_3217_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3217_, 0, v_toSeqLeft_3206_);
v___f_3218_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3218_, 0, v_toSeq_3205_);
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 4, v___f_3216_);
lean_ctor_set(v___x_3209_, 3, v___f_3217_);
lean_ctor_set(v___x_3209_, 2, v___f_3218_);
lean_ctor_set(v___x_3209_, 1, v___f_3211_);
lean_ctor_set(v___x_3209_, 0, v___x_3215_);
v___x_3220_ = v___x_3209_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3215_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v___f_3211_);
lean_ctor_set(v_reuseFailAlloc_3225_, 2, v___f_3218_);
lean_ctor_set(v_reuseFailAlloc_3225_, 3, v___f_3217_);
lean_ctor_set(v_reuseFailAlloc_3225_, 4, v___f_3216_);
v___x_3220_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
lean_object* v___x_3222_; 
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 1, v___f_3212_);
lean_ctor_set(v___x_3202_, 0, v___x_3220_);
v___x_3222_ = v___x_3202_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v___f_3212_);
v___x_3222_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3223_; 
v___x_3223_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_3223_, 0, lean_box(0));
lean_closure_set(v___x_3223_, 1, lean_box(0));
lean_closure_set(v___x_3223_, 2, v___x_3222_);
return v___x_3223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(lean_object* v_pu_3230_, lean_object* v_t_3231_){
_start:
{
uint8_t v_pu_boxed_3232_; uint8_t v_t_boxed_3233_; lean_object* v_res_3234_; 
v_pu_boxed_3232_ = lean_unbox(v_pu_3230_);
v_t_boxed_3233_ = lean_unbox(v_t_3231_);
v_res_3234_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_boxed_3232_, v_t_boxed_3233_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg(uint8_t v_pu_3235_, lean_object* v_inst_3236_, lean_object* v_result_3237_, lean_object* v_x_3238_){
_start:
{
if (lean_obj_tag(v_result_3237_) == 0)
{
lean_object* v_fvarId_3239_; lean_object* v___x_3240_; 
lean_dec(v_inst_3236_);
v_fvarId_3239_ = lean_ctor_get(v_result_3237_, 0);
lean_inc(v_fvarId_3239_);
lean_dec_ref_known(v_result_3237_, 1);
v___x_3240_ = lean_apply_1(v_x_3238_, v_fvarId_3239_);
return v___x_3240_;
}
else
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
lean_dec(v_x_3238_);
v___x_3241_ = lean_box(v_pu_3235_);
v___x_3242_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3242_, 0, v___x_3241_);
v___x_3243_ = lean_apply_2(v_inst_3236_, lean_box(0), v___x_3242_);
return v___x_3243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(lean_object* v_pu_3244_, lean_object* v_inst_3245_, lean_object* v_result_3246_, lean_object* v_x_3247_){
_start:
{
uint8_t v_pu_boxed_3248_; lean_object* v_res_3249_; 
v_pu_boxed_3248_ = lean_unbox(v_pu_3244_);
v_res_3249_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(v_pu_boxed_3248_, v_inst_3245_, v_result_3246_, v_x_3247_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult(lean_object* v_m_3250_, uint8_t v_pu_3251_, lean_object* v_inst_3252_, lean_object* v_inst_3253_, lean_object* v_result_3254_, lean_object* v_x_3255_){
_start:
{
if (lean_obj_tag(v_result_3254_) == 0)
{
lean_object* v_fvarId_3256_; lean_object* v___x_3257_; 
lean_dec(v_inst_3252_);
v_fvarId_3256_ = lean_ctor_get(v_result_3254_, 0);
lean_inc(v_fvarId_3256_);
lean_dec_ref_known(v_result_3254_, 1);
v___x_3257_ = lean_apply_1(v_x_3255_, v_fvarId_3256_);
return v___x_3257_;
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
lean_dec(v_x_3255_);
v___x_3258_ = lean_box(v_pu_3251_);
v___x_3259_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3259_, 0, v___x_3258_);
v___x_3260_ = lean_apply_2(v_inst_3252_, lean_box(0), v___x_3259_);
return v___x_3260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___boxed(lean_object* v_m_3261_, lean_object* v_pu_3262_, lean_object* v_inst_3263_, lean_object* v_inst_3264_, lean_object* v_result_3265_, lean_object* v_x_3266_){
_start:
{
uint8_t v_pu_boxed_3267_; lean_object* v_res_3268_; 
v_pu_boxed_3267_ = lean_unbox(v_pu_3262_);
v_res_3268_ = l_Lean_Compiler_LCNF_withNormFVarResult(v_m_3261_, v_pu_boxed_3267_, v_inst_3263_, v_inst_3264_, v_result_3265_, v_x_3266_);
lean_dec_ref(v_inst_3264_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(uint8_t v_pu_3269_, uint8_t v_t_3270_, lean_object* v_args_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_3269_, v___y_3272_, v_args_3271_, v_t_3270_);
v___x_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(lean_object* v_pu_3276_, lean_object* v_t_3277_, lean_object* v_args_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
uint8_t v_pu_boxed_3281_; uint8_t v_t_boxed_3282_; lean_object* v_res_3283_; 
v_pu_boxed_3281_ = lean_unbox(v_pu_3276_);
v_t_boxed_3282_ = lean_unbox(v_t_3277_);
v_res_3283_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_boxed_3281_, v_t_boxed_3282_, v_args_3278_, v___y_3279_);
lean_dec_ref(v___y_3279_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(uint8_t v_pu_3284_, uint8_t v_t_3285_, lean_object* v_i_3286_, lean_object* v_as_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v___x_3291_; uint8_t v___x_3292_; 
v___x_3291_ = lean_array_get_size(v_as_3287_);
v___x_3292_ = lean_nat_dec_lt(v_i_3286_, v___x_3291_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3293_; 
lean_dec(v_i_3286_);
v___x_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3293_, 0, v_as_3287_);
return v___x_3293_;
}
else
{
lean_object* v_a_3294_; lean_object* v_type_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v_a_3294_ = lean_array_fget_borrowed(v_as_3287_, v_i_3286_);
v_type_3295_ = lean_ctor_get(v_a_3294_, 2);
lean_inc_ref(v_type_3295_);
v___x_3296_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3284_, v___y_3288_, v_t_3285_, v_type_3295_);
lean_inc(v_a_3294_);
v___x_3297_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_3284_, v_a_3294_, v___x_3296_, v___y_3289_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; size_t v___x_3299_; size_t v___x_3300_; uint8_t v___x_3301_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref_known(v___x_3297_, 1);
v___x_3299_ = lean_ptr_addr(v_a_3294_);
v___x_3300_ = lean_ptr_addr(v_a_3298_);
v___x_3301_ = lean_usize_dec_eq(v___x_3299_, v___x_3300_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3302_ = lean_unsigned_to_nat(1u);
v___x_3303_ = lean_nat_add(v_i_3286_, v___x_3302_);
v___x_3304_ = lean_array_fset(v_as_3287_, v_i_3286_, v_a_3298_);
lean_dec(v_i_3286_);
v_i_3286_ = v___x_3303_;
v_as_3287_ = v___x_3304_;
goto _start;
}
else
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
lean_dec(v_a_3298_);
v___x_3306_ = lean_unsigned_to_nat(1u);
v___x_3307_ = lean_nat_add(v_i_3286_, v___x_3306_);
lean_dec(v_i_3286_);
v_i_3286_ = v___x_3307_;
goto _start;
}
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec_ref(v_as_3287_);
lean_dec(v_i_3286_);
v_a_3309_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3297_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3297_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(lean_object* v_pu_3317_, lean_object* v_t_3318_, lean_object* v_i_3319_, lean_object* v_as_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
uint8_t v_pu_boxed_3324_; uint8_t v_t_boxed_3325_; lean_object* v_res_3326_; 
v_pu_boxed_3324_ = lean_unbox(v_pu_3317_);
v_t_boxed_3325_ = lean_unbox(v_t_3318_);
v_res_3326_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_boxed_3324_, v_t_boxed_3325_, v_i_3319_, v_as_3320_, v___y_3321_, v___y_3322_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(uint8_t v_pu_3327_, uint8_t v_t_3328_, lean_object* v_ps_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3336_ = lean_unsigned_to_nat(0u);
v___x_3337_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_3327_, v_t_3328_, v___x_3336_, v_ps_3329_, v___y_3330_, v___y_3332_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(lean_object* v_pu_3338_, lean_object* v_t_3339_, lean_object* v_ps_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
uint8_t v_pu_boxed_3347_; uint8_t v_t_boxed_3348_; lean_object* v_res_3349_; 
v_pu_boxed_3347_ = lean_unbox(v_pu_3338_);
v_t_boxed_3348_ = lean_unbox(v_t_3339_);
v_res_3349_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_boxed_3347_, v_t_boxed_3348_, v_ps_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
lean_dec_ref(v___y_3341_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(uint8_t v_pu_3350_, uint8_t v_t_3351_, lean_object* v_decl_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v_type_3356_; lean_object* v_value_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v_type_3356_ = lean_ctor_get(v_decl_3352_, 2);
v_value_3357_ = lean_ctor_get(v_decl_3352_, 3);
lean_inc_ref(v_type_3356_);
v___x_3358_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3350_, v___y_3353_, v_t_3351_, v_type_3356_);
lean_inc(v_value_3357_);
v___x_3359_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3350_, v___y_3353_, v_value_3357_, v_t_3351_);
v___x_3360_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_3350_, v_decl_3352_, v___x_3358_, v___x_3359_, v___y_3354_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(lean_object* v_pu_3361_, lean_object* v_t_3362_, lean_object* v_decl_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
uint8_t v_pu_boxed_3367_; uint8_t v_t_boxed_3368_; lean_object* v_res_3369_; 
v_pu_boxed_3367_ = lean_unbox(v_pu_3361_);
v_t_boxed_3368_ = lean_unbox(v_t_3362_);
v_res_3369_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_boxed_3367_, v_t_boxed_3368_, v_decl_3363_, v___y_3364_, v___y_3365_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(uint8_t v_pu_3370_, uint8_t v_t_3371_, lean_object* v_i_3372_, lean_object* v_as_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v___x_3380_; uint8_t v___x_3381_; 
v___x_3380_ = lean_array_get_size(v_as_3373_);
v___x_3381_ = lean_nat_dec_lt(v_i_3372_, v___x_3380_);
if (v___x_3381_ == 0)
{
lean_object* v___x_3382_; 
lean_dec(v_i_3372_);
v___x_3382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3382_, 0, v_as_3373_);
return v___x_3382_;
}
else
{
lean_object* v_a_3383_; lean_object* v_a_3385_; 
v_a_3383_ = lean_array_fget_borrowed(v_as_3373_, v_i_3372_);
switch(lean_obj_tag(v_a_3383_))
{
case 0:
{
lean_object* v_params_3396_; lean_object* v_code_3397_; lean_object* v___x_3398_; 
v_params_3396_ = lean_ctor_get(v_a_3383_, 1);
v_code_3397_ = lean_ctor_get(v_a_3383_, 2);
lean_inc_ref(v_params_3396_);
v___x_3398_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_3370_, v_t_3371_, v_params_3396_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3400_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3398_, 1);
lean_inc_ref(v_code_3397_);
v___x_3400_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3370_, v_t_3371_, v_code_3397_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3402_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
lean_dec_ref_known(v___x_3400_, 1);
lean_inc_ref(v_a_3383_);
v___x_3402_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_3370_, v_a_3383_, v_a_3399_, v_a_3401_);
v_a_3385_ = v___x_3402_;
goto v___jp_3384_;
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec(v_a_3399_);
lean_dec_ref(v_as_3373_);
lean_dec(v_i_3372_);
v_a_3403_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3400_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3400_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec_ref(v_as_3373_);
lean_dec(v_i_3372_);
v_a_3411_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3398_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3398_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
case 1:
{
lean_object* v_code_3419_; lean_object* v___x_3420_; 
v_code_3419_ = lean_ctor_get(v_a_3383_, 1);
lean_inc_ref(v_code_3419_);
v___x_3420_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3370_, v_t_3371_, v_code_3419_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; lean_object* v___x_3422_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref_known(v___x_3420_, 1);
lean_inc_ref(v_a_3383_);
v___x_3422_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3383_, v_a_3421_);
v_a_3385_ = v___x_3422_;
goto v___jp_3384_;
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec_ref(v_as_3373_);
lean_dec(v_i_3372_);
v_a_3423_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3420_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3420_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
default: 
{
lean_object* v_code_3431_; lean_object* v___x_3432_; 
v_code_3431_ = lean_ctor_get(v_a_3383_, 0);
lean_inc_ref(v_code_3431_);
v___x_3432_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3370_, v_t_3371_, v_code_3431_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3434_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_a_3433_);
lean_dec_ref_known(v___x_3432_, 1);
lean_inc_ref(v_a_3383_);
v___x_3434_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3383_, v_a_3433_);
v_a_3385_ = v___x_3434_;
goto v___jp_3384_;
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_dec_ref(v_as_3373_);
lean_dec(v_i_3372_);
v_a_3435_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3432_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3432_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
}
v___jp_3384_:
{
size_t v___x_3386_; size_t v___x_3387_; uint8_t v___x_3388_; 
v___x_3386_ = lean_ptr_addr(v_a_3383_);
v___x_3387_ = lean_ptr_addr(v_a_3385_);
v___x_3388_ = lean_usize_dec_eq(v___x_3386_, v___x_3387_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3389_ = lean_unsigned_to_nat(1u);
v___x_3390_ = lean_nat_add(v_i_3372_, v___x_3389_);
v___x_3391_ = lean_array_fset(v_as_3373_, v_i_3372_, v_a_3385_);
lean_dec(v_i_3372_);
v_i_3372_ = v___x_3390_;
v_as_3373_ = v___x_3391_;
goto _start;
}
else
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
lean_dec_ref(v_a_3385_);
v___x_3393_ = lean_unsigned_to_nat(1u);
v___x_3394_ = lean_nat_add(v_i_3372_, v___x_3393_);
lean_dec(v_i_3372_);
v_i_3372_ = v___x_3394_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t v_pu_3443_, uint8_t v_t_3444_, lean_object* v_code_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_){
_start:
{
switch(lean_obj_tag(v_code_3445_))
{
case 0:
{
lean_object* v_decl_3452_; lean_object* v_k_3453_; lean_object* v___x_3454_; 
v_decl_3452_ = lean_ctor_get(v_code_3445_, 0);
v_k_3453_ = lean_ctor_get(v_code_3445_, 1);
lean_inc_ref(v_decl_3452_);
v___x_3454_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_3443_, v_t_3444_, v_decl_3452_, v_a_3446_, v_a_3448_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3456_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3455_);
lean_dec_ref_known(v___x_3454_, 1);
lean_inc_ref(v_k_3453_);
v___x_3456_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3443_, v_t_3444_, v_k_3453_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3484_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3459_ = v___x_3456_;
v_isShared_3460_ = v_isSharedCheck_3484_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3456_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3484_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
uint8_t v___y_3462_; size_t v___x_3478_; size_t v___x_3479_; uint8_t v___x_3480_; 
v___x_3478_ = lean_ptr_addr(v_k_3453_);
v___x_3479_ = lean_ptr_addr(v_a_3457_);
v___x_3480_ = lean_usize_dec_eq(v___x_3478_, v___x_3479_);
if (v___x_3480_ == 0)
{
v___y_3462_ = v___x_3480_;
goto v___jp_3461_;
}
else
{
size_t v___x_3481_; size_t v___x_3482_; uint8_t v___x_3483_; 
v___x_3481_ = lean_ptr_addr(v_decl_3452_);
v___x_3482_ = lean_ptr_addr(v_a_3455_);
v___x_3483_ = lean_usize_dec_eq(v___x_3481_, v___x_3482_);
v___y_3462_ = v___x_3483_;
goto v___jp_3461_;
}
v___jp_3461_:
{
if (v___y_3462_ == 0)
{
lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3472_; 
v_isSharedCheck_3472_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3472_ == 0)
{
lean_object* v_unused_3473_; lean_object* v_unused_3474_; 
v_unused_3473_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_3473_);
v_unused_3474_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3474_);
v___x_3464_ = v_code_3445_;
v_isShared_3465_ = v_isSharedCheck_3472_;
goto v_resetjp_3463_;
}
else
{
lean_dec(v_code_3445_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3472_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 1, v_a_3457_);
lean_ctor_set(v___x_3464_, 0, v_a_3455_);
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3455_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_a_3457_);
v___x_3467_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
lean_object* v___x_3469_; 
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 0, v___x_3467_);
v___x_3469_ = v___x_3459_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
else
{
lean_object* v___x_3476_; 
lean_dec(v_a_3457_);
lean_dec(v_a_3455_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 0, v_code_3445_);
v___x_3476_ = v___x_3459_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_code_3445_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
}
else
{
lean_dec(v_a_3455_);
lean_dec_ref_known(v_code_3445_, 2);
return v___x_3456_;
}
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec_ref_known(v_code_3445_, 2);
v_a_3485_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3454_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3454_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
case 1:
{
lean_object* v_decl_3493_; lean_object* v_k_3494_; lean_object* v___x_3495_; 
v_decl_3493_ = lean_ctor_get(v_code_3445_, 0);
v_k_3494_ = lean_ctor_get(v_code_3445_, 1);
lean_inc_ref(v_decl_3493_);
v___x_3495_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3443_, v_t_3444_, v_decl_3493_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3497_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
lean_inc_ref(v_k_3494_);
v___x_3497_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3443_, v_t_3444_, v_k_3494_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3525_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3500_ = v___x_3497_;
v_isShared_3501_ = v_isSharedCheck_3525_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3497_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3525_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
uint8_t v___y_3503_; size_t v___x_3519_; size_t v___x_3520_; uint8_t v___x_3521_; 
v___x_3519_ = lean_ptr_addr(v_k_3494_);
v___x_3520_ = lean_ptr_addr(v_a_3498_);
v___x_3521_ = lean_usize_dec_eq(v___x_3519_, v___x_3520_);
if (v___x_3521_ == 0)
{
v___y_3503_ = v___x_3521_;
goto v___jp_3502_;
}
else
{
size_t v___x_3522_; size_t v___x_3523_; uint8_t v___x_3524_; 
v___x_3522_ = lean_ptr_addr(v_decl_3493_);
v___x_3523_ = lean_ptr_addr(v_a_3496_);
v___x_3524_ = lean_usize_dec_eq(v___x_3522_, v___x_3523_);
v___y_3503_ = v___x_3524_;
goto v___jp_3502_;
}
v___jp_3502_:
{
if (v___y_3503_ == 0)
{
lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3513_; 
v_isSharedCheck_3513_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3513_ == 0)
{
lean_object* v_unused_3514_; lean_object* v_unused_3515_; 
v_unused_3514_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_3514_);
v_unused_3515_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3515_);
v___x_3505_ = v_code_3445_;
v_isShared_3506_ = v_isSharedCheck_3513_;
goto v_resetjp_3504_;
}
else
{
lean_dec(v_code_3445_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3513_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 1, v_a_3498_);
lean_ctor_set(v___x_3505_, 0, v_a_3496_);
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3496_);
lean_ctor_set(v_reuseFailAlloc_3512_, 1, v_a_3498_);
v___x_3508_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
lean_object* v___x_3510_; 
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 0, v___x_3508_);
v___x_3510_ = v___x_3500_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v___x_3508_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
else
{
lean_object* v___x_3517_; 
lean_dec(v_a_3498_);
lean_dec(v_a_3496_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 0, v_code_3445_);
v___x_3517_ = v___x_3500_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_code_3445_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
}
else
{
lean_dec(v_a_3496_);
lean_dec_ref_known(v_code_3445_, 2);
return v___x_3497_;
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec_ref_known(v_code_3445_, 2);
v_a_3526_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3495_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3495_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
case 2:
{
lean_object* v_decl_3534_; lean_object* v_k_3535_; lean_object* v___x_3536_; 
v_decl_3534_ = lean_ctor_get(v_code_3445_, 0);
v_k_3535_ = lean_ctor_get(v_code_3445_, 1);
lean_inc_ref(v_decl_3534_);
v___x_3536_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3443_, v_t_3444_, v_decl_3534_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3538_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3536_, 1);
lean_inc_ref(v_k_3535_);
v___x_3538_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3443_, v_t_3444_, v_k_3535_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3566_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3541_ = v___x_3538_;
v_isShared_3542_ = v_isSharedCheck_3566_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3538_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3566_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
uint8_t v___y_3544_; size_t v___x_3560_; size_t v___x_3561_; uint8_t v___x_3562_; 
v___x_3560_ = lean_ptr_addr(v_k_3535_);
v___x_3561_ = lean_ptr_addr(v_a_3539_);
v___x_3562_ = lean_usize_dec_eq(v___x_3560_, v___x_3561_);
if (v___x_3562_ == 0)
{
v___y_3544_ = v___x_3562_;
goto v___jp_3543_;
}
else
{
size_t v___x_3563_; size_t v___x_3564_; uint8_t v___x_3565_; 
v___x_3563_ = lean_ptr_addr(v_decl_3534_);
v___x_3564_ = lean_ptr_addr(v_a_3537_);
v___x_3565_ = lean_usize_dec_eq(v___x_3563_, v___x_3564_);
v___y_3544_ = v___x_3565_;
goto v___jp_3543_;
}
v___jp_3543_:
{
if (v___y_3544_ == 0)
{
lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3554_; 
v_isSharedCheck_3554_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3554_ == 0)
{
lean_object* v_unused_3555_; lean_object* v_unused_3556_; 
v_unused_3555_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_3555_);
v_unused_3556_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3556_);
v___x_3546_ = v_code_3445_;
v_isShared_3547_ = v_isSharedCheck_3554_;
goto v_resetjp_3545_;
}
else
{
lean_dec(v_code_3445_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3554_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
lean_ctor_set(v___x_3546_, 1, v_a_3539_);
lean_ctor_set(v___x_3546_, 0, v_a_3537_);
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3537_);
lean_ctor_set(v_reuseFailAlloc_3553_, 1, v_a_3539_);
v___x_3549_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v___x_3551_; 
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 0, v___x_3549_);
v___x_3551_ = v___x_3541_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3549_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
else
{
lean_object* v___x_3558_; 
lean_dec(v_a_3539_);
lean_dec(v_a_3537_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 0, v_code_3445_);
v___x_3558_ = v___x_3541_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_code_3445_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
}
else
{
lean_dec(v_a_3537_);
lean_dec_ref_known(v_code_3445_, 2);
return v___x_3538_;
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec_ref_known(v_code_3445_, 2);
v_a_3567_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3536_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3536_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3575_; lean_object* v_args_3576_; lean_object* v___x_3577_; 
v_fvarId_3575_ = lean_ctor_get(v_code_3445_, 0);
v_args_3576_ = lean_ctor_get(v_code_3445_, 1);
lean_inc(v_fvarId_3575_);
v___x_3577_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3446_, v_fvarId_3575_, v_t_3444_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_fvarId_3578_; lean_object* v___x_3579_; 
v_fvarId_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_fvarId_3578_);
lean_dec_ref_known(v___x_3577_, 1);
lean_inc_ref(v_args_3576_);
v___x_3579_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_3443_, v_t_3444_, v_args_3576_, v_a_3446_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3605_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3582_ = v___x_3579_;
v_isShared_3583_ = v_isSharedCheck_3605_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3579_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3605_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
uint8_t v___y_3585_; uint8_t v___x_3601_; 
v___x_3601_ = l_Lean_instBEqFVarId_beq(v_fvarId_3575_, v_fvarId_3578_);
if (v___x_3601_ == 0)
{
v___y_3585_ = v___x_3601_;
goto v___jp_3584_;
}
else
{
size_t v___x_3602_; size_t v___x_3603_; uint8_t v___x_3604_; 
v___x_3602_ = lean_ptr_addr(v_args_3576_);
v___x_3603_ = lean_ptr_addr(v_a_3580_);
v___x_3604_ = lean_usize_dec_eq(v___x_3602_, v___x_3603_);
v___y_3585_ = v___x_3604_;
goto v___jp_3584_;
}
v___jp_3584_:
{
if (v___y_3585_ == 0)
{
lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3595_; 
v_isSharedCheck_3595_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3595_ == 0)
{
lean_object* v_unused_3596_; lean_object* v_unused_3597_; 
v_unused_3596_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_3596_);
v_unused_3597_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3597_);
v___x_3587_ = v_code_3445_;
v_isShared_3588_ = v_isSharedCheck_3595_;
goto v_resetjp_3586_;
}
else
{
lean_dec(v_code_3445_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3595_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 1, v_a_3580_);
lean_ctor_set(v___x_3587_, 0, v_fvarId_3578_);
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_fvarId_3578_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v_a_3580_);
v___x_3590_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3592_; 
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 0, v___x_3590_);
v___x_3592_ = v___x_3582_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
else
{
lean_object* v___x_3599_; 
lean_dec(v_a_3580_);
lean_dec(v_fvarId_3578_);
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 0, v_code_3445_);
v___x_3599_ = v___x_3582_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_code_3445_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
lean_dec(v_fvarId_3578_);
lean_dec_ref_known(v_code_3445_, 2);
v_a_3606_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3579_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3579_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
else
{
lean_object* v___x_3614_; 
lean_dec_ref_known(v_code_3445_, 2);
v___x_3614_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3443_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
return v___x_3614_;
}
}
case 4:
{
lean_object* v_cases_3615_; lean_object* v_typeName_3616_; lean_object* v_resultType_3617_; lean_object* v_discr_3618_; lean_object* v_alts_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3666_; 
v_cases_3615_ = lean_ctor_get(v_code_3445_, 0);
lean_inc_ref(v_cases_3615_);
v_typeName_3616_ = lean_ctor_get(v_cases_3615_, 0);
v_resultType_3617_ = lean_ctor_get(v_cases_3615_, 1);
v_discr_3618_ = lean_ctor_get(v_cases_3615_, 2);
v_alts_3619_ = lean_ctor_get(v_cases_3615_, 3);
v_isSharedCheck_3666_ = !lean_is_exclusive(v_cases_3615_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3621_ = v_cases_3615_;
v_isShared_3622_ = v_isSharedCheck_3666_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_alts_3619_);
lean_inc(v_discr_3618_);
lean_inc(v_resultType_3617_);
lean_inc(v_typeName_3616_);
lean_dec(v_cases_3615_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3666_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; 
lean_inc_ref(v_resultType_3617_);
v___x_3623_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3443_, v_a_3446_, v_t_3444_, v_resultType_3617_);
lean_inc(v_discr_3618_);
v___x_3624_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3446_, v_discr_3618_, v_t_3444_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_fvarId_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3664_; 
v_fvarId_3625_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3627_ = v___x_3624_;
v_isShared_3628_ = v_isSharedCheck_3664_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_fvarId_3625_);
lean_dec(v___x_3624_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3664_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3629_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3619_);
v___x_3630_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_3443_, v_t_3444_, v___x_3629_, v_alts_3619_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3655_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3633_ = v___x_3630_;
v_isShared_3634_ = v_isSharedCheck_3655_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3630_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3655_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
uint8_t v___y_3646_; size_t v___x_3649_; size_t v___x_3650_; uint8_t v___x_3651_; 
v___x_3649_ = lean_ptr_addr(v_alts_3619_);
lean_dec_ref(v_alts_3619_);
v___x_3650_ = lean_ptr_addr(v_a_3631_);
v___x_3651_ = lean_usize_dec_eq(v___x_3649_, v___x_3650_);
if (v___x_3651_ == 0)
{
lean_dec_ref(v_resultType_3617_);
v___y_3646_ = v___x_3651_;
goto v___jp_3645_;
}
else
{
size_t v___x_3652_; size_t v___x_3653_; uint8_t v___x_3654_; 
v___x_3652_ = lean_ptr_addr(v_resultType_3617_);
lean_dec_ref(v_resultType_3617_);
v___x_3653_ = lean_ptr_addr(v___x_3623_);
v___x_3654_ = lean_usize_dec_eq(v___x_3652_, v___x_3653_);
v___y_3646_ = v___x_3654_;
goto v___jp_3645_;
}
v___jp_3635_:
{
lean_object* v___x_3637_; 
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 3, v_a_3631_);
lean_ctor_set(v___x_3621_, 2, v_fvarId_3625_);
lean_ctor_set(v___x_3621_, 1, v___x_3623_);
v___x_3637_ = v___x_3621_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_typeName_3616_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v___x_3623_);
lean_ctor_set(v_reuseFailAlloc_3644_, 2, v_fvarId_3625_);
lean_ctor_set(v_reuseFailAlloc_3644_, 3, v_a_3631_);
v___x_3637_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
lean_object* v___x_3639_; 
if (v_isShared_3628_ == 0)
{
lean_ctor_set_tag(v___x_3627_, 4);
lean_ctor_set(v___x_3627_, 0, v___x_3637_);
v___x_3639_ = v___x_3627_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3637_);
v___x_3639_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
lean_object* v___x_3641_; 
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 0, v___x_3639_);
v___x_3641_ = v___x_3633_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3639_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
v___jp_3645_:
{
if (v___y_3646_ == 0)
{
lean_dec(v_discr_3618_);
lean_dec_ref_known(v_code_3445_, 1);
goto v___jp_3635_;
}
else
{
uint8_t v___x_3647_; 
v___x_3647_ = l_Lean_instBEqFVarId_beq(v_discr_3618_, v_fvarId_3625_);
lean_dec(v_discr_3618_);
if (v___x_3647_ == 0)
{
lean_dec_ref_known(v_code_3445_, 1);
goto v___jp_3635_;
}
else
{
lean_object* v___x_3648_; 
lean_del_object(v___x_3633_);
lean_dec(v_a_3631_);
lean_del_object(v___x_3627_);
lean_dec(v_fvarId_3625_);
lean_dec_ref(v___x_3623_);
lean_del_object(v___x_3621_);
lean_dec(v_typeName_3616_);
v___x_3648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3648_, 0, v_code_3445_);
return v___x_3648_;
}
}
}
}
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
lean_del_object(v___x_3627_);
lean_dec(v_fvarId_3625_);
lean_dec_ref(v___x_3623_);
lean_del_object(v___x_3621_);
lean_dec_ref(v_alts_3619_);
lean_dec(v_discr_3618_);
lean_dec_ref(v_resultType_3617_);
lean_dec(v_typeName_3616_);
lean_dec_ref_known(v_code_3445_, 1);
v_a_3656_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3630_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3630_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
}
else
{
lean_object* v___x_3665_; 
lean_dec_ref(v___x_3623_);
lean_del_object(v___x_3621_);
lean_dec_ref(v_alts_3619_);
lean_dec(v_discr_3618_);
lean_dec_ref(v_resultType_3617_);
lean_dec(v_typeName_3616_);
lean_dec_ref_known(v_code_3445_, 1);
v___x_3665_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3443_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
return v___x_3665_;
}
}
}
case 5:
{
lean_object* v_fvarId_3667_; lean_object* v___x_3668_; 
v_fvarId_3667_ = lean_ctor_get(v_code_3445_, 0);
lean_inc(v_fvarId_3667_);
v___x_3668_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3446_, v_fvarId_3667_, v_t_3444_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_fvarId_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3688_; 
v_fvarId_3669_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3671_ = v___x_3668_;
v_isShared_3672_ = v_isSharedCheck_3688_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_fvarId_3669_);
lean_dec(v___x_3668_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3688_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
uint8_t v___x_3673_; 
v___x_3673_ = l_Lean_instBEqFVarId_beq(v_fvarId_3667_, v_fvarId_3669_);
if (v___x_3673_ == 0)
{
lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3683_; 
v_isSharedCheck_3683_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3683_ == 0)
{
lean_object* v_unused_3684_; 
v_unused_3684_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3684_);
v___x_3675_ = v_code_3445_;
v_isShared_3676_ = v_isSharedCheck_3683_;
goto v_resetjp_3674_;
}
else
{
lean_dec(v_code_3445_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3683_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v_fvarId_3669_);
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_fvarId_3669_);
v___x_3678_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3680_; 
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v___x_3678_);
v___x_3680_ = v___x_3671_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3678_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
else
{
lean_object* v___x_3686_; 
lean_dec(v_fvarId_3669_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v_code_3445_);
v___x_3686_ = v___x_3671_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_code_3445_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
else
{
lean_object* v___x_3689_; 
lean_dec_ref_known(v_code_3445_, 1);
v___x_3689_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3443_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
return v___x_3689_;
}
}
case 6:
{
lean_object* v_type_3690_; lean_object* v___x_3691_; size_t v___x_3692_; size_t v___x_3693_; uint8_t v___x_3694_; 
v_type_3690_ = lean_ctor_get(v_code_3445_, 0);
lean_inc_ref(v_type_3690_);
v___x_3691_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3443_, v_a_3446_, v_t_3444_, v_type_3690_);
v___x_3692_ = lean_ptr_addr(v_type_3690_);
v___x_3693_ = lean_ptr_addr(v___x_3691_);
v___x_3694_ = lean_usize_dec_eq(v___x_3692_, v___x_3693_);
if (v___x_3694_ == 0)
{
lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3702_; 
v_isSharedCheck_3702_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3702_ == 0)
{
lean_object* v_unused_3703_; 
v_unused_3703_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3703_);
v___x_3696_ = v_code_3445_;
v_isShared_3697_ = v_isSharedCheck_3702_;
goto v_resetjp_3695_;
}
else
{
lean_dec(v_code_3445_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3702_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 0, v___x_3691_);
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v___x_3691_);
v___x_3699_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
lean_object* v___x_3700_; 
v___x_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3699_);
return v___x_3700_;
}
}
}
else
{
lean_object* v___x_3704_; 
lean_dec_ref(v___x_3691_);
v___x_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3704_, 0, v_code_3445_);
return v___x_3704_;
}
}
case 7:
{
lean_object* v_fvarId_3705_; lean_object* v_i_3706_; lean_object* v_y_3707_; lean_object* v_k_3708_; lean_object* v___x_3709_; 
v_fvarId_3705_ = lean_ctor_get(v_code_3445_, 0);
v_i_3706_ = lean_ctor_get(v_code_3445_, 1);
v_y_3707_ = lean_ctor_get(v_code_3445_, 2);
v_k_3708_ = lean_ctor_get(v_code_3445_, 3);
lean_inc(v_fvarId_3705_);
v___x_3709_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3446_, v_fvarId_3705_, v_t_3444_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_fvarId_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v_fvarId_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_fvarId_3710_);
lean_dec_ref_known(v___x_3709_, 1);
lean_inc(v_y_3707_);
v___x_3711_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_3443_, v_a_3446_, v_y_3707_, v_t_3444_);
lean_inc_ref(v_k_3708_);
v___x_3712_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3443_, v_t_3444_, v_k_3708_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3774_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3715_ = v___x_3712_;
v_isShared_3716_ = v_isSharedCheck_3774_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3712_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3774_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
uint8_t v___y_3718_; size_t v___x_3770_; size_t v___x_3771_; uint8_t v___x_3772_; 
v___x_3770_ = lean_ptr_addr(v_fvarId_3705_);
v___x_3771_ = lean_ptr_addr(v_fvarId_3710_);
v___x_3772_ = lean_usize_dec_eq(v___x_3770_, v___x_3771_);
if (v___x_3772_ == 0)
{
v___y_3718_ = v___x_3772_;
goto v___jp_3717_;
}
else
{
uint8_t v___x_3773_; 
v___x_3773_ = lean_nat_dec_eq(v_i_3706_, v_i_3706_);
v___y_3718_ = v___x_3773_;
goto v___jp_3717_;
}
v___jp_3717_:
{
if (v___y_3718_ == 0)
{
lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3728_; 
lean_inc(v_i_3706_);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3728_ == 0)
{
lean_object* v_unused_3729_; lean_object* v_unused_3730_; lean_object* v_unused_3731_; lean_object* v_unused_3732_; 
v_unused_3729_ = lean_ctor_get(v_code_3445_, 3);
lean_dec(v_unused_3729_);
v_unused_3730_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_3730_);
v_unused_3731_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_3731_);
v_unused_3732_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3732_);
v___x_3720_ = v_code_3445_;
v_isShared_3721_ = v_isSharedCheck_3728_;
goto v_resetjp_3719_;
}
else
{
lean_dec(v_code_3445_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3728_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 3, v_a_3713_);
lean_ctor_set(v___x_3720_, 2, v___x_3711_);
lean_ctor_set(v___x_3720_, 0, v_fvarId_3710_);
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_fvarId_3710_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v_i_3706_);
lean_ctor_set(v_reuseFailAlloc_3727_, 2, v___x_3711_);
lean_ctor_set(v_reuseFailAlloc_3727_, 3, v_a_3713_);
v___x_3723_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3725_; 
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3723_);
v___x_3725_ = v___x_3715_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3723_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
else
{
size_t v___x_3733_; size_t v___x_3734_; uint8_t v___x_3735_; 
v___x_3733_ = lean_ptr_addr(v_y_3707_);
v___x_3734_ = lean_ptr_addr(v___x_3711_);
v___x_3735_ = lean_usize_dec_eq(v___x_3733_, v___x_3734_);
if (v___x_3735_ == 0)
{
lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3745_; 
lean_inc(v_i_3706_);
v_isSharedCheck_3745_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3745_ == 0)
{
lean_object* v_unused_3746_; lean_object* v_unused_3747_; lean_object* v_unused_3748_; lean_object* v_unused_3749_; 
v_unused_3746_ = lean_ctor_get(v_code_3445_, 3);
lean_dec(v_unused_3746_);
v_unused_3747_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_3747_);
v_unused_3748_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_3748_);
v_unused_3749_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3749_);
v___x_3737_ = v_code_3445_;
v_isShared_3738_ = v_isSharedCheck_3745_;
goto v_resetjp_3736_;
}
else
{
lean_dec(v_code_3445_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3745_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 3, v_a_3713_);
lean_ctor_set(v___x_3737_, 2, v___x_3711_);
lean_ctor_set(v___x_3737_, 0, v_fvarId_3710_);
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_fvarId_3710_);
lean_ctor_set(v_reuseFailAlloc_3744_, 1, v_i_3706_);
lean_ctor_set(v_reuseFailAlloc_3744_, 2, v___x_3711_);
lean_ctor_set(v_reuseFailAlloc_3744_, 3, v_a_3713_);
v___x_3740_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
lean_object* v___x_3742_; 
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3740_);
v___x_3742_ = v___x_3715_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3740_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
else
{
size_t v___x_3750_; size_t v___x_3751_; uint8_t v___x_3752_; 
v___x_3750_ = lean_ptr_addr(v_k_3708_);
v___x_3751_ = lean_ptr_addr(v_a_3713_);
v___x_3752_ = lean_usize_dec_eq(v___x_3750_, v___x_3751_);
if (v___x_3752_ == 0)
{
lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3762_; 
lean_inc(v_i_3706_);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3762_ == 0)
{
lean_object* v_unused_3763_; lean_object* v_unused_3764_; lean_object* v_unused_3765_; lean_object* v_unused_3766_; 
v_unused_3763_ = lean_ctor_get(v_code_3445_, 3);
lean_dec(v_unused_3763_);
v_unused_3764_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_3764_);
v_unused_3765_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_3765_);
v_unused_3766_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3766_);
v___x_3754_ = v_code_3445_;
v_isShared_3755_ = v_isSharedCheck_3762_;
goto v_resetjp_3753_;
}
else
{
lean_dec(v_code_3445_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3762_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 3, v_a_3713_);
lean_ctor_set(v___x_3754_, 2, v___x_3711_);
lean_ctor_set(v___x_3754_, 0, v_fvarId_3710_);
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_fvarId_3710_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_i_3706_);
lean_ctor_set(v_reuseFailAlloc_3761_, 2, v___x_3711_);
lean_ctor_set(v_reuseFailAlloc_3761_, 3, v_a_3713_);
v___x_3757_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
lean_object* v___x_3759_; 
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3757_);
v___x_3759_ = v___x_3715_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
else
{
lean_object* v___x_3768_; 
lean_dec(v_a_3713_);
lean_dec(v___x_3711_);
lean_dec(v_fvarId_3710_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v_code_3445_);
v___x_3768_ = v___x_3715_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_code_3445_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3711_);
lean_dec(v_fvarId_3710_);
lean_dec_ref_known(v_code_3445_, 4);
return v___x_3712_;
}
}
else
{
lean_object* v___x_3775_; 
lean_dec_ref_known(v_code_3445_, 4);
v___x_3775_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3443_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
return v___x_3775_;
}
}
case 8:
{
lean_object* v_fvarId_3776_; lean_object* v_i_3777_; lean_object* v_y_3778_; lean_object* v_k_3779_; lean_object* v___x_3780_; 
v_fvarId_3776_ = lean_ctor_get(v_code_3445_, 0);
v_i_3777_ = lean_ctor_get(v_code_3445_, 1);
v_y_3778_ = lean_ctor_get(v_code_3445_, 2);
v_k_3779_ = lean_ctor_get(v_code_3445_, 3);
lean_inc(v_fvarId_3776_);
v___x_3780_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3446_, v_fvarId_3776_, v_t_3444_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_fvarId_3781_; lean_object* v___x_3782_; 
v_fvarId_3781_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_fvarId_3781_);
lean_dec_ref_known(v___x_3780_, 1);
lean_inc(v_y_3778_);
v___x_3782_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3446_, v_y_3778_, v_t_3444_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_fvarId_3783_; lean_object* v___x_3784_; 
v_fvarId_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_fvarId_3783_);
lean_dec_ref_known(v___x_3782_, 1);
lean_inc_ref(v_k_3779_);
v___x_3784_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3443_, v_t_3444_, v_k_3779_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3846_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3787_ = v___x_3784_;
v_isShared_3788_ = v_isSharedCheck_3846_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3784_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3846_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
uint8_t v___y_3790_; size_t v___x_3842_; size_t v___x_3843_; uint8_t v___x_3844_; 
v___x_3842_ = lean_ptr_addr(v_fvarId_3776_);
v___x_3843_ = lean_ptr_addr(v_fvarId_3781_);
v___x_3844_ = lean_usize_dec_eq(v___x_3842_, v___x_3843_);
if (v___x_3844_ == 0)
{
v___y_3790_ = v___x_3844_;
goto v___jp_3789_;
}
else
{
uint8_t v___x_3845_; 
v___x_3845_ = lean_nat_dec_eq(v_i_3777_, v_i_3777_);
v___y_3790_ = v___x_3845_;
goto v___jp_3789_;
}
v___jp_3789_:
{
if (v___y_3790_ == 0)
{
lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3800_; 
lean_inc(v_i_3777_);
v_isSharedCheck_3800_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3800_ == 0)
{
lean_object* v_unused_3801_; lean_object* v_unused_3802_; lean_object* v_unused_3803_; lean_object* v_unused_3804_; 
v_unused_3801_ = lean_ctor_get(v_code_3445_, 3);
lean_dec(v_unused_3801_);
v_unused_3802_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_3802_);
v_unused_3803_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_3803_);
v_unused_3804_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3804_);
v___x_3792_ = v_code_3445_;
v_isShared_3793_ = v_isSharedCheck_3800_;
goto v_resetjp_3791_;
}
else
{
lean_dec(v_code_3445_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3800_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 3, v_a_3785_);
lean_ctor_set(v___x_3792_, 2, v_fvarId_3783_);
lean_ctor_set(v___x_3792_, 0, v_fvarId_3781_);
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_fvarId_3781_);
lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_i_3777_);
lean_ctor_set(v_reuseFailAlloc_3799_, 2, v_fvarId_3783_);
lean_ctor_set(v_reuseFailAlloc_3799_, 3, v_a_3785_);
v___x_3795_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
lean_object* v___x_3797_; 
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v___x_3795_);
v___x_3797_ = v___x_3787_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3795_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
else
{
size_t v___x_3805_; size_t v___x_3806_; uint8_t v___x_3807_; 
v___x_3805_ = lean_ptr_addr(v_y_3778_);
v___x_3806_ = lean_ptr_addr(v_fvarId_3783_);
v___x_3807_ = lean_usize_dec_eq(v___x_3805_, v___x_3806_);
if (v___x_3807_ == 0)
{
lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3817_; 
lean_inc(v_i_3777_);
v_isSharedCheck_3817_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3817_ == 0)
{
lean_object* v_unused_3818_; lean_object* v_unused_3819_; lean_object* v_unused_3820_; lean_object* v_unused_3821_; 
v_unused_3818_ = lean_ctor_get(v_code_3445_, 3);
lean_dec(v_unused_3818_);
v_unused_3819_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_3819_);
v_unused_3820_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_3820_);
v_unused_3821_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3821_);
v___x_3809_ = v_code_3445_;
v_isShared_3810_ = v_isSharedCheck_3817_;
goto v_resetjp_3808_;
}
else
{
lean_dec(v_code_3445_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3817_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 3, v_a_3785_);
lean_ctor_set(v___x_3809_, 2, v_fvarId_3783_);
lean_ctor_set(v___x_3809_, 0, v_fvarId_3781_);
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_fvarId_3781_);
lean_ctor_set(v_reuseFailAlloc_3816_, 1, v_i_3777_);
lean_ctor_set(v_reuseFailAlloc_3816_, 2, v_fvarId_3783_);
lean_ctor_set(v_reuseFailAlloc_3816_, 3, v_a_3785_);
v___x_3812_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
lean_object* v___x_3814_; 
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v___x_3812_);
v___x_3814_ = v___x_3787_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
else
{
size_t v___x_3822_; size_t v___x_3823_; uint8_t v___x_3824_; 
v___x_3822_ = lean_ptr_addr(v_k_3779_);
v___x_3823_ = lean_ptr_addr(v_a_3785_);
v___x_3824_ = lean_usize_dec_eq(v___x_3822_, v___x_3823_);
if (v___x_3824_ == 0)
{
lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3834_; 
lean_inc(v_i_3777_);
v_isSharedCheck_3834_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3834_ == 0)
{
lean_object* v_unused_3835_; lean_object* v_unused_3836_; lean_object* v_unused_3837_; lean_object* v_unused_3838_; 
v_unused_3835_ = lean_ctor_get(v_code_3445_, 3);
lean_dec(v_unused_3835_);
v_unused_3836_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_3836_);
v_unused_3837_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_3837_);
v_unused_3838_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3838_);
v___x_3826_ = v_code_3445_;
v_isShared_3827_ = v_isSharedCheck_3834_;
goto v_resetjp_3825_;
}
else
{
lean_dec(v_code_3445_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3834_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 3, v_a_3785_);
lean_ctor_set(v___x_3826_, 2, v_fvarId_3783_);
lean_ctor_set(v___x_3826_, 0, v_fvarId_3781_);
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_fvarId_3781_);
lean_ctor_set(v_reuseFailAlloc_3833_, 1, v_i_3777_);
lean_ctor_set(v_reuseFailAlloc_3833_, 2, v_fvarId_3783_);
lean_ctor_set(v_reuseFailAlloc_3833_, 3, v_a_3785_);
v___x_3829_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
lean_object* v___x_3831_; 
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v___x_3829_);
v___x_3831_ = v___x_3787_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3829_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
else
{
lean_object* v___x_3840_; 
lean_dec(v_a_3785_);
lean_dec(v_fvarId_3783_);
lean_dec(v_fvarId_3781_);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v_code_3445_);
v___x_3840_ = v___x_3787_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_code_3445_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_3783_);
lean_dec(v_fvarId_3781_);
lean_dec_ref_known(v_code_3445_, 4);
return v___x_3784_;
}
}
else
{
lean_object* v___x_3847_; 
lean_dec(v_fvarId_3781_);
lean_dec_ref_known(v_code_3445_, 4);
v___x_3847_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3443_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
return v___x_3847_;
}
}
else
{
lean_object* v___x_3848_; 
lean_dec_ref_known(v_code_3445_, 4);
v___x_3848_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3443_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
return v___x_3848_;
}
}
case 9:
{
lean_object* v_fvarId_3849_; lean_object* v_i_3850_; lean_object* v_offset_3851_; lean_object* v_y_3852_; lean_object* v_ty_3853_; lean_object* v_k_3854_; lean_object* v___x_3855_; 
v_fvarId_3849_ = lean_ctor_get(v_code_3445_, 0);
v_i_3850_ = lean_ctor_get(v_code_3445_, 1);
v_offset_3851_ = lean_ctor_get(v_code_3445_, 2);
v_y_3852_ = lean_ctor_get(v_code_3445_, 3);
v_ty_3853_ = lean_ctor_get(v_code_3445_, 4);
v_k_3854_ = lean_ctor_get(v_code_3445_, 5);
lean_inc(v_fvarId_3849_);
v___x_3855_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3446_, v_fvarId_3849_, v_t_3444_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_fvarId_3856_; lean_object* v___x_3857_; 
v_fvarId_3856_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_fvarId_3856_);
lean_dec_ref_known(v___x_3855_, 1);
lean_inc(v_y_3852_);
v___x_3857_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3446_, v_y_3852_, v_t_3444_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_fvarId_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v_fvarId_3858_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_fvarId_3858_);
lean_dec_ref_known(v___x_3857_, 1);
lean_inc_ref(v_ty_3853_);
v___x_3859_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3443_, v_a_3446_, v_t_3444_, v_ty_3853_);
lean_inc_ref(v_k_3854_);
v___x_3860_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3443_, v_t_3444_, v_k_3854_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3964_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3863_ = v___x_3860_;
v_isShared_3864_ = v_isSharedCheck_3964_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3860_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3964_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
uint8_t v___y_3866_; size_t v___x_3960_; size_t v___x_3961_; uint8_t v___x_3962_; 
v___x_3960_ = lean_ptr_addr(v_fvarId_3849_);
v___x_3961_ = lean_ptr_addr(v_fvarId_3856_);
v___x_3962_ = lean_usize_dec_eq(v___x_3960_, v___x_3961_);
if (v___x_3962_ == 0)
{
v___y_3866_ = v___x_3962_;
goto v___jp_3865_;
}
else
{
uint8_t v___x_3963_; 
v___x_3963_ = lean_nat_dec_eq(v_i_3850_, v_i_3850_);
v___y_3866_ = v___x_3963_;
goto v___jp_3865_;
}
v___jp_3865_:
{
if (v___y_3866_ == 0)
{
lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3876_; 
lean_inc(v_offset_3851_);
lean_inc(v_i_3850_);
v_isSharedCheck_3876_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3876_ == 0)
{
lean_object* v_unused_3877_; lean_object* v_unused_3878_; lean_object* v_unused_3879_; lean_object* v_unused_3880_; lean_object* v_unused_3881_; lean_object* v_unused_3882_; 
v_unused_3877_ = lean_ctor_get(v_code_3445_, 5);
lean_dec(v_unused_3877_);
v_unused_3878_ = lean_ctor_get(v_code_3445_, 4);
lean_dec(v_unused_3878_);
v_unused_3879_ = lean_ctor_get(v_code_3445_, 3);
lean_dec(v_unused_3879_);
v_unused_3880_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_3880_);
v_unused_3881_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_3881_);
v_unused_3882_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3882_);
v___x_3868_ = v_code_3445_;
v_isShared_3869_ = v_isSharedCheck_3876_;
goto v_resetjp_3867_;
}
else
{
lean_dec(v_code_3445_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3876_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 5, v_a_3861_);
lean_ctor_set(v___x_3868_, 4, v___x_3859_);
lean_ctor_set(v___x_3868_, 3, v_fvarId_3858_);
lean_ctor_set(v___x_3868_, 0, v_fvarId_3856_);
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_fvarId_3856_);
lean_ctor_set(v_reuseFailAlloc_3875_, 1, v_i_3850_);
lean_ctor_set(v_reuseFailAlloc_3875_, 2, v_offset_3851_);
lean_ctor_set(v_reuseFailAlloc_3875_, 3, v_fvarId_3858_);
lean_ctor_set(v_reuseFailAlloc_3875_, 4, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3875_, 5, v_a_3861_);
v___x_3871_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
lean_object* v___x_3873_; 
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3871_);
v___x_3873_ = v___x_3863_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3871_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
else
{
uint8_t v___x_3883_; 
v___x_3883_ = lean_nat_dec_eq(v_offset_3851_, v_offset_3851_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3893_; 
lean_inc(v_offset_3851_);
lean_inc(v_i_3850_);
v_isSharedCheck_3893_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3893_ == 0)
{
lean_object* v_unused_3894_; lean_object* v_unused_3895_; lean_object* v_unused_3896_; lean_object* v_unused_3897_; lean_object* v_unused_3898_; lean_object* v_unused_3899_; 
v_unused_3894_ = lean_ctor_get(v_code_3445_, 5);
lean_dec(v_unused_3894_);
v_unused_3895_ = lean_ctor_get(v_code_3445_, 4);
lean_dec(v_unused_3895_);
v_unused_3896_ = lean_ctor_get(v_code_3445_, 3);
lean_dec(v_unused_3896_);
v_unused_3897_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_3897_);
v_unused_3898_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_3898_);
v_unused_3899_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3899_);
v___x_3885_ = v_code_3445_;
v_isShared_3886_ = v_isSharedCheck_3893_;
goto v_resetjp_3884_;
}
else
{
lean_dec(v_code_3445_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3893_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 5, v_a_3861_);
lean_ctor_set(v___x_3885_, 4, v___x_3859_);
lean_ctor_set(v___x_3885_, 3, v_fvarId_3858_);
lean_ctor_set(v___x_3885_, 0, v_fvarId_3856_);
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_fvarId_3856_);
lean_ctor_set(v_reuseFailAlloc_3892_, 1, v_i_3850_);
lean_ctor_set(v_reuseFailAlloc_3892_, 2, v_offset_3851_);
lean_ctor_set(v_reuseFailAlloc_3892_, 3, v_fvarId_3858_);
lean_ctor_set(v_reuseFailAlloc_3892_, 4, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3892_, 5, v_a_3861_);
v___x_3888_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_object* v___x_3890_; 
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3888_);
v___x_3890_ = v___x_3863_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v___x_3888_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
else
{
size_t v___x_3900_; size_t v___x_3901_; uint8_t v___x_3902_; 
v___x_3900_ = lean_ptr_addr(v_y_3852_);
v___x_3901_ = lean_ptr_addr(v_fvarId_3858_);
v___x_3902_ = lean_usize_dec_eq(v___x_3900_, v___x_3901_);
if (v___x_3902_ == 0)
{
lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3912_; 
lean_inc(v_offset_3851_);
lean_inc(v_i_3850_);
v_isSharedCheck_3912_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3912_ == 0)
{
lean_object* v_unused_3913_; lean_object* v_unused_3914_; lean_object* v_unused_3915_; lean_object* v_unused_3916_; lean_object* v_unused_3917_; lean_object* v_unused_3918_; 
v_unused_3913_ = lean_ctor_get(v_code_3445_, 5);
lean_dec(v_unused_3913_);
v_unused_3914_ = lean_ctor_get(v_code_3445_, 4);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_code_3445_, 3);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_3916_);
v_unused_3917_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_3917_);
v_unused_3918_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3918_);
v___x_3904_ = v_code_3445_;
v_isShared_3905_ = v_isSharedCheck_3912_;
goto v_resetjp_3903_;
}
else
{
lean_dec(v_code_3445_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3912_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3907_; 
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 5, v_a_3861_);
lean_ctor_set(v___x_3904_, 4, v___x_3859_);
lean_ctor_set(v___x_3904_, 3, v_fvarId_3858_);
lean_ctor_set(v___x_3904_, 0, v_fvarId_3856_);
v___x_3907_ = v___x_3904_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_fvarId_3856_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_i_3850_);
lean_ctor_set(v_reuseFailAlloc_3911_, 2, v_offset_3851_);
lean_ctor_set(v_reuseFailAlloc_3911_, 3, v_fvarId_3858_);
lean_ctor_set(v_reuseFailAlloc_3911_, 4, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3911_, 5, v_a_3861_);
v___x_3907_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3909_; 
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3907_);
v___x_3909_ = v___x_3863_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3907_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
else
{
size_t v___x_3919_; size_t v___x_3920_; uint8_t v___x_3921_; 
v___x_3919_ = lean_ptr_addr(v_ty_3853_);
v___x_3920_ = lean_ptr_addr(v___x_3859_);
v___x_3921_ = lean_usize_dec_eq(v___x_3919_, v___x_3920_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3931_; 
lean_inc(v_offset_3851_);
lean_inc(v_i_3850_);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3931_ == 0)
{
lean_object* v_unused_3932_; lean_object* v_unused_3933_; lean_object* v_unused_3934_; lean_object* v_unused_3935_; lean_object* v_unused_3936_; lean_object* v_unused_3937_; 
v_unused_3932_ = lean_ctor_get(v_code_3445_, 5);
lean_dec(v_unused_3932_);
v_unused_3933_ = lean_ctor_get(v_code_3445_, 4);
lean_dec(v_unused_3933_);
v_unused_3934_ = lean_ctor_get(v_code_3445_, 3);
lean_dec(v_unused_3934_);
v_unused_3935_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_3935_);
v_unused_3936_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_3936_);
v_unused_3937_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3937_);
v___x_3923_ = v_code_3445_;
v_isShared_3924_ = v_isSharedCheck_3931_;
goto v_resetjp_3922_;
}
else
{
lean_dec(v_code_3445_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3931_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 5, v_a_3861_);
lean_ctor_set(v___x_3923_, 4, v___x_3859_);
lean_ctor_set(v___x_3923_, 3, v_fvarId_3858_);
lean_ctor_set(v___x_3923_, 0, v_fvarId_3856_);
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_fvarId_3856_);
lean_ctor_set(v_reuseFailAlloc_3930_, 1, v_i_3850_);
lean_ctor_set(v_reuseFailAlloc_3930_, 2, v_offset_3851_);
lean_ctor_set(v_reuseFailAlloc_3930_, 3, v_fvarId_3858_);
lean_ctor_set(v_reuseFailAlloc_3930_, 4, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3930_, 5, v_a_3861_);
v___x_3926_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
lean_object* v___x_3928_; 
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3926_);
v___x_3928_ = v___x_3863_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3926_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
else
{
size_t v___x_3938_; size_t v___x_3939_; uint8_t v___x_3940_; 
v___x_3938_ = lean_ptr_addr(v_k_3854_);
v___x_3939_ = lean_ptr_addr(v_a_3861_);
v___x_3940_ = lean_usize_dec_eq(v___x_3938_, v___x_3939_);
if (v___x_3940_ == 0)
{
lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3950_; 
lean_inc(v_offset_3851_);
lean_inc(v_i_3850_);
v_isSharedCheck_3950_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3950_ == 0)
{
lean_object* v_unused_3951_; lean_object* v_unused_3952_; lean_object* v_unused_3953_; lean_object* v_unused_3954_; lean_object* v_unused_3955_; lean_object* v_unused_3956_; 
v_unused_3951_ = lean_ctor_get(v_code_3445_, 5);
lean_dec(v_unused_3951_);
v_unused_3952_ = lean_ctor_get(v_code_3445_, 4);
lean_dec(v_unused_3952_);
v_unused_3953_ = lean_ctor_get(v_code_3445_, 3);
lean_dec(v_unused_3953_);
v_unused_3954_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_3954_);
v_unused_3955_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_3955_);
v_unused_3956_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3956_);
v___x_3942_ = v_code_3445_;
v_isShared_3943_ = v_isSharedCheck_3950_;
goto v_resetjp_3941_;
}
else
{
lean_dec(v_code_3445_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3950_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 5, v_a_3861_);
lean_ctor_set(v___x_3942_, 4, v___x_3859_);
lean_ctor_set(v___x_3942_, 3, v_fvarId_3858_);
lean_ctor_set(v___x_3942_, 0, v_fvarId_3856_);
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_fvarId_3856_);
lean_ctor_set(v_reuseFailAlloc_3949_, 1, v_i_3850_);
lean_ctor_set(v_reuseFailAlloc_3949_, 2, v_offset_3851_);
lean_ctor_set(v_reuseFailAlloc_3949_, 3, v_fvarId_3858_);
lean_ctor_set(v_reuseFailAlloc_3949_, 4, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3949_, 5, v_a_3861_);
v___x_3945_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
lean_object* v___x_3947_; 
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3945_);
v___x_3947_ = v___x_3863_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3945_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
else
{
lean_object* v___x_3958_; 
lean_dec(v_a_3861_);
lean_dec_ref(v___x_3859_);
lean_dec(v_fvarId_3858_);
lean_dec(v_fvarId_3856_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v_code_3445_);
v___x_3958_ = v___x_3863_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_code_3445_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
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
lean_dec_ref(v___x_3859_);
lean_dec(v_fvarId_3858_);
lean_dec(v_fvarId_3856_);
lean_dec_ref_known(v_code_3445_, 6);
return v___x_3860_;
}
}
else
{
lean_object* v___x_3965_; 
lean_dec(v_fvarId_3856_);
lean_dec_ref_known(v_code_3445_, 6);
v___x_3965_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3443_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
return v___x_3965_;
}
}
else
{
lean_object* v___x_3966_; 
lean_dec_ref_known(v_code_3445_, 6);
v___x_3966_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3443_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
return v___x_3966_;
}
}
case 10:
{
lean_object* v_fvarId_3967_; lean_object* v_cidx_3968_; lean_object* v_k_3969_; lean_object* v___x_3970_; 
v_fvarId_3967_ = lean_ctor_get(v_code_3445_, 0);
v_cidx_3968_ = lean_ctor_get(v_code_3445_, 1);
v_k_3969_ = lean_ctor_get(v_code_3445_, 2);
lean_inc(v_fvarId_3967_);
v___x_3970_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3446_, v_fvarId_3967_, v_t_3444_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_fvarId_3971_; lean_object* v___x_3972_; 
v_fvarId_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc(v_fvarId_3971_);
lean_dec_ref_known(v___x_3970_, 1);
lean_inc_ref(v_k_3969_);
v___x_3972_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3443_, v_t_3444_, v_k_3969_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_4015_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_3975_ = v___x_3972_;
v_isShared_3976_ = v_isSharedCheck_4015_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3972_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_4015_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
uint8_t v___y_3978_; size_t v___x_4011_; size_t v___x_4012_; uint8_t v___x_4013_; 
v___x_4011_ = lean_ptr_addr(v_fvarId_3967_);
v___x_4012_ = lean_ptr_addr(v_fvarId_3971_);
v___x_4013_ = lean_usize_dec_eq(v___x_4011_, v___x_4012_);
if (v___x_4013_ == 0)
{
v___y_3978_ = v___x_4013_;
goto v___jp_3977_;
}
else
{
uint8_t v___x_4014_; 
v___x_4014_ = lean_nat_dec_eq(v_cidx_3968_, v_cidx_3968_);
v___y_3978_ = v___x_4014_;
goto v___jp_3977_;
}
v___jp_3977_:
{
if (v___y_3978_ == 0)
{
lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3988_; 
lean_inc(v_cidx_3968_);
v_isSharedCheck_3988_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_3988_ == 0)
{
lean_object* v_unused_3989_; lean_object* v_unused_3990_; lean_object* v_unused_3991_; 
v_unused_3989_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_3989_);
v_unused_3990_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_3990_);
v_unused_3991_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_3991_);
v___x_3980_ = v_code_3445_;
v_isShared_3981_ = v_isSharedCheck_3988_;
goto v_resetjp_3979_;
}
else
{
lean_dec(v_code_3445_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3988_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 2, v_a_3973_);
lean_ctor_set(v___x_3980_, 0, v_fvarId_3971_);
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_fvarId_3971_);
lean_ctor_set(v_reuseFailAlloc_3987_, 1, v_cidx_3968_);
lean_ctor_set(v_reuseFailAlloc_3987_, 2, v_a_3973_);
v___x_3983_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
lean_object* v___x_3985_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 0, v___x_3983_);
v___x_3985_ = v___x_3975_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v___x_3983_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
else
{
size_t v___x_3992_; size_t v___x_3993_; uint8_t v___x_3994_; 
v___x_3992_ = lean_ptr_addr(v_k_3969_);
v___x_3993_ = lean_ptr_addr(v_a_3973_);
v___x_3994_ = lean_usize_dec_eq(v___x_3992_, v___x_3993_);
if (v___x_3994_ == 0)
{
lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4004_; 
lean_inc(v_cidx_3968_);
v_isSharedCheck_4004_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_4004_ == 0)
{
lean_object* v_unused_4005_; lean_object* v_unused_4006_; lean_object* v_unused_4007_; 
v_unused_4005_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_4005_);
v_unused_4006_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_4006_);
v_unused_4007_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_4007_);
v___x_3996_ = v_code_3445_;
v_isShared_3997_ = v_isSharedCheck_4004_;
goto v_resetjp_3995_;
}
else
{
lean_dec(v_code_3445_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4004_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 2, v_a_3973_);
lean_ctor_set(v___x_3996_, 0, v_fvarId_3971_);
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_fvarId_3971_);
lean_ctor_set(v_reuseFailAlloc_4003_, 1, v_cidx_3968_);
lean_ctor_set(v_reuseFailAlloc_4003_, 2, v_a_3973_);
v___x_3999_ = v_reuseFailAlloc_4003_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
lean_object* v___x_4001_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 0, v___x_3999_);
v___x_4001_ = v___x_3975_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3999_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
else
{
lean_object* v___x_4009_; 
lean_dec(v_a_3973_);
lean_dec(v_fvarId_3971_);
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 0, v_code_3445_);
v___x_4009_ = v___x_3975_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_code_3445_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_3971_);
lean_dec_ref_known(v_code_3445_, 3);
return v___x_3972_;
}
}
else
{
lean_object* v___x_4016_; 
lean_dec_ref_known(v_code_3445_, 3);
v___x_4016_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3443_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
return v___x_4016_;
}
}
case 11:
{
lean_object* v_fvarId_4017_; lean_object* v_n_4018_; uint8_t v_check_4019_; uint8_t v_persistent_4020_; lean_object* v_k_4021_; lean_object* v___x_4022_; 
v_fvarId_4017_ = lean_ctor_get(v_code_3445_, 0);
v_n_4018_ = lean_ctor_get(v_code_3445_, 1);
v_check_4019_ = lean_ctor_get_uint8(v_code_3445_, sizeof(void*)*3);
v_persistent_4020_ = lean_ctor_get_uint8(v_code_3445_, sizeof(void*)*3 + 1);
v_k_4021_ = lean_ctor_get(v_code_3445_, 2);
lean_inc(v_fvarId_4017_);
v___x_4022_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3446_, v_fvarId_4017_, v_t_3444_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_fvarId_4023_; lean_object* v___x_4024_; 
v_fvarId_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc(v_fvarId_4023_);
lean_dec_ref_known(v___x_4022_, 1);
lean_inc_ref(v_k_4021_);
v___x_4024_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3443_, v_t_3444_, v_k_4021_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4067_; 
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4027_ = v___x_4024_;
v_isShared_4028_ = v_isSharedCheck_4067_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___x_4024_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4067_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
uint8_t v___y_4030_; size_t v___x_4063_; size_t v___x_4064_; uint8_t v___x_4065_; 
v___x_4063_ = lean_ptr_addr(v_fvarId_4017_);
v___x_4064_ = lean_ptr_addr(v_fvarId_4023_);
v___x_4065_ = lean_usize_dec_eq(v___x_4063_, v___x_4064_);
if (v___x_4065_ == 0)
{
v___y_4030_ = v___x_4065_;
goto v___jp_4029_;
}
else
{
uint8_t v___x_4066_; 
v___x_4066_ = lean_nat_dec_eq(v_n_4018_, v_n_4018_);
v___y_4030_ = v___x_4066_;
goto v___jp_4029_;
}
v___jp_4029_:
{
if (v___y_4030_ == 0)
{
lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4040_; 
lean_inc(v_n_4018_);
v_isSharedCheck_4040_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_4040_ == 0)
{
lean_object* v_unused_4041_; lean_object* v_unused_4042_; lean_object* v_unused_4043_; 
v_unused_4041_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_4041_);
v_unused_4042_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_4042_);
v_unused_4043_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_4043_);
v___x_4032_ = v_code_3445_;
v_isShared_4033_ = v_isSharedCheck_4040_;
goto v_resetjp_4031_;
}
else
{
lean_dec(v_code_3445_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4040_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 2, v_a_4025_);
lean_ctor_set(v___x_4032_, 0, v_fvarId_4023_);
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_fvarId_4023_);
lean_ctor_set(v_reuseFailAlloc_4039_, 1, v_n_4018_);
lean_ctor_set(v_reuseFailAlloc_4039_, 2, v_a_4025_);
lean_ctor_set_uint8(v_reuseFailAlloc_4039_, sizeof(void*)*3, v_check_4019_);
lean_ctor_set_uint8(v_reuseFailAlloc_4039_, sizeof(void*)*3 + 1, v_persistent_4020_);
v___x_4035_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
lean_object* v___x_4037_; 
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 0, v___x_4035_);
v___x_4037_ = v___x_4027_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v___x_4035_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
}
else
{
size_t v___x_4044_; size_t v___x_4045_; uint8_t v___x_4046_; 
v___x_4044_ = lean_ptr_addr(v_k_4021_);
v___x_4045_ = lean_ptr_addr(v_a_4025_);
v___x_4046_ = lean_usize_dec_eq(v___x_4044_, v___x_4045_);
if (v___x_4046_ == 0)
{
lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4056_; 
lean_inc(v_n_4018_);
v_isSharedCheck_4056_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_4056_ == 0)
{
lean_object* v_unused_4057_; lean_object* v_unused_4058_; lean_object* v_unused_4059_; 
v_unused_4057_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_4057_);
v_unused_4058_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_4058_);
v_unused_4059_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_4059_);
v___x_4048_ = v_code_3445_;
v_isShared_4049_ = v_isSharedCheck_4056_;
goto v_resetjp_4047_;
}
else
{
lean_dec(v_code_3445_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4056_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 2, v_a_4025_);
lean_ctor_set(v___x_4048_, 0, v_fvarId_4023_);
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_fvarId_4023_);
lean_ctor_set(v_reuseFailAlloc_4055_, 1, v_n_4018_);
lean_ctor_set(v_reuseFailAlloc_4055_, 2, v_a_4025_);
lean_ctor_set_uint8(v_reuseFailAlloc_4055_, sizeof(void*)*3, v_check_4019_);
lean_ctor_set_uint8(v_reuseFailAlloc_4055_, sizeof(void*)*3 + 1, v_persistent_4020_);
v___x_4051_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
lean_object* v___x_4053_; 
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 0, v___x_4051_);
v___x_4053_ = v___x_4027_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v___x_4051_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
else
{
lean_object* v___x_4061_; 
lean_dec(v_a_4025_);
lean_dec(v_fvarId_4023_);
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 0, v_code_3445_);
v___x_4061_ = v___x_4027_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_code_3445_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4023_);
lean_dec_ref_known(v_code_3445_, 3);
return v___x_4024_;
}
}
else
{
lean_object* v___x_4068_; 
lean_dec_ref_known(v_code_3445_, 3);
v___x_4068_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3443_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
return v___x_4068_;
}
}
case 12:
{
lean_object* v_fvarId_4069_; lean_object* v_n_4070_; uint8_t v_check_4071_; uint8_t v_persistent_4072_; lean_object* v_objs_x3f_4073_; lean_object* v_k_4074_; lean_object* v___x_4075_; 
v_fvarId_4069_ = lean_ctor_get(v_code_3445_, 0);
v_n_4070_ = lean_ctor_get(v_code_3445_, 1);
v_check_4071_ = lean_ctor_get_uint8(v_code_3445_, sizeof(void*)*4);
v_persistent_4072_ = lean_ctor_get_uint8(v_code_3445_, sizeof(void*)*4 + 1);
v_objs_x3f_4073_ = lean_ctor_get(v_code_3445_, 2);
v_k_4074_ = lean_ctor_get(v_code_3445_, 3);
lean_inc(v_fvarId_4069_);
v___x_4075_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3446_, v_fvarId_4069_, v_t_3444_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_fvarId_4076_; lean_object* v___x_4077_; 
v_fvarId_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_fvarId_4076_);
lean_dec_ref_known(v___x_4075_, 1);
lean_inc_ref(v_k_4074_);
v___x_4077_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3443_, v_t_3444_, v_k_4074_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4138_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4080_ = v___x_4077_;
v_isShared_4081_ = v_isSharedCheck_4138_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4077_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4138_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
uint8_t v___y_4083_; size_t v___x_4134_; size_t v___x_4135_; uint8_t v___x_4136_; 
v___x_4134_ = lean_ptr_addr(v_fvarId_4069_);
v___x_4135_ = lean_ptr_addr(v_fvarId_4076_);
v___x_4136_ = lean_usize_dec_eq(v___x_4134_, v___x_4135_);
if (v___x_4136_ == 0)
{
v___y_4083_ = v___x_4136_;
goto v___jp_4082_;
}
else
{
uint8_t v___x_4137_; 
v___x_4137_ = lean_nat_dec_eq(v_n_4070_, v_n_4070_);
v___y_4083_ = v___x_4137_;
goto v___jp_4082_;
}
v___jp_4082_:
{
if (v___y_4083_ == 0)
{
lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4093_; 
lean_inc(v_objs_x3f_4073_);
lean_inc(v_n_4070_);
v_isSharedCheck_4093_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_4093_ == 0)
{
lean_object* v_unused_4094_; lean_object* v_unused_4095_; lean_object* v_unused_4096_; lean_object* v_unused_4097_; 
v_unused_4094_ = lean_ctor_get(v_code_3445_, 3);
lean_dec(v_unused_4094_);
v_unused_4095_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_4095_);
v_unused_4096_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_4096_);
v_unused_4097_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_4097_);
v___x_4085_ = v_code_3445_;
v_isShared_4086_ = v_isSharedCheck_4093_;
goto v_resetjp_4084_;
}
else
{
lean_dec(v_code_3445_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4093_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 3, v_a_4078_);
lean_ctor_set(v___x_4085_, 0, v_fvarId_4076_);
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_fvarId_4076_);
lean_ctor_set(v_reuseFailAlloc_4092_, 1, v_n_4070_);
lean_ctor_set(v_reuseFailAlloc_4092_, 2, v_objs_x3f_4073_);
lean_ctor_set(v_reuseFailAlloc_4092_, 3, v_a_4078_);
lean_ctor_set_uint8(v_reuseFailAlloc_4092_, sizeof(void*)*4, v_check_4071_);
lean_ctor_set_uint8(v_reuseFailAlloc_4092_, sizeof(void*)*4 + 1, v_persistent_4072_);
v___x_4088_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
lean_object* v___x_4090_; 
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v___x_4088_);
v___x_4090_ = v___x_4080_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4088_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
else
{
size_t v___x_4098_; uint8_t v___x_4099_; 
v___x_4098_ = lean_ptr_addr(v_objs_x3f_4073_);
v___x_4099_ = lean_usize_dec_eq(v___x_4098_, v___x_4098_);
if (v___x_4099_ == 0)
{
lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4109_; 
lean_inc(v_objs_x3f_4073_);
lean_inc(v_n_4070_);
v_isSharedCheck_4109_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_4109_ == 0)
{
lean_object* v_unused_4110_; lean_object* v_unused_4111_; lean_object* v_unused_4112_; lean_object* v_unused_4113_; 
v_unused_4110_ = lean_ctor_get(v_code_3445_, 3);
lean_dec(v_unused_4110_);
v_unused_4111_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_4111_);
v_unused_4112_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_4112_);
v_unused_4113_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_4113_);
v___x_4101_ = v_code_3445_;
v_isShared_4102_ = v_isSharedCheck_4109_;
goto v_resetjp_4100_;
}
else
{
lean_dec(v_code_3445_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4109_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 3, v_a_4078_);
lean_ctor_set(v___x_4101_, 0, v_fvarId_4076_);
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_fvarId_4076_);
lean_ctor_set(v_reuseFailAlloc_4108_, 1, v_n_4070_);
lean_ctor_set(v_reuseFailAlloc_4108_, 2, v_objs_x3f_4073_);
lean_ctor_set(v_reuseFailAlloc_4108_, 3, v_a_4078_);
lean_ctor_set_uint8(v_reuseFailAlloc_4108_, sizeof(void*)*4, v_check_4071_);
lean_ctor_set_uint8(v_reuseFailAlloc_4108_, sizeof(void*)*4 + 1, v_persistent_4072_);
v___x_4104_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
lean_object* v___x_4106_; 
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v___x_4104_);
v___x_4106_ = v___x_4080_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v___x_4104_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
else
{
size_t v___x_4114_; size_t v___x_4115_; uint8_t v___x_4116_; 
v___x_4114_ = lean_ptr_addr(v_k_4074_);
v___x_4115_ = lean_ptr_addr(v_a_4078_);
v___x_4116_ = lean_usize_dec_eq(v___x_4114_, v___x_4115_);
if (v___x_4116_ == 0)
{
lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4126_; 
lean_inc(v_objs_x3f_4073_);
lean_inc(v_n_4070_);
v_isSharedCheck_4126_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_4126_ == 0)
{
lean_object* v_unused_4127_; lean_object* v_unused_4128_; lean_object* v_unused_4129_; lean_object* v_unused_4130_; 
v_unused_4127_ = lean_ctor_get(v_code_3445_, 3);
lean_dec(v_unused_4127_);
v_unused_4128_ = lean_ctor_get(v_code_3445_, 2);
lean_dec(v_unused_4128_);
v_unused_4129_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_4129_);
v_unused_4130_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_4130_);
v___x_4118_ = v_code_3445_;
v_isShared_4119_ = v_isSharedCheck_4126_;
goto v_resetjp_4117_;
}
else
{
lean_dec(v_code_3445_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4126_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 3, v_a_4078_);
lean_ctor_set(v___x_4118_, 0, v_fvarId_4076_);
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_fvarId_4076_);
lean_ctor_set(v_reuseFailAlloc_4125_, 1, v_n_4070_);
lean_ctor_set(v_reuseFailAlloc_4125_, 2, v_objs_x3f_4073_);
lean_ctor_set(v_reuseFailAlloc_4125_, 3, v_a_4078_);
lean_ctor_set_uint8(v_reuseFailAlloc_4125_, sizeof(void*)*4, v_check_4071_);
lean_ctor_set_uint8(v_reuseFailAlloc_4125_, sizeof(void*)*4 + 1, v_persistent_4072_);
v___x_4121_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
lean_object* v___x_4123_; 
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v___x_4121_);
v___x_4123_ = v___x_4080_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v___x_4121_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
else
{
lean_object* v___x_4132_; 
lean_dec(v_a_4078_);
lean_dec(v_fvarId_4076_);
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v_code_3445_);
v___x_4132_ = v___x_4080_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_code_3445_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4076_);
lean_dec_ref_known(v_code_3445_, 4);
return v___x_4077_;
}
}
else
{
lean_object* v___x_4139_; 
lean_dec_ref_known(v_code_3445_, 4);
v___x_4139_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3443_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
return v___x_4139_;
}
}
default: 
{
lean_object* v_fvarId_4140_; lean_object* v_k_4141_; lean_object* v___x_4142_; 
v_fvarId_4140_ = lean_ctor_get(v_code_3445_, 0);
v_k_4141_ = lean_ctor_get(v_code_3445_, 1);
lean_inc(v_fvarId_4140_);
v___x_4142_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3446_, v_fvarId_4140_, v_t_3444_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_fvarId_4143_; lean_object* v___x_4144_; 
v_fvarId_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_fvarId_4143_);
lean_dec_ref_known(v___x_4142_, 1);
lean_inc_ref(v_k_4141_);
v___x_4144_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3443_, v_t_3444_, v_k_4141_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4172_; 
v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4147_ = v___x_4144_;
v_isShared_4148_ = v_isSharedCheck_4172_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4144_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4172_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
uint8_t v___y_4150_; size_t v___x_4166_; size_t v___x_4167_; uint8_t v___x_4168_; 
v___x_4166_ = lean_ptr_addr(v_fvarId_4140_);
v___x_4167_ = lean_ptr_addr(v_fvarId_4143_);
v___x_4168_ = lean_usize_dec_eq(v___x_4166_, v___x_4167_);
if (v___x_4168_ == 0)
{
v___y_4150_ = v___x_4168_;
goto v___jp_4149_;
}
else
{
size_t v___x_4169_; size_t v___x_4170_; uint8_t v___x_4171_; 
v___x_4169_ = lean_ptr_addr(v_k_4141_);
v___x_4170_ = lean_ptr_addr(v_a_4145_);
v___x_4171_ = lean_usize_dec_eq(v___x_4169_, v___x_4170_);
v___y_4150_ = v___x_4171_;
goto v___jp_4149_;
}
v___jp_4149_:
{
if (v___y_4150_ == 0)
{
lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4160_; 
v_isSharedCheck_4160_ = !lean_is_exclusive(v_code_3445_);
if (v_isSharedCheck_4160_ == 0)
{
lean_object* v_unused_4161_; lean_object* v_unused_4162_; 
v_unused_4161_ = lean_ctor_get(v_code_3445_, 1);
lean_dec(v_unused_4161_);
v_unused_4162_ = lean_ctor_get(v_code_3445_, 0);
lean_dec(v_unused_4162_);
v___x_4152_ = v_code_3445_;
v_isShared_4153_ = v_isSharedCheck_4160_;
goto v_resetjp_4151_;
}
else
{
lean_dec(v_code_3445_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4160_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 1, v_a_4145_);
lean_ctor_set(v___x_4152_, 0, v_fvarId_4143_);
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_fvarId_4143_);
lean_ctor_set(v_reuseFailAlloc_4159_, 1, v_a_4145_);
v___x_4155_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
lean_object* v___x_4157_; 
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 0, v___x_4155_);
v___x_4157_ = v___x_4147_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4155_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
else
{
lean_object* v___x_4164_; 
lean_dec(v_a_4145_);
lean_dec(v_fvarId_4143_);
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 0, v_code_3445_);
v___x_4164_ = v___x_4147_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_code_3445_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_4143_);
lean_dec_ref_known(v_code_3445_, 2);
return v___x_4144_;
}
}
else
{
lean_object* v___x_4173_; 
lean_dec_ref_known(v_code_3445_, 2);
v___x_4173_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3443_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
return v___x_4173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t v_pu_4174_, uint8_t v_t_4175_, lean_object* v_decl_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_){
_start:
{
lean_object* v_params_4183_; lean_object* v_type_4184_; lean_object* v_value_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v_params_4183_ = lean_ctor_get(v_decl_4176_, 2);
v_type_4184_ = lean_ctor_get(v_decl_4176_, 3);
v_value_4185_ = lean_ctor_get(v_decl_4176_, 4);
lean_inc_ref(v_type_4184_);
v___x_4186_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4174_, v_a_4177_, v_t_4175_, v_type_4184_);
lean_inc_ref(v_params_4183_);
v___x_4187_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4174_, v_t_4175_, v_params_4183_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_object* v_a_4188_; lean_object* v___x_4189_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc(v_a_4188_);
lean_dec_ref_known(v___x_4187_, 1);
lean_inc_ref(v_value_4185_);
v___x_4189_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4174_, v_t_4175_, v_value_4185_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; lean_object* v___x_4191_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref_known(v___x_4189_, 1);
v___x_4191_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_4174_, v_decl_4176_, v___x_4186_, v_a_4188_, v_a_4190_, v_a_4179_);
return v___x_4191_;
}
else
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4199_; 
lean_dec(v_a_4188_);
lean_dec_ref(v___x_4186_);
lean_dec_ref(v_decl_4176_);
v_a_4192_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4194_ = v___x_4189_;
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4189_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4197_; 
if (v_isShared_4195_ == 0)
{
v___x_4197_ = v___x_4194_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4192_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
else
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4207_; 
lean_dec_ref(v___x_4186_);
lean_dec_ref(v_decl_4176_);
v_a_4200_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4202_ = v___x_4187_;
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4187_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4205_; 
if (v_isShared_4203_ == 0)
{
v___x_4205_ = v___x_4202_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_a_4200_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp___boxed(lean_object* v_pu_4208_, lean_object* v_t_4209_, lean_object* v_decl_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_){
_start:
{
uint8_t v_pu_boxed_4217_; uint8_t v_t_boxed_4218_; lean_object* v_res_4219_; 
v_pu_boxed_4217_ = lean_unbox(v_pu_4208_);
v_t_boxed_4218_ = lean_unbox(v_t_4209_);
v_res_4219_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_boxed_4217_, v_t_boxed_4218_, v_decl_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_);
lean_dec(v_a_4215_);
lean_dec_ref(v_a_4214_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
lean_dec_ref(v_a_4211_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(lean_object* v_pu_4220_, lean_object* v_t_4221_, lean_object* v_i_4222_, lean_object* v_as_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
uint8_t v_pu_boxed_4230_; uint8_t v_t_boxed_4231_; lean_object* v_res_4232_; 
v_pu_boxed_4230_ = lean_unbox(v_pu_4220_);
v_t_boxed_4231_ = lean_unbox(v_t_4221_);
v_res_4232_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_boxed_4230_, v_t_boxed_4231_, v_i_4222_, v_as_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_);
lean_dec(v___y_4228_);
lean_dec_ref(v___y_4227_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
lean_dec_ref(v___y_4224_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp___boxed(lean_object* v_pu_4233_, lean_object* v_t_4234_, lean_object* v_code_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_){
_start:
{
uint8_t v_pu_boxed_4242_; uint8_t v_t_boxed_4243_; lean_object* v_res_4244_; 
v_pu_boxed_4242_ = lean_unbox(v_pu_4233_);
v_t_boxed_4243_ = lean_unbox(v_t_4234_);
v_res_4244_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_boxed_4242_, v_t_boxed_4243_, v_code_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_);
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
lean_dec(v_a_4238_);
lean_dec_ref(v_a_4237_);
lean_dec_ref(v_a_4236_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(uint8_t v_pu_4245_, uint8_t v_t_4246_, uint8_t v_pu_4247_, uint8_t v_t_4248_, lean_object* v_decl_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
lean_object* v___x_4256_; 
v___x_4256_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_4247_, v_t_4248_, v_decl_4249_, v___y_4250_, v___y_4252_);
return v___x_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(lean_object* v_pu_4257_, lean_object* v_t_4258_, lean_object* v_pu_4259_, lean_object* v_t_4260_, lean_object* v_decl_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
uint8_t v_pu_boxed_4268_; uint8_t v_t_boxed_4269_; uint8_t v_pu_boxed_4270_; uint8_t v_t_boxed_4271_; lean_object* v_res_4272_; 
v_pu_boxed_4268_ = lean_unbox(v_pu_4257_);
v_t_boxed_4269_ = lean_unbox(v_t_4258_);
v_pu_boxed_4270_ = lean_unbox(v_pu_4259_);
v_t_boxed_4271_ = lean_unbox(v_t_4260_);
v_res_4272_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(v_pu_boxed_4268_, v_t_boxed_4269_, v_pu_boxed_4270_, v_t_boxed_4271_, v_decl_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec_ref(v___y_4262_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(uint8_t v_pu_4273_, uint8_t v_t_4274_, uint8_t v_pu_4275_, uint8_t v_t_4276_, lean_object* v_args_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_){
_start:
{
lean_object* v___x_4284_; 
v___x_4284_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_4275_, v_t_4276_, v_args_4277_, v___y_4278_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(lean_object* v_pu_4285_, lean_object* v_t_4286_, lean_object* v_pu_4287_, lean_object* v_t_4288_, lean_object* v_args_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
uint8_t v_pu_boxed_4296_; uint8_t v_t_boxed_4297_; uint8_t v_pu_boxed_4298_; uint8_t v_t_boxed_4299_; lean_object* v_res_4300_; 
v_pu_boxed_4296_ = lean_unbox(v_pu_4285_);
v_t_boxed_4297_ = lean_unbox(v_t_4286_);
v_pu_boxed_4298_ = lean_unbox(v_pu_4287_);
v_t_boxed_4299_ = lean_unbox(v_t_4288_);
v_res_4300_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(v_pu_boxed_4296_, v_t_boxed_4297_, v_pu_boxed_4298_, v_t_boxed_4299_, v_args_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec_ref(v___y_4290_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(uint8_t v_pu_4301_, uint8_t v_t_4302_, uint8_t v_pu_4303_, uint8_t v_t_4304_, lean_object* v_ps_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v___x_4312_; 
v___x_4312_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4303_, v_t_4304_, v_ps_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
return v___x_4312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(lean_object* v_pu_4313_, lean_object* v_t_4314_, lean_object* v_pu_4315_, lean_object* v_t_4316_, lean_object* v_ps_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
uint8_t v_pu_boxed_4324_; uint8_t v_t_boxed_4325_; uint8_t v_pu_boxed_4326_; uint8_t v_t_boxed_4327_; lean_object* v_res_4328_; 
v_pu_boxed_4324_ = lean_unbox(v_pu_4313_);
v_t_boxed_4325_ = lean_unbox(v_t_4314_);
v_pu_boxed_4326_ = lean_unbox(v_pu_4315_);
v_t_boxed_4327_ = lean_unbox(v_t_4316_);
v_res_4328_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(v_pu_boxed_4324_, v_t_boxed_4325_, v_pu_boxed_4326_, v_t_boxed_4327_, v_ps_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
lean_dec_ref(v___y_4318_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(uint8_t v_pu_4329_, uint8_t v_t_4330_, lean_object* v_i_4331_, lean_object* v_as_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_){
_start:
{
lean_object* v___x_4339_; 
v___x_4339_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_4329_, v_t_4330_, v_i_4331_, v_as_4332_, v___y_4333_, v___y_4335_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(lean_object* v_pu_4340_, lean_object* v_t_4341_, lean_object* v_i_4342_, lean_object* v_as_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
uint8_t v_pu_boxed_4350_; uint8_t v_t_boxed_4351_; lean_object* v_res_4352_; 
v_pu_boxed_4350_ = lean_unbox(v_pu_4340_);
v_t_boxed_4351_ = lean_unbox(v_t_4341_);
v_res_4352_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_boxed_4350_, v_t_boxed_4351_, v_i_4342_, v_as_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec_ref(v___y_4344_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(uint8_t v_pu_4353_, uint8_t v_t_4354_, lean_object* v_decl_4355_, lean_object* v_inst_4356_, lean_object* v_____do__lift_4357_){
_start:
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4358_ = lean_box(v_pu_4353_);
v___x_4359_ = lean_box(v_t_4354_);
v___x_4360_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDeclImp___boxed), 9, 4);
lean_closure_set(v___x_4360_, 0, v___x_4358_);
lean_closure_set(v___x_4360_, 1, v___x_4359_);
lean_closure_set(v___x_4360_, 2, v_decl_4355_);
lean_closure_set(v___x_4360_, 3, v_____do__lift_4357_);
v___x_4361_ = lean_apply_2(v_inst_4356_, lean_box(0), v___x_4360_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(lean_object* v_pu_4362_, lean_object* v_t_4363_, lean_object* v_decl_4364_, lean_object* v_inst_4365_, lean_object* v_____do__lift_4366_){
_start:
{
uint8_t v_pu_boxed_4367_; uint8_t v_t_boxed_4368_; lean_object* v_res_4369_; 
v_pu_boxed_4367_ = lean_unbox(v_pu_4362_);
v_t_boxed_4368_ = lean_unbox(v_t_4363_);
v_res_4369_ = l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(v_pu_boxed_4367_, v_t_boxed_4368_, v_decl_4364_, v_inst_4365_, v_____do__lift_4366_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg(uint8_t v_pu_4370_, uint8_t v_t_4371_, lean_object* v_inst_4372_, lean_object* v_inst_4373_, lean_object* v_inst_4374_, lean_object* v_decl_4375_){
_start:
{
lean_object* v_toBind_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___f_4379_; lean_object* v___x_4380_; 
v_toBind_4376_ = lean_ctor_get(v_inst_4373_, 1);
lean_inc(v_toBind_4376_);
lean_dec_ref(v_inst_4373_);
v___x_4377_ = lean_box(v_pu_4370_);
v___x_4378_ = lean_box(v_t_4371_);
v___f_4379_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4379_, 0, v___x_4377_);
lean_closure_set(v___f_4379_, 1, v___x_4378_);
lean_closure_set(v___f_4379_, 2, v_decl_4375_);
lean_closure_set(v___f_4379_, 3, v_inst_4372_);
v___x_4380_ = lean_apply_4(v_toBind_4376_, lean_box(0), lean_box(0), v_inst_4374_, v___f_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(lean_object* v_pu_4381_, lean_object* v_t_4382_, lean_object* v_inst_4383_, lean_object* v_inst_4384_, lean_object* v_inst_4385_, lean_object* v_decl_4386_){
_start:
{
uint8_t v_pu_boxed_4387_; uint8_t v_t_boxed_4388_; lean_object* v_res_4389_; 
v_pu_boxed_4387_ = lean_unbox(v_pu_4381_);
v_t_boxed_4388_ = lean_unbox(v_t_4382_);
v_res_4389_ = l_Lean_Compiler_LCNF_normFunDecl___redArg(v_pu_boxed_4387_, v_t_boxed_4388_, v_inst_4383_, v_inst_4384_, v_inst_4385_, v_decl_4386_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl(lean_object* v_m_4390_, uint8_t v_pu_4391_, uint8_t v_t_4392_, lean_object* v_inst_4393_, lean_object* v_inst_4394_, lean_object* v_inst_4395_, lean_object* v_decl_4396_){
_start:
{
lean_object* v_toBind_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___f_4400_; lean_object* v___x_4401_; 
v_toBind_4397_ = lean_ctor_get(v_inst_4394_, 1);
lean_inc(v_toBind_4397_);
lean_dec_ref(v_inst_4394_);
v___x_4398_ = lean_box(v_pu_4391_);
v___x_4399_ = lean_box(v_t_4392_);
v___f_4400_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4400_, 0, v___x_4398_);
lean_closure_set(v___f_4400_, 1, v___x_4399_);
lean_closure_set(v___f_4400_, 2, v_decl_4396_);
lean_closure_set(v___f_4400_, 3, v_inst_4393_);
v___x_4401_ = lean_apply_4(v_toBind_4397_, lean_box(0), lean_box(0), v_inst_4395_, v___f_4400_);
return v___x_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___boxed(lean_object* v_m_4402_, lean_object* v_pu_4403_, lean_object* v_t_4404_, lean_object* v_inst_4405_, lean_object* v_inst_4406_, lean_object* v_inst_4407_, lean_object* v_decl_4408_){
_start:
{
uint8_t v_pu_boxed_4409_; uint8_t v_t_boxed_4410_; lean_object* v_res_4411_; 
v_pu_boxed_4409_ = lean_unbox(v_pu_4403_);
v_t_boxed_4410_ = lean_unbox(v_t_4404_);
v_res_4411_ = l_Lean_Compiler_LCNF_normFunDecl(v_m_4402_, v_pu_boxed_4409_, v_t_boxed_4410_, v_inst_4405_, v_inst_4406_, v_inst_4407_, v_decl_4408_);
return v_res_4411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0(uint8_t v_pu_4412_, uint8_t v_t_4413_, lean_object* v_code_4414_, lean_object* v_inst_4415_, lean_object* v_____do__lift_4416_){
_start:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4417_ = lean_box(v_pu_4412_);
v___x_4418_ = lean_box(v_t_4413_);
v___x_4419_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCodeImp___boxed), 9, 4);
lean_closure_set(v___x_4419_, 0, v___x_4417_);
lean_closure_set(v___x_4419_, 1, v___x_4418_);
lean_closure_set(v___x_4419_, 2, v_code_4414_);
lean_closure_set(v___x_4419_, 3, v_____do__lift_4416_);
v___x_4420_ = lean_apply_2(v_inst_4415_, lean_box(0), v___x_4419_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(lean_object* v_pu_4421_, lean_object* v_t_4422_, lean_object* v_code_4423_, lean_object* v_inst_4424_, lean_object* v_____do__lift_4425_){
_start:
{
uint8_t v_pu_boxed_4426_; uint8_t v_t_boxed_4427_; lean_object* v_res_4428_; 
v_pu_boxed_4426_ = lean_unbox(v_pu_4421_);
v_t_boxed_4427_ = lean_unbox(v_t_4422_);
v_res_4428_ = l_Lean_Compiler_LCNF_normCode___redArg___lam__0(v_pu_boxed_4426_, v_t_boxed_4427_, v_code_4423_, v_inst_4424_, v_____do__lift_4425_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg(uint8_t v_pu_4429_, uint8_t v_t_4430_, lean_object* v_inst_4431_, lean_object* v_inst_4432_, lean_object* v_inst_4433_, lean_object* v_code_4434_){
_start:
{
lean_object* v_toBind_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___f_4438_; lean_object* v___x_4439_; 
v_toBind_4435_ = lean_ctor_get(v_inst_4432_, 1);
lean_inc(v_toBind_4435_);
lean_dec_ref(v_inst_4432_);
v___x_4436_ = lean_box(v_pu_4429_);
v___x_4437_ = lean_box(v_t_4430_);
v___f_4438_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4438_, 0, v___x_4436_);
lean_closure_set(v___f_4438_, 1, v___x_4437_);
lean_closure_set(v___f_4438_, 2, v_code_4434_);
lean_closure_set(v___f_4438_, 3, v_inst_4431_);
v___x_4439_ = lean_apply_4(v_toBind_4435_, lean_box(0), lean_box(0), v_inst_4433_, v___f_4438_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___boxed(lean_object* v_pu_4440_, lean_object* v_t_4441_, lean_object* v_inst_4442_, lean_object* v_inst_4443_, lean_object* v_inst_4444_, lean_object* v_code_4445_){
_start:
{
uint8_t v_pu_boxed_4446_; uint8_t v_t_boxed_4447_; lean_object* v_res_4448_; 
v_pu_boxed_4446_ = lean_unbox(v_pu_4440_);
v_t_boxed_4447_ = lean_unbox(v_t_4441_);
v_res_4448_ = l_Lean_Compiler_LCNF_normCode___redArg(v_pu_boxed_4446_, v_t_boxed_4447_, v_inst_4442_, v_inst_4443_, v_inst_4444_, v_code_4445_);
return v_res_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode(lean_object* v_m_4449_, uint8_t v_pu_4450_, uint8_t v_t_4451_, lean_object* v_inst_4452_, lean_object* v_inst_4453_, lean_object* v_inst_4454_, lean_object* v_code_4455_){
_start:
{
lean_object* v_toBind_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___f_4459_; lean_object* v___x_4460_; 
v_toBind_4456_ = lean_ctor_get(v_inst_4453_, 1);
lean_inc(v_toBind_4456_);
lean_dec_ref(v_inst_4453_);
v___x_4457_ = lean_box(v_pu_4450_);
v___x_4458_ = lean_box(v_t_4451_);
v___f_4459_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4459_, 0, v___x_4457_);
lean_closure_set(v___f_4459_, 1, v___x_4458_);
lean_closure_set(v___f_4459_, 2, v_code_4455_);
lean_closure_set(v___f_4459_, 3, v_inst_4452_);
v___x_4460_ = lean_apply_4(v_toBind_4456_, lean_box(0), lean_box(0), v_inst_4454_, v___f_4459_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___boxed(lean_object* v_m_4461_, lean_object* v_pu_4462_, lean_object* v_t_4463_, lean_object* v_inst_4464_, lean_object* v_inst_4465_, lean_object* v_inst_4466_, lean_object* v_code_4467_){
_start:
{
uint8_t v_pu_boxed_4468_; uint8_t v_t_boxed_4469_; lean_object* v_res_4470_; 
v_pu_boxed_4468_ = lean_unbox(v_pu_4462_);
v_t_boxed_4469_ = lean_unbox(v_t_4463_);
v_res_4470_ = l_Lean_Compiler_LCNF_normCode(v_m_4461_, v_pu_boxed_4468_, v_t_boxed_4469_, v_inst_4464_, v_inst_4465_, v_inst_4466_, v_code_4467_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t v_pu_4471_, lean_object* v_e_4472_, lean_object* v_s_4473_, uint8_t v_translator_4474_){
_start:
{
lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4476_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4471_, v_s_4473_, v_translator_4474_, v_e_4472_);
v___x_4477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4476_);
return v___x_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(lean_object* v_pu_4478_, lean_object* v_e_4479_, lean_object* v_s_4480_, lean_object* v_translator_4481_, lean_object* v_a_4482_){
_start:
{
uint8_t v_pu_boxed_4483_; uint8_t v_translator_boxed_4484_; lean_object* v_res_4485_; 
v_pu_boxed_4483_ = lean_unbox(v_pu_4478_);
v_translator_boxed_4484_ = lean_unbox(v_translator_4481_);
v_res_4485_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_boxed_4483_, v_e_4479_, v_s_4480_, v_translator_boxed_4484_);
lean_dec_ref(v_s_4480_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(uint8_t v_pu_4486_, lean_object* v_e_4487_, lean_object* v_s_4488_, uint8_t v_translator_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_){
_start:
{
lean_object* v___x_4495_; 
v___x_4495_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_4486_, v_e_4487_, v_s_4488_, v_translator_4489_);
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___boxed(lean_object* v_pu_4496_, lean_object* v_e_4497_, lean_object* v_s_4498_, lean_object* v_translator_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_){
_start:
{
uint8_t v_pu_boxed_4505_; uint8_t v_translator_boxed_4506_; lean_object* v_res_4507_; 
v_pu_boxed_4505_ = lean_unbox(v_pu_4496_);
v_translator_boxed_4506_ = lean_unbox(v_translator_4499_);
v_res_4507_ = l_Lean_Compiler_LCNF_replaceExprFVars(v_pu_boxed_4505_, v_e_4497_, v_s_4498_, v_translator_boxed_4506_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_);
lean_dec(v_a_4503_);
lean_dec_ref(v_a_4502_);
lean_dec(v_a_4501_);
lean_dec_ref(v_a_4500_);
lean_dec_ref(v_s_4498_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t v_pu_4508_, lean_object* v_code_4509_, lean_object* v_s_4510_, uint8_t v_translator_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_){
_start:
{
lean_object* v___x_4517_; 
v___x_4517_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4508_, v_translator_4511_, v_code_4509_, v_s_4510_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_);
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars___boxed(lean_object* v_pu_4518_, lean_object* v_code_4519_, lean_object* v_s_4520_, lean_object* v_translator_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_){
_start:
{
uint8_t v_pu_boxed_4527_; uint8_t v_translator_boxed_4528_; lean_object* v_res_4529_; 
v_pu_boxed_4527_ = lean_unbox(v_pu_4518_);
v_translator_boxed_4528_ = lean_unbox(v_translator_4521_);
v_res_4529_ = l_Lean_Compiler_LCNF_replaceFVars(v_pu_boxed_4527_, v_code_4519_, v_s_4520_, v_translator_boxed_4528_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
lean_dec(v_a_4523_);
lean_dec_ref(v_a_4522_);
lean_dec_ref(v_s_4520_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object* v_a_4533_){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4535_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1));
v___x_4536_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4535_, v_a_4533_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(lean_object* v_a_4537_, lean_object* v_a_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4537_);
lean_dec(v_a_4537_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_){
_start:
{
lean_object* v___x_4545_; 
v___x_4545_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4541_);
return v___x_4545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___boxed(lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_);
lean_dec(v_a_4549_);
lean_dec_ref(v_a_4548_);
lean_dec(v_a_4547_);
lean_dec_ref(v_a_4546_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t v_pu_4552_, lean_object* v_type_4553_, uint8_t v_borrow_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_){
_start:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v_a_4562_; lean_object* v___x_4563_; 
v___x_4560_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_4561_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4560_, v_a_4556_);
v_a_4562_ = lean_ctor_get(v___x_4561_, 0);
lean_inc(v_a_4562_);
lean_dec_ref(v___x_4561_);
v___x_4563_ = l_Lean_Compiler_LCNF_mkParam(v_pu_4552_, v_a_4562_, v_type_4553_, v_borrow_4554_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_);
return v___x_4563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam___boxed(lean_object* v_pu_4564_, lean_object* v_type_4565_, lean_object* v_borrow_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_){
_start:
{
uint8_t v_pu_boxed_4572_; uint8_t v_borrow_boxed_4573_; lean_object* v_res_4574_; 
v_pu_boxed_4572_ = lean_unbox(v_pu_4564_);
v_borrow_boxed_4573_ = lean_unbox(v_borrow_4566_);
v_res_4574_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_boxed_4572_, v_type_4565_, v_borrow_boxed_4573_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_);
lean_dec(v_a_4570_);
lean_dec_ref(v_a_4569_);
lean_dec(v_a_4568_);
lean_dec_ref(v_a_4567_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object* v_a_4575_){
_start:
{
lean_object* v_config_4577_; lean_object* v___x_4578_; 
v_config_4577_ = lean_ctor_get(v_a_4575_, 0);
lean_inc_ref(v_config_4577_);
v___x_4578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4578_, 0, v_config_4577_);
return v___x_4578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg___boxed(lean_object* v_a_4579_, lean_object* v_a_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4579_);
lean_dec_ref(v_a_4579_);
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_){
_start:
{
lean_object* v___x_4587_; 
v___x_4587_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4582_);
return v___x_4587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___boxed(lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_){
_start:
{
lean_object* v_res_4593_; 
v_res_4593_ = l_Lean_Compiler_LCNF_getConfig(v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_);
lean_dec(v_a_4591_);
lean_dec_ref(v_a_4590_);
lean_dec(v_a_4589_);
lean_dec_ref(v_a_4588_);
return v_res_4593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object* v_x_4594_, lean_object* v_s_4595_, uint8_t v_phase_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_){
_start:
{
lean_object* v___x_4600_; lean_object* v_options_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; 
v___x_4600_ = lean_st_mk_ref(v_s_4595_);
v_options_4601_ = lean_ctor_get(v_a_4597_, 2);
v___x_4602_ = l_Lean_Compiler_LCNF_toConfigOptions(v_options_4601_);
v___x_4603_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
lean_ctor_set_uint8(v___x_4603_, sizeof(void*)*1, v_phase_4596_);
lean_inc(v_a_4598_);
lean_inc_ref(v_a_4597_);
lean_inc(v___x_4600_);
v___x_4604_ = lean_apply_5(v_x_4594_, v___x_4603_, v___x_4600_, v_a_4597_, v_a_4598_, lean_box(0));
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4613_; 
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4607_ = v___x_4604_;
v_isShared_4608_ = v_isSharedCheck_4613_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4604_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4613_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4609_; lean_object* v___x_4611_; 
v___x_4609_ = lean_st_ref_get(v___x_4600_);
lean_dec(v___x_4600_);
lean_dec(v___x_4609_);
if (v_isShared_4608_ == 0)
{
v___x_4611_ = v___x_4607_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_a_4605_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
else
{
lean_dec(v___x_4600_);
return v___x_4604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(lean_object* v_x_4614_, lean_object* v_s_4615_, lean_object* v_phase_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_){
_start:
{
uint8_t v_phase_boxed_4620_; lean_object* v_res_4621_; 
v_phase_boxed_4620_ = lean_unbox(v_phase_4616_);
v_res_4621_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4614_, v_s_4615_, v_phase_boxed_4620_, v_a_4617_, v_a_4618_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
return v_res_4621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run(lean_object* v_00_u03b1_4622_, lean_object* v_x_4623_, lean_object* v_s_4624_, uint8_t v_phase_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_){
_start:
{
lean_object* v___x_4629_; 
v___x_4629_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4623_, v_s_4624_, v_phase_4625_, v_a_4626_, v_a_4627_);
return v___x_4629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object* v_00_u03b1_4630_, lean_object* v_x_4631_, lean_object* v_s_4632_, lean_object* v_phase_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_){
_start:
{
uint8_t v_phase_boxed_4637_; lean_object* v_res_4638_; 
v_phase_boxed_4637_ = lean_unbox(v_phase_4633_);
v_res_4638_ = l_Lean_Compiler_LCNF_CompilerM_run(v_00_u03b1_4630_, v_x_4631_, v_s_4632_, v_phase_boxed_4637_, v_a_4634_, v_a_4635_);
lean_dec(v_a_4635_);
lean_dec_ref(v_a_4634_);
return v_res_4638_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0(void){
_start:
{
lean_object* v___x_4639_; 
v___x_4639_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object* v_00_u03b1_4640_, lean_object* v_00_u03b2_4641_, lean_object* v_inst_4642_, lean_object* v_inst_4643_){
_start:
{
lean_object* v___x_4644_; 
v___x_4644_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object* v_00_u03b1_4645_, lean_object* v_00_u03b2_4646_, lean_object* v_inst_4647_, lean_object* v_inst_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(v_00_u03b1_4645_, v_00_u03b2_4646_, v_inst_4647_, v_inst_4648_);
lean_dec_ref(v_inst_4648_);
lean_dec_ref(v_inst_4647_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension(lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_){
_start:
{
lean_object* v___x_4654_; 
v___x_4654_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0);
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_){
_start:
{
lean_object* v_res_4659_; 
v_res_4659_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension(v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_);
lean_dec_ref(v_a_4658_);
lean_dec_ref(v_a_4657_);
return v_res_4659_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; 
v___x_4663_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2));
v___x_4664_ = lean_unsigned_to_nat(14u);
v___x_4665_ = lean_unsigned_to_nat(178u);
v___x_4666_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1));
v___x_4667_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0));
v___x_4668_ = l_mkPanicMessageWithDecl(v___x_4667_, v___x_4666_, v___x_4665_, v___x_4664_, v___x_4663_);
return v___x_4668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(lean_object* v_inst_4669_, lean_object* v_inst_4670_, lean_object* v_snd_4671_, lean_object* v_inst_4672_, lean_object* v_s_4673_, lean_object* v_e_4674_){
_start:
{
lean_object* v_fst_4675_; lean_object* v_snd_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4691_; 
v_fst_4675_ = lean_ctor_get(v_s_4673_, 0);
v_snd_4676_ = lean_ctor_get(v_s_4673_, 1);
v_isSharedCheck_4691_ = !lean_is_exclusive(v_s_4673_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4678_ = v_s_4673_;
v_isShared_4679_ = v_isSharedCheck_4691_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_snd_4676_);
lean_inc(v_fst_4675_);
lean_dec(v_s_4673_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4691_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4680_; lean_object* v___y_4682_; lean_object* v___x_4687_; 
lean_inc_n(v_e_4674_, 2);
v___x_4680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4680_, 0, v_e_4674_);
lean_ctor_set(v___x_4680_, 1, v_fst_4675_);
lean_inc_ref(v_inst_4670_);
lean_inc_ref(v_inst_4669_);
v___x_4687_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4669_, v_inst_4670_, v_snd_4671_, v_e_4674_);
if (lean_obj_tag(v___x_4687_) == 0)
{
lean_object* v___x_4688_; lean_object* v___x_4689_; 
v___x_4688_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3);
v___x_4689_ = l_panic___redArg(v_inst_4672_, v___x_4688_);
v___y_4682_ = v___x_4689_;
goto v___jp_4681_;
}
else
{
lean_object* v_val_4690_; 
v_val_4690_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_val_4690_);
lean_dec_ref_known(v___x_4687_, 1);
v___y_4682_ = v_val_4690_;
goto v___jp_4681_;
}
v___jp_4681_:
{
lean_object* v___x_4683_; lean_object* v___x_4685_; 
v___x_4683_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4669_, v_inst_4670_, v_snd_4676_, v_e_4674_, v___y_4682_);
if (v_isShared_4679_ == 0)
{
lean_ctor_set(v___x_4678_, 1, v___x_4683_);
lean_ctor_set(v___x_4678_, 0, v___x_4680_);
v___x_4685_ = v___x_4678_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v___x_4680_);
lean_ctor_set(v_reuseFailAlloc_4686_, 1, v___x_4683_);
v___x_4685_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
return v___x_4685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed(lean_object* v_inst_4692_, lean_object* v_inst_4693_, lean_object* v_snd_4694_, lean_object* v_inst_4695_, lean_object* v_s_4696_, lean_object* v_e_4697_){
_start:
{
lean_object* v_res_4698_; 
v_res_4698_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(v_inst_4692_, v_inst_4693_, v_snd_4694_, v_inst_4695_, v_s_4696_, v_e_4697_);
lean_dec(v_inst_4695_);
lean_dec(v_snd_4694_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object* v_inst_4701_, lean_object* v_inst_4702_, lean_object* v_inst_4703_, lean_object* v_oldState_4704_, lean_object* v_newState_4705_, lean_object* v_x_4706_, lean_object* v_s_4707_){
_start:
{
lean_object* v_fst_4708_; lean_object* v_snd_4709_; lean_object* v_fst_4710_; lean_object* v___f_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v_newEntries_4716_; lean_object* v___x_4717_; 
v_fst_4708_ = lean_ctor_get(v_newState_4705_, 0);
lean_inc_n(v_fst_4708_, 2);
v_snd_4709_ = lean_ctor_get(v_newState_4705_, 1);
lean_inc(v_snd_4709_);
lean_dec_ref(v_newState_4705_);
v_fst_4710_ = lean_ctor_get(v_oldState_4704_, 0);
v___f_4711_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_4711_, 0, v_inst_4701_);
lean_closure_set(v___f_4711_, 1, v_inst_4702_);
lean_closure_set(v___f_4711_, 2, v_snd_4709_);
lean_closure_set(v___f_4711_, 3, v_inst_4703_);
v___x_4712_ = l_List_lengthTR___redArg(v_fst_4708_);
v___x_4713_ = l_List_lengthTR___redArg(v_fst_4710_);
v___x_4714_ = lean_nat_sub(v___x_4712_, v___x_4713_);
lean_dec(v___x_4713_);
lean_dec(v___x_4712_);
v___x_4715_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0));
v_newEntries_4716_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fst_4708_, v_fst_4708_, v___x_4714_, v___x_4715_);
lean_dec(v_fst_4708_);
v___x_4717_ = l_List_foldl___redArg(v___f_4711_, v_s_4707_, v_newEntries_4716_);
return v___x_4717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object* v_inst_4718_, lean_object* v_inst_4719_, lean_object* v_inst_4720_, lean_object* v_oldState_4721_, lean_object* v_newState_4722_, lean_object* v_x_4723_, lean_object* v_s_4724_){
_start:
{
lean_object* v_res_4725_; 
v_res_4725_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(v_inst_4718_, v_inst_4719_, v_inst_4720_, v_oldState_4721_, v_newState_4722_, v_x_4723_, v_s_4724_);
lean_dec(v_x_4723_);
lean_dec_ref(v_oldState_4721_);
return v_res_4725_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0(void){
_start:
{
lean_object* v___x_4726_; 
v___x_4726_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4726_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1(void){
_start:
{
lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4727_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0);
v___x_4728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4728_, 0, v___x_4727_);
return v___x_4728_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2(void){
_start:
{
lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; 
v___x_4729_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1);
v___x_4730_ = lean_box(0);
v___x_4731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4731_, 0, v___x_4730_);
lean_ctor_set(v___x_4731_, 1, v___x_4729_);
return v___x_4731_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3(void){
_start:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4732_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2);
v___x_4733_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_4733_, 0, lean_box(0));
lean_closure_set(v___x_4733_, 1, lean_box(0));
lean_closure_set(v___x_4733_, 2, v___x_4732_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object* v_inst_4734_, lean_object* v_inst_4735_, lean_object* v_inst_4736_){
_start:
{
lean_object* v___f_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; 
v___f_4738_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4738_, 0, v_inst_4734_);
lean_closure_set(v___f_4738_, 1, v_inst_4735_);
lean_closure_set(v___f_4738_, 2, v_inst_4736_);
v___x_4739_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3);
v___x_4740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4740_, 0, v___f_4738_);
v___x_4741_ = lean_box(0);
v___x_4742_ = l_Lean_registerEnvExtension___redArg(v___x_4739_, v___x_4740_, v___x_4741_);
if (lean_obj_tag(v___x_4742_) == 0)
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4750_; 
v_a_4743_ = lean_ctor_get(v___x_4742_, 0);
v_isSharedCheck_4750_ = !lean_is_exclusive(v___x_4742_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4745_ = v___x_4742_;
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_a_4743_);
lean_dec(v___x_4742_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v___x_4748_; 
if (v_isShared_4746_ == 0)
{
v___x_4748_ = v___x_4745_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_a_4743_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
else
{
lean_object* v_a_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4758_; 
v_a_4751_ = lean_ctor_get(v___x_4742_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4742_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4753_ = v___x_4742_;
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_a_4751_);
lean_dec(v___x_4742_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v___x_4756_; 
if (v_isShared_4754_ == 0)
{
v___x_4756_ = v___x_4753_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_a_4751_);
v___x_4756_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
return v___x_4756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object* v_inst_4759_, lean_object* v_inst_4760_, lean_object* v_inst_4761_, lean_object* v_a_4762_){
_start:
{
lean_object* v_res_4763_; 
v_res_4763_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4759_, v_inst_4760_, v_inst_4761_);
return v_res_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object* v_00_u03b1_4764_, lean_object* v_00_u03b2_4765_, lean_object* v_inst_4766_, lean_object* v_inst_4767_, lean_object* v_inst_4768_){
_start:
{
lean_object* v___x_4770_; 
v___x_4770_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4766_, v_inst_4767_, v_inst_4768_);
return v___x_4770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object* v_00_u03b1_4771_, lean_object* v_00_u03b2_4772_, lean_object* v_inst_4773_, lean_object* v_inst_4774_, lean_object* v_inst_4775_, lean_object* v_a_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l_Lean_Compiler_LCNF_CacheExtension_register(v_00_u03b1_4771_, v_00_u03b2_4772_, v_inst_4773_, v_inst_4774_, v_inst_4775_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object* v_a_4778_, lean_object* v_inst_4779_, lean_object* v_inst_4780_, lean_object* v_b_4781_, lean_object* v_x_4782_){
_start:
{
lean_object* v_fst_4783_; lean_object* v_snd_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4793_; 
v_fst_4783_ = lean_ctor_get(v_x_4782_, 0);
v_snd_4784_ = lean_ctor_get(v_x_4782_, 1);
v_isSharedCheck_4793_ = !lean_is_exclusive(v_x_4782_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4786_ = v_x_4782_;
v_isShared_4787_ = v_isSharedCheck_4793_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_snd_4784_);
lean_inc(v_fst_4783_);
lean_dec(v_x_4782_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4793_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4791_; 
lean_inc(v_a_4778_);
v___x_4788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4788_, 0, v_a_4778_);
lean_ctor_set(v___x_4788_, 1, v_fst_4783_);
v___x_4789_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4779_, v_inst_4780_, v_snd_4784_, v_a_4778_, v_b_4781_);
if (v_isShared_4787_ == 0)
{
lean_ctor_set(v___x_4786_, 1, v___x_4789_);
lean_ctor_set(v___x_4786_, 0, v___x_4788_);
v___x_4791_ = v___x_4786_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4788_);
lean_ctor_set(v_reuseFailAlloc_4792_, 1, v___x_4789_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_4794_; 
v___x_4794_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4794_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_4795_; lean_object* v___x_4796_; 
v___x_4795_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0);
v___x_4796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4796_, 0, v___x_4795_);
return v___x_4796_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2(void){
_start:
{
lean_object* v___x_4797_; lean_object* v___x_4798_; 
v___x_4797_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1);
v___x_4798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4798_, 0, v___x_4797_);
lean_ctor_set(v___x_4798_, 1, v___x_4797_);
return v___x_4798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object* v_inst_4799_, lean_object* v_inst_4800_, lean_object* v_ext_4801_, lean_object* v_a_4802_, lean_object* v_b_4803_, lean_object* v_a_4804_){
_start:
{
lean_object* v___x_4806_; lean_object* v_env_4807_; lean_object* v_nextMacroScope_4808_; lean_object* v_ngen_4809_; lean_object* v_auxDeclNGen_4810_; lean_object* v_traceState_4811_; lean_object* v_messages_4812_; lean_object* v_infoState_4813_; lean_object* v_snapshotTasks_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4829_; 
v___x_4806_ = lean_st_ref_take(v_a_4804_);
v_env_4807_ = lean_ctor_get(v___x_4806_, 0);
v_nextMacroScope_4808_ = lean_ctor_get(v___x_4806_, 1);
v_ngen_4809_ = lean_ctor_get(v___x_4806_, 2);
v_auxDeclNGen_4810_ = lean_ctor_get(v___x_4806_, 3);
v_traceState_4811_ = lean_ctor_get(v___x_4806_, 4);
v_messages_4812_ = lean_ctor_get(v___x_4806_, 6);
v_infoState_4813_ = lean_ctor_get(v___x_4806_, 7);
v_snapshotTasks_4814_ = lean_ctor_get(v___x_4806_, 8);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4829_ == 0)
{
lean_object* v_unused_4830_; 
v_unused_4830_ = lean_ctor_get(v___x_4806_, 5);
lean_dec(v_unused_4830_);
v___x_4816_ = v___x_4806_;
v_isShared_4817_ = v_isSharedCheck_4829_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_snapshotTasks_4814_);
lean_inc(v_infoState_4813_);
lean_inc(v_messages_4812_);
lean_inc(v_traceState_4811_);
lean_inc(v_auxDeclNGen_4810_);
lean_inc(v_ngen_4809_);
lean_inc(v_nextMacroScope_4808_);
lean_inc(v_env_4807_);
lean_dec(v___x_4806_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4829_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v_asyncMode_4818_; lean_object* v___f_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4824_; 
v_asyncMode_4818_ = lean_ctor_get(v_ext_4801_, 2);
lean_inc(v_asyncMode_4818_);
v___f_4819_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4819_, 0, v_a_4802_);
lean_closure_set(v___f_4819_, 1, v_inst_4799_);
lean_closure_set(v___f_4819_, 2, v_inst_4800_);
lean_closure_set(v___f_4819_, 3, v_b_4803_);
v___x_4820_ = lean_box(0);
v___x_4821_ = l_Lean_EnvExtension_modifyState___redArg(v_ext_4801_, v_env_4807_, v___f_4819_, v_asyncMode_4818_, v___x_4820_);
lean_dec(v_asyncMode_4818_);
v___x_4822_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2);
if (v_isShared_4817_ == 0)
{
lean_ctor_set(v___x_4816_, 5, v___x_4822_);
lean_ctor_set(v___x_4816_, 0, v___x_4821_);
v___x_4824_ = v___x_4816_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v___x_4821_);
lean_ctor_set(v_reuseFailAlloc_4828_, 1, v_nextMacroScope_4808_);
lean_ctor_set(v_reuseFailAlloc_4828_, 2, v_ngen_4809_);
lean_ctor_set(v_reuseFailAlloc_4828_, 3, v_auxDeclNGen_4810_);
lean_ctor_set(v_reuseFailAlloc_4828_, 4, v_traceState_4811_);
lean_ctor_set(v_reuseFailAlloc_4828_, 5, v___x_4822_);
lean_ctor_set(v_reuseFailAlloc_4828_, 6, v_messages_4812_);
lean_ctor_set(v_reuseFailAlloc_4828_, 7, v_infoState_4813_);
lean_ctor_set(v_reuseFailAlloc_4828_, 8, v_snapshotTasks_4814_);
v___x_4824_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4825_ = lean_st_ref_set(v_a_4804_, v___x_4824_);
v___x_4826_ = lean_box(0);
v___x_4827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4827_, 0, v___x_4826_);
return v___x_4827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object* v_inst_4831_, lean_object* v_inst_4832_, lean_object* v_ext_4833_, lean_object* v_a_4834_, lean_object* v_b_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_){
_start:
{
lean_object* v_res_4838_; 
v_res_4838_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4831_, v_inst_4832_, v_ext_4833_, v_a_4834_, v_b_4835_, v_a_4836_);
lean_dec(v_a_4836_);
return v_res_4838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object* v_00_u03b1_4839_, lean_object* v_00_u03b2_4840_, lean_object* v_inst_4841_, lean_object* v_inst_4842_, lean_object* v_inst_4843_, lean_object* v_ext_4844_, lean_object* v_a_4845_, lean_object* v_b_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_){
_start:
{
lean_object* v___x_4850_; 
v___x_4850_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4841_, v_inst_4842_, v_ext_4844_, v_a_4845_, v_b_4846_, v_a_4848_);
return v___x_4850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object* v_00_u03b1_4851_, lean_object* v_00_u03b2_4852_, lean_object* v_inst_4853_, lean_object* v_inst_4854_, lean_object* v_inst_4855_, lean_object* v_ext_4856_, lean_object* v_a_4857_, lean_object* v_b_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_){
_start:
{
lean_object* v_res_4862_; 
v_res_4862_ = l_Lean_Compiler_LCNF_CacheExtension_insert(v_00_u03b1_4851_, v_00_u03b2_4852_, v_inst_4853_, v_inst_4854_, v_inst_4855_, v_ext_4856_, v_a_4857_, v_b_4858_, v_a_4859_, v_a_4860_);
lean_dec(v_a_4860_);
lean_dec_ref(v_a_4859_);
lean_dec(v_inst_4855_);
return v_res_4862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object* v_inst_4863_, lean_object* v_inst_4864_, lean_object* v_ext_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_){
_start:
{
lean_object* v___x_4869_; lean_object* v_env_4870_; lean_object* v_asyncMode_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v_snd_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4869_ = lean_st_ref_get(v_a_4867_);
v_env_4870_ = lean_ctor_get(v___x_4869_, 0);
lean_inc_ref(v_env_4870_);
lean_dec(v___x_4869_);
v_asyncMode_4871_ = lean_ctor_get(v_ext_4865_, 2);
v___x_4872_ = lean_box(0);
v___x_4873_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v_inst_4863_, v_inst_4864_);
v___x_4874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4872_);
lean_ctor_set(v___x_4874_, 1, v___x_4873_);
v___x_4875_ = lean_box(0);
v___x_4876_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4874_, v_ext_4865_, v_env_4870_, v_asyncMode_4871_, v___x_4875_);
lean_dec_ref_known(v___x_4874_, 2);
v_snd_4877_ = lean_ctor_get(v___x_4876_, 1);
lean_inc(v_snd_4877_);
lean_dec(v___x_4876_);
v___x_4878_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4863_, v_inst_4864_, v_snd_4877_, v_a_4866_);
lean_dec(v_snd_4877_);
v___x_4879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4878_);
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object* v_inst_4880_, lean_object* v_inst_4881_, lean_object* v_ext_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_){
_start:
{
lean_object* v_res_4886_; 
v_res_4886_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4880_, v_inst_4881_, v_ext_4882_, v_a_4883_, v_a_4884_);
lean_dec(v_a_4884_);
lean_dec_ref(v_ext_4882_);
return v_res_4886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object* v_00_u03b1_4887_, lean_object* v_00_u03b2_4888_, lean_object* v_inst_4889_, lean_object* v_inst_4890_, lean_object* v_inst_4891_, lean_object* v_ext_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_){
_start:
{
lean_object* v___x_4897_; 
v___x_4897_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_4889_, v_inst_4890_, v_ext_4892_, v_a_4893_, v_a_4895_);
return v___x_4897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object* v_00_u03b1_4898_, lean_object* v_00_u03b2_4899_, lean_object* v_inst_4900_, lean_object* v_inst_4901_, lean_object* v_inst_4902_, lean_object* v_ext_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_){
_start:
{
lean_object* v_res_4908_; 
v_res_4908_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(v_00_u03b1_4898_, v_00_u03b2_4899_, v_inst_4900_, v_inst_4901_, v_inst_4902_, v_ext_4903_, v_a_4904_, v_a_4905_, v_a_4906_);
lean_dec(v_a_4906_);
lean_dec_ref(v_a_4905_);
lean_dec_ref(v_ext_4903_);
lean_dec(v_inst_4902_);
return v_res_4908_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_LCtx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ConfigOptions(uint8_t builtin);
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
