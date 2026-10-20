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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited___redArg();
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toConfigOptions(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_takeNewEntries___redArg(lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParam(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default___redArg();
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(uint8_t, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseCode(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParams(uint8_t, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0;
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
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2;
static const lean_string_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "CacheExtension"};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__6_value;
static const lean_string_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "register"};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(114, 63, 216, 176, 94, 170, 18, 246)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value_aux_3),((lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(147, 186, 41, 27, 108, 56, 19, 46)}};
static const lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Compiler_LCNF_Phase_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Compiler_LCNF_Phase_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg(lean_object* v_base_22_){
_start:
{
lean_inc(v_base_22_);
return v_base_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg___boxed(lean_object* v_base_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Compiler_LCNF_Phase_base_elim___redArg(v_base_23_);
lean_dec(v_base_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_base_28_){
_start:
{
lean_inc(v_base_28_);
return v_base_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_base_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Compiler_LCNF_Phase_base_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_base_32_);
lean_dec(v_base_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(lean_object* v_mono_35_){
_start:
{
lean_inc(v_mono_35_);
return v_mono_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg___boxed(lean_object* v_mono_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(v_mono_36_);
lean_dec(v_mono_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_mono_41_){
_start:
{
lean_inc(v_mono_41_);
return v_mono_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_mono_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Compiler_LCNF_Phase_mono_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_mono_45_);
lean_dec(v_mono_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(lean_object* v_impure_48_){
_start:
{
lean_inc(v_impure_48_);
return v_impure_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg___boxed(lean_object* v_impure_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(v_impure_49_);
lean_dec(v_impure_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_impure_54_){
_start:
{
lean_inc(v_impure_54_);
return v_impure_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_impure_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Compiler_LCNF_Phase_impure_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_impure_58_);
lean_dec(v_impure_58_);
return v_res_60_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_instInhabitedPhase_default(void){
_start:
{
uint8_t v___x_61_; 
v___x_61_ = 0;
return v___x_61_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_instInhabitedPhase(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Phase_ofNat(lean_object* v_n_63_){
_start:
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = lean_nat_dec_le(v_n_63_, v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_66_ = lean_unsigned_to_nat(1u);
v___x_67_ = lean_nat_dec_le(v_n_63_, v___x_66_);
if (v___x_67_ == 0)
{
uint8_t v___x_68_; 
v___x_68_ = 2;
return v___x_68_;
}
else
{
uint8_t v___x_69_; 
v___x_69_ = 1;
return v___x_69_;
}
}
else
{
uint8_t v___x_70_; 
v___x_70_ = 0;
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ofNat___boxed(lean_object* v_n_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Lean_Compiler_LCNF_Phase_ofNat(v_n_71_);
lean_dec(v_n_71_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableEqPhase(uint8_t v_x_74_, uint8_t v_y_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_76_ = lean_box(v_x_74_);
v___x_77_ = lean_obj_tag_nat(v___x_76_);
lean_dec(v___x_76_);
v___x_78_ = lean_box(v_y_75_);
v___x_79_ = lean_obj_tag_nat(v___x_78_);
lean_dec(v___x_78_);
v___x_80_ = lean_nat_dec_eq(v___x_77_, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableEqPhase___boxed(lean_object* v_x_81_, lean_object* v_y_82_){
_start:
{
uint8_t v_x_23__boxed_83_; uint8_t v_y_24__boxed_84_; uint8_t v_res_85_; lean_object* v_r_86_; 
v_x_23__boxed_83_ = lean_unbox(v_x_81_);
v_y_24__boxed_84_ = lean_unbox(v_y_82_);
v_res_85_ = l_Lean_Compiler_LCNF_instDecidableEqPhase(v_x_23__boxed_83_, v_y_24__boxed_84_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t v_x_87_){
_start:
{
if (v_x_87_ == 2)
{
uint8_t v___x_88_; 
v___x_88_ = 1;
return v___x_88_;
}
else
{
uint8_t v___x_89_; 
v___x_89_ = 0;
return v___x_89_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toPurity___boxed(lean_object* v_x_90_){
_start:
{
uint8_t v_x_23__boxed_91_; uint8_t v_res_92_; lean_object* v_r_93_; 
v_x_23__boxed_91_ = lean_unbox(v_x_90_);
v_res_92_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_x_23__boxed_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_box(0);
v___x_95_ = lean_unsigned_to_nat(16u);
v___x_96_ = lean_mk_array(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1);
v___x_101_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
lean_ctor_set(v___x_101_, 2, v___x_100_);
lean_ctor_set(v___x_101_, 3, v___x_100_);
lean_ctor_set(v___x_101_, 4, v___x_100_);
lean_ctor_set(v___x_101_, 5, v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v___x_102_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default(void){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState(void){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default;
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0(void){
_start:
{
lean_object* v___x_107_; uint8_t v___x_108_; lean_object* v___x_109_; 
v___x_107_ = l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default;
v___x_108_ = 0;
v___x_109_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_109_, 0, v___x_107_);
lean_ctor_set_uint8(v___x_109_, sizeof(void*)*1, v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default;
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(lean_object* v_00_u03b1_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___y_113_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object* v_00_u03b1_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(v_00_u03b1_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object* v_00_u03b1_128_, lean_object* v_00_u03b2_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___x_137_; 
lean_inc(v___y_135_);
lean_inc_ref(v___y_134_);
lean_inc(v___y_133_);
lean_inc_ref(v___y_132_);
v___x_137_ = lean_apply_5(v___y_130_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, lean_box(0));
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_139_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_138_);
lean_dec_ref_known(v___x_137_, 1);
lean_inc(v___y_135_);
lean_inc_ref(v___y_134_);
lean_inc(v___y_133_);
lean_inc_ref(v___y_132_);
v___x_139_ = lean_apply_6(v___y_131_, v_a_138_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, lean_box(0));
return v___x_139_;
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
lean_dec_ref(v___y_131_);
v_a_140_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_137_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_137_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object* v_00_u03b1_148_, lean_object* v_00_u03b2_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(v_00_u03b1_148_, v_00_u03b2_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
return v_res_157_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_instMonadEIO___redArg();
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0);
v___x_160_ = l_StateRefT_x27_instMonad___redArg(v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM(void){
_start:
{
lean_object* v___x_165_; lean_object* v_toApplicative_166_; lean_object* v_toFunctor_167_; lean_object* v_toSeq_168_; lean_object* v_toSeqLeft_169_; lean_object* v_toSeqRight_170_; lean_object* v___f_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___f_176_; lean_object* v___f_177_; lean_object* v___f_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v_toApplicative_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_209_; 
v___x_165_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_166_ = lean_ctor_get(v___x_165_, 0);
v_toFunctor_167_ = lean_ctor_get(v_toApplicative_166_, 0);
v_toSeq_168_ = lean_ctor_get(v_toApplicative_166_, 2);
v_toSeqLeft_169_ = lean_ctor_get(v_toApplicative_166_, 3);
v_toSeqRight_170_ = lean_ctor_get(v_toApplicative_166_, 4);
v___f_171_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_172_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_167_, 2);
v___f_173_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_173_, 0, v_toFunctor_167_);
v___f_174_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_174_, 0, v_toFunctor_167_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v___f_173_);
lean_ctor_set(v___x_175_, 1, v___f_174_);
lean_inc(v_toSeqRight_170_);
v___f_176_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_176_, 0, v_toSeqRight_170_);
lean_inc(v_toSeqLeft_169_);
v___f_177_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_177_, 0, v_toSeqLeft_169_);
lean_inc(v_toSeq_168_);
v___f_178_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_178_, 0, v_toSeq_168_);
v___x_179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_179_, 0, v___x_175_);
lean_ctor_set(v___x_179_, 1, v___f_171_);
lean_ctor_set(v___x_179_, 2, v___f_178_);
lean_ctor_set(v___x_179_, 3, v___f_177_);
lean_ctor_set(v___x_179_, 4, v___f_176_);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___f_172_);
v___x_181_ = l_StateRefT_x27_instMonad___redArg(v___x_180_);
v_toApplicative_182_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; 
v_unused_210_ = lean_ctor_get(v___x_181_, 1);
lean_dec(v_unused_210_);
v___x_184_ = v___x_181_;
v_isShared_185_ = v_isSharedCheck_209_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_toApplicative_182_);
lean_dec(v___x_181_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_209_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v_toFunctor_186_; lean_object* v_toSeq_187_; lean_object* v_toSeqLeft_188_; lean_object* v_toSeqRight_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_207_; 
v_toFunctor_186_ = lean_ctor_get(v_toApplicative_182_, 0);
v_toSeq_187_ = lean_ctor_get(v_toApplicative_182_, 2);
v_toSeqLeft_188_ = lean_ctor_get(v_toApplicative_182_, 3);
v_toSeqRight_189_ = lean_ctor_get(v_toApplicative_182_, 4);
v_isSharedCheck_207_ = !lean_is_exclusive(v_toApplicative_182_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v_toApplicative_182_, 1);
lean_dec(v_unused_208_);
v___x_191_ = v_toApplicative_182_;
v_isShared_192_ = v_isSharedCheck_207_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_toSeqRight_189_);
lean_inc(v_toSeqLeft_188_);
lean_inc(v_toSeq_187_);
lean_inc(v_toFunctor_186_);
lean_dec(v_toApplicative_182_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_207_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___x_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___x_202_; 
v___f_193_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_194_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_186_);
v___f_195_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_195_, 0, v_toFunctor_186_);
v___f_196_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_196_, 0, v_toFunctor_186_);
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v___f_195_);
lean_ctor_set(v___x_197_, 1, v___f_196_);
v___f_198_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_198_, 0, v_toSeqRight_189_);
v___f_199_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_199_, 0, v_toSeqLeft_188_);
v___f_200_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_200_, 0, v_toSeq_187_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 4, v___f_198_);
lean_ctor_set(v___x_191_, 3, v___f_199_);
lean_ctor_set(v___x_191_, 2, v___f_200_);
lean_ctor_set(v___x_191_, 1, v___f_193_);
lean_ctor_set(v___x_191_, 0, v___x_197_);
v___x_202_ = v___x_191_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v___f_193_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v___f_200_);
lean_ctor_set(v_reuseFailAlloc_206_, 3, v___f_199_);
lean_ctor_set(v_reuseFailAlloc_206_, 4, v___f_198_);
v___x_202_ = v_reuseFailAlloc_206_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_204_; 
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v___f_194_);
lean_ctor_set(v___x_184_, 0, v___x_202_);
v___x_204_ = v___x_184_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___f_194_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg(uint8_t v_phase_211_, lean_object* v_x_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_config_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_config_218_ = lean_ctor_get(v_a_213_, 0);
lean_inc_ref(v_config_218_);
v___x_219_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_219_, 0, v_config_218_);
lean_ctor_set_uint8(v___x_219_, sizeof(void*)*1, v_phase_211_);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
lean_inc(v_a_214_);
v___x_220_ = lean_apply_5(v_x_212_, v___x_219_, v_a_214_, v_a_215_, v_a_216_, lean_box(0));
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg___boxed(lean_object* v_phase_221_, lean_object* v_x_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
uint8_t v_phase_boxed_228_; lean_object* v_res_229_; 
v_phase_boxed_228_ = lean_unbox(v_phase_221_);
v_res_229_ = l_Lean_Compiler_LCNF_withPhase___redArg(v_phase_boxed_228_, v_x_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase(lean_object* v_00_u03b1_230_, uint8_t v_phase_231_, lean_object* v_x_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_config_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_config_238_ = lean_ctor_get(v_a_233_, 0);
lean_inc_ref(v_config_238_);
v___x_239_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_239_, 0, v_config_238_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*1, v_phase_231_);
lean_inc(v_a_236_);
lean_inc_ref(v_a_235_);
lean_inc(v_a_234_);
v___x_240_ = lean_apply_5(v_x_232_, v___x_239_, v_a_234_, v_a_235_, v_a_236_, lean_box(0));
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___boxed(lean_object* v_00_u03b1_241_, lean_object* v_phase_242_, lean_object* v_x_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
uint8_t v_phase_boxed_249_; lean_object* v_res_250_; 
v_phase_boxed_249_ = lean_unbox(v_phase_242_);
v_res_250_ = l_Lean_Compiler_LCNF_withPhase(v_00_u03b1_241_, v_phase_boxed_249_, v_x_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object* v_a_251_){
_start:
{
uint8_t v_phase_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v_phase_253_ = lean_ctor_get_uint8(v_a_251_, sizeof(void*)*1);
v___x_254_ = lean_box(v_phase_253_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg___boxed(lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_256_);
lean_dec_ref(v_a_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase(lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_259_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___boxed(lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Compiler_LCNF_getPhase(v_a_265_, v_a_266_, v_a_267_, v_a_268_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object* v_a_271_){
_start:
{
lean_object* v___x_273_; lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_284_; 
v___x_273_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_271_);
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_284_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_284_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_284_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
uint8_t v___x_278_; uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_278_ = lean_unbox(v_a_274_);
lean_dec(v_a_274_);
v___x_279_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_278_);
v___x_280_ = lean_box(v___x_279_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_280_);
v___x_282_ = v___x_276_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg___boxed(lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_285_);
lean_dec_ref(v_a_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity(lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_288_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___boxed(lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Compiler_LCNF_getPurity(v_a_294_, v_a_295_, v_a_296_, v_a_297_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg(lean_object* v_a_300_){
_start:
{
lean_object* v___x_302_; lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_318_; 
v___x_302_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_300_);
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_318_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_318_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_318_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
uint8_t v___x_307_; 
v___x_307_ = lean_unbox(v_a_303_);
lean_dec(v_a_303_);
if (v___x_307_ == 0)
{
uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_308_ = 1;
v___x_309_ = lean_box(v___x_308_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_309_);
v___x_311_ = v___x_305_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
else
{
uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_313_ = 0;
v___x_314_ = lean_box(v___x_313_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_314_);
v___x_316_ = v___x_305_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg___boxed(lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_319_);
lean_dec_ref(v_a_319_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase(lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_322_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___boxed(lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Compiler_LCNF_inBasePhase(v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
return v_res_333_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0(void){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_334_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_337_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_338_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
lean_ctor_set(v___x_340_, 2, v___x_339_);
lean_ctor_set(v___x_340_, 3, v___x_339_);
lean_ctor_set(v___x_340_, 4, v___x_338_);
lean_ctor_set(v___x_340_, 5, v___x_338_);
lean_ctor_set(v___x_340_, 6, v___x_338_);
lean_ctor_set(v___x_340_, 7, v___x_338_);
lean_ctor_set(v___x_340_, 8, v___x_338_);
lean_ctor_set(v___x_340_, 9, v___x_338_);
lean_ctor_set(v___x_340_, 10, v___x_338_);
lean_ctor_set(v___x_340_, 11, v___x_337_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(lean_object* v_msgData_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v___x_347_; lean_object* v_env_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_347_ = lean_st_ref_get(v___y_345_);
v_env_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc_ref(v_env_348_);
lean_dec(v___x_347_);
v___x_349_ = lean_st_ref_get(v___y_343_);
v___x_350_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_342_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_372_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_372_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_372_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_372_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v_lctx_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_370_; 
v_lctx_355_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v___x_349_, 1);
lean_dec(v_unused_371_);
v___x_357_ = v___x_349_;
v_isShared_358_ = v_isSharedCheck_370_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_lctx_355_);
lean_dec(v___x_349_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_370_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_359_ = lean_unbox(v_a_351_);
lean_dec(v_a_351_);
v___x_360_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_355_, v___x_359_);
lean_dec_ref(v_lctx_355_);
v___x_361_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_344_);
v___x_362_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
v___x_363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_363_, 0, v_env_348_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
lean_ctor_set(v___x_363_, 2, v___x_360_);
lean_ctor_set(v___x_363_, 3, v___x_361_);
if (v_isShared_358_ == 0)
{
lean_ctor_set_tag(v___x_357_, 3);
lean_ctor_set(v___x_357_, 1, v_msgData_341_);
lean_ctor_set(v___x_357_, 0, v___x_363_);
v___x_365_ = v___x_357_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_msgData_341_);
v___x_365_ = v_reuseFailAlloc_369_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_367_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_365_);
v___x_367_ = v___x_353_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec(v___x_349_);
lean_dec_ref(v_env_348_);
lean_dec_ref(v_msgData_341_);
v_a_373_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_350_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_350_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed(lean_object* v_msgData_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(v_msgData_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(lean_object* v_msg_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_ref_396_; lean_object* v___x_397_; lean_object* v_env_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_ref_396_ = lean_ctor_get(v___y_393_, 2);
v___x_397_ = lean_st_ref_get(v___y_394_);
v_env_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc_ref(v_env_398_);
lean_dec(v___x_397_);
v___x_399_ = lean_st_ref_get(v___y_392_);
v___x_400_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_391_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_423_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_423_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_423_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_423_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_lctx_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_421_; 
v_lctx_405_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v___x_399_, 1);
lean_dec(v_unused_422_);
v___x_407_ = v___x_399_;
v_isShared_408_ = v_isSharedCheck_421_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_lctx_405_);
lean_dec(v___x_399_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_421_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
uint8_t v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_409_ = lean_unbox(v_a_401_);
lean_dec(v_a_401_);
v___x_410_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_405_, v___x_409_);
lean_dec_ref(v_lctx_405_);
v___x_411_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_393_);
v___x_412_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
v___x_413_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_413_, 0, v_env_398_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
lean_ctor_set(v___x_413_, 2, v___x_410_);
lean_ctor_set(v___x_413_, 3, v___x_411_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 3);
lean_ctor_set(v___x_407_, 1, v_msg_390_);
lean_ctor_set(v___x_407_, 0, v___x_413_);
v___x_415_ = v___x_407_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_msg_390_);
v___x_415_ = v_reuseFailAlloc_420_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
lean_inc(v_ref_396_);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v_ref_396_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 1);
lean_ctor_set(v___x_403_, 0, v___x_416_);
v___x_418_ = v___x_403_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec(v___x_399_);
lean_dec_ref(v_env_398_);
lean_dec_ref(v_msg_390_);
v_a_424_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_400_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_400_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg___boxed(lean_object* v_msg_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(lean_object* v_00_u03b1_439_, lean_object* v_msg_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___boxed(lean_object* v_00_u03b1_447_, lean_object* v_msg_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(v_00_u03b1_447_, v_msg_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(lean_object* v_a_455_, lean_object* v_x_456_){
_start:
{
if (lean_obj_tag(v_x_456_) == 0)
{
lean_object* v___x_457_; 
v___x_457_ = lean_box(0);
return v___x_457_;
}
else
{
lean_object* v_key_458_; lean_object* v_value_459_; lean_object* v_tail_460_; uint8_t v___x_461_; 
v_key_458_ = lean_ctor_get(v_x_456_, 0);
v_value_459_ = lean_ctor_get(v_x_456_, 1);
v_tail_460_ = lean_ctor_get(v_x_456_, 2);
v___x_461_ = l_Lean_instBEqFVarId_beq(v_key_458_, v_a_455_);
if (v___x_461_ == 0)
{
v_x_456_ = v_tail_460_;
goto _start;
}
else
{
lean_object* v___x_463_; 
lean_inc(v_value_459_);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v_value_459_);
return v___x_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg___boxed(lean_object* v_a_464_, lean_object* v_x_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_464_, v_x_465_);
lean_dec(v_x_465_);
lean_dec(v_a_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object* v_m_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_buckets_469_; lean_object* v___x_470_; uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v___x_473_; uint64_t v_fold_474_; uint64_t v___x_475_; uint64_t v___x_476_; uint64_t v___x_477_; size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_buckets_469_ = lean_ctor_get(v_m_467_, 1);
v___x_470_ = lean_array_get_size(v_buckets_469_);
v___x_471_ = l_Lean_instHashableFVarId_hash(v_a_468_);
v___x_472_ = 32ULL;
v___x_473_ = lean_uint64_shift_right(v___x_471_, v___x_472_);
v_fold_474_ = lean_uint64_xor(v___x_471_, v___x_473_);
v___x_475_ = 16ULL;
v___x_476_ = lean_uint64_shift_right(v_fold_474_, v___x_475_);
v___x_477_ = lean_uint64_xor(v_fold_474_, v___x_476_);
v___x_478_ = lean_uint64_to_usize(v___x_477_);
v___x_479_ = lean_usize_of_nat(v___x_470_);
v___x_480_ = ((size_t)1ULL);
v___x_481_ = lean_usize_sub(v___x_479_, v___x_480_);
v___x_482_ = lean_usize_land(v___x_478_, v___x_481_);
v___x_483_ = lean_array_uget_borrowed(v_buckets_469_, v___x_482_);
v___x_484_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_468_, v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg___boxed(lean_object* v_m_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_485_, v_a_486_);
lean_dec(v_a_486_);
lean_dec_ref(v_m_485_);
return v_res_487_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getType___closed__1(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = ((lean_object*)(l_Lean_Compiler_LCNF_getType___closed__0));
v___x_490_ = l_Lean_stringToMessageData(v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType(lean_object* v_fvarId_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___x_497_; lean_object* v_lctx_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_563_; 
v___x_497_ = lean_st_ref_get(v_a_493_);
v_lctx_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v___x_497_, 1);
lean_dec(v_unused_564_);
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_563_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_lctx_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_563_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_492_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_554_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_554_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_554_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_554_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___y_508_; lean_object* v___y_522_; lean_object* v___y_537_; uint8_t v___x_551_; 
v___x_551_ = lean_unbox(v_a_503_);
if (v___x_551_ == 0)
{
lean_object* v_letDeclsPure_552_; 
v_letDeclsPure_552_ = lean_ctor_get(v_lctx_498_, 2);
lean_inc_ref(v_letDeclsPure_552_);
v___y_537_ = v_letDeclsPure_552_;
goto v___jp_536_;
}
else
{
lean_object* v_letDeclsImpure_553_; 
v_letDeclsImpure_553_ = lean_ctor_get(v_lctx_498_, 3);
lean_inc_ref(v_letDeclsImpure_553_);
v___y_537_ = v_letDeclsImpure_553_;
goto v___jp_536_;
}
v___jp_507_:
{
lean_object* v___x_509_; 
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_508_, v_fvarId_491_);
lean_dec_ref(v___y_508_);
if (lean_obj_tag(v___x_509_) == 1)
{
lean_object* v_val_510_; lean_object* v_type_511_; lean_object* v___x_513_; 
lean_del_object(v___x_500_);
lean_dec(v_fvarId_491_);
v_val_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_val_510_);
lean_dec_ref_known(v___x_509_, 1);
v_type_511_ = lean_ctor_get(v_val_510_, 3);
lean_inc_ref(v_type_511_);
lean_dec(v_val_510_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v_type_511_);
v___x_513_ = v___x_505_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_type_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
lean_dec(v___x_509_);
lean_del_object(v___x_505_);
v___x_515_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_516_ = l_Lean_MessageData_ofName(v_fvarId_491_);
if (v_isShared_501_ == 0)
{
lean_ctor_set_tag(v___x_500_, 7);
lean_ctor_set(v___x_500_, 1, v___x_516_);
lean_ctor_set(v___x_500_, 0, v___x_515_);
v___x_518_ = v___x_500_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v___x_516_);
v___x_518_ = v_reuseFailAlloc_520_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_518_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
return v___x_519_;
}
}
}
v___jp_521_:
{
lean_object* v___x_523_; 
v___x_523_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_522_, v_fvarId_491_);
lean_dec_ref(v___y_522_);
if (lean_obj_tag(v___x_523_) == 1)
{
lean_object* v_val_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_532_; 
lean_del_object(v___x_505_);
lean_dec(v_a_503_);
lean_del_object(v___x_500_);
lean_dec_ref(v_lctx_498_);
lean_dec(v_fvarId_491_);
v_val_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_532_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_val_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v_type_528_; lean_object* v___x_530_; 
v_type_528_ = lean_ctor_get(v_val_524_, 2);
lean_inc_ref(v_type_528_);
lean_dec(v_val_524_);
if (v_isShared_527_ == 0)
{
lean_ctor_set_tag(v___x_526_, 0);
lean_ctor_set(v___x_526_, 0, v_type_528_);
v___x_530_ = v___x_526_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_type_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
else
{
uint8_t v___x_533_; 
lean_dec(v___x_523_);
v___x_533_ = lean_unbox(v_a_503_);
lean_dec(v_a_503_);
if (v___x_533_ == 0)
{
lean_object* v_funDeclsPure_534_; 
v_funDeclsPure_534_ = lean_ctor_get(v_lctx_498_, 4);
lean_inc_ref(v_funDeclsPure_534_);
lean_dec_ref(v_lctx_498_);
v___y_508_ = v_funDeclsPure_534_;
goto v___jp_507_;
}
else
{
lean_object* v_funDeclsImpure_535_; 
v_funDeclsImpure_535_ = lean_ctor_get(v_lctx_498_, 5);
lean_inc_ref(v_funDeclsImpure_535_);
lean_dec_ref(v_lctx_498_);
v___y_508_ = v_funDeclsImpure_535_;
goto v___jp_507_;
}
}
}
v___jp_536_:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_537_, v_fvarId_491_);
lean_dec_ref(v___y_537_);
if (lean_obj_tag(v___x_538_) == 1)
{
lean_object* v_val_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_547_; 
lean_del_object(v___x_505_);
lean_dec(v_a_503_);
lean_del_object(v___x_500_);
lean_dec_ref(v_lctx_498_);
lean_dec(v_fvarId_491_);
v_val_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_547_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_val_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_type_543_; lean_object* v___x_545_; 
v_type_543_ = lean_ctor_get(v_val_539_, 2);
lean_inc_ref(v_type_543_);
lean_dec(v_val_539_);
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 0);
lean_ctor_set(v___x_541_, 0, v_type_543_);
v___x_545_ = v___x_541_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_type_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
else
{
uint8_t v___x_548_; 
lean_dec(v___x_538_);
v___x_548_ = lean_unbox(v_a_503_);
if (v___x_548_ == 0)
{
lean_object* v_paramsPure_549_; 
v_paramsPure_549_ = lean_ctor_get(v_lctx_498_, 0);
lean_inc_ref(v_paramsPure_549_);
v___y_522_ = v_paramsPure_549_;
goto v___jp_521_;
}
else
{
lean_object* v_paramsImpure_550_; 
v_paramsImpure_550_ = lean_ctor_get(v_lctx_498_, 1);
lean_inc_ref(v_paramsImpure_550_);
v___y_522_ = v_paramsImpure_550_;
goto v___jp_521_;
}
}
}
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_del_object(v___x_500_);
lean_dec_ref(v_lctx_498_);
lean_dec(v_fvarId_491_);
v_a_555_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_502_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_502_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType___boxed(lean_object* v_fvarId_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Compiler_LCNF_getType(v_fvarId_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(lean_object* v_00_u03b2_572_, lean_object* v_m_573_, lean_object* v_a_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_573_, v_a_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(lean_object* v_00_u03b2_576_, lean_object* v_m_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(v_00_u03b2_576_, v_m_577_, v_a_578_);
lean_dec(v_a_578_);
lean_dec_ref(v_m_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(lean_object* v_00_u03b2_580_, lean_object* v_a_581_, lean_object* v_x_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_581_, v_x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_584_, lean_object* v_a_585_, lean_object* v_x_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(v_00_u03b2_584_, v_a_585_, v_x_586_);
lean_dec(v_x_586_);
lean_dec(v_a_585_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object* v_fvarId_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___x_594_; lean_object* v_lctx_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_660_; 
v___x_594_ = lean_st_ref_get(v_a_590_);
v_lctx_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v___x_594_, 1);
lean_dec(v_unused_661_);
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_660_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_lctx_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_660_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_589_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_651_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_651_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_651_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_651_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___y_605_; lean_object* v___y_619_; lean_object* v___y_634_; uint8_t v___x_648_; 
v___x_648_ = lean_unbox(v_a_600_);
if (v___x_648_ == 0)
{
lean_object* v_letDeclsPure_649_; 
v_letDeclsPure_649_ = lean_ctor_get(v_lctx_595_, 2);
lean_inc_ref(v_letDeclsPure_649_);
v___y_634_ = v_letDeclsPure_649_;
goto v___jp_633_;
}
else
{
lean_object* v_letDeclsImpure_650_; 
v_letDeclsImpure_650_ = lean_ctor_get(v_lctx_595_, 3);
lean_inc_ref(v_letDeclsImpure_650_);
v___y_634_ = v_letDeclsImpure_650_;
goto v___jp_633_;
}
v___jp_604_:
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_605_, v_fvarId_588_);
lean_dec_ref(v___y_605_);
if (lean_obj_tag(v___x_606_) == 1)
{
lean_object* v_val_607_; lean_object* v_binderName_608_; lean_object* v___x_610_; 
lean_del_object(v___x_597_);
lean_dec(v_fvarId_588_);
v_val_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_val_607_);
lean_dec_ref_known(v___x_606_, 1);
v_binderName_608_ = lean_ctor_get(v_val_607_, 1);
lean_inc(v_binderName_608_);
lean_dec(v_val_607_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v_binderName_608_);
v___x_610_ = v___x_602_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_binderName_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
lean_dec(v___x_606_);
lean_del_object(v___x_602_);
v___x_612_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_613_ = l_Lean_MessageData_ofName(v_fvarId_588_);
if (v_isShared_598_ == 0)
{
lean_ctor_set_tag(v___x_597_, 7);
lean_ctor_set(v___x_597_, 1, v___x_613_);
lean_ctor_set(v___x_597_, 0, v___x_612_);
v___x_615_ = v___x_597_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___x_613_);
v___x_615_ = v_reuseFailAlloc_617_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_615_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
return v___x_616_;
}
}
}
v___jp_618_:
{
lean_object* v___x_620_; 
v___x_620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_619_, v_fvarId_588_);
lean_dec_ref(v___y_619_);
if (lean_obj_tag(v___x_620_) == 1)
{
lean_object* v_val_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_629_; 
lean_del_object(v___x_602_);
lean_dec(v_a_600_);
lean_del_object(v___x_597_);
lean_dec_ref(v_lctx_595_);
lean_dec(v_fvarId_588_);
v_val_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_629_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_val_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v_binderName_625_; lean_object* v___x_627_; 
v_binderName_625_ = lean_ctor_get(v_val_621_, 1);
lean_inc(v_binderName_625_);
lean_dec(v_val_621_);
if (v_isShared_624_ == 0)
{
lean_ctor_set_tag(v___x_623_, 0);
lean_ctor_set(v___x_623_, 0, v_binderName_625_);
v___x_627_ = v___x_623_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_binderName_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
else
{
uint8_t v___x_630_; 
lean_dec(v___x_620_);
v___x_630_ = lean_unbox(v_a_600_);
lean_dec(v_a_600_);
if (v___x_630_ == 0)
{
lean_object* v_funDeclsPure_631_; 
v_funDeclsPure_631_ = lean_ctor_get(v_lctx_595_, 4);
lean_inc_ref(v_funDeclsPure_631_);
lean_dec_ref(v_lctx_595_);
v___y_605_ = v_funDeclsPure_631_;
goto v___jp_604_;
}
else
{
lean_object* v_funDeclsImpure_632_; 
v_funDeclsImpure_632_ = lean_ctor_get(v_lctx_595_, 5);
lean_inc_ref(v_funDeclsImpure_632_);
lean_dec_ref(v_lctx_595_);
v___y_605_ = v_funDeclsImpure_632_;
goto v___jp_604_;
}
}
}
v___jp_633_:
{
lean_object* v___x_635_; 
v___x_635_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_634_, v_fvarId_588_);
lean_dec_ref(v___y_634_);
if (lean_obj_tag(v___x_635_) == 1)
{
lean_object* v_val_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_644_; 
lean_del_object(v___x_602_);
lean_dec(v_a_600_);
lean_del_object(v___x_597_);
lean_dec_ref(v_lctx_595_);
lean_dec(v_fvarId_588_);
v_val_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_644_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_644_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_val_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_644_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v_binderName_640_; lean_object* v___x_642_; 
v_binderName_640_ = lean_ctor_get(v_val_636_, 1);
lean_inc(v_binderName_640_);
lean_dec(v_val_636_);
if (v_isShared_639_ == 0)
{
lean_ctor_set_tag(v___x_638_, 0);
lean_ctor_set(v___x_638_, 0, v_binderName_640_);
v___x_642_ = v___x_638_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_binderName_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
else
{
uint8_t v___x_645_; 
lean_dec(v___x_635_);
v___x_645_ = lean_unbox(v_a_600_);
if (v___x_645_ == 0)
{
lean_object* v_paramsPure_646_; 
v_paramsPure_646_ = lean_ctor_get(v_lctx_595_, 0);
lean_inc_ref(v_paramsPure_646_);
v___y_619_ = v_paramsPure_646_;
goto v___jp_618_;
}
else
{
lean_object* v_paramsImpure_647_; 
v_paramsImpure_647_ = lean_ctor_get(v_lctx_595_, 1);
lean_inc_ref(v_paramsImpure_647_);
v___y_619_ = v_paramsImpure_647_;
goto v___jp_618_;
}
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_del_object(v___x_597_);
lean_dec_ref(v_lctx_595_);
lean_dec(v_fvarId_588_);
v_a_652_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_599_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_599_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName___boxed(lean_object* v_fvarId_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t v_pu_669_, lean_object* v_fvarId_670_, lean_object* v_a_671_){
_start:
{
lean_object* v___x_673_; lean_object* v___y_675_; 
v___x_673_ = lean_st_ref_get(v_a_671_);
if (v_pu_669_ == 0)
{
lean_object* v_lctx_678_; lean_object* v_paramsPure_679_; 
v_lctx_678_ = lean_ctor_get(v___x_673_, 0);
lean_inc_ref(v_lctx_678_);
lean_dec(v___x_673_);
v_paramsPure_679_ = lean_ctor_get(v_lctx_678_, 0);
lean_inc_ref(v_paramsPure_679_);
lean_dec_ref(v_lctx_678_);
v___y_675_ = v_paramsPure_679_;
goto v___jp_674_;
}
else
{
lean_object* v_lctx_680_; lean_object* v_paramsImpure_681_; 
v_lctx_680_ = lean_ctor_get(v___x_673_, 0);
lean_inc_ref(v_lctx_680_);
lean_dec(v___x_673_);
v_paramsImpure_681_ = lean_ctor_get(v_lctx_680_, 1);
lean_inc_ref(v_paramsImpure_681_);
lean_dec_ref(v_lctx_680_);
v___y_675_ = v_paramsImpure_681_;
goto v___jp_674_;
}
v___jp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_675_, v_fvarId_670_);
lean_dec_ref(v___y_675_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(lean_object* v_pu_682_, lean_object* v_fvarId_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
uint8_t v_pu_boxed_686_; lean_object* v_res_687_; 
v_pu_boxed_686_ = lean_unbox(v_pu_682_);
v_res_687_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_boxed_686_, v_fvarId_683_, v_a_684_);
lean_dec(v_a_684_);
lean_dec(v_fvarId_683_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f(uint8_t v_pu_688_, lean_object* v_fvarId_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_688_, v_fvarId_689_, v_a_691_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___boxed(lean_object* v_pu_696_, lean_object* v_fvarId_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
uint8_t v_pu_boxed_703_; lean_object* v_res_704_; 
v_pu_boxed_703_ = lean_unbox(v_pu_696_);
v_res_704_ = l_Lean_Compiler_LCNF_findParam_x3f(v_pu_boxed_703_, v_fvarId_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_fvarId_697_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t v_pu_705_, lean_object* v_fvarId_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___x_709_; lean_object* v___y_711_; 
v___x_709_ = lean_st_ref_get(v_a_707_);
if (v_pu_705_ == 0)
{
lean_object* v_lctx_714_; lean_object* v_letDeclsPure_715_; 
v_lctx_714_ = lean_ctor_get(v___x_709_, 0);
lean_inc_ref(v_lctx_714_);
lean_dec(v___x_709_);
v_letDeclsPure_715_ = lean_ctor_get(v_lctx_714_, 2);
lean_inc_ref(v_letDeclsPure_715_);
lean_dec_ref(v_lctx_714_);
v___y_711_ = v_letDeclsPure_715_;
goto v___jp_710_;
}
else
{
lean_object* v_lctx_716_; lean_object* v_letDeclsImpure_717_; 
v_lctx_716_ = lean_ctor_get(v___x_709_, 0);
lean_inc_ref(v_lctx_716_);
lean_dec(v___x_709_);
v_letDeclsImpure_717_ = lean_ctor_get(v_lctx_716_, 3);
lean_inc_ref(v_letDeclsImpure_717_);
lean_dec_ref(v_lctx_716_);
v___y_711_ = v_letDeclsImpure_717_;
goto v___jp_710_;
}
v___jp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_711_, v_fvarId_706_);
lean_dec_ref(v___y_711_);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(lean_object* v_pu_718_, lean_object* v_fvarId_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
uint8_t v_pu_boxed_722_; lean_object* v_res_723_; 
v_pu_boxed_722_ = lean_unbox(v_pu_718_);
v_res_723_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_boxed_722_, v_fvarId_719_, v_a_720_);
lean_dec(v_a_720_);
lean_dec(v_fvarId_719_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(uint8_t v_pu_724_, lean_object* v_fvarId_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_724_, v_fvarId_725_, v_a_727_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(lean_object* v_pu_732_, lean_object* v_fvarId_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
uint8_t v_pu_boxed_739_; lean_object* v_res_740_; 
v_pu_boxed_739_ = lean_unbox(v_pu_732_);
v_res_740_ = l_Lean_Compiler_LCNF_findLetDecl_x3f(v_pu_boxed_739_, v_fvarId_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_fvarId_733_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t v_pu_741_, lean_object* v_fvarId_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___x_745_; lean_object* v___y_747_; 
v___x_745_ = lean_st_ref_get(v_a_743_);
if (v_pu_741_ == 0)
{
lean_object* v_lctx_750_; lean_object* v_funDeclsPure_751_; 
v_lctx_750_ = lean_ctor_get(v___x_745_, 0);
lean_inc_ref(v_lctx_750_);
lean_dec(v___x_745_);
v_funDeclsPure_751_ = lean_ctor_get(v_lctx_750_, 4);
lean_inc_ref(v_funDeclsPure_751_);
lean_dec_ref(v_lctx_750_);
v___y_747_ = v_funDeclsPure_751_;
goto v___jp_746_;
}
else
{
lean_object* v_lctx_752_; lean_object* v_funDeclsImpure_753_; 
v_lctx_752_ = lean_ctor_get(v___x_745_, 0);
lean_inc_ref(v_lctx_752_);
lean_dec(v___x_745_);
v_funDeclsImpure_753_ = lean_ctor_get(v_lctx_752_, 5);
lean_inc_ref(v_funDeclsImpure_753_);
lean_dec_ref(v_lctx_752_);
v___y_747_ = v_funDeclsImpure_753_;
goto v___jp_746_;
}
v___jp_746_:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_747_, v_fvarId_742_);
lean_dec_ref(v___y_747_);
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(lean_object* v_pu_754_, lean_object* v_fvarId_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
uint8_t v_pu_boxed_758_; lean_object* v_res_759_; 
v_pu_boxed_758_ = lean_unbox(v_pu_754_);
v_res_759_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_boxed_758_, v_fvarId_755_, v_a_756_);
lean_dec(v_a_756_);
lean_dec(v_fvarId_755_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(uint8_t v_pu_760_, lean_object* v_fvarId_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_760_, v_fvarId_761_, v_a_763_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(lean_object* v_pu_768_, lean_object* v_fvarId_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
uint8_t v_pu_boxed_775_; lean_object* v_res_776_; 
v_pu_boxed_775_ = lean_unbox(v_pu_768_);
v_res_776_ = l_Lean_Compiler_LCNF_findFunDecl_x3f(v_pu_boxed_775_, v_fvarId_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_fvarId_769_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t v_pu_777_, lean_object* v_fvarId_778_, lean_object* v_a_779_){
_start:
{
lean_object* v___x_781_; lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_802_; 
v___x_781_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_777_, v_fvarId_778_, v_a_779_);
v_a_782_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_802_ == 0)
{
v___x_784_ = v___x_781_;
v_isShared_785_ = v_isSharedCheck_802_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_802_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
if (lean_obj_tag(v_a_782_) == 1)
{
lean_object* v_val_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_797_; 
v_val_786_ = lean_ctor_get(v_a_782_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v_a_782_);
if (v_isSharedCheck_797_ == 0)
{
v___x_788_ = v_a_782_;
v_isShared_789_ = v_isSharedCheck_797_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_val_786_);
lean_dec(v_a_782_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_797_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v_value_790_; lean_object* v___x_792_; 
v_value_790_ = lean_ctor_get(v_val_786_, 3);
lean_inc(v_value_790_);
lean_dec(v_val_786_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v_value_790_);
v___x_792_ = v___x_788_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_value_790_);
v___x_792_ = v_reuseFailAlloc_796_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_794_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_792_);
v___x_794_ = v___x_784_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
else
{
lean_object* v___x_798_; lean_object* v___x_800_; 
lean_dec(v_a_782_);
v___x_798_ = lean_box(0);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_798_);
v___x_800_ = v___x_784_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg___boxed(lean_object* v_pu_803_, lean_object* v_fvarId_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
uint8_t v_pu_boxed_807_; lean_object* v_res_808_; 
v_pu_boxed_807_ = lean_unbox(v_pu_803_);
v_res_808_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_boxed_807_, v_fvarId_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec(v_fvarId_804_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f(uint8_t v_pu_809_, lean_object* v_fvarId_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_809_, v_fvarId_810_, v_a_812_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(lean_object* v_pu_817_, lean_object* v_fvarId_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
uint8_t v_pu_boxed_824_; lean_object* v_res_825_; 
v_pu_boxed_824_ = lean_unbox(v_pu_817_);
v_res_825_ = l_Lean_Compiler_LCNF_findLetValue_x3f(v_pu_boxed_824_, v_fvarId_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_fvarId_818_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg(lean_object* v_fvarId_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
uint8_t v___x_834_; lean_object* v___x_835_; 
v___x_834_ = 0;
v___x_835_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_834_, v_fvarId_826_, v_a_827_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_863_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_863_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_863_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_863_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
if (lean_obj_tag(v_a_836_) == 1)
{
lean_object* v_val_840_; 
v_val_840_ = lean_ctor_get(v_a_836_, 0);
lean_inc(v_val_840_);
lean_dec_ref_known(v_a_836_, 1);
if (lean_obj_tag(v_val_840_) == 3)
{
lean_object* v_declName_841_; lean_object* v___x_842_; lean_object* v_env_849_; uint8_t v___x_850_; lean_object* v___x_851_; 
v_declName_841_ = lean_ctor_get(v_val_840_, 0);
lean_inc(v_declName_841_);
lean_dec_ref_known(v_val_840_, 3);
v___x_842_ = lean_st_ref_get(v_a_828_);
v_env_849_ = lean_ctor_get(v___x_842_, 0);
lean_inc_ref(v_env_849_);
lean_dec(v___x_842_);
v___x_850_ = 0;
v___x_851_ = l_Lean_Environment_find_x3f(v_env_849_, v_declName_841_, v___x_850_);
if (lean_obj_tag(v___x_851_) == 1)
{
lean_object* v_val_852_; 
v_val_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_val_852_);
lean_dec_ref_known(v___x_851_, 1);
if (lean_obj_tag(v_val_852_) == 6)
{
lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_861_; 
lean_del_object(v___x_838_);
v_isSharedCheck_861_ = !lean_is_exclusive(v_val_852_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; 
v_unused_862_ = lean_ctor_get(v_val_852_, 0);
lean_dec(v_unused_862_);
v___x_854_ = v_val_852_;
v_isShared_855_ = v_isSharedCheck_861_;
goto v_resetjp_853_;
}
else
{
lean_dec(v_val_852_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_861_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
uint8_t v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_856_ = 1;
v___x_857_ = lean_box(v___x_856_);
if (v_isShared_855_ == 0)
{
lean_ctor_set_tag(v___x_854_, 0);
lean_ctor_set(v___x_854_, 0, v___x_857_);
v___x_859_ = v___x_854_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
else
{
lean_dec(v_val_852_);
goto v___jp_843_;
}
}
else
{
lean_dec(v___x_851_);
goto v___jp_843_;
}
v___jp_843_:
{
uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_844_ = 0;
v___x_845_ = lean_box(v___x_844_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_845_);
v___x_847_ = v___x_838_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
lean_dec(v_val_840_);
lean_del_object(v___x_838_);
goto v___jp_830_;
}
}
else
{
lean_del_object(v___x_838_);
lean_dec(v_a_836_);
goto v___jp_830_;
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v_a_864_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_835_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_835_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
v___jp_830_:
{
uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = 0;
v___x_832_ = lean_box(v___x_831_);
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg___boxed(lean_object* v_fvarId_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_872_, v_a_873_, v_a_874_);
lean_dec(v_a_874_);
lean_dec(v_a_873_);
lean_dec(v_fvarId_872_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp(lean_object* v_fvarId_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_877_, v_a_879_, v_a_881_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___boxed(lean_object* v_fvarId_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_Compiler_LCNF_isConstructorApp(v_fvarId_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_fvarId_884_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object* v_arg_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
if (lean_obj_tag(v_arg_891_) == 1)
{
lean_object* v_fvarId_895_; lean_object* v___x_896_; 
v_fvarId_895_ = lean_ctor_get(v_arg_891_, 0);
v___x_896_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_895_, v_a_892_, v_a_893_);
return v___x_896_;
}
else
{
uint8_t v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = 0;
v___x_898_ = lean_box(v___x_897_);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(lean_object* v_arg_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_900_, v_a_901_, v_a_902_);
lean_dec(v_a_902_);
lean_dec(v_a_901_);
lean_dec(v_arg_900_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp(uint8_t v_pu_905_, lean_object* v_arg_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_906_, v_a_908_, v_a_910_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(lean_object* v_pu_913_, lean_object* v_arg_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
uint8_t v_pu_boxed_920_; lean_object* v_res_921_; 
v_pu_boxed_920_ = lean_unbox(v_pu_913_);
v_res_921_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp(v_pu_boxed_920_, v_arg_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_arg_914_);
return v_res_921_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getParam___closed__1(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParam___closed__0));
v___x_924_ = l_Lean_stringToMessageData(v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam(uint8_t v_pu_925_, lean_object* v_fvarId_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v___x_932_; lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_945_; 
v___x_932_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_925_, v_fvarId_926_, v_a_928_);
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_945_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_945_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_945_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
if (lean_obj_tag(v_a_933_) == 1)
{
lean_object* v_val_937_; lean_object* v___x_939_; 
lean_dec(v_fvarId_926_);
v_val_937_ = lean_ctor_get(v_a_933_, 0);
lean_inc(v_val_937_);
lean_dec_ref_known(v_a_933_, 1);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v_val_937_);
v___x_939_ = v___x_935_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_val_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_del_object(v___x_935_);
lean_dec(v_a_933_);
v___x_941_ = lean_obj_once(&l_Lean_Compiler_LCNF_getParam___closed__1, &l_Lean_Compiler_LCNF_getParam___closed__1_once, _init_l_Lean_Compiler_LCNF_getParam___closed__1);
v___x_942_ = l_Lean_MessageData_ofName(v_fvarId_926_);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_943_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
return v___x_944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam___boxed(lean_object* v_pu_946_, lean_object* v_fvarId_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
uint8_t v_pu_boxed_953_; lean_object* v_res_954_; 
v_pu_boxed_953_ = lean_unbox(v_pu_946_);
v_res_954_ = l_Lean_Compiler_LCNF_getParam(v_pu_boxed_953_, v_fvarId_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
return v_res_954_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l_Lean_Compiler_LCNF_getLetDecl___closed__0));
v___x_957_ = l_Lean_stringToMessageData(v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl(uint8_t v_pu_958_, lean_object* v_fvarId_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v___x_965_; lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_978_; 
v___x_965_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_958_, v_fvarId_959_, v_a_961_);
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_978_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_978_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_978_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
if (lean_obj_tag(v_a_966_) == 1)
{
lean_object* v_val_970_; lean_object* v___x_972_; 
lean_dec(v_fvarId_959_);
v_val_970_ = lean_ctor_get(v_a_966_, 0);
lean_inc(v_val_970_);
lean_dec_ref_known(v_a_966_, 1);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v_val_970_);
v___x_972_ = v___x_968_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_val_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
lean_del_object(v___x_968_);
lean_dec(v_a_966_);
v___x_974_ = lean_obj_once(&l_Lean_Compiler_LCNF_getLetDecl___closed__1, &l_Lean_Compiler_LCNF_getLetDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1);
v___x_975_ = l_Lean_MessageData_ofName(v_fvarId_959_);
v___x_976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_976_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
return v___x_977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl___boxed(lean_object* v_pu_979_, lean_object* v_fvarId_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
uint8_t v_pu_boxed_986_; lean_object* v_res_987_; 
v_pu_boxed_986_ = lean_unbox(v_pu_979_);
v_res_987_ = l_Lean_Compiler_LCNF_getLetDecl(v_pu_boxed_986_, v_fvarId_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
return v_res_987_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Lean_Compiler_LCNF_getFunDecl___closed__0));
v___x_990_ = l_Lean_stringToMessageData(v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t v_pu_991_, lean_object* v_fvarId_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v___x_998_; lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1011_; 
v___x_998_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_991_, v_fvarId_992_, v_a_994_);
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1011_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1011_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
if (lean_obj_tag(v_a_999_) == 1)
{
lean_object* v_val_1003_; lean_object* v___x_1005_; 
lean_dec(v_fvarId_992_);
v_val_1003_ = lean_ctor_get(v_a_999_, 0);
lean_inc(v_val_1003_);
lean_dec_ref_known(v_a_999_, 1);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v_val_1003_);
v___x_1005_ = v___x_1001_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_val_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_del_object(v___x_1001_);
lean_dec(v_a_999_);
v___x_1007_ = lean_obj_once(&l_Lean_Compiler_LCNF_getFunDecl___closed__1, &l_Lean_Compiler_LCNF_getFunDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1);
v___x_1008_ = l_Lean_MessageData_ofName(v_fvarId_992_);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_1009_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
return v___x_1010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl___boxed(lean_object* v_pu_1012_, lean_object* v_fvarId_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
uint8_t v_pu_boxed_1019_; lean_object* v_res_1020_; 
v_pu_boxed_1019_ = lean_unbox(v_pu_1012_);
v_res_1020_ = l_Lean_Compiler_LCNF_getFunDecl(v_pu_boxed_1019_, v_fvarId_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg(lean_object* v_f_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v___x_1024_; lean_object* v_lctx_1025_; lean_object* v_nextIdx_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1037_; 
v___x_1024_ = lean_st_ref_take(v_a_1022_);
v_lctx_1025_ = lean_ctor_get(v___x_1024_, 0);
v_nextIdx_1026_ = lean_ctor_get(v___x_1024_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1028_ = v___x_1024_;
v_isShared_1029_ = v_isSharedCheck_1037_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_nextIdx_1026_);
lean_inc(v_lctx_1025_);
lean_dec(v___x_1024_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1037_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1030_ = lean_box(0);
v___x_1031_ = lean_apply_1(v_f_1021_, v_lctx_1025_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1031_);
v___x_1033_ = v___x_1028_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_nextIdx_1026_);
v___x_1033_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_st_ref_put(v_a_1022_, v___x_1033_);
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1030_);
return v___x_1035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(lean_object* v_f_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Compiler_LCNF_modifyLCtx___redArg(v_f_1038_, v_a_1039_);
lean_dec(v_a_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx(lean_object* v_f_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v___x_1048_; lean_object* v_lctx_1049_; lean_object* v_nextIdx_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1061_; 
v___x_1048_ = lean_st_ref_take(v_a_1044_);
v_lctx_1049_ = lean_ctor_get(v___x_1048_, 0);
v_nextIdx_1050_ = lean_ctor_get(v___x_1048_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1052_ = v___x_1048_;
v_isShared_1053_ = v_isSharedCheck_1061_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_nextIdx_1050_);
lean_inc(v_lctx_1049_);
lean_dec(v___x_1048_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1061_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1054_ = lean_box(0);
v___x_1055_ = lean_apply_1(v_f_1042_, v_lctx_1049_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1055_);
v___x_1057_ = v___x_1052_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_nextIdx_1050_);
v___x_1057_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_st_ref_put(v_a_1044_, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1054_);
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___boxed(lean_object* v_f_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_Compiler_LCNF_modifyLCtx(v_f_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t v_pu_1069_, lean_object* v_decl_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v___x_1073_; lean_object* v_lctx_1074_; lean_object* v_nextIdx_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1086_; 
v___x_1073_ = lean_st_ref_take(v_a_1071_);
v_lctx_1074_ = lean_ctor_get(v___x_1073_, 0);
v_nextIdx_1075_ = lean_ctor_get(v___x_1073_, 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1077_ = v___x_1073_;
v_isShared_1078_ = v_isSharedCheck_1086_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_nextIdx_1075_);
lean_inc(v_lctx_1074_);
lean_dec(v___x_1073_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1086_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1079_ = lean_box(0);
v___x_1080_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_1069_, v_lctx_1074_, v_decl_1070_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1080_);
v___x_1082_ = v___x_1077_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_nextIdx_1075_);
v___x_1082_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_st_ref_put(v_a_1071_, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1079_);
return v___x_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(lean_object* v_pu_1087_, lean_object* v_decl_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
uint8_t v_pu_boxed_1091_; lean_object* v_res_1092_; 
v_pu_boxed_1091_ = lean_unbox(v_pu_1087_);
v_res_1092_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_boxed_1091_, v_decl_1088_, v_a_1089_);
lean_dec(v_a_1089_);
lean_dec_ref(v_decl_1088_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(uint8_t v_pu_1093_, lean_object* v_decl_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1093_, v_decl_1094_, v_a_1096_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___boxed(lean_object* v_pu_1101_, lean_object* v_decl_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
uint8_t v_pu_boxed_1108_; lean_object* v_res_1109_; 
v_pu_boxed_1108_ = lean_unbox(v_pu_1101_);
v_res_1109_ = l_Lean_Compiler_LCNF_eraseLetDecl(v_pu_boxed_1108_, v_decl_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec_ref(v_decl_1102_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t v_pu_1110_, lean_object* v_decl_1111_, uint8_t v_recursive_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v___x_1115_; lean_object* v_lctx_1116_; lean_object* v_nextIdx_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1128_; 
v___x_1115_ = lean_st_ref_take(v_a_1113_);
v_lctx_1116_ = lean_ctor_get(v___x_1115_, 0);
v_nextIdx_1117_ = lean_ctor_get(v___x_1115_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1119_ = v___x_1115_;
v_isShared_1120_ = v_isSharedCheck_1128_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_nextIdx_1117_);
lean_inc(v_lctx_1116_);
lean_dec(v___x_1115_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1128_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1121_ = lean_box(0);
v___x_1122_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_1110_, v_lctx_1116_, v_decl_1111_, v_recursive_1112_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v___x_1122_);
v___x_1124_ = v___x_1119_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_nextIdx_1117_);
v___x_1124_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_st_ref_put(v_a_1113_, v___x_1124_);
v___x_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1121_);
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(lean_object* v_pu_1129_, lean_object* v_decl_1130_, lean_object* v_recursive_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
uint8_t v_pu_boxed_1134_; uint8_t v_recursive_boxed_1135_; lean_object* v_res_1136_; 
v_pu_boxed_1134_ = lean_unbox(v_pu_1129_);
v_recursive_boxed_1135_ = lean_unbox(v_recursive_1131_);
v_res_1136_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_boxed_1134_, v_decl_1130_, v_recursive_boxed_1135_, v_a_1132_);
lean_dec(v_a_1132_);
lean_dec_ref(v_decl_1130_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(uint8_t v_pu_1137_, lean_object* v_decl_1138_, uint8_t v_recursive_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1137_, v_decl_1138_, v_recursive_1139_, v_a_1141_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___boxed(lean_object* v_pu_1146_, lean_object* v_decl_1147_, lean_object* v_recursive_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
uint8_t v_pu_boxed_1154_; uint8_t v_recursive_boxed_1155_; lean_object* v_res_1156_; 
v_pu_boxed_1154_ = lean_unbox(v_pu_1146_);
v_recursive_boxed_1155_ = lean_unbox(v_recursive_1148_);
v_res_1156_ = l_Lean_Compiler_LCNF_eraseFunDecl(v_pu_boxed_1154_, v_decl_1147_, v_recursive_boxed_1155_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec_ref(v_decl_1147_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t v_pu_1157_, lean_object* v_code_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v___x_1161_; lean_object* v_lctx_1162_; lean_object* v_nextIdx_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1174_; 
v___x_1161_ = lean_st_ref_take(v_a_1159_);
v_lctx_1162_ = lean_ctor_get(v___x_1161_, 0);
v_nextIdx_1163_ = lean_ctor_get(v___x_1161_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1165_ = v___x_1161_;
v_isShared_1166_ = v_isSharedCheck_1174_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_nextIdx_1163_);
lean_inc(v_lctx_1162_);
lean_dec(v___x_1161_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1174_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1167_ = lean_box(0);
v___x_1168_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1157_, v_code_1158_, v_lctx_1162_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1168_);
v___x_1170_ = v___x_1165_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_nextIdx_1163_);
v___x_1170_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_st_ref_put(v_a_1159_, v___x_1170_);
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1167_);
return v___x_1172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(lean_object* v_pu_1175_, lean_object* v_code_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
uint8_t v_pu_boxed_1179_; lean_object* v_res_1180_; 
v_pu_boxed_1179_ = lean_unbox(v_pu_1175_);
v_res_1180_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_boxed_1179_, v_code_1176_, v_a_1177_);
lean_dec(v_a_1177_);
lean_dec_ref(v_code_1176_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode(uint8_t v_pu_1181_, lean_object* v_code_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_1181_, v_code_1182_, v_a_1184_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___boxed(lean_object* v_pu_1189_, lean_object* v_code_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
uint8_t v_pu_boxed_1196_; lean_object* v_res_1197_; 
v_pu_boxed_1196_ = lean_unbox(v_pu_1189_);
v_res_1197_ = l_Lean_Compiler_LCNF_eraseCode(v_pu_boxed_1196_, v_code_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
lean_dec_ref(v_code_1190_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t v_pu_1198_, lean_object* v_param_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v___x_1202_; lean_object* v_lctx_1203_; lean_object* v_nextIdx_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1215_; 
v___x_1202_ = lean_st_ref_take(v_a_1200_);
v_lctx_1203_ = lean_ctor_get(v___x_1202_, 0);
v_nextIdx_1204_ = lean_ctor_get(v___x_1202_, 1);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1206_ = v___x_1202_;
v_isShared_1207_ = v_isSharedCheck_1215_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_nextIdx_1204_);
lean_inc(v_lctx_1203_);
lean_dec(v___x_1202_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1215_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1208_ = lean_box(0);
v___x_1209_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_1198_, v_lctx_1203_, v_param_1199_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1209_);
v___x_1211_ = v___x_1206_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_nextIdx_1204_);
v___x_1211_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_st_ref_put(v_a_1200_, v___x_1211_);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1208_);
return v___x_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(lean_object* v_pu_1216_, lean_object* v_param_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
uint8_t v_pu_boxed_1220_; lean_object* v_res_1221_; 
v_pu_boxed_1220_ = lean_unbox(v_pu_1216_);
v_res_1221_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_boxed_1220_, v_param_1217_, v_a_1218_);
lean_dec(v_a_1218_);
lean_dec_ref(v_param_1217_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam(uint8_t v_pu_1222_, lean_object* v_param_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_1222_, v_param_1223_, v_a_1225_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___boxed(lean_object* v_pu_1230_, lean_object* v_param_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
uint8_t v_pu_boxed_1237_; lean_object* v_res_1238_; 
v_pu_boxed_1237_ = lean_unbox(v_pu_1230_);
v_res_1238_ = l_Lean_Compiler_LCNF_eraseParam(v_pu_boxed_1237_, v_param_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec_ref(v_param_1231_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t v_pu_1239_, lean_object* v_params_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v___x_1243_; lean_object* v_lctx_1244_; lean_object* v_nextIdx_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1256_; 
v___x_1243_ = lean_st_ref_take(v_a_1241_);
v_lctx_1244_ = lean_ctor_get(v___x_1243_, 0);
v_nextIdx_1245_ = lean_ctor_get(v___x_1243_, 1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1247_ = v___x_1243_;
v_isShared_1248_ = v_isSharedCheck_1256_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_nextIdx_1245_);
lean_inc(v_lctx_1244_);
lean_dec(v___x_1243_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1256_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1249_ = lean_box(0);
v___x_1250_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_1239_, v_lctx_1244_, v_params_1240_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1250_);
v___x_1252_ = v___x_1247_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_nextIdx_1245_);
v___x_1252_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_st_ref_put(v_a_1241_, v___x_1252_);
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1249_);
return v___x_1254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(lean_object* v_pu_1257_, lean_object* v_params_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
uint8_t v_pu_boxed_1261_; lean_object* v_res_1262_; 
v_pu_boxed_1261_ = lean_unbox(v_pu_1257_);
v_res_1262_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_boxed_1261_, v_params_1258_, v_a_1259_);
lean_dec(v_a_1259_);
lean_dec_ref(v_params_1258_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams(uint8_t v_pu_1263_, lean_object* v_params_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1263_, v_params_1264_, v_a_1266_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___boxed(lean_object* v_pu_1271_, lean_object* v_params_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
uint8_t v_pu_boxed_1278_; lean_object* v_res_1279_; 
v_pu_boxed_1278_ = lean_unbox(v_pu_1271_);
v_res_1279_ = l_Lean_Compiler_LCNF_eraseParams(v_pu_boxed_1278_, v_params_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec_ref(v_params_1272_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t v_pu_1280_, lean_object* v_decl_1281_, lean_object* v_a_1282_){
_start:
{
switch(lean_obj_tag(v_decl_1281_))
{
case 0:
{
lean_object* v_decl_1284_; lean_object* v___x_1285_; 
v_decl_1284_ = lean_ctor_get(v_decl_1281_, 0);
v___x_1285_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1280_, v_decl_1284_, v_a_1282_);
return v___x_1285_;
}
case 1:
{
lean_object* v_decl_1286_; uint8_t v___x_1287_; lean_object* v___x_1288_; 
v_decl_1286_ = lean_ctor_get(v_decl_1281_, 0);
v___x_1287_ = 1;
v___x_1288_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1280_, v_decl_1286_, v___x_1287_, v_a_1282_);
return v___x_1288_;
}
case 2:
{
lean_object* v_decl_1289_; uint8_t v___x_1290_; lean_object* v___x_1291_; 
v_decl_1289_ = lean_ctor_get(v_decl_1281_, 0);
v___x_1290_ = 1;
v___x_1291_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1280_, v_decl_1289_, v___x_1290_, v_a_1282_);
return v___x_1291_;
}
default: 
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = lean_box(0);
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
return v___x_1293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(lean_object* v_pu_1294_, lean_object* v_decl_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
uint8_t v_pu_boxed_1298_; lean_object* v_res_1299_; 
v_pu_boxed_1298_ = lean_unbox(v_pu_1294_);
v_res_1299_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_boxed_1298_, v_decl_1295_, v_a_1296_);
lean_dec(v_a_1296_);
lean_dec_ref(v_decl_1295_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(uint8_t v_pu_1300_, lean_object* v_decl_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1300_, v_decl_1301_, v_a_1303_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(lean_object* v_pu_1308_, lean_object* v_decl_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
uint8_t v_pu_boxed_1315_; lean_object* v_res_1316_; 
v_pu_boxed_1315_ = lean_unbox(v_pu_1308_);
v_res_1316_ = l_Lean_Compiler_LCNF_eraseCodeDecl(v_pu_boxed_1315_, v_decl_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec_ref(v_decl_1309_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(uint8_t v_pu_1317_, lean_object* v_as_1318_, size_t v_i_1319_, size_t v_stop_1320_, lean_object* v_b_1321_, lean_object* v___y_1322_){
_start:
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_usize_dec_eq(v_i_1319_, v_stop_1320_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_array_uget_borrowed(v_as_1318_, v_i_1319_);
v___x_1326_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1317_, v___x_1325_, v___y_1322_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; size_t v___x_1328_; size_t v___x_1329_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1326_, 1);
v___x_1328_ = ((size_t)1ULL);
v___x_1329_ = lean_usize_add(v_i_1319_, v___x_1328_);
v_i_1319_ = v___x_1329_;
v_b_1321_ = v_a_1327_;
goto _start;
}
else
{
return v___x_1326_;
}
}
else
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1331_, 0, v_b_1321_);
return v___x_1331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(lean_object* v_pu_1332_, lean_object* v_as_1333_, lean_object* v_i_1334_, lean_object* v_stop_1335_, lean_object* v_b_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
uint8_t v_pu_boxed_1339_; size_t v_i_boxed_1340_; size_t v_stop_boxed_1341_; lean_object* v_res_1342_; 
v_pu_boxed_1339_ = lean_unbox(v_pu_1332_);
v_i_boxed_1340_ = lean_unbox_usize(v_i_1334_);
lean_dec(v_i_1334_);
v_stop_boxed_1341_ = lean_unbox_usize(v_stop_1335_);
lean_dec(v_stop_1335_);
v_res_1342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_boxed_1339_, v_as_1333_, v_i_boxed_1340_, v_stop_boxed_1341_, v_b_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v_as_1333_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(uint8_t v_pu_1343_, lean_object* v_decls_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = lean_array_get_size(v_decls_1344_);
v___x_1352_ = lean_box(0);
v___x_1353_ = lean_nat_dec_lt(v___x_1350_, v___x_1351_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1352_);
return v___x_1354_;
}
else
{
size_t v___x_1355_; size_t v___x_1356_; lean_object* v___x_1357_; 
v___x_1355_ = ((size_t)0ULL);
v___x_1356_ = lean_usize_of_nat(v___x_1351_);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1343_, v_decls_1344_, v___x_1355_, v___x_1356_, v___x_1352_, v_a_1346_);
return v___x_1357_;
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
v___x_1485_ = lean_unsigned_to_nat(215u);
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
lean_object* v_fn_1506_; lean_object* v_arg_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; size_t v___x_1510_; size_t v___x_1511_; uint8_t v___x_1512_; 
v_fn_1506_ = lean_ctor_get(v_e_1492_, 0);
v_arg_1507_ = lean_ctor_get(v_e_1492_, 1);
lean_inc_ref(v_fn_1506_);
v___x_1508_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1489_, v_s_1490_, v_translator_1491_, v_fn_1506_);
lean_inc_ref(v_arg_1507_);
v___x_1509_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1489_, v_s_1490_, v_translator_1491_, v_arg_1507_);
v___x_1510_ = lean_ptr_addr(v_fn_1506_);
v___x_1511_ = lean_ptr_addr(v___x_1508_);
v___x_1512_ = lean_usize_dec_eq(v___x_1510_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec_ref_known(v_e_1492_, 2);
v___x_1513_ = l_Lean_Expr_app___override(v___x_1508_, v___x_1509_);
v___x_1514_ = l_Lean_Expr_headBeta(v___x_1513_);
return v___x_1514_;
}
else
{
size_t v___x_1515_; size_t v___x_1516_; uint8_t v___x_1517_; 
v___x_1515_ = lean_ptr_addr(v_arg_1507_);
v___x_1516_ = lean_ptr_addr(v___x_1509_);
v___x_1517_ = lean_usize_dec_eq(v___x_1515_, v___x_1516_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec_ref_known(v_e_1492_, 2);
v___x_1518_ = l_Lean_Expr_app___override(v___x_1508_, v___x_1509_);
v___x_1519_ = l_Lean_Expr_headBeta(v___x_1518_);
return v___x_1519_;
}
else
{
lean_object* v___x_1520_; 
lean_dec_ref(v___x_1509_);
lean_dec_ref(v___x_1508_);
v___x_1520_ = l_Lean_Expr_headBeta(v_e_1492_);
return v___x_1520_;
}
}
}
case 6:
{
lean_object* v_binderName_1521_; lean_object* v_binderType_1522_; lean_object* v_body_1523_; uint8_t v_binderInfo_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; size_t v___x_1527_; size_t v___x_1528_; uint8_t v___x_1529_; 
v_binderName_1521_ = lean_ctor_get(v_e_1492_, 0);
v_binderType_1522_ = lean_ctor_get(v_e_1492_, 1);
v_body_1523_ = lean_ctor_get(v_e_1492_, 2);
v_binderInfo_1524_ = lean_ctor_get_uint8(v_e_1492_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1522_);
v___x_1525_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1489_, v_s_1490_, v_translator_1491_, v_binderType_1522_);
lean_inc_ref(v_body_1523_);
v___x_1526_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1489_, v_s_1490_, v_translator_1491_, v_body_1523_);
v___x_1527_ = lean_ptr_addr(v_binderType_1522_);
v___x_1528_ = lean_ptr_addr(v___x_1525_);
v___x_1529_ = lean_usize_dec_eq(v___x_1527_, v___x_1528_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; 
lean_inc(v_binderName_1521_);
lean_dec_ref_known(v_e_1492_, 3);
v___x_1530_ = l_Lean_Expr_lam___override(v_binderName_1521_, v___x_1525_, v___x_1526_, v_binderInfo_1524_);
return v___x_1530_;
}
else
{
size_t v___x_1531_; size_t v___x_1532_; uint8_t v___x_1533_; 
v___x_1531_ = lean_ptr_addr(v_body_1523_);
v___x_1532_ = lean_ptr_addr(v___x_1526_);
v___x_1533_ = lean_usize_dec_eq(v___x_1531_, v___x_1532_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; 
lean_inc(v_binderName_1521_);
lean_dec_ref_known(v_e_1492_, 3);
v___x_1534_ = l_Lean_Expr_lam___override(v_binderName_1521_, v___x_1525_, v___x_1526_, v_binderInfo_1524_);
return v___x_1534_;
}
else
{
uint8_t v___x_1535_; 
v___x_1535_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1524_, v_binderInfo_1524_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; 
lean_inc(v_binderName_1521_);
lean_dec_ref_known(v_e_1492_, 3);
v___x_1536_ = l_Lean_Expr_lam___override(v_binderName_1521_, v___x_1525_, v___x_1526_, v_binderInfo_1524_);
return v___x_1536_;
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
lean_object* v_binderName_1537_; lean_object* v_binderType_1538_; lean_object* v_body_1539_; uint8_t v_binderInfo_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; size_t v___x_1543_; size_t v___x_1544_; uint8_t v___x_1545_; 
v_binderName_1537_ = lean_ctor_get(v_e_1492_, 0);
v_binderType_1538_ = lean_ctor_get(v_e_1492_, 1);
v_body_1539_ = lean_ctor_get(v_e_1492_, 2);
v_binderInfo_1540_ = lean_ctor_get_uint8(v_e_1492_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1538_);
v___x_1541_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1489_, v_s_1490_, v_translator_1491_, v_binderType_1538_);
lean_inc_ref(v_body_1539_);
v___x_1542_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1489_, v_s_1490_, v_translator_1491_, v_body_1539_);
v___x_1543_ = lean_ptr_addr(v_binderType_1538_);
v___x_1544_ = lean_ptr_addr(v___x_1541_);
v___x_1545_ = lean_usize_dec_eq(v___x_1543_, v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; 
lean_inc(v_binderName_1537_);
lean_dec_ref_known(v_e_1492_, 3);
v___x_1546_ = l_Lean_Expr_forallE___override(v_binderName_1537_, v___x_1541_, v___x_1542_, v_binderInfo_1540_);
return v___x_1546_;
}
else
{
size_t v___x_1547_; size_t v___x_1548_; uint8_t v___x_1549_; 
v___x_1547_ = lean_ptr_addr(v_body_1539_);
v___x_1548_ = lean_ptr_addr(v___x_1542_);
v___x_1549_ = lean_usize_dec_eq(v___x_1547_, v___x_1548_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; 
lean_inc(v_binderName_1537_);
lean_dec_ref_known(v_e_1492_, 3);
v___x_1550_ = l_Lean_Expr_forallE___override(v_binderName_1537_, v___x_1541_, v___x_1542_, v_binderInfo_1540_);
return v___x_1550_;
}
else
{
uint8_t v___x_1551_; 
v___x_1551_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1540_, v_binderInfo_1540_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; 
lean_inc(v_binderName_1537_);
lean_dec_ref_known(v_e_1492_, 3);
v___x_1552_ = l_Lean_Expr_forallE___override(v_binderName_1537_, v___x_1541_, v___x_1542_, v_binderInfo_1540_);
return v___x_1552_;
}
else
{
lean_dec_ref(v___x_1542_);
lean_dec_ref(v___x_1541_);
return v_e_1492_;
}
}
}
}
case 8:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_dec_ref_known(v_e_1492_, 4);
v___x_1553_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3, &l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
v___x_1554_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_1553_);
return v___x_1554_;
}
case 10:
{
lean_object* v_data_1555_; lean_object* v_expr_1556_; lean_object* v___x_1557_; size_t v___x_1558_; size_t v___x_1559_; uint8_t v___x_1560_; 
v_data_1555_ = lean_ctor_get(v_e_1492_, 0);
v_expr_1556_ = lean_ctor_get(v_e_1492_, 1);
lean_inc_ref(v_expr_1556_);
v___x_1557_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1489_, v_s_1490_, v_translator_1491_, v_expr_1556_);
v___x_1558_ = lean_ptr_addr(v_expr_1556_);
v___x_1559_ = lean_ptr_addr(v___x_1557_);
v___x_1560_ = lean_usize_dec_eq(v___x_1558_, v___x_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; 
lean_inc(v_data_1555_);
lean_dec_ref_known(v_e_1492_, 2);
v___x_1561_ = l_Lean_Expr_mdata___override(v_data_1555_, v___x_1557_);
return v___x_1561_;
}
else
{
lean_dec_ref(v___x_1557_);
return v_e_1492_;
}
}
case 11:
{
lean_object* v_typeName_1562_; lean_object* v_idx_1563_; lean_object* v_struct_1564_; lean_object* v___x_1565_; size_t v___x_1566_; size_t v___x_1567_; uint8_t v___x_1568_; 
v_typeName_1562_ = lean_ctor_get(v_e_1492_, 0);
v_idx_1563_ = lean_ctor_get(v_e_1492_, 1);
v_struct_1564_ = lean_ctor_get(v_e_1492_, 2);
lean_inc_ref(v_struct_1564_);
v___x_1565_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1489_, v_s_1490_, v_translator_1491_, v_struct_1564_);
v___x_1566_ = lean_ptr_addr(v_struct_1564_);
v___x_1567_ = lean_ptr_addr(v___x_1565_);
v___x_1568_ = lean_usize_dec_eq(v___x_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; 
lean_inc(v_idx_1563_);
lean_inc(v_typeName_1562_);
lean_dec_ref_known(v_e_1492_, 3);
v___x_1569_ = l_Lean_Expr_proj___override(v_typeName_1562_, v_idx_1563_, v___x_1565_);
return v___x_1569_;
}
else
{
lean_dec_ref(v___x_1565_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t v_pu_1570_, lean_object* v_s_1571_, uint8_t v_translator_1572_, lean_object* v_e_1573_){
_start:
{
if (lean_obj_tag(v_e_1573_) == 5)
{
lean_object* v_fn_1574_; lean_object* v_arg_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; size_t v___x_1578_; size_t v___x_1579_; uint8_t v___x_1580_; 
v_fn_1574_ = lean_ctor_get(v_e_1573_, 0);
v_arg_1575_ = lean_ctor_get(v_e_1573_, 1);
lean_inc_ref(v_fn_1574_);
v___x_1576_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1570_, v_s_1571_, v_translator_1572_, v_fn_1574_);
lean_inc_ref(v_arg_1575_);
v___x_1577_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1570_, v_s_1571_, v_translator_1572_, v_arg_1575_);
v___x_1578_ = lean_ptr_addr(v_fn_1574_);
v___x_1579_ = lean_ptr_addr(v___x_1576_);
v___x_1580_ = lean_usize_dec_eq(v___x_1578_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; 
lean_dec_ref_known(v_e_1573_, 2);
v___x_1581_ = l_Lean_Expr_app___override(v___x_1576_, v___x_1577_);
return v___x_1581_;
}
else
{
size_t v___x_1582_; size_t v___x_1583_; uint8_t v___x_1584_; 
v___x_1582_ = lean_ptr_addr(v_arg_1575_);
v___x_1583_ = lean_ptr_addr(v___x_1577_);
v___x_1584_ = lean_usize_dec_eq(v___x_1582_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; 
lean_dec_ref_known(v_e_1573_, 2);
v___x_1585_ = l_Lean_Expr_app___override(v___x_1576_, v___x_1577_);
return v___x_1585_;
}
else
{
lean_dec_ref(v___x_1577_);
lean_dec_ref(v___x_1576_);
return v_e_1573_;
}
}
}
else
{
lean_object* v___x_1586_; 
v___x_1586_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1570_, v_s_1571_, v_translator_1572_, v_e_1573_);
return v___x_1586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object* v_pu_1587_, lean_object* v_s_1588_, lean_object* v_translator_1589_, lean_object* v_e_1590_){
_start:
{
uint8_t v_pu_boxed_1591_; uint8_t v_translator_boxed_1592_; lean_object* v_res_1593_; 
v_pu_boxed_1591_ = lean_unbox(v_pu_1587_);
v_translator_boxed_1592_ = lean_unbox(v_translator_1589_);
v_res_1593_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_boxed_1591_, v_s_1588_, v_translator_boxed_1592_, v_e_1590_);
lean_dec_ref(v_s_1588_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object* v_pu_1594_, lean_object* v_s_1595_, lean_object* v_translator_1596_, lean_object* v_e_1597_){
_start:
{
uint8_t v_pu_boxed_1598_; uint8_t v_translator_boxed_1599_; lean_object* v_res_1600_; 
v_pu_boxed_1598_ = lean_unbox(v_pu_1594_);
v_translator_boxed_1599_ = lean_unbox(v_translator_1596_);
v_res_1600_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_boxed_1598_, v_s_1595_, v_translator_boxed_1599_, v_e_1597_);
lean_dec_ref(v_s_1595_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t v_pu_1601_, lean_object* v_s_1602_, lean_object* v_e_1603_, uint8_t v_translator_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1601_, v_s_1602_, v_translator_1604_, v_e_1603_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object* v_pu_1606_, lean_object* v_s_1607_, lean_object* v_e_1608_, lean_object* v_translator_1609_){
_start:
{
uint8_t v_pu_boxed_1610_; uint8_t v_translator_boxed_1611_; lean_object* v_res_1612_; 
v_pu_boxed_1610_ = lean_unbox(v_pu_1606_);
v_translator_boxed_1611_ = lean_unbox(v_translator_1609_);
v_res_1612_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(v_pu_boxed_1610_, v_s_1607_, v_e_1608_, v_translator_boxed_1611_);
lean_dec_ref(v_s_1607_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___impl(lean_object* v_x_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_obj_tag_nat(v_x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___impl___boxed(lean_object* v_x_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___impl(v_x_1615_);
lean_dec(v_x_1615_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(lean_object* v_t_1617_, lean_object* v_k_1618_){
_start:
{
if (lean_obj_tag(v_t_1617_) == 0)
{
lean_object* v_fvarId_1619_; lean_object* v___x_1620_; 
v_fvarId_1619_ = lean_ctor_get(v_t_1617_, 0);
lean_inc(v_fvarId_1619_);
lean_dec_ref_known(v_t_1617_, 1);
v___x_1620_ = lean_apply_1(v_k_1618_, v_fvarId_1619_);
return v___x_1620_;
}
else
{
return v_k_1618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(lean_object* v_motive_1621_, lean_object* v_ctorIdx_1622_, lean_object* v_t_1623_, lean_object* v_h_1624_, lean_object* v_k_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1623_, v_k_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(lean_object* v_motive_1627_, lean_object* v_ctorIdx_1628_, lean_object* v_t_1629_, lean_object* v_h_1630_, lean_object* v_k_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(v_motive_1627_, v_ctorIdx_1628_, v_t_1629_, v_h_1630_, v_k_1631_);
lean_dec(v_ctorIdx_1628_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(lean_object* v_t_1633_, lean_object* v_fvar_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1633_, v_fvar_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(lean_object* v_motive_1636_, lean_object* v_t_1637_, lean_object* v_h_1638_, lean_object* v_fvar_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1637_, v_fvar_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(lean_object* v_t_1641_, lean_object* v_erased_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1641_, v_erased_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(lean_object* v_motive_1644_, lean_object* v_t_1645_, lean_object* v_h_1646_, lean_object* v_erased_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1645_, v_erased_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object* v_s_1653_, lean_object* v_fvarId_1654_, uint8_t v_translator_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1653_, v_fvarId_1654_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1657_, 0, v_fvarId_1654_);
return v___x_1657_;
}
else
{
lean_object* v_val_1658_; 
lean_dec(v_fvarId_1654_);
v_val_1658_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_val_1658_);
lean_dec_ref_known(v___x_1656_, 1);
if (lean_obj_tag(v_val_1658_) == 1)
{
if (v_translator_1655_ == 0)
{
lean_object* v_fvarId_1659_; 
v_fvarId_1659_ = lean_ctor_get(v_val_1658_, 0);
lean_inc(v_fvarId_1659_);
lean_dec_ref_known(v_val_1658_, 1);
v_fvarId_1654_ = v_fvarId_1659_;
goto _start;
}
else
{
lean_object* v_fvarId_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
v_fvarId_1661_ = lean_ctor_get(v_val_1658_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_val_1658_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v_val_1658_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_fvarId_1661_);
lean_dec(v_val_1658_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set_tag(v___x_1663_, 0);
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_fvarId_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_object* v___x_1669_; 
lean_dec(v_val_1658_);
v___x_1669_ = lean_box(1);
return v___x_1669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg___boxed(lean_object* v_s_1670_, lean_object* v_fvarId_1671_, lean_object* v_translator_1672_){
_start:
{
uint8_t v_translator_boxed_1673_; lean_object* v_res_1674_; 
v_translator_boxed_1673_ = lean_unbox(v_translator_1672_);
v_res_1674_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1670_, v_fvarId_1671_, v_translator_boxed_1673_);
lean_dec_ref(v_s_1670_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp(uint8_t v_pu_1675_, lean_object* v_s_1676_, lean_object* v_fvarId_1677_, uint8_t v_translator_1678_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1676_, v_fvarId_1677_, v_translator_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___boxed(lean_object* v_pu_1680_, lean_object* v_s_1681_, lean_object* v_fvarId_1682_, lean_object* v_translator_1683_){
_start:
{
uint8_t v_pu_boxed_1684_; uint8_t v_translator_boxed_1685_; lean_object* v_res_1686_; 
v_pu_boxed_1684_ = lean_unbox(v_pu_1680_);
v_translator_boxed_1685_ = lean_unbox(v_translator_1683_);
v_res_1686_ = l_Lean_Compiler_LCNF_normFVarImp(v_pu_boxed_1684_, v_s_1681_, v_fvarId_1682_, v_translator_boxed_1685_);
lean_dec_ref(v_s_1681_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t v_pu_1687_, lean_object* v_s_1688_, lean_object* v_arg_1689_, uint8_t v_translator_1690_){
_start:
{
switch(lean_obj_tag(v_arg_1689_))
{
case 0:
{
return v_arg_1689_;
}
case 1:
{
lean_object* v_fvarId_1691_; lean_object* v___x_1692_; 
v_fvarId_1691_ = lean_ctor_get(v_arg_1689_, 0);
v___x_1692_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1688_, v_fvarId_1691_);
if (lean_obj_tag(v___x_1692_) == 0)
{
return v_arg_1689_;
}
else
{
lean_object* v_val_1693_; 
lean_dec_ref_known(v_arg_1689_, 1);
v_val_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_val_1693_);
lean_dec_ref_known(v___x_1692_, 1);
switch(lean_obj_tag(v_val_1693_))
{
case 0:
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_box(0);
return v___x_1694_;
}
case 1:
{
lean_object* v_fvarId_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1703_; 
v_fvarId_1695_ = lean_ctor_get(v_val_1693_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_val_1693_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1697_ = v_val_1693_;
v_isShared_1698_ = v_isSharedCheck_1703_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_fvarId_1695_);
lean_dec(v_val_1693_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1703_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_fvarId_1695_);
v___x_1700_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
if (v_translator_1690_ == 0)
{
v_arg_1689_ = v___x_1700_;
goto _start;
}
else
{
return v___x_1700_;
}
}
}
}
default: 
{
lean_object* v_expr_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
v_expr_1704_ = lean_ctor_get(v_val_1693_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_val_1693_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v_val_1693_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_expr_1704_);
lean_dec(v_val_1693_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_expr_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
}
default: 
{
lean_object* v_expr_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v_expr_1712_ = lean_ctor_get(v_arg_1689_, 0);
lean_inc_ref(v_expr_1712_);
v___x_1713_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1687_, v_s_1688_, v_translator_1690_, v_expr_1712_);
v___x_1714_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1687_, v_arg_1689_, v___x_1713_);
return v___x_1714_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp___boxed(lean_object* v_pu_1715_, lean_object* v_s_1716_, lean_object* v_arg_1717_, lean_object* v_translator_1718_){
_start:
{
uint8_t v_pu_boxed_1719_; uint8_t v_translator_boxed_1720_; lean_object* v_res_1721_; 
v_pu_boxed_1719_ = lean_unbox(v_pu_1715_);
v_translator_boxed_1720_ = lean_unbox(v_translator_1718_);
v_res_1721_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_boxed_1719_, v_s_1716_, v_arg_1717_, v_translator_boxed_1720_);
lean_dec_ref(v_s_1716_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(uint8_t v_pu_1722_, lean_object* v_s_1723_, uint8_t v_translator_1724_, lean_object* v_i_1725_, lean_object* v_as_1726_){
_start:
{
lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1727_ = lean_array_get_size(v_as_1726_);
v___x_1728_ = lean_nat_dec_lt(v_i_1725_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_dec(v_i_1725_);
return v_as_1726_;
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1730_; size_t v___x_1731_; size_t v___x_1732_; uint8_t v___x_1733_; 
v_a_1729_ = lean_array_fget_borrowed(v_as_1726_, v_i_1725_);
lean_inc(v_a_1729_);
v___x_1730_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1722_, v_s_1723_, v_a_1729_, v_translator_1724_);
v___x_1731_ = lean_ptr_addr(v_a_1729_);
v___x_1732_ = lean_ptr_addr(v___x_1730_);
v___x_1733_ = lean_usize_dec_eq(v___x_1731_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1735_ = lean_nat_add(v_i_1725_, v___x_1734_);
v___x_1736_ = lean_array_fset(v_as_1726_, v_i_1725_, v___x_1730_);
lean_dec(v_i_1725_);
v_i_1725_ = v___x_1735_;
v_as_1726_ = v___x_1736_;
goto _start;
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v___x_1730_);
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = lean_nat_add(v_i_1725_, v___x_1738_);
lean_dec(v_i_1725_);
v_i_1725_ = v___x_1739_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0___boxed(lean_object* v_pu_1741_, lean_object* v_s_1742_, lean_object* v_translator_1743_, lean_object* v_i_1744_, lean_object* v_as_1745_){
_start:
{
uint8_t v_pu_boxed_1746_; uint8_t v_translator_boxed_1747_; lean_object* v_res_1748_; 
v_pu_boxed_1746_ = lean_unbox(v_pu_1741_);
v_translator_boxed_1747_ = lean_unbox(v_translator_1743_);
v_res_1748_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_boxed_1746_, v_s_1742_, v_translator_boxed_1747_, v_i_1744_, v_as_1745_);
lean_dec_ref(v_s_1742_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t v_pu_1749_, lean_object* v_s_1750_, lean_object* v_args_1751_, uint8_t v_translator_1752_){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_unsigned_to_nat(0u);
v___x_1754_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_1749_, v_s_1750_, v_translator_1752_, v___x_1753_, v_args_1751_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(lean_object* v_pu_1755_, lean_object* v_s_1756_, lean_object* v_args_1757_, lean_object* v_translator_1758_){
_start:
{
uint8_t v_pu_boxed_1759_; uint8_t v_translator_boxed_1760_; lean_object* v_res_1761_; 
v_pu_boxed_1759_ = lean_unbox(v_pu_1755_);
v_translator_boxed_1760_ = lean_unbox(v_translator_1758_);
v_res_1761_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_boxed_1759_, v_s_1756_, v_args_1757_, v_translator_boxed_1760_);
lean_dec_ref(v_s_1756_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t v_pu_1762_, lean_object* v_s_1763_, lean_object* v_e_1764_, uint8_t v_translator_1765_){
_start:
{
lean_object* v_fvarId_1767_; lean_object* v_args_1773_; 
switch(lean_obj_tag(v_e_1764_))
{
case 2:
{
lean_object* v_struct_1776_; lean_object* v___x_1777_; 
v_struct_1776_ = lean_ctor_get(v_e_1764_, 2);
lean_inc(v_struct_1776_);
v___x_1777_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1763_, v_struct_1776_, v_translator_1765_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_fvarId_1778_; lean_object* v___x_1779_; 
v_fvarId_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_fvarId_1778_);
lean_dec_ref_known(v___x_1777_, 1);
v___x_1779_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1762_, v_e_1764_, v_fvarId_1778_);
return v___x_1779_;
}
else
{
lean_object* v___x_1780_; 
lean_dec_ref_known(v_e_1764_, 3);
v___x_1780_ = lean_box(1);
return v___x_1780_;
}
}
case 3:
{
lean_object* v_args_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_args_1781_ = lean_ctor_get(v_e_1764_, 2);
lean_inc_ref(v_args_1781_);
v___x_1782_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1762_, v_s_1763_, v_args_1781_, v_translator_1765_);
v___x_1783_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1764_, v___x_1782_);
return v___x_1783_;
}
case 4:
{
lean_object* v_fvarId_1784_; lean_object* v_args_1785_; lean_object* v___x_1786_; 
v_fvarId_1784_ = lean_ctor_get(v_e_1764_, 0);
v_args_1785_ = lean_ctor_get(v_e_1764_, 1);
lean_inc(v_fvarId_1784_);
v___x_1786_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1763_, v_fvarId_1784_, v_translator_1765_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_fvarId_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v_fvarId_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_fvarId_1787_);
lean_dec_ref_known(v___x_1786_, 1);
lean_inc_ref(v_args_1785_);
v___x_1788_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1762_, v_s_1763_, v_args_1785_, v_translator_1765_);
v___x_1789_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___redArg(v_e_1764_, v_fvarId_1787_, v___x_1788_);
return v___x_1789_;
}
else
{
lean_object* v___x_1790_; 
lean_dec_ref_known(v_e_1764_, 2);
v___x_1790_ = lean_box(1);
return v___x_1790_;
}
}
case 5:
{
lean_object* v_args_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v_args_1791_ = lean_ctor_get(v_e_1764_, 1);
lean_inc_ref(v_args_1791_);
v___x_1792_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1762_, v_s_1763_, v_args_1791_, v_translator_1765_);
v___x_1793_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1764_, v___x_1792_);
return v___x_1793_;
}
case 6:
{
lean_object* v_var_1794_; 
v_var_1794_ = lean_ctor_get(v_e_1764_, 1);
lean_inc(v_var_1794_);
v_fvarId_1767_ = v_var_1794_;
goto v___jp_1766_;
}
case 7:
{
lean_object* v_var_1795_; 
v_var_1795_ = lean_ctor_get(v_e_1764_, 1);
lean_inc(v_var_1795_);
v_fvarId_1767_ = v_var_1795_;
goto v___jp_1766_;
}
case 8:
{
lean_object* v_var_1796_; lean_object* v___x_1797_; 
v_var_1796_ = lean_ctor_get(v_e_1764_, 2);
lean_inc(v_var_1796_);
v___x_1797_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1763_, v_var_1796_, v_translator_1765_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_fvarId_1798_; lean_object* v___x_1799_; 
v_fvarId_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_fvarId_1798_);
lean_dec_ref_known(v___x_1797_, 1);
v___x_1799_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1762_, v_e_1764_, v_fvarId_1798_);
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; 
lean_dec_ref_known(v_e_1764_, 3);
v___x_1800_ = lean_box(1);
return v___x_1800_;
}
}
case 9:
{
lean_object* v_args_1801_; 
v_args_1801_ = lean_ctor_get(v_e_1764_, 1);
lean_inc_ref(v_args_1801_);
v_args_1773_ = v_args_1801_;
goto v___jp_1772_;
}
case 10:
{
lean_object* v_args_1802_; 
v_args_1802_ = lean_ctor_get(v_e_1764_, 1);
lean_inc_ref(v_args_1802_);
v_args_1773_ = v_args_1802_;
goto v___jp_1772_;
}
case 11:
{
lean_object* v_n_1803_; lean_object* v_var_1804_; lean_object* v___x_1805_; 
v_n_1803_ = lean_ctor_get(v_e_1764_, 0);
lean_inc(v_n_1803_);
v_var_1804_ = lean_ctor_get(v_e_1764_, 1);
lean_inc(v_var_1804_);
v___x_1805_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1763_, v_var_1804_, v_translator_1765_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_fvarId_1806_; lean_object* v___x_1807_; 
v_fvarId_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_fvarId_1806_);
lean_dec_ref_known(v___x_1805_, 1);
v___x_1807_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp___redArg(v_e_1764_, v_n_1803_, v_fvarId_1806_);
return v___x_1807_;
}
else
{
lean_object* v___x_1808_; 
lean_dec_ref_known(v_e_1764_, 2);
lean_dec(v_n_1803_);
v___x_1808_ = lean_box(1);
return v___x_1808_;
}
}
case 12:
{
lean_object* v_var_1809_; lean_object* v_i_1810_; uint8_t v_updateHeader_1811_; lean_object* v_args_1812_; lean_object* v___x_1813_; 
v_var_1809_ = lean_ctor_get(v_e_1764_, 0);
v_i_1810_ = lean_ctor_get(v_e_1764_, 1);
lean_inc_ref(v_i_1810_);
v_updateHeader_1811_ = lean_ctor_get_uint8(v_e_1764_, sizeof(void*)*3);
v_args_1812_ = lean_ctor_get(v_e_1764_, 2);
lean_inc(v_var_1809_);
v___x_1813_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1763_, v_var_1809_, v_translator_1765_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_fvarId_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v_fvarId_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_fvarId_1814_);
lean_dec_ref_known(v___x_1813_, 1);
lean_inc_ref(v_args_1812_);
v___x_1815_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1762_, v_s_1763_, v_args_1812_, v_translator_1765_);
v___x_1816_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp___redArg(v_e_1764_, v_fvarId_1814_, v_i_1810_, v_updateHeader_1811_, v___x_1815_);
return v___x_1816_;
}
else
{
lean_object* v___x_1817_; 
lean_dec_ref(v_i_1810_);
lean_dec_ref_known(v_e_1764_, 3);
v___x_1817_ = lean_box(1);
return v___x_1817_;
}
}
case 13:
{
lean_object* v_ty_1818_; lean_object* v_fvarId_1819_; lean_object* v___x_1820_; 
v_ty_1818_ = lean_ctor_get(v_e_1764_, 0);
lean_inc_ref(v_ty_1818_);
v_fvarId_1819_ = lean_ctor_get(v_e_1764_, 1);
lean_inc(v_fvarId_1819_);
v___x_1820_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1763_, v_fvarId_1819_, v_translator_1765_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_fvarId_1821_; lean_object* v___x_1822_; 
v_fvarId_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_fvarId_1821_);
lean_dec_ref_known(v___x_1820_, 1);
v___x_1822_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp___redArg(v_e_1764_, v_ty_1818_, v_fvarId_1821_);
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; 
lean_dec_ref_known(v_e_1764_, 2);
lean_dec_ref(v_ty_1818_);
v___x_1823_ = lean_box(1);
return v___x_1823_;
}
}
case 14:
{
lean_object* v_fvarId_1824_; lean_object* v___x_1825_; 
v_fvarId_1824_ = lean_ctor_get(v_e_1764_, 0);
lean_inc(v_fvarId_1824_);
v___x_1825_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1763_, v_fvarId_1824_, v_translator_1765_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_fvarId_1826_; lean_object* v___x_1827_; 
v_fvarId_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_fvarId_1826_);
lean_dec_ref_known(v___x_1825_, 1);
v___x_1827_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp___redArg(v_e_1764_, v_fvarId_1826_);
return v___x_1827_;
}
else
{
lean_object* v___x_1828_; 
lean_dec_ref_known(v_e_1764_, 1);
v___x_1828_ = lean_box(1);
return v___x_1828_;
}
}
case 15:
{
lean_object* v_fvarId_1829_; lean_object* v___x_1830_; 
v_fvarId_1829_ = lean_ctor_get(v_e_1764_, 0);
lean_inc(v_fvarId_1829_);
v___x_1830_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1763_, v_fvarId_1829_, v_translator_1765_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_fvarId_1831_; lean_object* v___x_1832_; 
v_fvarId_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_fvarId_1831_);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1832_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp___redArg(v_e_1764_, v_fvarId_1831_);
return v___x_1832_;
}
else
{
lean_object* v___x_1833_; 
lean_dec_ref_known(v_e_1764_, 1);
v___x_1833_ = lean_box(1);
return v___x_1833_;
}
}
default: 
{
return v_e_1764_;
}
}
v___jp_1766_:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1763_, v_fvarId_1767_, v_translator_1765_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_fvarId_1769_; lean_object* v___x_1770_; 
v_fvarId_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_fvarId_1769_);
lean_dec_ref_known(v___x_1768_, 1);
v___x_1770_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1762_, v_e_1764_, v_fvarId_1769_);
return v___x_1770_;
}
else
{
lean_object* v___x_1771_; 
lean_dec(v_e_1764_);
v___x_1771_ = lean_box(1);
return v___x_1771_;
}
}
v___jp_1772_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1762_, v_s_1763_, v_args_1773_, v_translator_1765_);
v___x_1775_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1764_, v___x_1774_);
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp___boxed(lean_object* v_pu_1834_, lean_object* v_s_1835_, lean_object* v_e_1836_, lean_object* v_translator_1837_){
_start:
{
uint8_t v_pu_boxed_1838_; uint8_t v_translator_boxed_1839_; lean_object* v_res_1840_; 
v_pu_boxed_1838_ = lean_unbox(v_pu_1834_);
v_translator_boxed_1839_ = lean_unbox(v_translator_1837_);
v_res_1840_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_boxed_1838_, v_s_1835_, v_e_1836_, v_translator_boxed_1839_);
lean_dec_ref(v_s_1835_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(lean_object* v_inst_1841_, lean_object* v_inst_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_apply_2(v_inst_1841_, lean_box(0), v_inst_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(uint8_t v_pu_1844_, uint8_t v_t_1845_, lean_object* v_m_1846_, lean_object* v_n_1847_, lean_object* v_inst_1848_, lean_object* v_inst_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = lean_apply_2(v_inst_1848_, lean_box(0), v_inst_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(lean_object* v_pu_1851_, lean_object* v_t_1852_, lean_object* v_m_1853_, lean_object* v_n_1854_, lean_object* v_inst_1855_, lean_object* v_inst_1856_){
_start:
{
uint8_t v_pu_boxed_1857_; uint8_t v_t_boxed_1858_; lean_object* v_res_1859_; 
v_pu_boxed_1857_ = lean_unbox(v_pu_1851_);
v_t_boxed_1858_ = lean_unbox(v_t_1852_);
v_res_1859_ = l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(v_pu_boxed_1857_, v_t_boxed_1858_, v_m_1853_, v_n_1854_, v_inst_1855_, v_inst_1856_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0(lean_object* v_inst_1860_, lean_object* v_inst_1861_, lean_object* v_f_1862_){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_apply_1(v_inst_1860_, v_f_1862_);
v___x_1864_ = lean_apply_2(v_inst_1861_, lean_box(0), v___x_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(lean_object* v_inst_1865_, lean_object* v_inst_1866_){
_start:
{
lean_object* v___f_1867_; 
v___f_1867_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1867_, 0, v_inst_1866_);
lean_closure_set(v___f_1867_, 1, v_inst_1865_);
return v___f_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(uint8_t v_pu_1868_, lean_object* v_m_1869_, lean_object* v_n_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_){
_start:
{
lean_object* v___f_1873_; 
v___f_1873_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1873_, 0, v_inst_1872_);
lean_closure_set(v___f_1873_, 1, v_inst_1871_);
return v___f_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(lean_object* v_pu_1874_, lean_object* v_m_1875_, lean_object* v_n_1876_, lean_object* v_inst_1877_, lean_object* v_inst_1878_){
_start:
{
uint8_t v_pu_boxed_1879_; lean_object* v_res_1880_; 
v_pu_boxed_1879_ = lean_unbox(v_pu_1874_);
v_res_1880_ = l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(v_pu_boxed_1879_, v_m_1875_, v_n_1876_, v_inst_1877_, v_inst_1878_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___lam__0(lean_object* v___x_1881_, lean_object* v___x_1882_, lean_object* v_fvarId_1883_, lean_object* v_arg_1884_, lean_object* v_s_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1881_, v___x_1882_, v_s_1885_, v_fvarId_1883_, v_arg_1884_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg(lean_object* v_inst_1889_, lean_object* v_fvarId_1890_, lean_object* v_arg_1891_){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___f_1894_; lean_object* v___x_1895_; 
v___x_1892_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1893_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1894_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1894_, 0, v___x_1892_);
lean_closure_set(v___f_1894_, 1, v___x_1893_);
lean_closure_set(v___f_1894_, 2, v_fvarId_1890_);
lean_closure_set(v___f_1894_, 3, v_arg_1891_);
v___x_1895_ = lean_apply_1(v_inst_1889_, v___f_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst(lean_object* v_m_1896_, uint8_t v_pu_1897_, lean_object* v_inst_1898_, lean_object* v_fvarId_1899_, lean_object* v_arg_1900_){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___f_1903_; lean_object* v___x_1904_; 
v___x_1901_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1902_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1903_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1903_, 0, v___x_1901_);
lean_closure_set(v___f_1903_, 1, v___x_1902_);
lean_closure_set(v___f_1903_, 2, v_fvarId_1899_);
lean_closure_set(v___f_1903_, 3, v_arg_1900_);
v___x_1904_ = lean_apply_1(v_inst_1898_, v___f_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___boxed(lean_object* v_m_1905_, lean_object* v_pu_1906_, lean_object* v_inst_1907_, lean_object* v_fvarId_1908_, lean_object* v_arg_1909_){
_start:
{
uint8_t v_pu_boxed_1910_; lean_object* v_res_1911_; 
v_pu_boxed_1910_ = lean_unbox(v_pu_1906_);
v_res_1911_ = l_Lean_Compiler_LCNF_addSubst(v_m_1905_, v_pu_boxed_1910_, v_inst_1907_, v_fvarId_1908_, v_arg_1909_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0(lean_object* v_fvarId_x27_1912_, lean_object* v___x_1913_, lean_object* v___x_1914_, lean_object* v_fvarId_1915_, lean_object* v_s_1916_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_fvarId_x27_1912_);
v___x_1918_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1913_, v___x_1914_, v_s_1916_, v_fvarId_1915_, v___x_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg(lean_object* v_inst_1919_, lean_object* v_fvarId_1920_, lean_object* v_fvarId_x27_1921_){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___f_1924_; lean_object* v___x_1925_; 
v___x_1922_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1923_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1924_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1924_, 0, v_fvarId_x27_1921_);
lean_closure_set(v___f_1924_, 1, v___x_1922_);
lean_closure_set(v___f_1924_, 2, v___x_1923_);
lean_closure_set(v___f_1924_, 3, v_fvarId_1920_);
v___x_1925_ = lean_apply_1(v_inst_1919_, v___f_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst(lean_object* v_m_1926_, uint8_t v_ph_1927_, lean_object* v_inst_1928_, lean_object* v_fvarId_1929_, lean_object* v_fvarId_x27_1930_){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___f_1933_; lean_object* v___x_1934_; 
v___x_1931_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1932_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1933_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1933_, 0, v_fvarId_x27_1930_);
lean_closure_set(v___f_1933_, 1, v___x_1931_);
lean_closure_set(v___f_1933_, 2, v___x_1932_);
lean_closure_set(v___f_1933_, 3, v_fvarId_1929_);
v___x_1934_ = lean_apply_1(v_inst_1928_, v___f_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___boxed(lean_object* v_m_1935_, lean_object* v_ph_1936_, lean_object* v_inst_1937_, lean_object* v_fvarId_1938_, lean_object* v_fvarId_x27_1939_){
_start:
{
uint8_t v_ph_boxed_1940_; lean_object* v_res_1941_; 
v_ph_boxed_1940_ = lean_unbox(v_ph_1936_);
v_res_1941_ = l_Lean_Compiler_LCNF_addFVarSubst(v_m_1935_, v_ph_boxed_1940_, v_inst_1937_, v_fvarId_1938_, v_fvarId_x27_1939_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(lean_object* v_fvarId_1942_, uint8_t v_t_1943_, lean_object* v_toPure_1944_, lean_object* v_____do__lift_1945_){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_____do__lift_1945_, v_fvarId_1942_, v_t_1943_);
v___x_1947_ = lean_apply_2(v_toPure_1944_, lean_box(0), v___x_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(lean_object* v_fvarId_1948_, lean_object* v_t_1949_, lean_object* v_toPure_1950_, lean_object* v_____do__lift_1951_){
_start:
{
uint8_t v_t_boxed_1952_; lean_object* v_res_1953_; 
v_t_boxed_1952_ = lean_unbox(v_t_1949_);
v_res_1953_ = l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(v_fvarId_1948_, v_t_boxed_1952_, v_toPure_1950_, v_____do__lift_1951_);
lean_dec_ref(v_____do__lift_1951_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg(uint8_t v_t_1954_, lean_object* v_inst_1955_, lean_object* v_inst_1956_, lean_object* v_fvarId_1957_){
_start:
{
lean_object* v_toApplicative_1958_; lean_object* v_toBind_1959_; lean_object* v_toPure_1960_; lean_object* v___x_1961_; lean_object* v___f_1962_; lean_object* v___x_1963_; 
v_toApplicative_1958_ = lean_ctor_get(v_inst_1956_, 0);
lean_inc_ref(v_toApplicative_1958_);
v_toBind_1959_ = lean_ctor_get(v_inst_1956_, 1);
lean_inc(v_toBind_1959_);
lean_dec_ref(v_inst_1956_);
v_toPure_1960_ = lean_ctor_get(v_toApplicative_1958_, 1);
lean_inc(v_toPure_1960_);
lean_dec_ref(v_toApplicative_1958_);
v___x_1961_ = lean_box(v_t_1954_);
v___f_1962_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1962_, 0, v_fvarId_1957_);
lean_closure_set(v___f_1962_, 1, v___x_1961_);
lean_closure_set(v___f_1962_, 2, v_toPure_1960_);
v___x_1963_ = lean_apply_4(v_toBind_1959_, lean_box(0), lean_box(0), v_inst_1955_, v___f_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___boxed(lean_object* v_t_1964_, lean_object* v_inst_1965_, lean_object* v_inst_1966_, lean_object* v_fvarId_1967_){
_start:
{
uint8_t v_t_boxed_1968_; lean_object* v_res_1969_; 
v_t_boxed_1968_ = lean_unbox(v_t_1964_);
v_res_1969_ = l_Lean_Compiler_LCNF_normFVar___redArg(v_t_boxed_1968_, v_inst_1965_, v_inst_1966_, v_fvarId_1967_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar(lean_object* v_m_1970_, uint8_t v_pu_1971_, uint8_t v_t_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_fvarId_1975_){
_start:
{
lean_object* v_toApplicative_1976_; lean_object* v_toBind_1977_; lean_object* v_toPure_1978_; lean_object* v___x_1979_; lean_object* v___f_1980_; lean_object* v___x_1981_; 
v_toApplicative_1976_ = lean_ctor_get(v_inst_1974_, 0);
lean_inc_ref(v_toApplicative_1976_);
v_toBind_1977_ = lean_ctor_get(v_inst_1974_, 1);
lean_inc(v_toBind_1977_);
lean_dec_ref(v_inst_1974_);
v_toPure_1978_ = lean_ctor_get(v_toApplicative_1976_, 1);
lean_inc(v_toPure_1978_);
lean_dec_ref(v_toApplicative_1976_);
v___x_1979_ = lean_box(v_t_1972_);
v___f_1980_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1980_, 0, v_fvarId_1975_);
lean_closure_set(v___f_1980_, 1, v___x_1979_);
lean_closure_set(v___f_1980_, 2, v_toPure_1978_);
v___x_1981_ = lean_apply_4(v_toBind_1977_, lean_box(0), lean_box(0), v_inst_1973_, v___f_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___boxed(lean_object* v_m_1982_, lean_object* v_pu_1983_, lean_object* v_t_1984_, lean_object* v_inst_1985_, lean_object* v_inst_1986_, lean_object* v_fvarId_1987_){
_start:
{
uint8_t v_pu_boxed_1988_; uint8_t v_t_boxed_1989_; lean_object* v_res_1990_; 
v_pu_boxed_1988_ = lean_unbox(v_pu_1983_);
v_t_boxed_1989_ = lean_unbox(v_t_1984_);
v_res_1990_ = l_Lean_Compiler_LCNF_normFVar(v_m_1982_, v_pu_boxed_1988_, v_t_boxed_1989_, v_inst_1985_, v_inst_1986_, v_fvarId_1987_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(uint8_t v_pu_1991_, uint8_t v_t_1992_, lean_object* v_e_1993_, lean_object* v_toPure_1994_, lean_object* v_____do__lift_1995_){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1991_, v_____do__lift_1995_, v_t_1992_, v_e_1993_);
v___x_1997_ = lean_apply_2(v_toPure_1994_, lean_box(0), v___x_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(lean_object* v_pu_1998_, lean_object* v_t_1999_, lean_object* v_e_2000_, lean_object* v_toPure_2001_, lean_object* v_____do__lift_2002_){
_start:
{
uint8_t v_pu_boxed_2003_; uint8_t v_t_boxed_2004_; lean_object* v_res_2005_; 
v_pu_boxed_2003_ = lean_unbox(v_pu_1998_);
v_t_boxed_2004_ = lean_unbox(v_t_1999_);
v_res_2005_ = l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(v_pu_boxed_2003_, v_t_boxed_2004_, v_e_2000_, v_toPure_2001_, v_____do__lift_2002_);
lean_dec_ref(v_____do__lift_2002_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg(uint8_t v_pu_2006_, uint8_t v_t_2007_, lean_object* v_inst_2008_, lean_object* v_inst_2009_, lean_object* v_e_2010_){
_start:
{
lean_object* v_toApplicative_2011_; lean_object* v_toBind_2012_; lean_object* v_toPure_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___f_2016_; lean_object* v___x_2017_; 
v_toApplicative_2011_ = lean_ctor_get(v_inst_2009_, 0);
lean_inc_ref(v_toApplicative_2011_);
v_toBind_2012_ = lean_ctor_get(v_inst_2009_, 1);
lean_inc(v_toBind_2012_);
lean_dec_ref(v_inst_2009_);
v_toPure_2013_ = lean_ctor_get(v_toApplicative_2011_, 1);
lean_inc(v_toPure_2013_);
lean_dec_ref(v_toApplicative_2011_);
v___x_2014_ = lean_box(v_pu_2006_);
v___x_2015_ = lean_box(v_t_2007_);
v___f_2016_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2016_, 0, v___x_2014_);
lean_closure_set(v___f_2016_, 1, v___x_2015_);
lean_closure_set(v___f_2016_, 2, v_e_2010_);
lean_closure_set(v___f_2016_, 3, v_toPure_2013_);
v___x_2017_ = lean_apply_4(v_toBind_2012_, lean_box(0), lean_box(0), v_inst_2008_, v___f_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___boxed(lean_object* v_pu_2018_, lean_object* v_t_2019_, lean_object* v_inst_2020_, lean_object* v_inst_2021_, lean_object* v_e_2022_){
_start:
{
uint8_t v_pu_boxed_2023_; uint8_t v_t_boxed_2024_; lean_object* v_res_2025_; 
v_pu_boxed_2023_ = lean_unbox(v_pu_2018_);
v_t_boxed_2024_ = lean_unbox(v_t_2019_);
v_res_2025_ = l_Lean_Compiler_LCNF_normExpr___redArg(v_pu_boxed_2023_, v_t_boxed_2024_, v_inst_2020_, v_inst_2021_, v_e_2022_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr(lean_object* v_m_2026_, uint8_t v_pu_2027_, uint8_t v_t_2028_, lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_e_2031_){
_start:
{
lean_object* v_toApplicative_2032_; lean_object* v_toBind_2033_; lean_object* v_toPure_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___f_2037_; lean_object* v___x_2038_; 
v_toApplicative_2032_ = lean_ctor_get(v_inst_2030_, 0);
lean_inc_ref(v_toApplicative_2032_);
v_toBind_2033_ = lean_ctor_get(v_inst_2030_, 1);
lean_inc(v_toBind_2033_);
lean_dec_ref(v_inst_2030_);
v_toPure_2034_ = lean_ctor_get(v_toApplicative_2032_, 1);
lean_inc(v_toPure_2034_);
lean_dec_ref(v_toApplicative_2032_);
v___x_2035_ = lean_box(v_pu_2027_);
v___x_2036_ = lean_box(v_t_2028_);
v___f_2037_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2037_, 0, v___x_2035_);
lean_closure_set(v___f_2037_, 1, v___x_2036_);
lean_closure_set(v___f_2037_, 2, v_e_2031_);
lean_closure_set(v___f_2037_, 3, v_toPure_2034_);
v___x_2038_ = lean_apply_4(v_toBind_2033_, lean_box(0), lean_box(0), v_inst_2029_, v___f_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___boxed(lean_object* v_m_2039_, lean_object* v_pu_2040_, lean_object* v_t_2041_, lean_object* v_inst_2042_, lean_object* v_inst_2043_, lean_object* v_e_2044_){
_start:
{
uint8_t v_pu_boxed_2045_; uint8_t v_t_boxed_2046_; lean_object* v_res_2047_; 
v_pu_boxed_2045_ = lean_unbox(v_pu_2040_);
v_t_boxed_2046_ = lean_unbox(v_t_2041_);
v_res_2047_ = l_Lean_Compiler_LCNF_normExpr(v_m_2039_, v_pu_boxed_2045_, v_t_boxed_2046_, v_inst_2042_, v_inst_2043_, v_e_2044_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0(uint8_t v_pu_2048_, lean_object* v_arg_2049_, uint8_t v_t_2050_, lean_object* v_toPure_2051_, lean_object* v_____do__lift_2052_){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2048_, v_____do__lift_2052_, v_arg_2049_, v_t_2050_);
v___x_2054_ = lean_apply_2(v_toPure_2051_, lean_box(0), v___x_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(lean_object* v_pu_2055_, lean_object* v_arg_2056_, lean_object* v_t_2057_, lean_object* v_toPure_2058_, lean_object* v_____do__lift_2059_){
_start:
{
uint8_t v_pu_boxed_2060_; uint8_t v_t_boxed_2061_; lean_object* v_res_2062_; 
v_pu_boxed_2060_ = lean_unbox(v_pu_2055_);
v_t_boxed_2061_ = lean_unbox(v_t_2057_);
v_res_2062_ = l_Lean_Compiler_LCNF_normArg___redArg___lam__0(v_pu_boxed_2060_, v_arg_2056_, v_t_boxed_2061_, v_toPure_2058_, v_____do__lift_2059_);
lean_dec_ref(v_____do__lift_2059_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg(uint8_t v_pu_2063_, uint8_t v_t_2064_, lean_object* v_inst_2065_, lean_object* v_inst_2066_, lean_object* v_arg_2067_){
_start:
{
lean_object* v_toApplicative_2068_; lean_object* v_toBind_2069_; lean_object* v_toPure_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___f_2073_; lean_object* v___x_2074_; 
v_toApplicative_2068_ = lean_ctor_get(v_inst_2066_, 0);
lean_inc_ref(v_toApplicative_2068_);
v_toBind_2069_ = lean_ctor_get(v_inst_2066_, 1);
lean_inc(v_toBind_2069_);
lean_dec_ref(v_inst_2066_);
v_toPure_2070_ = lean_ctor_get(v_toApplicative_2068_, 1);
lean_inc(v_toPure_2070_);
lean_dec_ref(v_toApplicative_2068_);
v___x_2071_ = lean_box(v_pu_2063_);
v___x_2072_ = lean_box(v_t_2064_);
v___f_2073_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2073_, 0, v___x_2071_);
lean_closure_set(v___f_2073_, 1, v_arg_2067_);
lean_closure_set(v___f_2073_, 2, v___x_2072_);
lean_closure_set(v___f_2073_, 3, v_toPure_2070_);
v___x_2074_ = lean_apply_4(v_toBind_2069_, lean_box(0), lean_box(0), v_inst_2065_, v___f_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___boxed(lean_object* v_pu_2075_, lean_object* v_t_2076_, lean_object* v_inst_2077_, lean_object* v_inst_2078_, lean_object* v_arg_2079_){
_start:
{
uint8_t v_pu_boxed_2080_; uint8_t v_t_boxed_2081_; lean_object* v_res_2082_; 
v_pu_boxed_2080_ = lean_unbox(v_pu_2075_);
v_t_boxed_2081_ = lean_unbox(v_t_2076_);
v_res_2082_ = l_Lean_Compiler_LCNF_normArg___redArg(v_pu_boxed_2080_, v_t_boxed_2081_, v_inst_2077_, v_inst_2078_, v_arg_2079_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg(lean_object* v_m_2083_, uint8_t v_pu_2084_, uint8_t v_t_2085_, lean_object* v_inst_2086_, lean_object* v_inst_2087_, lean_object* v_arg_2088_){
_start:
{
lean_object* v_toApplicative_2089_; lean_object* v_toBind_2090_; lean_object* v_toPure_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___f_2094_; lean_object* v___x_2095_; 
v_toApplicative_2089_ = lean_ctor_get(v_inst_2087_, 0);
lean_inc_ref(v_toApplicative_2089_);
v_toBind_2090_ = lean_ctor_get(v_inst_2087_, 1);
lean_inc(v_toBind_2090_);
lean_dec_ref(v_inst_2087_);
v_toPure_2091_ = lean_ctor_get(v_toApplicative_2089_, 1);
lean_inc(v_toPure_2091_);
lean_dec_ref(v_toApplicative_2089_);
v___x_2092_ = lean_box(v_pu_2084_);
v___x_2093_ = lean_box(v_t_2085_);
v___f_2094_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2094_, 0, v___x_2092_);
lean_closure_set(v___f_2094_, 1, v_arg_2088_);
lean_closure_set(v___f_2094_, 2, v___x_2093_);
lean_closure_set(v___f_2094_, 3, v_toPure_2091_);
v___x_2095_ = lean_apply_4(v_toBind_2090_, lean_box(0), lean_box(0), v_inst_2086_, v___f_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___boxed(lean_object* v_m_2096_, lean_object* v_pu_2097_, lean_object* v_t_2098_, lean_object* v_inst_2099_, lean_object* v_inst_2100_, lean_object* v_arg_2101_){
_start:
{
uint8_t v_pu_boxed_2102_; uint8_t v_t_boxed_2103_; lean_object* v_res_2104_; 
v_pu_boxed_2102_ = lean_unbox(v_pu_2097_);
v_t_boxed_2103_ = lean_unbox(v_t_2098_);
v_res_2104_ = l_Lean_Compiler_LCNF_normArg(v_m_2096_, v_pu_boxed_2102_, v_t_boxed_2103_, v_inst_2099_, v_inst_2100_, v_arg_2101_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(uint8_t v_pu_2105_, lean_object* v_e_2106_, uint8_t v_t_2107_, lean_object* v_toPure_2108_, lean_object* v_____do__lift_2109_){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_2105_, v_____do__lift_2109_, v_e_2106_, v_t_2107_);
v___x_2111_ = lean_apply_2(v_toPure_2108_, lean_box(0), v___x_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(lean_object* v_pu_2112_, lean_object* v_e_2113_, lean_object* v_t_2114_, lean_object* v_toPure_2115_, lean_object* v_____do__lift_2116_){
_start:
{
uint8_t v_pu_boxed_2117_; uint8_t v_t_boxed_2118_; lean_object* v_res_2119_; 
v_pu_boxed_2117_ = lean_unbox(v_pu_2112_);
v_t_boxed_2118_ = lean_unbox(v_t_2114_);
v_res_2119_ = l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(v_pu_boxed_2117_, v_e_2113_, v_t_boxed_2118_, v_toPure_2115_, v_____do__lift_2116_);
lean_dec_ref(v_____do__lift_2116_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg(uint8_t v_pu_2120_, uint8_t v_t_2121_, lean_object* v_inst_2122_, lean_object* v_inst_2123_, lean_object* v_e_2124_){
_start:
{
lean_object* v_toApplicative_2125_; lean_object* v_toBind_2126_; lean_object* v_toPure_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___f_2130_; lean_object* v___x_2131_; 
v_toApplicative_2125_ = lean_ctor_get(v_inst_2123_, 0);
lean_inc_ref(v_toApplicative_2125_);
v_toBind_2126_ = lean_ctor_get(v_inst_2123_, 1);
lean_inc(v_toBind_2126_);
lean_dec_ref(v_inst_2123_);
v_toPure_2127_ = lean_ctor_get(v_toApplicative_2125_, 1);
lean_inc(v_toPure_2127_);
lean_dec_ref(v_toApplicative_2125_);
v___x_2128_ = lean_box(v_pu_2120_);
v___x_2129_ = lean_box(v_t_2121_);
v___f_2130_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2130_, 0, v___x_2128_);
lean_closure_set(v___f_2130_, 1, v_e_2124_);
lean_closure_set(v___f_2130_, 2, v___x_2129_);
lean_closure_set(v___f_2130_, 3, v_toPure_2127_);
v___x_2131_ = lean_apply_4(v_toBind_2126_, lean_box(0), lean_box(0), v_inst_2122_, v___f_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(lean_object* v_pu_2132_, lean_object* v_t_2133_, lean_object* v_inst_2134_, lean_object* v_inst_2135_, lean_object* v_e_2136_){
_start:
{
uint8_t v_pu_boxed_2137_; uint8_t v_t_boxed_2138_; lean_object* v_res_2139_; 
v_pu_boxed_2137_ = lean_unbox(v_pu_2132_);
v_t_boxed_2138_ = lean_unbox(v_t_2133_);
v_res_2139_ = l_Lean_Compiler_LCNF_normLetValue___redArg(v_pu_boxed_2137_, v_t_boxed_2138_, v_inst_2134_, v_inst_2135_, v_e_2136_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue(lean_object* v_m_2140_, uint8_t v_pu_2141_, uint8_t v_t_2142_, lean_object* v_inst_2143_, lean_object* v_inst_2144_, lean_object* v_e_2145_){
_start:
{
lean_object* v_toApplicative_2146_; lean_object* v_toBind_2147_; lean_object* v_toPure_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___f_2151_; lean_object* v___x_2152_; 
v_toApplicative_2146_ = lean_ctor_get(v_inst_2144_, 0);
lean_inc_ref(v_toApplicative_2146_);
v_toBind_2147_ = lean_ctor_get(v_inst_2144_, 1);
lean_inc(v_toBind_2147_);
lean_dec_ref(v_inst_2144_);
v_toPure_2148_ = lean_ctor_get(v_toApplicative_2146_, 1);
lean_inc(v_toPure_2148_);
lean_dec_ref(v_toApplicative_2146_);
v___x_2149_ = lean_box(v_pu_2141_);
v___x_2150_ = lean_box(v_t_2142_);
v___f_2151_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2151_, 0, v___x_2149_);
lean_closure_set(v___f_2151_, 1, v_e_2145_);
lean_closure_set(v___f_2151_, 2, v___x_2150_);
lean_closure_set(v___f_2151_, 3, v_toPure_2148_);
v___x_2152_ = lean_apply_4(v_toBind_2147_, lean_box(0), lean_box(0), v_inst_2143_, v___f_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___boxed(lean_object* v_m_2153_, lean_object* v_pu_2154_, lean_object* v_t_2155_, lean_object* v_inst_2156_, lean_object* v_inst_2157_, lean_object* v_e_2158_){
_start:
{
uint8_t v_pu_boxed_2159_; uint8_t v_t_boxed_2160_; lean_object* v_res_2161_; 
v_pu_boxed_2159_ = lean_unbox(v_pu_2154_);
v_t_boxed_2160_ = lean_unbox(v_t_2155_);
v_res_2161_ = l_Lean_Compiler_LCNF_normLetValue(v_m_2153_, v_pu_boxed_2159_, v_t_boxed_2160_, v_inst_2156_, v_inst_2157_, v_e_2158_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore(uint8_t v_pu_2162_, lean_object* v_s_2163_, lean_object* v_e_2164_, uint8_t v_translator_2165_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2162_, v_s_2163_, v_translator_2165_, v_e_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore___boxed(lean_object* v_pu_2167_, lean_object* v_s_2168_, lean_object* v_e_2169_, lean_object* v_translator_2170_){
_start:
{
uint8_t v_pu_boxed_2171_; uint8_t v_translator_boxed_2172_; lean_object* v_res_2173_; 
v_pu_boxed_2171_ = lean_unbox(v_pu_2167_);
v_translator_boxed_2172_ = lean_unbox(v_translator_2170_);
v_res_2173_ = l_Lean_Compiler_LCNF_normExprCore(v_pu_boxed_2171_, v_s_2168_, v_e_2169_, v_translator_boxed_2172_);
lean_dec_ref(v_s_2168_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(uint8_t v_pu_2174_, lean_object* v_args_2175_, uint8_t v_t_2176_, lean_object* v_toPure_2177_, lean_object* v_____do__lift_2178_){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_2174_, v_____do__lift_2178_, v_args_2175_, v_t_2176_);
v___x_2180_ = lean_apply_2(v_toPure_2177_, lean_box(0), v___x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(lean_object* v_pu_2181_, lean_object* v_args_2182_, lean_object* v_t_2183_, lean_object* v_toPure_2184_, lean_object* v_____do__lift_2185_){
_start:
{
uint8_t v_pu_boxed_2186_; uint8_t v_t_boxed_2187_; lean_object* v_res_2188_; 
v_pu_boxed_2186_ = lean_unbox(v_pu_2181_);
v_t_boxed_2187_ = lean_unbox(v_t_2183_);
v_res_2188_ = l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(v_pu_boxed_2186_, v_args_2182_, v_t_boxed_2187_, v_toPure_2184_, v_____do__lift_2185_);
lean_dec_ref(v_____do__lift_2185_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg(uint8_t v_pu_2189_, uint8_t v_t_2190_, lean_object* v_inst_2191_, lean_object* v_inst_2192_, lean_object* v_args_2193_){
_start:
{
lean_object* v_toApplicative_2194_; lean_object* v_toBind_2195_; lean_object* v_toPure_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___f_2199_; lean_object* v___x_2200_; 
v_toApplicative_2194_ = lean_ctor_get(v_inst_2192_, 0);
lean_inc_ref(v_toApplicative_2194_);
v_toBind_2195_ = lean_ctor_get(v_inst_2192_, 1);
lean_inc(v_toBind_2195_);
lean_dec_ref(v_inst_2192_);
v_toPure_2196_ = lean_ctor_get(v_toApplicative_2194_, 1);
lean_inc(v_toPure_2196_);
lean_dec_ref(v_toApplicative_2194_);
v___x_2197_ = lean_box(v_pu_2189_);
v___x_2198_ = lean_box(v_t_2190_);
v___f_2199_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2199_, 0, v___x_2197_);
lean_closure_set(v___f_2199_, 1, v_args_2193_);
lean_closure_set(v___f_2199_, 2, v___x_2198_);
lean_closure_set(v___f_2199_, 3, v_toPure_2196_);
v___x_2200_ = lean_apply_4(v_toBind_2195_, lean_box(0), lean_box(0), v_inst_2191_, v___f_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___boxed(lean_object* v_pu_2201_, lean_object* v_t_2202_, lean_object* v_inst_2203_, lean_object* v_inst_2204_, lean_object* v_args_2205_){
_start:
{
uint8_t v_pu_boxed_2206_; uint8_t v_t_boxed_2207_; lean_object* v_res_2208_; 
v_pu_boxed_2206_ = lean_unbox(v_pu_2201_);
v_t_boxed_2207_ = lean_unbox(v_t_2202_);
v_res_2208_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_boxed_2206_, v_t_boxed_2207_, v_inst_2203_, v_inst_2204_, v_args_2205_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs(lean_object* v_m_2209_, uint8_t v_pu_2210_, uint8_t v_t_2211_, lean_object* v_inst_2212_, lean_object* v_inst_2213_, lean_object* v_args_2214_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_2210_, v_t_2211_, v_inst_2212_, v_inst_2213_, v_args_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___boxed(lean_object* v_m_2216_, lean_object* v_pu_2217_, lean_object* v_t_2218_, lean_object* v_inst_2219_, lean_object* v_inst_2220_, lean_object* v_args_2221_){
_start:
{
uint8_t v_pu_boxed_2222_; uint8_t v_t_boxed_2223_; lean_object* v_res_2224_; 
v_pu_boxed_2222_ = lean_unbox(v_pu_2217_);
v_t_boxed_2223_ = lean_unbox(v_t_2218_);
v_res_2224_ = l_Lean_Compiler_LCNF_normArgs(v_m_2216_, v_pu_boxed_2222_, v_t_boxed_2223_, v_inst_2219_, v_inst_2220_, v_args_2221_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object* v_binderName_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v___x_2228_; lean_object* v_nextIdx_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v_lctx_2232_; lean_object* v_nextIdx_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2244_; 
v___x_2228_ = lean_st_ref_get(v_a_2226_);
v_nextIdx_2229_ = lean_ctor_get(v___x_2228_, 1);
lean_inc(v_nextIdx_2229_);
lean_dec(v___x_2228_);
v___x_2230_ = l_Lean_Name_num___override(v_binderName_2225_, v_nextIdx_2229_);
v___x_2231_ = lean_st_ref_take(v_a_2226_);
v_lctx_2232_ = lean_ctor_get(v___x_2231_, 0);
v_nextIdx_2233_ = lean_ctor_get(v___x_2231_, 1);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2235_ = v___x_2231_;
v_isShared_2236_ = v_isSharedCheck_2244_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_nextIdx_2233_);
lean_inc(v_lctx_2232_);
lean_dec(v___x_2231_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2244_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2240_; 
v___x_2237_ = lean_unsigned_to_nat(1u);
v___x_2238_ = lean_nat_add(v_nextIdx_2233_, v___x_2237_);
lean_dec(v_nextIdx_2233_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 1, v___x_2238_);
v___x_2240_ = v___x_2235_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_lctx_2232_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = lean_st_ref_put(v_a_2226_, v___x_2240_);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2230_);
return v___x_2242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(lean_object* v_binderName_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2245_, v_a_2246_);
lean_dec(v_a_2246_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object* v_binderName_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2249_, v_a_2251_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(lean_object* v_binderName_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_Compiler_LCNF_mkFreshBinderName(v_binderName_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
lean_dec(v_a_2260_);
lean_dec_ref(v_a_2259_);
lean_dec(v_a_2258_);
lean_dec_ref(v_a_2257_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(lean_object* v_binderName_2263_, lean_object* v_baseName_2264_, lean_object* v_a_2265_){
_start:
{
uint8_t v___x_2267_; 
v___x_2267_ = l_Lean_Name_isAnonymous(v_binderName_2263_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; 
lean_dec(v_baseName_2264_);
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v_binderName_2263_);
return v___x_2268_;
}
else
{
lean_object* v___x_2269_; 
lean_dec(v_binderName_2263_);
v___x_2269_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_baseName_2264_, v_a_2265_);
return v___x_2269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(lean_object* v_binderName_2270_, lean_object* v_baseName_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2270_, v_baseName_2271_, v_a_2272_);
lean_dec(v_a_2272_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous(lean_object* v_binderName_2275_, lean_object* v_baseName_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2275_, v_baseName_2276_, v_a_2278_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(lean_object* v_binderName_2283_, lean_object* v_baseName_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_Compiler_LCNF_ensureNotAnonymous(v_binderName_2283_, v_baseName_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; lean_object* v_ngen_2294_; lean_object* v_namePrefix_2295_; lean_object* v_idx_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2326_; 
v___x_2293_ = lean_st_ref_get(v___y_2291_);
v_ngen_2294_ = lean_ctor_get(v___x_2293_, 2);
lean_inc_ref(v_ngen_2294_);
lean_dec(v___x_2293_);
v_namePrefix_2295_ = lean_ctor_get(v_ngen_2294_, 0);
v_idx_2296_ = lean_ctor_get(v_ngen_2294_, 1);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_ngen_2294_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2298_ = v_ngen_2294_;
v_isShared_2299_ = v_isSharedCheck_2326_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_idx_2296_);
lean_inc(v_namePrefix_2295_);
lean_dec(v_ngen_2294_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2326_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v_r_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
lean_inc(v_idx_2296_);
lean_inc(v_namePrefix_2295_);
v_r_2300_ = l_Lean_Name_num___override(v_namePrefix_2295_, v_idx_2296_);
v___x_2301_ = lean_unsigned_to_nat(1u);
v___x_2302_ = lean_nat_add(v_idx_2296_, v___x_2301_);
lean_dec(v_idx_2296_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 1, v___x_2302_);
v___x_2304_ = v___x_2298_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_namePrefix_2295_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2305_; lean_object* v_env_2306_; lean_object* v_nextMacroScope_2307_; lean_object* v_auxDeclNGen_2308_; lean_object* v_traceState_2309_; lean_object* v_cache_2310_; lean_object* v_recordedDeps_2311_; lean_object* v_messages_2312_; lean_object* v_infoState_2313_; lean_object* v_snapshotTasks_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2323_; 
v___x_2305_ = lean_st_ref_take(v___y_2291_);
v_env_2306_ = lean_ctor_get(v___x_2305_, 0);
v_nextMacroScope_2307_ = lean_ctor_get(v___x_2305_, 1);
v_auxDeclNGen_2308_ = lean_ctor_get(v___x_2305_, 3);
v_traceState_2309_ = lean_ctor_get(v___x_2305_, 4);
v_cache_2310_ = lean_ctor_get(v___x_2305_, 5);
v_recordedDeps_2311_ = lean_ctor_get(v___x_2305_, 6);
v_messages_2312_ = lean_ctor_get(v___x_2305_, 7);
v_infoState_2313_ = lean_ctor_get(v___x_2305_, 8);
v_snapshotTasks_2314_ = lean_ctor_get(v___x_2305_, 9);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2323_ == 0)
{
lean_object* v_unused_2324_; 
v_unused_2324_ = lean_ctor_get(v___x_2305_, 2);
lean_dec(v_unused_2324_);
v___x_2316_ = v___x_2305_;
v_isShared_2317_ = v_isSharedCheck_2323_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_snapshotTasks_2314_);
lean_inc(v_infoState_2313_);
lean_inc(v_messages_2312_);
lean_inc(v_recordedDeps_2311_);
lean_inc(v_cache_2310_);
lean_inc(v_traceState_2309_);
lean_inc(v_auxDeclNGen_2308_);
lean_inc(v_nextMacroScope_2307_);
lean_inc(v_env_2306_);
lean_dec(v___x_2305_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2323_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 2, v___x_2304_);
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_env_2306_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_nextMacroScope_2307_);
lean_ctor_set(v_reuseFailAlloc_2322_, 2, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2322_, 3, v_auxDeclNGen_2308_);
lean_ctor_set(v_reuseFailAlloc_2322_, 4, v_traceState_2309_);
lean_ctor_set(v_reuseFailAlloc_2322_, 5, v_cache_2310_);
lean_ctor_set(v_reuseFailAlloc_2322_, 6, v_recordedDeps_2311_);
lean_ctor_set(v_reuseFailAlloc_2322_, 7, v_messages_2312_);
lean_ctor_set(v_reuseFailAlloc_2322_, 8, v_infoState_2313_);
lean_ctor_set(v_reuseFailAlloc_2322_, 9, v_snapshotTasks_2314_);
v___x_2319_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = lean_st_ref_put(v___y_2291_, v___x_2319_);
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v_r_2300_);
return v___x_2321_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2327_);
lean_dec(v___y_2327_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v___x_2335_; lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
v___x_2335_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2333_);
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t v_pu_2353_, lean_object* v_binderName_2354_, lean_object* v_type_2355_, uint8_t v_borrow_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2386_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref_known(v___x_2362_, 1);
v___x_2364_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_2365_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2354_, v___x_2364_, v_a_2358_);
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2368_ = v___x_2365_;
v_isShared_2369_ = v_isSharedCheck_2386_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2365_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2386_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v_lctx_2372_; lean_object* v_nextIdx_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2385_; 
v___x_2370_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2370_, 0, v_a_2363_);
lean_ctor_set(v___x_2370_, 1, v_a_2366_);
lean_ctor_set(v___x_2370_, 2, v_type_2355_);
lean_ctor_set_uint8(v___x_2370_, sizeof(void*)*3, v_borrow_2356_);
v___x_2371_ = lean_st_ref_take(v_a_2358_);
v_lctx_2372_ = lean_ctor_get(v___x_2371_, 0);
v_nextIdx_2373_ = lean_ctor_get(v___x_2371_, 1);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2375_ = v___x_2371_;
v_isShared_2376_ = v_isSharedCheck_2385_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_nextIdx_2373_);
lean_inc(v_lctx_2372_);
lean_dec(v___x_2371_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2385_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2379_; 
lean_inc_ref(v___x_2370_);
v___x_2377_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2353_, v_lctx_2372_, v___x_2370_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v___x_2377_);
v___x_2379_ = v___x_2375_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2377_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_nextIdx_2373_);
v___x_2379_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2380_ = lean_st_ref_put(v_a_2358_, v___x_2379_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2370_);
v___x_2382_ = v___x_2368_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2370_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec_ref(v_type_2355_);
lean_dec(v_binderName_2354_);
v_a_2387_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2362_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2362_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam___boxed(lean_object* v_pu_2395_, lean_object* v_binderName_2396_, lean_object* v_type_2397_, lean_object* v_borrow_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
uint8_t v_pu_boxed_2404_; uint8_t v_borrow_boxed_2405_; lean_object* v_res_2406_; 
v_pu_boxed_2404_ = lean_unbox(v_pu_2395_);
v_borrow_boxed_2405_ = lean_unbox(v_borrow_2398_);
v_res_2406_ = l_Lean_Compiler_LCNF_mkParam(v_pu_boxed_2404_, v_binderName_2396_, v_type_2397_, v_borrow_boxed_2405_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2410_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t v_pu_2422_, lean_object* v_binderName_2423_, lean_object* v_type_2424_, lean_object* v_value_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2455_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_a_2432_);
lean_dec_ref_known(v___x_2431_, 1);
v___x_2433_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2434_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2423_, v___x_2433_, v_a_2427_);
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2437_ = v___x_2434_;
v_isShared_2438_ = v_isSharedCheck_2455_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2434_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2455_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v_lctx_2441_; lean_object* v_nextIdx_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2454_; 
v___x_2439_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2439_, 0, v_a_2432_);
lean_ctor_set(v___x_2439_, 1, v_a_2435_);
lean_ctor_set(v___x_2439_, 2, v_type_2424_);
lean_ctor_set(v___x_2439_, 3, v_value_2425_);
v___x_2440_ = lean_st_ref_take(v_a_2427_);
v_lctx_2441_ = lean_ctor_get(v___x_2440_, 0);
v_nextIdx_2442_ = lean_ctor_get(v___x_2440_, 1);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2444_ = v___x_2440_;
v_isShared_2445_ = v_isSharedCheck_2454_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_nextIdx_2442_);
lean_inc(v_lctx_2441_);
lean_dec(v___x_2440_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2454_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
lean_inc_ref(v___x_2439_);
v___x_2446_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2422_, v_lctx_2441_, v___x_2439_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 0, v___x_2446_);
v___x_2448_ = v___x_2444_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_nextIdx_2442_);
v___x_2448_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; lean_object* v___x_2451_; 
v___x_2449_ = lean_st_ref_put(v_a_2427_, v___x_2448_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v___x_2439_);
v___x_2451_ = v___x_2437_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2439_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec(v_value_2425_);
lean_dec_ref(v_type_2424_);
lean_dec(v_binderName_2423_);
v_a_2456_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2431_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2431_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl___boxed(lean_object* v_pu_2464_, lean_object* v_binderName_2465_, lean_object* v_type_2466_, lean_object* v_value_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_){
_start:
{
uint8_t v_pu_boxed_2473_; lean_object* v_res_2474_; 
v_pu_boxed_2473_ = lean_unbox(v_pu_2464_);
v_res_2474_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_boxed_2473_, v_binderName_2465_, v_type_2466_, v_value_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t v_pu_2478_, lean_object* v_binderName_2479_, lean_object* v_type_2480_, lean_object* v_params_2481_, lean_object* v_value_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v___x_2488_; 
v___x_2488_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2512_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2489_);
lean_dec_ref_known(v___x_2488_, 1);
v___x_2490_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFunDecl___closed__1));
v___x_2491_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2479_, v___x_2490_, v_a_2484_);
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2494_ = v___x_2491_;
v_isShared_2495_ = v_isSharedCheck_2512_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2512_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v_lctx_2498_; lean_object* v_nextIdx_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2511_; 
v___x_2496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2496_, 0, v_a_2489_);
lean_ctor_set(v___x_2496_, 1, v_a_2492_);
lean_ctor_set(v___x_2496_, 2, v_params_2481_);
lean_ctor_set(v___x_2496_, 3, v_type_2480_);
lean_ctor_set(v___x_2496_, 4, v_value_2482_);
v___x_2497_ = lean_st_ref_take(v_a_2484_);
v_lctx_2498_ = lean_ctor_get(v___x_2497_, 0);
v_nextIdx_2499_ = lean_ctor_get(v___x_2497_, 1);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2501_ = v___x_2497_;
v_isShared_2502_ = v_isSharedCheck_2511_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_nextIdx_2499_);
lean_inc(v_lctx_2498_);
lean_dec(v___x_2497_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2511_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; lean_object* v___x_2505_; 
lean_inc_ref(v___x_2496_);
v___x_2503_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2478_, v_lctx_2498_, v___x_2496_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 0, v___x_2503_);
v___x_2505_ = v___x_2501_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2503_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_nextIdx_2499_);
v___x_2505_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2506_ = lean_st_ref_put(v_a_2484_, v___x_2505_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v___x_2496_);
v___x_2508_ = v___x_2494_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2496_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec_ref(v_value_2482_);
lean_dec_ref(v_params_2481_);
lean_dec_ref(v_type_2480_);
lean_dec(v_binderName_2479_);
v_a_2513_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2488_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2488_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl___boxed(lean_object* v_pu_2521_, lean_object* v_binderName_2522_, lean_object* v_type_2523_, lean_object* v_params_2524_, lean_object* v_value_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_){
_start:
{
uint8_t v_pu_boxed_2531_; lean_object* v_res_2532_; 
v_pu_boxed_2531_ = lean_unbox(v_pu_2521_);
v_res_2532_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_boxed_2531_, v_binderName_2522_, v_type_2523_, v_params_2524_, v_value_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t v_pu_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v_a_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2539_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2540_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2539_, v_a_2535_);
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2541_);
lean_dec_ref(v___x_2540_);
v___x_2542_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2543_ = lean_box(1);
v___x_2544_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2533_, v_a_2541_, v___x_2542_, v___x_2543_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(lean_object* v_pu_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
uint8_t v_pu_boxed_2551_; lean_object* v_res_2552_; 
v_pu_boxed_2551_ = lean_unbox(v_pu_2545_);
v_res_2552_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_boxed_2551_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t v_pu_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2570_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2570_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2570_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v_fvarId_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2568_; 
v_fvarId_2564_ = lean_ctor_get(v_a_2560_, 0);
lean_inc(v_fvarId_2564_);
v___x_2565_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2565_, 0, v_fvarId_2564_);
v___x_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2566_, 0, v_a_2560_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2566_);
v___x_2568_ = v___x_2562_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
v_a_2571_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___x_2559_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2559_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased___boxed(lean_object* v_pu_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
uint8_t v_pu_boxed_2585_; lean_object* v_res_2586_; 
v_pu_boxed_2585_ = lean_unbox(v_pu_2579_);
v_res_2586_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_boxed_2585_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_);
lean_dec(v_a_2583_);
lean_dec_ref(v_a_2582_);
lean_dec(v_a_2581_);
lean_dec_ref(v_a_2580_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t v_pu_2587_, lean_object* v_p_2588_, lean_object* v_type_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v_fvarId_2592_; lean_object* v_binderName_2593_; lean_object* v_type_2594_; uint8_t v_borrow_2595_; size_t v___x_2596_; size_t v___x_2597_; uint8_t v___x_2598_; 
v_fvarId_2592_ = lean_ctor_get(v_p_2588_, 0);
v_binderName_2593_ = lean_ctor_get(v_p_2588_, 1);
v_type_2594_ = lean_ctor_get(v_p_2588_, 2);
v_borrow_2595_ = lean_ctor_get_uint8(v_p_2588_, sizeof(void*)*3);
v___x_2596_ = lean_ptr_addr(v_type_2589_);
v___x_2597_ = lean_ptr_addr(v_type_2594_);
v___x_2598_ = lean_usize_dec_eq(v___x_2596_, v___x_2597_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2618_; 
lean_inc(v_binderName_2593_);
lean_inc(v_fvarId_2592_);
v_isSharedCheck_2618_ = !lean_is_exclusive(v_p_2588_);
if (v_isSharedCheck_2618_ == 0)
{
lean_object* v_unused_2619_; lean_object* v_unused_2620_; lean_object* v_unused_2621_; 
v_unused_2619_ = lean_ctor_get(v_p_2588_, 2);
lean_dec(v_unused_2619_);
v_unused_2620_ = lean_ctor_get(v_p_2588_, 1);
lean_dec(v_unused_2620_);
v_unused_2621_ = lean_ctor_get(v_p_2588_, 0);
lean_dec(v_unused_2621_);
v___x_2600_ = v_p_2588_;
v_isShared_2601_ = v_isSharedCheck_2618_;
goto v_resetjp_2599_;
}
else
{
lean_dec(v_p_2588_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2618_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v_p_2603_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 2, v_type_2589_);
v_p_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_fvarId_2592_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_binderName_2593_);
lean_ctor_set(v_reuseFailAlloc_2617_, 2, v_type_2589_);
lean_ctor_set_uint8(v_reuseFailAlloc_2617_, sizeof(void*)*3, v_borrow_2595_);
v_p_2603_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
lean_object* v___x_2604_; lean_object* v_lctx_2605_; lean_object* v_nextIdx_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2616_; 
v___x_2604_ = lean_st_ref_take(v_a_2590_);
v_lctx_2605_ = lean_ctor_get(v___x_2604_, 0);
v_nextIdx_2606_ = lean_ctor_get(v___x_2604_, 1);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2608_ = v___x_2604_;
v_isShared_2609_ = v_isSharedCheck_2616_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_nextIdx_2606_);
lean_inc(v_lctx_2605_);
lean_dec(v___x_2604_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2616_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2610_; lean_object* v___x_2612_; 
lean_inc_ref(v_p_2603_);
v___x_2610_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2587_, v_lctx_2605_, v_p_2603_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v___x_2610_);
v___x_2612_ = v___x_2608_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2610_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_nextIdx_2606_);
v___x_2612_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = lean_st_ref_put(v_a_2590_, v___x_2612_);
v___x_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2614_, 0, v_p_2603_);
return v___x_2614_;
}
}
}
}
}
else
{
lean_object* v___x_2622_; 
lean_dec_ref(v_type_2589_);
v___x_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2622_, 0, v_p_2588_);
return v___x_2622_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(lean_object* v_pu_2623_, lean_object* v_p_2624_, lean_object* v_type_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_){
_start:
{
uint8_t v_pu_boxed_2628_; lean_object* v_res_2629_; 
v_pu_boxed_2628_ = lean_unbox(v_pu_2623_);
v_res_2629_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_boxed_2628_, v_p_2624_, v_type_2625_, v_a_2626_);
lean_dec(v_a_2626_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(uint8_t v_pu_2630_, lean_object* v_p_2631_, lean_object* v_type_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_2630_, v_p_2631_, v_type_2632_, v_a_2634_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object* v_pu_2639_, lean_object* v_p_2640_, lean_object* v_type_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
uint8_t v_pu_boxed_2647_; lean_object* v_res_2648_; 
v_pu_boxed_2647_ = lean_unbox(v_pu_2639_);
v_res_2648_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(v_pu_boxed_2647_, v_p_2640_, v_type_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t v_pu_2649_, lean_object* v_p_2650_, uint8_t v_borrow_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v_fvarId_2654_; lean_object* v_binderName_2655_; lean_object* v_type_2656_; uint8_t v_borrow_2657_; 
v_fvarId_2654_ = lean_ctor_get(v_p_2650_, 0);
v_binderName_2655_ = lean_ctor_get(v_p_2650_, 1);
v_type_2656_ = lean_ctor_get(v_p_2650_, 2);
v_borrow_2657_ = lean_ctor_get_uint8(v_p_2650_, sizeof(void*)*3);
if (v_borrow_2657_ == 0)
{
if (v_borrow_2651_ == 0)
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v_p_2650_);
return v___x_2673_;
}
else
{
lean_inc_ref(v_type_2656_);
lean_inc(v_binderName_2655_);
lean_inc(v_fvarId_2654_);
lean_dec_ref(v_p_2650_);
goto v___jp_2658_;
}
}
else
{
if (v_borrow_2651_ == 0)
{
lean_inc_ref(v_type_2656_);
lean_inc(v_binderName_2655_);
lean_inc(v_fvarId_2654_);
lean_dec_ref(v_p_2650_);
goto v___jp_2658_;
}
else
{
lean_object* v___x_2674_; 
v___x_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2674_, 0, v_p_2650_);
return v___x_2674_;
}
}
v___jp_2658_:
{
lean_object* v_p_2659_; lean_object* v___x_2660_; lean_object* v_lctx_2661_; lean_object* v_nextIdx_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2672_; 
v_p_2659_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_p_2659_, 0, v_fvarId_2654_);
lean_ctor_set(v_p_2659_, 1, v_binderName_2655_);
lean_ctor_set(v_p_2659_, 2, v_type_2656_);
lean_ctor_set_uint8(v_p_2659_, sizeof(void*)*3, v_borrow_2651_);
v___x_2660_ = lean_st_ref_take(v_a_2652_);
v_lctx_2661_ = lean_ctor_get(v___x_2660_, 0);
v_nextIdx_2662_ = lean_ctor_get(v___x_2660_, 1);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2664_ = v___x_2660_;
v_isShared_2665_ = v_isSharedCheck_2672_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_nextIdx_2662_);
lean_inc(v_lctx_2661_);
lean_dec(v___x_2660_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2672_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2666_; lean_object* v___x_2668_; 
lean_inc_ref(v_p_2659_);
v___x_2666_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2649_, v_lctx_2661_, v_p_2659_);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v___x_2666_);
v___x_2668_ = v___x_2664_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_nextIdx_2662_);
v___x_2668_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = lean_st_ref_put(v_a_2652_, v___x_2668_);
v___x_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2670_, 0, v_p_2659_);
return v___x_2670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(lean_object* v_pu_2675_, lean_object* v_p_2676_, lean_object* v_borrow_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_){
_start:
{
uint8_t v_pu_boxed_2680_; uint8_t v_borrow_boxed_2681_; lean_object* v_res_2682_; 
v_pu_boxed_2680_ = lean_unbox(v_pu_2675_);
v_borrow_boxed_2681_ = lean_unbox(v_borrow_2677_);
v_res_2682_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_boxed_2680_, v_p_2676_, v_borrow_boxed_2681_, v_a_2678_);
lean_dec(v_a_2678_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(uint8_t v_pu_2683_, lean_object* v_p_2684_, uint8_t v_borrow_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_2683_, v_p_2684_, v_borrow_2685_, v_a_2687_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(lean_object* v_pu_2692_, lean_object* v_p_2693_, lean_object* v_borrow_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
uint8_t v_pu_boxed_2700_; uint8_t v_borrow_boxed_2701_; lean_object* v_res_2702_; 
v_pu_boxed_2700_ = lean_unbox(v_pu_2692_);
v_borrow_boxed_2701_ = lean_unbox(v_borrow_2694_);
v_res_2702_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(v_pu_boxed_2700_, v_p_2693_, v_borrow_boxed_2701_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
lean_dec(v_a_2698_);
lean_dec_ref(v_a_2697_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t v_pu_2703_, lean_object* v_decl_2704_, lean_object* v_type_2705_, lean_object* v_value_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v_fvarId_2709_; lean_object* v_binderName_2710_; lean_object* v_type_2711_; lean_object* v_value_2712_; size_t v___x_2728_; size_t v___x_2729_; uint8_t v___x_2730_; 
v_fvarId_2709_ = lean_ctor_get(v_decl_2704_, 0);
v_binderName_2710_ = lean_ctor_get(v_decl_2704_, 1);
v_type_2711_ = lean_ctor_get(v_decl_2704_, 2);
v_value_2712_ = lean_ctor_get(v_decl_2704_, 3);
v___x_2728_ = lean_ptr_addr(v_type_2705_);
v___x_2729_ = lean_ptr_addr(v_type_2711_);
v___x_2730_ = lean_usize_dec_eq(v___x_2728_, v___x_2729_);
if (v___x_2730_ == 0)
{
lean_inc(v_binderName_2710_);
lean_inc(v_fvarId_2709_);
lean_dec_ref(v_decl_2704_);
goto v___jp_2713_;
}
else
{
size_t v___x_2731_; size_t v___x_2732_; uint8_t v___x_2733_; 
v___x_2731_ = lean_ptr_addr(v_value_2706_);
v___x_2732_ = lean_ptr_addr(v_value_2712_);
v___x_2733_ = lean_usize_dec_eq(v___x_2731_, v___x_2732_);
if (v___x_2733_ == 0)
{
lean_inc(v_binderName_2710_);
lean_inc(v_fvarId_2709_);
lean_dec_ref(v_decl_2704_);
goto v___jp_2713_;
}
else
{
lean_object* v___x_2734_; 
lean_dec(v_value_2706_);
lean_dec_ref(v_type_2705_);
v___x_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2734_, 0, v_decl_2704_);
return v___x_2734_;
}
}
v___jp_2713_:
{
lean_object* v_decl_2714_; lean_object* v___x_2715_; lean_object* v_lctx_2716_; lean_object* v_nextIdx_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2727_; 
v_decl_2714_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_decl_2714_, 0, v_fvarId_2709_);
lean_ctor_set(v_decl_2714_, 1, v_binderName_2710_);
lean_ctor_set(v_decl_2714_, 2, v_type_2705_);
lean_ctor_set(v_decl_2714_, 3, v_value_2706_);
v___x_2715_ = lean_st_ref_take(v_a_2707_);
v_lctx_2716_ = lean_ctor_get(v___x_2715_, 0);
v_nextIdx_2717_ = lean_ctor_get(v___x_2715_, 1);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2719_ = v___x_2715_;
v_isShared_2720_ = v_isSharedCheck_2727_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_nextIdx_2717_);
lean_inc(v_lctx_2716_);
lean_dec(v___x_2715_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2727_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2721_; lean_object* v___x_2723_; 
lean_inc_ref(v_decl_2714_);
v___x_2721_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2703_, v_lctx_2716_, v_decl_2714_);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v___x_2721_);
v___x_2723_ = v___x_2719_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2721_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_nextIdx_2717_);
v___x_2723_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = lean_st_ref_put(v_a_2707_, v___x_2723_);
v___x_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2725_, 0, v_decl_2714_);
return v___x_2725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(lean_object* v_pu_2735_, lean_object* v_decl_2736_, lean_object* v_type_2737_, lean_object* v_value_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_){
_start:
{
uint8_t v_pu_boxed_2741_; lean_object* v_res_2742_; 
v_pu_boxed_2741_ = lean_unbox(v_pu_2735_);
v_res_2742_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_boxed_2741_, v_decl_2736_, v_type_2737_, v_value_2738_, v_a_2739_);
lean_dec(v_a_2739_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(uint8_t v_pu_2743_, lean_object* v_decl_2744_, lean_object* v_type_2745_, lean_object* v_value_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2743_, v_decl_2744_, v_type_2745_, v_value_2746_, v_a_2748_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object* v_pu_2753_, lean_object* v_decl_2754_, lean_object* v_type_2755_, lean_object* v_value_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
uint8_t v_pu_boxed_2762_; lean_object* v_res_2763_; 
v_pu_boxed_2762_ = lean_unbox(v_pu_2753_);
v_res_2763_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(v_pu_boxed_2762_, v_decl_2754_, v_type_2755_, v_value_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec_ref(v_a_2757_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t v_pu_2764_, lean_object* v_decl_2765_, lean_object* v_value_2766_, lean_object* v_a_2767_){
_start:
{
lean_object* v_type_2769_; lean_object* v___x_2770_; 
v_type_2769_ = lean_ctor_get(v_decl_2765_, 2);
lean_inc_ref(v_type_2769_);
v___x_2770_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2764_, v_decl_2765_, v_type_2769_, v_value_2766_, v_a_2767_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(lean_object* v_pu_2771_, lean_object* v_decl_2772_, lean_object* v_value_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_){
_start:
{
uint8_t v_pu_boxed_2776_; lean_object* v_res_2777_; 
v_pu_boxed_2776_ = lean_unbox(v_pu_2771_);
v_res_2777_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_boxed_2776_, v_decl_2772_, v_value_2773_, v_a_2774_);
lean_dec(v_a_2774_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(uint8_t v_pu_2778_, lean_object* v_decl_2779_, lean_object* v_value_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_2778_, v_decl_2779_, v_value_2780_, v_a_2782_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(lean_object* v_pu_2787_, lean_object* v_decl_2788_, lean_object* v_value_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
uint8_t v_pu_boxed_2795_; lean_object* v_res_2796_; 
v_pu_boxed_2795_ = lean_unbox(v_pu_2787_);
v_res_2796_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(v_pu_boxed_2795_, v_decl_2788_, v_value_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t v_pu_2797_, lean_object* v_decl_2798_, lean_object* v_type_2799_, lean_object* v_params_2800_, lean_object* v_value_2801_, lean_object* v_a_2802_){
_start:
{
lean_object* v_fvarId_2804_; lean_object* v_binderName_2805_; lean_object* v_params_2806_; lean_object* v_type_2807_; lean_object* v_value_2808_; size_t v___x_2824_; size_t v___x_2825_; uint8_t v___x_2826_; 
v_fvarId_2804_ = lean_ctor_get(v_decl_2798_, 0);
v_binderName_2805_ = lean_ctor_get(v_decl_2798_, 1);
v_params_2806_ = lean_ctor_get(v_decl_2798_, 2);
v_type_2807_ = lean_ctor_get(v_decl_2798_, 3);
v_value_2808_ = lean_ctor_get(v_decl_2798_, 4);
v___x_2824_ = lean_ptr_addr(v_type_2799_);
v___x_2825_ = lean_ptr_addr(v_type_2807_);
v___x_2826_ = lean_usize_dec_eq(v___x_2824_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_inc(v_binderName_2805_);
lean_inc(v_fvarId_2804_);
lean_dec_ref(v_decl_2798_);
goto v___jp_2809_;
}
else
{
size_t v___x_2827_; size_t v___x_2828_; uint8_t v___x_2829_; 
v___x_2827_ = lean_ptr_addr(v_params_2800_);
v___x_2828_ = lean_ptr_addr(v_params_2806_);
v___x_2829_ = lean_usize_dec_eq(v___x_2827_, v___x_2828_);
if (v___x_2829_ == 0)
{
lean_inc(v_binderName_2805_);
lean_inc(v_fvarId_2804_);
lean_dec_ref(v_decl_2798_);
goto v___jp_2809_;
}
else
{
size_t v___x_2830_; size_t v___x_2831_; uint8_t v___x_2832_; 
v___x_2830_ = lean_ptr_addr(v_value_2801_);
v___x_2831_ = lean_ptr_addr(v_value_2808_);
v___x_2832_ = lean_usize_dec_eq(v___x_2830_, v___x_2831_);
if (v___x_2832_ == 0)
{
lean_inc(v_binderName_2805_);
lean_inc(v_fvarId_2804_);
lean_dec_ref(v_decl_2798_);
goto v___jp_2809_;
}
else
{
lean_object* v___x_2833_; 
lean_dec_ref(v_value_2801_);
lean_dec_ref(v_params_2800_);
lean_dec_ref(v_type_2799_);
v___x_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2833_, 0, v_decl_2798_);
return v___x_2833_;
}
}
}
v___jp_2809_:
{
lean_object* v_decl_2810_; lean_object* v___x_2811_; lean_object* v_lctx_2812_; lean_object* v_nextIdx_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2823_; 
v_decl_2810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_decl_2810_, 0, v_fvarId_2804_);
lean_ctor_set(v_decl_2810_, 1, v_binderName_2805_);
lean_ctor_set(v_decl_2810_, 2, v_params_2800_);
lean_ctor_set(v_decl_2810_, 3, v_type_2799_);
lean_ctor_set(v_decl_2810_, 4, v_value_2801_);
v___x_2811_ = lean_st_ref_take(v_a_2802_);
v_lctx_2812_ = lean_ctor_get(v___x_2811_, 0);
v_nextIdx_2813_ = lean_ctor_get(v___x_2811_, 1);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2815_ = v___x_2811_;
v_isShared_2816_ = v_isSharedCheck_2823_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_nextIdx_2813_);
lean_inc(v_lctx_2812_);
lean_dec(v___x_2811_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2823_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2817_; lean_object* v___x_2819_; 
lean_inc_ref(v_decl_2810_);
v___x_2817_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2797_, v_lctx_2812_, v_decl_2810_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2817_);
v___x_2819_ = v___x_2815_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2817_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_nextIdx_2813_);
v___x_2819_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = lean_st_ref_put(v_a_2802_, v___x_2819_);
v___x_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2821_, 0, v_decl_2810_);
return v___x_2821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(lean_object* v_pu_2834_, lean_object* v_decl_2835_, lean_object* v_type_2836_, lean_object* v_params_2837_, lean_object* v_value_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
uint8_t v_pu_boxed_2841_; lean_object* v_res_2842_; 
v_pu_boxed_2841_ = lean_unbox(v_pu_2834_);
v_res_2842_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_boxed_2841_, v_decl_2835_, v_type_2836_, v_params_2837_, v_value_2838_, v_a_2839_);
lean_dec(v_a_2839_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(uint8_t v_pu_2843_, lean_object* v_decl_2844_, lean_object* v_type_2845_, lean_object* v_params_2846_, lean_object* v_value_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2843_, v_decl_2844_, v_type_2845_, v_params_2846_, v_value_2847_, v_a_2849_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object* v_pu_2854_, lean_object* v_decl_2855_, lean_object* v_type_2856_, lean_object* v_params_2857_, lean_object* v_value_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
uint8_t v_pu_boxed_2864_; lean_object* v_res_2865_; 
v_pu_boxed_2864_ = lean_unbox(v_pu_2854_);
v_res_2865_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(v_pu_boxed_2864_, v_decl_2855_, v_type_2856_, v_params_2857_, v_value_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_);
lean_dec(v_a_2862_);
lean_dec_ref(v_a_2861_);
lean_dec(v_a_2860_);
lean_dec_ref(v_a_2859_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(uint8_t v_pu_2866_, lean_object* v_decl_2867_, lean_object* v_type_2868_, lean_object* v_value_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v_params_2872_; lean_object* v___x_2873_; 
v_params_2872_ = lean_ctor_get(v_decl_2867_, 2);
lean_inc_ref(v_params_2872_);
v___x_2873_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2866_, v_decl_2867_, v_type_2868_, v_params_2872_, v_value_2869_, v_a_2870_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(lean_object* v_pu_2874_, lean_object* v_decl_2875_, lean_object* v_type_2876_, lean_object* v_value_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_){
_start:
{
uint8_t v_pu_boxed_2880_; lean_object* v_res_2881_; 
v_pu_boxed_2880_ = lean_unbox(v_pu_2874_);
v_res_2881_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(v_pu_boxed_2880_, v_decl_2875_, v_type_2876_, v_value_2877_, v_a_2878_);
lean_dec(v_a_2878_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27(uint8_t v_pu_2882_, lean_object* v_decl_2883_, lean_object* v_type_2884_, lean_object* v_value_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v_params_2891_; lean_object* v___x_2892_; 
v_params_2891_ = lean_ctor_get(v_decl_2883_, 2);
lean_inc_ref(v_params_2891_);
v___x_2892_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2882_, v_decl_2883_, v_type_2884_, v_params_2891_, v_value_2885_, v_a_2887_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(lean_object* v_pu_2893_, lean_object* v_decl_2894_, lean_object* v_type_2895_, lean_object* v_value_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_){
_start:
{
uint8_t v_pu_boxed_2902_; lean_object* v_res_2903_; 
v_pu_boxed_2902_ = lean_unbox(v_pu_2893_);
v_res_2903_ = l_Lean_Compiler_LCNF_FunDecl_update_x27(v_pu_boxed_2902_, v_decl_2894_, v_type_2895_, v_value_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(uint8_t v_pu_2904_, lean_object* v_decl_2905_, lean_object* v_value_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_params_2909_; lean_object* v_type_2910_; lean_object* v___x_2911_; 
v_params_2909_ = lean_ctor_get(v_decl_2905_, 2);
lean_inc_ref(v_params_2909_);
v_type_2910_ = lean_ctor_get(v_decl_2905_, 3);
lean_inc_ref(v_type_2910_);
v___x_2911_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2904_, v_decl_2905_, v_type_2910_, v_params_2909_, v_value_2906_, v_a_2907_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(lean_object* v_pu_2912_, lean_object* v_decl_2913_, lean_object* v_value_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_){
_start:
{
uint8_t v_pu_boxed_2917_; lean_object* v_res_2918_; 
v_pu_boxed_2917_ = lean_unbox(v_pu_2912_);
v_res_2918_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(v_pu_boxed_2917_, v_decl_2913_, v_value_2914_, v_a_2915_);
lean_dec(v_a_2915_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue(uint8_t v_pu_2919_, lean_object* v_decl_2920_, lean_object* v_value_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_){
_start:
{
lean_object* v_params_2927_; lean_object* v_type_2928_; lean_object* v___x_2929_; 
v_params_2927_ = lean_ctor_get(v_decl_2920_, 2);
lean_inc_ref(v_params_2927_);
v_type_2928_ = lean_ctor_get(v_decl_2920_, 3);
lean_inc_ref(v_type_2928_);
v___x_2929_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2919_, v_decl_2920_, v_type_2928_, v_params_2927_, v_value_2921_, v_a_2923_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(lean_object* v_pu_2930_, lean_object* v_decl_2931_, lean_object* v_value_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_){
_start:
{
uint8_t v_pu_boxed_2938_; lean_object* v_res_2939_; 
v_pu_boxed_2938_ = lean_unbox(v_pu_2930_);
v_res_2939_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(v_pu_boxed_2938_, v_decl_2931_, v_value_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_);
lean_dec(v_a_2936_);
lean_dec_ref(v_a_2935_);
lean_dec(v_a_2934_);
lean_dec_ref(v_a_2933_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0(uint8_t v_pu_2940_, lean_object* v_p_2941_, lean_object* v_inst_2942_, lean_object* v_____do__lift_2943_){
_start:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2944_ = lean_box(v_pu_2940_);
v___x_2945_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_2945_, 0, v___x_2944_);
lean_closure_set(v___x_2945_, 1, v_p_2941_);
lean_closure_set(v___x_2945_, 2, v_____do__lift_2943_);
v___x_2946_ = lean_apply_2(v_inst_2942_, lean_box(0), v___x_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(lean_object* v_pu_2947_, lean_object* v_p_2948_, lean_object* v_inst_2949_, lean_object* v_____do__lift_2950_){
_start:
{
uint8_t v_pu_boxed_2951_; lean_object* v_res_2952_; 
v_pu_boxed_2951_ = lean_unbox(v_pu_2947_);
v_res_2952_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__0(v_pu_boxed_2951_, v_p_2948_, v_inst_2949_, v_____do__lift_2950_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1(uint8_t v_pu_2953_, uint8_t v_t_2954_, lean_object* v_type_2955_, lean_object* v_toPure_2956_, lean_object* v_____do__lift_2957_){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2953_, v_____do__lift_2957_, v_t_2954_, v_type_2955_);
v___x_2959_ = lean_apply_2(v_toPure_2956_, lean_box(0), v___x_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(lean_object* v_pu_2960_, lean_object* v_t_2961_, lean_object* v_type_2962_, lean_object* v_toPure_2963_, lean_object* v_____do__lift_2964_){
_start:
{
uint8_t v_pu_boxed_2965_; uint8_t v_t_boxed_2966_; lean_object* v_res_2967_; 
v_pu_boxed_2965_ = lean_unbox(v_pu_2960_);
v_t_boxed_2966_ = lean_unbox(v_t_2961_);
v_res_2967_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(v_pu_boxed_2965_, v_t_boxed_2966_, v_type_2962_, v_toPure_2963_, v_____do__lift_2964_);
lean_dec_ref(v_____do__lift_2964_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg(uint8_t v_pu_2968_, uint8_t v_t_2969_, lean_object* v_inst_2970_, lean_object* v_inst_2971_, lean_object* v_inst_2972_, lean_object* v_p_2973_){
_start:
{
lean_object* v_toApplicative_2974_; lean_object* v_toBind_2975_; lean_object* v_type_2976_; lean_object* v_toPure_2977_; lean_object* v___x_2978_; lean_object* v___f_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___f_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v_toApplicative_2974_ = lean_ctor_get(v_inst_2971_, 0);
lean_inc_ref(v_toApplicative_2974_);
v_toBind_2975_ = lean_ctor_get(v_inst_2971_, 1);
lean_inc_n(v_toBind_2975_, 2);
lean_dec_ref(v_inst_2971_);
v_type_2976_ = lean_ctor_get(v_p_2973_, 2);
lean_inc_ref(v_type_2976_);
v_toPure_2977_ = lean_ctor_get(v_toApplicative_2974_, 1);
lean_inc(v_toPure_2977_);
lean_dec_ref(v_toApplicative_2974_);
v___x_2978_ = lean_box(v_pu_2968_);
v___f_2979_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2979_, 0, v___x_2978_);
lean_closure_set(v___f_2979_, 1, v_p_2973_);
lean_closure_set(v___f_2979_, 2, v_inst_2970_);
v___x_2980_ = lean_box(v_pu_2968_);
v___x_2981_ = lean_box(v_t_2969_);
v___f_2982_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2982_, 0, v___x_2980_);
lean_closure_set(v___f_2982_, 1, v___x_2981_);
lean_closure_set(v___f_2982_, 2, v_type_2976_);
lean_closure_set(v___f_2982_, 3, v_toPure_2977_);
v___x_2983_ = lean_apply_4(v_toBind_2975_, lean_box(0), lean_box(0), v_inst_2972_, v___f_2982_);
v___x_2984_ = lean_apply_4(v_toBind_2975_, lean_box(0), lean_box(0), v___x_2983_, v___f_2979_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___boxed(lean_object* v_pu_2985_, lean_object* v_t_2986_, lean_object* v_inst_2987_, lean_object* v_inst_2988_, lean_object* v_inst_2989_, lean_object* v_p_2990_){
_start:
{
uint8_t v_pu_boxed_2991_; uint8_t v_t_boxed_2992_; lean_object* v_res_2993_; 
v_pu_boxed_2991_ = lean_unbox(v_pu_2985_);
v_t_boxed_2992_ = lean_unbox(v_t_2986_);
v_res_2993_ = l_Lean_Compiler_LCNF_normParam___redArg(v_pu_boxed_2991_, v_t_boxed_2992_, v_inst_2987_, v_inst_2988_, v_inst_2989_, v_p_2990_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam(lean_object* v_m_2994_, uint8_t v_pu_2995_, uint8_t v_t_2996_, lean_object* v_inst_2997_, lean_object* v_inst_2998_, lean_object* v_inst_2999_, lean_object* v_p_3000_){
_start:
{
lean_object* v_toApplicative_3001_; lean_object* v_toBind_3002_; lean_object* v_type_3003_; lean_object* v_toPure_3004_; lean_object* v___x_3005_; lean_object* v___f_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___f_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v_toApplicative_3001_ = lean_ctor_get(v_inst_2998_, 0);
lean_inc_ref(v_toApplicative_3001_);
v_toBind_3002_ = lean_ctor_get(v_inst_2998_, 1);
lean_inc_n(v_toBind_3002_, 2);
lean_dec_ref(v_inst_2998_);
v_type_3003_ = lean_ctor_get(v_p_3000_, 2);
lean_inc_ref(v_type_3003_);
v_toPure_3004_ = lean_ctor_get(v_toApplicative_3001_, 1);
lean_inc(v_toPure_3004_);
lean_dec_ref(v_toApplicative_3001_);
v___x_3005_ = lean_box(v_pu_2995_);
v___f_3006_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3006_, 0, v___x_3005_);
lean_closure_set(v___f_3006_, 1, v_p_3000_);
lean_closure_set(v___f_3006_, 2, v_inst_2997_);
v___x_3007_ = lean_box(v_pu_2995_);
v___x_3008_ = lean_box(v_t_2996_);
v___f_3009_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3009_, 0, v___x_3007_);
lean_closure_set(v___f_3009_, 1, v___x_3008_);
lean_closure_set(v___f_3009_, 2, v_type_3003_);
lean_closure_set(v___f_3009_, 3, v_toPure_3004_);
v___x_3010_ = lean_apply_4(v_toBind_3002_, lean_box(0), lean_box(0), v_inst_2999_, v___f_3009_);
v___x_3011_ = lean_apply_4(v_toBind_3002_, lean_box(0), lean_box(0), v___x_3010_, v___f_3006_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___boxed(lean_object* v_m_3012_, lean_object* v_pu_3013_, lean_object* v_t_3014_, lean_object* v_inst_3015_, lean_object* v_inst_3016_, lean_object* v_inst_3017_, lean_object* v_p_3018_){
_start:
{
uint8_t v_pu_boxed_3019_; uint8_t v_t_boxed_3020_; lean_object* v_res_3021_; 
v_pu_boxed_3019_ = lean_unbox(v_pu_3013_);
v_t_boxed_3020_ = lean_unbox(v_t_3014_);
v_res_3021_ = l_Lean_Compiler_LCNF_normParam(v_m_3012_, v_pu_boxed_3019_, v_t_boxed_3020_, v_inst_3015_, v_inst_3016_, v_inst_3017_, v_p_3018_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg(uint8_t v_pu_3022_, uint8_t v_t_3023_, lean_object* v_inst_3024_, lean_object* v_inst_3025_, lean_object* v_inst_3026_, lean_object* v_ps_3027_){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3028_ = lean_box(v_pu_3022_);
v___x_3029_ = lean_box(v_t_3023_);
lean_inc_ref(v_inst_3025_);
v___x_3030_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___boxed), 7, 6);
lean_closure_set(v___x_3030_, 0, lean_box(0));
lean_closure_set(v___x_3030_, 1, v___x_3028_);
lean_closure_set(v___x_3030_, 2, v___x_3029_);
lean_closure_set(v___x_3030_, 3, v_inst_3024_);
lean_closure_set(v___x_3030_, 4, v_inst_3025_);
lean_closure_set(v___x_3030_, 5, v_inst_3026_);
v___x_3031_ = lean_unsigned_to_nat(0u);
v___x_3032_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_3025_, v___x_3030_, v___x_3031_, v_ps_3027_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg___boxed(lean_object* v_pu_3033_, lean_object* v_t_3034_, lean_object* v_inst_3035_, lean_object* v_inst_3036_, lean_object* v_inst_3037_, lean_object* v_ps_3038_){
_start:
{
uint8_t v_pu_boxed_3039_; uint8_t v_t_boxed_3040_; lean_object* v_res_3041_; 
v_pu_boxed_3039_ = lean_unbox(v_pu_3033_);
v_t_boxed_3040_ = lean_unbox(v_t_3034_);
v_res_3041_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_boxed_3039_, v_t_boxed_3040_, v_inst_3035_, v_inst_3036_, v_inst_3037_, v_ps_3038_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams(lean_object* v_m_3042_, uint8_t v_pu_3043_, uint8_t v_t_3044_, lean_object* v_inst_3045_, lean_object* v_inst_3046_, lean_object* v_inst_3047_, lean_object* v_ps_3048_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_3043_, v_t_3044_, v_inst_3045_, v_inst_3046_, v_inst_3047_, v_ps_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___boxed(lean_object* v_m_3050_, lean_object* v_pu_3051_, lean_object* v_t_3052_, lean_object* v_inst_3053_, lean_object* v_inst_3054_, lean_object* v_inst_3055_, lean_object* v_ps_3056_){
_start:
{
uint8_t v_pu_boxed_3057_; uint8_t v_t_boxed_3058_; lean_object* v_res_3059_; 
v_pu_boxed_3057_ = lean_unbox(v_pu_3051_);
v_t_boxed_3058_ = lean_unbox(v_t_3052_);
v_res_3059_ = l_Lean_Compiler_LCNF_normParams(v_m_3050_, v_pu_boxed_3057_, v_t_boxed_3058_, v_inst_3053_, v_inst_3054_, v_inst_3055_, v_ps_3056_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(uint8_t v_pu_3060_, lean_object* v_decl_3061_, lean_object* v_____do__lift_3062_, lean_object* v_inst_3063_, lean_object* v_____do__lift_3064_){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = lean_box(v_pu_3060_);
v___x_3066_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_3066_, 0, v___x_3065_);
lean_closure_set(v___x_3066_, 1, v_decl_3061_);
lean_closure_set(v___x_3066_, 2, v_____do__lift_3062_);
lean_closure_set(v___x_3066_, 3, v_____do__lift_3064_);
v___x_3067_ = lean_apply_2(v_inst_3063_, lean_box(0), v___x_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(lean_object* v_pu_3068_, lean_object* v_decl_3069_, lean_object* v_____do__lift_3070_, lean_object* v_inst_3071_, lean_object* v_____do__lift_3072_){
_start:
{
uint8_t v_pu_boxed_3073_; lean_object* v_res_3074_; 
v_pu_boxed_3073_ = lean_unbox(v_pu_3068_);
v_res_3074_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(v_pu_boxed_3073_, v_decl_3069_, v_____do__lift_3070_, v_inst_3071_, v_____do__lift_3072_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(uint8_t v_pu_3075_, lean_object* v_value_3076_, uint8_t v_t_3077_, lean_object* v_toPure_3078_, lean_object* v_____do__lift_3079_){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3075_, v_____do__lift_3079_, v_value_3076_, v_t_3077_);
v___x_3081_ = lean_apply_2(v_toPure_3078_, lean_box(0), v___x_3080_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(lean_object* v_pu_3082_, lean_object* v_value_3083_, lean_object* v_t_3084_, lean_object* v_toPure_3085_, lean_object* v_____do__lift_3086_){
_start:
{
uint8_t v_pu_boxed_3087_; uint8_t v_t_boxed_3088_; lean_object* v_res_3089_; 
v_pu_boxed_3087_ = lean_unbox(v_pu_3082_);
v_t_boxed_3088_ = lean_unbox(v_t_3084_);
v_res_3089_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(v_pu_boxed_3087_, v_value_3083_, v_t_boxed_3088_, v_toPure_3085_, v_____do__lift_3086_);
lean_dec_ref(v_____do__lift_3086_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(uint8_t v_pu_3090_, lean_object* v_decl_3091_, lean_object* v_inst_3092_, lean_object* v_value_3093_, uint8_t v_t_3094_, lean_object* v_toPure_3095_, lean_object* v_toBind_3096_, lean_object* v_inst_3097_, lean_object* v_____do__lift_3098_){
_start:
{
lean_object* v___x_3099_; lean_object* v___f_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___f_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3099_ = lean_box(v_pu_3090_);
v___f_3100_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3100_, 0, v___x_3099_);
lean_closure_set(v___f_3100_, 1, v_decl_3091_);
lean_closure_set(v___f_3100_, 2, v_____do__lift_3098_);
lean_closure_set(v___f_3100_, 3, v_inst_3092_);
v___x_3101_ = lean_box(v_pu_3090_);
v___x_3102_ = lean_box(v_t_3094_);
v___f_3103_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3103_, 0, v___x_3101_);
lean_closure_set(v___f_3103_, 1, v_value_3093_);
lean_closure_set(v___f_3103_, 2, v___x_3102_);
lean_closure_set(v___f_3103_, 3, v_toPure_3095_);
lean_inc(v_toBind_3096_);
v___x_3104_ = lean_apply_4(v_toBind_3096_, lean_box(0), lean_box(0), v_inst_3097_, v___f_3103_);
v___x_3105_ = lean_apply_4(v_toBind_3096_, lean_box(0), lean_box(0), v___x_3104_, v___f_3100_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(lean_object* v_pu_3106_, lean_object* v_decl_3107_, lean_object* v_inst_3108_, lean_object* v_value_3109_, lean_object* v_t_3110_, lean_object* v_toPure_3111_, lean_object* v_toBind_3112_, lean_object* v_inst_3113_, lean_object* v_____do__lift_3114_){
_start:
{
uint8_t v_pu_boxed_3115_; uint8_t v_t_boxed_3116_; lean_object* v_res_3117_; 
v_pu_boxed_3115_ = lean_unbox(v_pu_3106_);
v_t_boxed_3116_ = lean_unbox(v_t_3110_);
v_res_3117_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(v_pu_boxed_3115_, v_decl_3107_, v_inst_3108_, v_value_3109_, v_t_boxed_3116_, v_toPure_3111_, v_toBind_3112_, v_inst_3113_, v_____do__lift_3114_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg(uint8_t v_pu_3118_, uint8_t v_t_3119_, lean_object* v_inst_3120_, lean_object* v_inst_3121_, lean_object* v_inst_3122_, lean_object* v_decl_3123_){
_start:
{
lean_object* v_toApplicative_3124_; lean_object* v_toBind_3125_; lean_object* v_type_3126_; lean_object* v_value_3127_; lean_object* v_toPure_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___f_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___f_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v_toApplicative_3124_ = lean_ctor_get(v_inst_3121_, 0);
lean_inc_ref(v_toApplicative_3124_);
v_toBind_3125_ = lean_ctor_get(v_inst_3121_, 1);
lean_inc_n(v_toBind_3125_, 3);
lean_dec_ref(v_inst_3121_);
v_type_3126_ = lean_ctor_get(v_decl_3123_, 2);
lean_inc_ref(v_type_3126_);
v_value_3127_ = lean_ctor_get(v_decl_3123_, 3);
lean_inc(v_value_3127_);
v_toPure_3128_ = lean_ctor_get(v_toApplicative_3124_, 1);
lean_inc_n(v_toPure_3128_, 2);
lean_dec_ref(v_toApplicative_3124_);
v___x_3129_ = lean_box(v_pu_3118_);
v___x_3130_ = lean_box(v_t_3119_);
lean_inc(v_inst_3122_);
v___f_3131_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_3131_, 0, v___x_3129_);
lean_closure_set(v___f_3131_, 1, v_decl_3123_);
lean_closure_set(v___f_3131_, 2, v_inst_3120_);
lean_closure_set(v___f_3131_, 3, v_value_3127_);
lean_closure_set(v___f_3131_, 4, v___x_3130_);
lean_closure_set(v___f_3131_, 5, v_toPure_3128_);
lean_closure_set(v___f_3131_, 6, v_toBind_3125_);
lean_closure_set(v___f_3131_, 7, v_inst_3122_);
v___x_3132_ = lean_box(v_pu_3118_);
v___x_3133_ = lean_box(v_t_3119_);
v___f_3134_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3134_, 0, v___x_3132_);
lean_closure_set(v___f_3134_, 1, v___x_3133_);
lean_closure_set(v___f_3134_, 2, v_type_3126_);
lean_closure_set(v___f_3134_, 3, v_toPure_3128_);
v___x_3135_ = lean_apply_4(v_toBind_3125_, lean_box(0), lean_box(0), v_inst_3122_, v___f_3134_);
v___x_3136_ = lean_apply_4(v_toBind_3125_, lean_box(0), lean_box(0), v___x_3135_, v___f_3131_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(lean_object* v_pu_3137_, lean_object* v_t_3138_, lean_object* v_inst_3139_, lean_object* v_inst_3140_, lean_object* v_inst_3141_, lean_object* v_decl_3142_){
_start:
{
uint8_t v_pu_boxed_3143_; uint8_t v_t_boxed_3144_; lean_object* v_res_3145_; 
v_pu_boxed_3143_ = lean_unbox(v_pu_3137_);
v_t_boxed_3144_ = lean_unbox(v_t_3138_);
v_res_3145_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_boxed_3143_, v_t_boxed_3144_, v_inst_3139_, v_inst_3140_, v_inst_3141_, v_decl_3142_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl(lean_object* v_m_3146_, uint8_t v_pu_3147_, uint8_t v_t_3148_, lean_object* v_inst_3149_, lean_object* v_inst_3150_, lean_object* v_inst_3151_, lean_object* v_decl_3152_){
_start:
{
lean_object* v___x_3153_; 
v___x_3153_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_3147_, v_t_3148_, v_inst_3149_, v_inst_3150_, v_inst_3151_, v_decl_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___boxed(lean_object* v_m_3154_, lean_object* v_pu_3155_, lean_object* v_t_3156_, lean_object* v_inst_3157_, lean_object* v_inst_3158_, lean_object* v_inst_3159_, lean_object* v_decl_3160_){
_start:
{
uint8_t v_pu_boxed_3161_; uint8_t v_t_boxed_3162_; lean_object* v_res_3163_; 
v_pu_boxed_3161_ = lean_unbox(v_pu_3155_);
v_t_boxed_3162_ = lean_unbox(v_t_3156_);
v_res_3163_ = l_Lean_Compiler_LCNF_normLetDecl(v_m_3154_, v_pu_boxed_3161_, v_t_boxed_3162_, v_inst_3157_, v_inst_3158_, v_inst_3159_, v_decl_3160_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg(){
_start:
{
lean_object* v___x_3165_; lean_object* v_toApplicative_3166_; lean_object* v_toFunctor_3167_; lean_object* v_toSeq_3168_; lean_object* v_toSeqLeft_3169_; lean_object* v_toSeqRight_3170_; lean_object* v___f_3171_; lean_object* v___f_3172_; lean_object* v___f_3173_; lean_object* v___f_3174_; lean_object* v___x_3175_; lean_object* v___f_3176_; lean_object* v___f_3177_; lean_object* v___f_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v_toApplicative_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3210_; 
v___x_3165_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_3166_ = lean_ctor_get(v___x_3165_, 0);
v_toFunctor_3167_ = lean_ctor_get(v_toApplicative_3166_, 0);
v_toSeq_3168_ = lean_ctor_get(v_toApplicative_3166_, 2);
v_toSeqLeft_3169_ = lean_ctor_get(v_toApplicative_3166_, 3);
v_toSeqRight_3170_ = lean_ctor_get(v_toApplicative_3166_, 4);
v___f_3171_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_3172_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_3167_, 2);
v___f_3173_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3173_, 0, v_toFunctor_3167_);
v___f_3174_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3174_, 0, v_toFunctor_3167_);
v___x_3175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___f_3173_);
lean_ctor_set(v___x_3175_, 1, v___f_3174_);
lean_inc(v_toSeqRight_3170_);
v___f_3176_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3176_, 0, v_toSeqRight_3170_);
lean_inc(v_toSeqLeft_3169_);
v___f_3177_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3177_, 0, v_toSeqLeft_3169_);
lean_inc(v_toSeq_3168_);
v___f_3178_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3178_, 0, v_toSeq_3168_);
v___x_3179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3175_);
lean_ctor_set(v___x_3179_, 1, v___f_3171_);
lean_ctor_set(v___x_3179_, 2, v___f_3178_);
lean_ctor_set(v___x_3179_, 3, v___f_3177_);
lean_ctor_set(v___x_3179_, 4, v___f_3176_);
v___x_3180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
lean_ctor_set(v___x_3180_, 1, v___f_3172_);
v___x_3181_ = l_StateRefT_x27_instMonad___redArg(v___x_3180_);
v_toApplicative_3182_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3210_ == 0)
{
lean_object* v_unused_3211_; 
v_unused_3211_ = lean_ctor_get(v___x_3181_, 1);
lean_dec(v_unused_3211_);
v___x_3184_ = v___x_3181_;
v_isShared_3185_ = v_isSharedCheck_3210_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_toApplicative_3182_);
lean_dec(v___x_3181_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3210_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v_toFunctor_3186_; lean_object* v_toSeq_3187_; lean_object* v_toSeqLeft_3188_; lean_object* v_toSeqRight_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3208_; 
v_toFunctor_3186_ = lean_ctor_get(v_toApplicative_3182_, 0);
v_toSeq_3187_ = lean_ctor_get(v_toApplicative_3182_, 2);
v_toSeqLeft_3188_ = lean_ctor_get(v_toApplicative_3182_, 3);
v_toSeqRight_3189_ = lean_ctor_get(v_toApplicative_3182_, 4);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_toApplicative_3182_);
if (v_isSharedCheck_3208_ == 0)
{
lean_object* v_unused_3209_; 
v_unused_3209_ = lean_ctor_get(v_toApplicative_3182_, 1);
lean_dec(v_unused_3209_);
v___x_3191_ = v_toApplicative_3182_;
v_isShared_3192_ = v_isSharedCheck_3208_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_toSeqRight_3189_);
lean_inc(v_toSeqLeft_3188_);
lean_inc(v_toSeq_3187_);
lean_inc(v_toFunctor_3186_);
lean_dec(v_toApplicative_3182_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3208_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___f_3193_; lean_object* v___f_3194_; lean_object* v___f_3195_; lean_object* v___f_3196_; lean_object* v___x_3197_; lean_object* v___f_3198_; lean_object* v___f_3199_; lean_object* v___f_3200_; lean_object* v___x_3202_; 
v___f_3193_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_3194_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_3186_);
v___f_3195_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3195_, 0, v_toFunctor_3186_);
v___f_3196_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3196_, 0, v_toFunctor_3186_);
v___x_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___f_3195_);
lean_ctor_set(v___x_3197_, 1, v___f_3196_);
v___f_3198_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3198_, 0, v_toSeqRight_3189_);
v___f_3199_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3199_, 0, v_toSeqLeft_3188_);
v___f_3200_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3200_, 0, v_toSeq_3187_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 4, v___f_3198_);
lean_ctor_set(v___x_3191_, 3, v___f_3199_);
lean_ctor_set(v___x_3191_, 2, v___f_3200_);
lean_ctor_set(v___x_3191_, 1, v___f_3193_);
lean_ctor_set(v___x_3191_, 0, v___x_3197_);
v___x_3202_ = v___x_3191_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3197_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v___f_3193_);
lean_ctor_set(v_reuseFailAlloc_3207_, 2, v___f_3200_);
lean_ctor_set(v_reuseFailAlloc_3207_, 3, v___f_3199_);
lean_ctor_set(v_reuseFailAlloc_3207_, 4, v___f_3198_);
v___x_3202_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
lean_object* v___x_3204_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 1, v___f_3194_);
lean_ctor_set(v___x_3184_, 0, v___x_3202_);
v___x_3204_ = v___x_3184_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v___f_3194_);
v___x_3204_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
lean_object* v___x_3205_; 
v___x_3205_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_3205_, 0, lean_box(0));
lean_closure_set(v___x_3205_, 1, lean_box(0));
lean_closure_set(v___x_3205_, 2, v___x_3204_);
return v___x_3205_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg___boxed(lean_object* v___dummy_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg();
return v_res_3213_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0(void){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg();
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(uint8_t v_pu_3215_, uint8_t v_t_3216_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0, &l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0_once, _init_l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(lean_object* v_pu_3218_, lean_object* v_t_3219_){
_start:
{
uint8_t v_pu_boxed_3220_; uint8_t v_t_boxed_3221_; lean_object* v_res_3222_; 
v_pu_boxed_3220_ = lean_unbox(v_pu_3218_);
v_t_boxed_3221_ = lean_unbox(v_t_3219_);
v_res_3222_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_boxed_3220_, v_t_boxed_3221_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg(uint8_t v_pu_3223_, lean_object* v_inst_3224_, lean_object* v_result_3225_, lean_object* v_x_3226_){
_start:
{
if (lean_obj_tag(v_result_3225_) == 0)
{
lean_object* v_fvarId_3227_; lean_object* v___x_3228_; 
lean_dec(v_inst_3224_);
v_fvarId_3227_ = lean_ctor_get(v_result_3225_, 0);
lean_inc(v_fvarId_3227_);
lean_dec_ref_known(v_result_3225_, 1);
v___x_3228_ = lean_apply_1(v_x_3226_, v_fvarId_3227_);
return v___x_3228_;
}
else
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
lean_dec(v_x_3226_);
v___x_3229_ = lean_box(v_pu_3223_);
v___x_3230_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3230_, 0, v___x_3229_);
v___x_3231_ = lean_apply_2(v_inst_3224_, lean_box(0), v___x_3230_);
return v___x_3231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(lean_object* v_pu_3232_, lean_object* v_inst_3233_, lean_object* v_result_3234_, lean_object* v_x_3235_){
_start:
{
uint8_t v_pu_boxed_3236_; lean_object* v_res_3237_; 
v_pu_boxed_3236_ = lean_unbox(v_pu_3232_);
v_res_3237_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(v_pu_boxed_3236_, v_inst_3233_, v_result_3234_, v_x_3235_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult(lean_object* v_m_3238_, uint8_t v_pu_3239_, lean_object* v_inst_3240_, lean_object* v_inst_3241_, lean_object* v_result_3242_, lean_object* v_x_3243_){
_start:
{
if (lean_obj_tag(v_result_3242_) == 0)
{
lean_object* v_fvarId_3244_; lean_object* v___x_3245_; 
lean_dec(v_inst_3240_);
v_fvarId_3244_ = lean_ctor_get(v_result_3242_, 0);
lean_inc(v_fvarId_3244_);
lean_dec_ref_known(v_result_3242_, 1);
v___x_3245_ = lean_apply_1(v_x_3243_, v_fvarId_3244_);
return v___x_3245_;
}
else
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
lean_dec(v_x_3243_);
v___x_3246_ = lean_box(v_pu_3239_);
v___x_3247_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3247_, 0, v___x_3246_);
v___x_3248_ = lean_apply_2(v_inst_3240_, lean_box(0), v___x_3247_);
return v___x_3248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___boxed(lean_object* v_m_3249_, lean_object* v_pu_3250_, lean_object* v_inst_3251_, lean_object* v_inst_3252_, lean_object* v_result_3253_, lean_object* v_x_3254_){
_start:
{
uint8_t v_pu_boxed_3255_; lean_object* v_res_3256_; 
v_pu_boxed_3255_ = lean_unbox(v_pu_3250_);
v_res_3256_ = l_Lean_Compiler_LCNF_withNormFVarResult(v_m_3249_, v_pu_boxed_3255_, v_inst_3251_, v_inst_3252_, v_result_3253_, v_x_3254_);
lean_dec_ref(v_inst_3252_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(uint8_t v_pu_3257_, uint8_t v_t_3258_, lean_object* v_args_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_3257_, v___y_3260_, v_args_3259_, v_t_3258_);
v___x_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(lean_object* v_pu_3264_, lean_object* v_t_3265_, lean_object* v_args_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
uint8_t v_pu_boxed_3269_; uint8_t v_t_boxed_3270_; lean_object* v_res_3271_; 
v_pu_boxed_3269_ = lean_unbox(v_pu_3264_);
v_t_boxed_3270_ = lean_unbox(v_t_3265_);
v_res_3271_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_boxed_3269_, v_t_boxed_3270_, v_args_3266_, v___y_3267_);
lean_dec_ref(v___y_3267_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(uint8_t v_pu_3272_, uint8_t v_t_3273_, lean_object* v_i_3274_, lean_object* v_as_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v___x_3279_; uint8_t v___x_3280_; 
v___x_3279_ = lean_array_get_size(v_as_3275_);
v___x_3280_ = lean_nat_dec_lt(v_i_3274_, v___x_3279_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3281_; 
lean_dec(v_i_3274_);
v___x_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3281_, 0, v_as_3275_);
return v___x_3281_;
}
else
{
lean_object* v_a_3282_; lean_object* v_type_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v_a_3282_ = lean_array_fget_borrowed(v_as_3275_, v_i_3274_);
v_type_3283_ = lean_ctor_get(v_a_3282_, 2);
lean_inc_ref(v_type_3283_);
v___x_3284_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3272_, v___y_3276_, v_t_3273_, v_type_3283_);
lean_inc(v_a_3282_);
v___x_3285_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_3272_, v_a_3282_, v___x_3284_, v___y_3277_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; size_t v___x_3287_; size_t v___x_3288_; uint8_t v___x_3289_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
lean_dec_ref_known(v___x_3285_, 1);
v___x_3287_ = lean_ptr_addr(v_a_3282_);
v___x_3288_ = lean_ptr_addr(v_a_3286_);
v___x_3289_ = lean_usize_dec_eq(v___x_3287_, v___x_3288_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3290_ = lean_unsigned_to_nat(1u);
v___x_3291_ = lean_nat_add(v_i_3274_, v___x_3290_);
v___x_3292_ = lean_array_fset(v_as_3275_, v_i_3274_, v_a_3286_);
lean_dec(v_i_3274_);
v_i_3274_ = v___x_3291_;
v_as_3275_ = v___x_3292_;
goto _start;
}
else
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
lean_dec(v_a_3286_);
v___x_3294_ = lean_unsigned_to_nat(1u);
v___x_3295_ = lean_nat_add(v_i_3274_, v___x_3294_);
lean_dec(v_i_3274_);
v_i_3274_ = v___x_3295_;
goto _start;
}
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_dec_ref(v_as_3275_);
lean_dec(v_i_3274_);
v_a_3297_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3285_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3285_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(lean_object* v_pu_3305_, lean_object* v_t_3306_, lean_object* v_i_3307_, lean_object* v_as_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
uint8_t v_pu_boxed_3312_; uint8_t v_t_boxed_3313_; lean_object* v_res_3314_; 
v_pu_boxed_3312_ = lean_unbox(v_pu_3305_);
v_t_boxed_3313_ = lean_unbox(v_t_3306_);
v_res_3314_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_boxed_3312_, v_t_boxed_3313_, v_i_3307_, v_as_3308_, v___y_3309_, v___y_3310_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(uint8_t v_pu_3315_, uint8_t v_t_3316_, lean_object* v_ps_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = lean_unsigned_to_nat(0u);
v___x_3325_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_3315_, v_t_3316_, v___x_3324_, v_ps_3317_, v___y_3318_, v___y_3320_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(lean_object* v_pu_3326_, lean_object* v_t_3327_, lean_object* v_ps_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
uint8_t v_pu_boxed_3335_; uint8_t v_t_boxed_3336_; lean_object* v_res_3337_; 
v_pu_boxed_3335_ = lean_unbox(v_pu_3326_);
v_t_boxed_3336_ = lean_unbox(v_t_3327_);
v_res_3337_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_boxed_3335_, v_t_boxed_3336_, v_ps_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec_ref(v___y_3329_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(uint8_t v_pu_3338_, uint8_t v_t_3339_, lean_object* v_decl_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_type_3344_; lean_object* v_value_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v_type_3344_ = lean_ctor_get(v_decl_3340_, 2);
v_value_3345_ = lean_ctor_get(v_decl_3340_, 3);
lean_inc_ref(v_type_3344_);
v___x_3346_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3338_, v___y_3341_, v_t_3339_, v_type_3344_);
lean_inc(v_value_3345_);
v___x_3347_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3338_, v___y_3341_, v_value_3345_, v_t_3339_);
v___x_3348_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_3338_, v_decl_3340_, v___x_3346_, v___x_3347_, v___y_3342_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(lean_object* v_pu_3349_, lean_object* v_t_3350_, lean_object* v_decl_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
uint8_t v_pu_boxed_3355_; uint8_t v_t_boxed_3356_; lean_object* v_res_3357_; 
v_pu_boxed_3355_ = lean_unbox(v_pu_3349_);
v_t_boxed_3356_ = lean_unbox(v_t_3350_);
v_res_3357_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_boxed_3355_, v_t_boxed_3356_, v_decl_3351_, v___y_3352_, v___y_3353_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(uint8_t v_pu_3358_, uint8_t v_t_3359_, lean_object* v_i_3360_, lean_object* v_as_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v___x_3368_; uint8_t v___x_3369_; 
v___x_3368_ = lean_array_get_size(v_as_3361_);
v___x_3369_ = lean_nat_dec_lt(v_i_3360_, v___x_3368_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; 
lean_dec(v_i_3360_);
v___x_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3370_, 0, v_as_3361_);
return v___x_3370_;
}
else
{
lean_object* v_a_3371_; lean_object* v_a_3373_; 
v_a_3371_ = lean_array_fget_borrowed(v_as_3361_, v_i_3360_);
switch(lean_obj_tag(v_a_3371_))
{
case 0:
{
lean_object* v_params_3384_; lean_object* v_code_3385_; lean_object* v___x_3386_; 
v_params_3384_ = lean_ctor_get(v_a_3371_, 1);
v_code_3385_ = lean_ctor_get(v_a_3371_, 2);
lean_inc_ref(v_params_3384_);
v___x_3386_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_3358_, v_t_3359_, v_params_3384_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3388_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3386_, 1);
lean_inc_ref(v_code_3385_);
v___x_3388_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3358_, v_t_3359_, v_code_3385_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3390_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3388_, 1);
lean_inc_ref(v_a_3371_);
v___x_3390_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_3358_, v_a_3371_, v_a_3387_, v_a_3389_);
v_a_3373_ = v___x_3390_;
goto v___jp_3372_;
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec(v_a_3387_);
lean_dec_ref(v_as_3361_);
lean_dec(v_i_3360_);
v_a_3391_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3388_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3388_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
else
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec_ref(v_as_3361_);
lean_dec(v_i_3360_);
v_a_3399_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3386_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3386_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
case 1:
{
lean_object* v_code_3407_; lean_object* v___x_3408_; 
v_code_3407_ = lean_ctor_get(v_a_3371_, 1);
lean_inc_ref(v_code_3407_);
v___x_3408_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3358_, v_t_3359_, v_code_3407_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3410_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref_known(v___x_3408_, 1);
lean_inc_ref(v_a_3371_);
v___x_3410_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3371_, v_a_3409_);
v_a_3373_ = v___x_3410_;
goto v___jp_3372_;
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec_ref(v_as_3361_);
lean_dec(v_i_3360_);
v_a_3411_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3408_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3408_);
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
default: 
{
lean_object* v_code_3419_; lean_object* v___x_3420_; 
v_code_3419_ = lean_ctor_get(v_a_3371_, 0);
lean_inc_ref(v_code_3419_);
v___x_3420_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3358_, v_t_3359_, v_code_3419_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; lean_object* v___x_3422_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref_known(v___x_3420_, 1);
lean_inc_ref(v_a_3371_);
v___x_3422_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3371_, v_a_3421_);
v_a_3373_ = v___x_3422_;
goto v___jp_3372_;
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec_ref(v_as_3361_);
lean_dec(v_i_3360_);
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
}
v___jp_3372_:
{
size_t v___x_3374_; size_t v___x_3375_; uint8_t v___x_3376_; 
v___x_3374_ = lean_ptr_addr(v_a_3371_);
v___x_3375_ = lean_ptr_addr(v_a_3373_);
v___x_3376_ = lean_usize_dec_eq(v___x_3374_, v___x_3375_);
if (v___x_3376_ == 0)
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3377_ = lean_unsigned_to_nat(1u);
v___x_3378_ = lean_nat_add(v_i_3360_, v___x_3377_);
v___x_3379_ = lean_array_fset(v_as_3361_, v_i_3360_, v_a_3373_);
lean_dec(v_i_3360_);
v_i_3360_ = v___x_3378_;
v_as_3361_ = v___x_3379_;
goto _start;
}
else
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
lean_dec_ref(v_a_3373_);
v___x_3381_ = lean_unsigned_to_nat(1u);
v___x_3382_ = lean_nat_add(v_i_3360_, v___x_3381_);
lean_dec(v_i_3360_);
v_i_3360_ = v___x_3382_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t v_pu_3431_, uint8_t v_t_3432_, lean_object* v_code_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_){
_start:
{
switch(lean_obj_tag(v_code_3433_))
{
case 0:
{
lean_object* v_decl_3440_; lean_object* v_k_3441_; lean_object* v___x_3442_; 
v_decl_3440_ = lean_ctor_get(v_code_3433_, 0);
v_k_3441_ = lean_ctor_get(v_code_3433_, 1);
lean_inc_ref(v_decl_3440_);
v___x_3442_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_3431_, v_t_3432_, v_decl_3440_, v_a_3434_, v_a_3436_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; lean_object* v___x_3444_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_a_3443_);
lean_dec_ref_known(v___x_3442_, 1);
lean_inc_ref(v_k_3441_);
v___x_3444_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3431_, v_t_3432_, v_k_3441_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3482_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3447_ = v___x_3444_;
v_isShared_3448_ = v_isSharedCheck_3482_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3444_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3482_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
size_t v___x_3449_; size_t v___x_3450_; uint8_t v___x_3451_; 
v___x_3449_ = lean_ptr_addr(v_k_3441_);
v___x_3450_ = lean_ptr_addr(v_a_3445_);
v___x_3451_ = lean_usize_dec_eq(v___x_3449_, v___x_3450_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3461_; 
v_isSharedCheck_3461_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3461_ == 0)
{
lean_object* v_unused_3462_; lean_object* v_unused_3463_; 
v_unused_3462_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3462_);
v_unused_3463_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3463_);
v___x_3453_ = v_code_3433_;
v_isShared_3454_ = v_isSharedCheck_3461_;
goto v_resetjp_3452_;
}
else
{
lean_dec(v_code_3433_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3461_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 1, v_a_3445_);
lean_ctor_set(v___x_3453_, 0, v_a_3443_);
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3443_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v_a_3445_);
v___x_3456_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3458_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v___x_3456_);
v___x_3458_ = v___x_3447_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3456_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
else
{
size_t v___x_3464_; size_t v___x_3465_; uint8_t v___x_3466_; 
v___x_3464_ = lean_ptr_addr(v_decl_3440_);
v___x_3465_ = lean_ptr_addr(v_a_3443_);
v___x_3466_ = lean_usize_dec_eq(v___x_3464_, v___x_3465_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3476_; 
v_isSharedCheck_3476_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3476_ == 0)
{
lean_object* v_unused_3477_; lean_object* v_unused_3478_; 
v_unused_3477_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3477_);
v_unused_3478_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3478_);
v___x_3468_ = v_code_3433_;
v_isShared_3469_ = v_isSharedCheck_3476_;
goto v_resetjp_3467_;
}
else
{
lean_dec(v_code_3433_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3476_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 1, v_a_3445_);
lean_ctor_set(v___x_3468_, 0, v_a_3443_);
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3443_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v_a_3445_);
v___x_3471_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
lean_object* v___x_3473_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v___x_3471_);
v___x_3473_ = v___x_3447_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
else
{
lean_object* v___x_3480_; 
lean_dec(v_a_3445_);
lean_dec(v_a_3443_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v_code_3433_);
v___x_3480_ = v___x_3447_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_code_3433_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
}
else
{
lean_dec(v_a_3443_);
lean_dec_ref_known(v_code_3433_, 2);
return v___x_3444_;
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec_ref_known(v_code_3433_, 2);
v_a_3483_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3442_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3442_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
case 1:
{
lean_object* v_decl_3491_; lean_object* v_k_3492_; lean_object* v___x_3493_; 
v_decl_3491_ = lean_ctor_get(v_code_3433_, 0);
v_k_3492_ = lean_ctor_get(v_code_3433_, 1);
lean_inc_ref(v_decl_3491_);
v___x_3493_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3431_, v_t_3432_, v_decl_3491_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3495_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref_known(v___x_3493_, 1);
lean_inc_ref(v_k_3492_);
v___x_3495_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3431_, v_t_3432_, v_k_3492_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3533_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3498_ = v___x_3495_;
v_isShared_3499_ = v_isSharedCheck_3533_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3495_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3533_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
size_t v___x_3500_; size_t v___x_3501_; uint8_t v___x_3502_; 
v___x_3500_ = lean_ptr_addr(v_k_3492_);
v___x_3501_ = lean_ptr_addr(v_a_3496_);
v___x_3502_ = lean_usize_dec_eq(v___x_3500_, v___x_3501_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3512_; 
v_isSharedCheck_3512_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3512_ == 0)
{
lean_object* v_unused_3513_; lean_object* v_unused_3514_; 
v_unused_3513_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3513_);
v_unused_3514_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3514_);
v___x_3504_ = v_code_3433_;
v_isShared_3505_ = v_isSharedCheck_3512_;
goto v_resetjp_3503_;
}
else
{
lean_dec(v_code_3433_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3512_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 1, v_a_3496_);
lean_ctor_set(v___x_3504_, 0, v_a_3494_);
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3494_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_a_3496_);
v___x_3507_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
lean_object* v___x_3509_; 
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3507_);
v___x_3509_ = v___x_3498_;
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
size_t v___x_3515_; size_t v___x_3516_; uint8_t v___x_3517_; 
v___x_3515_ = lean_ptr_addr(v_decl_3491_);
v___x_3516_ = lean_ptr_addr(v_a_3494_);
v___x_3517_ = lean_usize_dec_eq(v___x_3515_, v___x_3516_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3527_; 
v_isSharedCheck_3527_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3527_ == 0)
{
lean_object* v_unused_3528_; lean_object* v_unused_3529_; 
v_unused_3528_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3528_);
v_unused_3529_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3529_);
v___x_3519_ = v_code_3433_;
v_isShared_3520_ = v_isSharedCheck_3527_;
goto v_resetjp_3518_;
}
else
{
lean_dec(v_code_3433_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3527_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 1, v_a_3496_);
lean_ctor_set(v___x_3519_, 0, v_a_3494_);
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3494_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v_a_3496_);
v___x_3522_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
lean_object* v___x_3524_; 
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3522_);
v___x_3524_ = v___x_3498_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
else
{
lean_object* v___x_3531_; 
lean_dec(v_a_3496_);
lean_dec(v_a_3494_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v_code_3433_);
v___x_3531_ = v___x_3498_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_code_3433_);
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
}
else
{
lean_dec(v_a_3494_);
lean_dec_ref_known(v_code_3433_, 2);
return v___x_3495_;
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_dec_ref_known(v_code_3433_, 2);
v_a_3534_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3493_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3493_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
case 2:
{
lean_object* v_decl_3542_; lean_object* v_k_3543_; lean_object* v___x_3544_; 
v_decl_3542_ = lean_ctor_get(v_code_3433_, 0);
v_k_3543_ = lean_ctor_get(v_code_3433_, 1);
lean_inc_ref(v_decl_3542_);
v___x_3544_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3431_, v_t_3432_, v_decl_3542_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v___x_3546_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_a_3545_);
lean_dec_ref_known(v___x_3544_, 1);
lean_inc_ref(v_k_3543_);
v___x_3546_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3431_, v_t_3432_, v_k_3543_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3584_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3549_ = v___x_3546_;
v_isShared_3550_ = v_isSharedCheck_3584_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3546_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3584_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
size_t v___x_3551_; size_t v___x_3552_; uint8_t v___x_3553_; 
v___x_3551_ = lean_ptr_addr(v_k_3543_);
v___x_3552_ = lean_ptr_addr(v_a_3547_);
v___x_3553_ = lean_usize_dec_eq(v___x_3551_, v___x_3552_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3563_; 
v_isSharedCheck_3563_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3563_ == 0)
{
lean_object* v_unused_3564_; lean_object* v_unused_3565_; 
v_unused_3564_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3564_);
v_unused_3565_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3565_);
v___x_3555_ = v_code_3433_;
v_isShared_3556_ = v_isSharedCheck_3563_;
goto v_resetjp_3554_;
}
else
{
lean_dec(v_code_3433_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3563_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 1, v_a_3547_);
lean_ctor_set(v___x_3555_, 0, v_a_3545_);
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3545_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v_a_3547_);
v___x_3558_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
lean_object* v___x_3560_; 
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3558_);
v___x_3560_ = v___x_3549_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3558_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
else
{
size_t v___x_3566_; size_t v___x_3567_; uint8_t v___x_3568_; 
v___x_3566_ = lean_ptr_addr(v_decl_3542_);
v___x_3567_ = lean_ptr_addr(v_a_3545_);
v___x_3568_ = lean_usize_dec_eq(v___x_3566_, v___x_3567_);
if (v___x_3568_ == 0)
{
lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3578_; 
v_isSharedCheck_3578_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3578_ == 0)
{
lean_object* v_unused_3579_; lean_object* v_unused_3580_; 
v_unused_3579_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3579_);
v_unused_3580_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3580_);
v___x_3570_ = v_code_3433_;
v_isShared_3571_ = v_isSharedCheck_3578_;
goto v_resetjp_3569_;
}
else
{
lean_dec(v_code_3433_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3578_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 1, v_a_3547_);
lean_ctor_set(v___x_3570_, 0, v_a_3545_);
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3545_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v_a_3547_);
v___x_3573_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
lean_object* v___x_3575_; 
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3573_);
v___x_3575_ = v___x_3549_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3573_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
else
{
lean_object* v___x_3582_; 
lean_dec(v_a_3547_);
lean_dec(v_a_3545_);
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v_code_3433_);
v___x_3582_ = v___x_3549_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_code_3433_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
}
else
{
lean_dec(v_a_3545_);
lean_dec_ref_known(v_code_3433_, 2);
return v___x_3546_;
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_dec_ref_known(v_code_3433_, 2);
v_a_3585_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_3544_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3544_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3593_; lean_object* v_args_3594_; lean_object* v___x_3595_; 
v_fvarId_3593_ = lean_ctor_get(v_code_3433_, 0);
v_args_3594_ = lean_ctor_get(v_code_3433_, 1);
lean_inc(v_fvarId_3593_);
v___x_3595_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3434_, v_fvarId_3593_, v_t_3432_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_fvarId_3596_; lean_object* v___x_3597_; 
v_fvarId_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_fvarId_3596_);
lean_dec_ref_known(v___x_3595_, 1);
lean_inc_ref(v_args_3594_);
v___x_3597_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_3431_, v_t_3432_, v_args_3594_, v_a_3434_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3633_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3633_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3633_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
uint8_t v___x_3602_; 
v___x_3602_ = l_Lean_instBEqFVarId_beq(v_fvarId_3593_, v_fvarId_3596_);
if (v___x_3602_ == 0)
{
lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3612_; 
v_isSharedCheck_3612_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3612_ == 0)
{
lean_object* v_unused_3613_; lean_object* v_unused_3614_; 
v_unused_3613_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3613_);
v_unused_3614_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3614_);
v___x_3604_ = v_code_3433_;
v_isShared_3605_ = v_isSharedCheck_3612_;
goto v_resetjp_3603_;
}
else
{
lean_dec(v_code_3433_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3612_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 1, v_a_3598_);
lean_ctor_set(v___x_3604_, 0, v_fvarId_3596_);
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_fvarId_3596_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_a_3598_);
v___x_3607_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3609_; 
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3607_);
v___x_3609_ = v___x_3600_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3607_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
else
{
size_t v___x_3615_; size_t v___x_3616_; uint8_t v___x_3617_; 
v___x_3615_ = lean_ptr_addr(v_args_3594_);
v___x_3616_ = lean_ptr_addr(v_a_3598_);
v___x_3617_ = lean_usize_dec_eq(v___x_3615_, v___x_3616_);
if (v___x_3617_ == 0)
{
lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3627_; 
v_isSharedCheck_3627_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3627_ == 0)
{
lean_object* v_unused_3628_; lean_object* v_unused_3629_; 
v_unused_3628_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3628_);
v_unused_3629_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3629_);
v___x_3619_ = v_code_3433_;
v_isShared_3620_ = v_isSharedCheck_3627_;
goto v_resetjp_3618_;
}
else
{
lean_dec(v_code_3433_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3627_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 1, v_a_3598_);
lean_ctor_set(v___x_3619_, 0, v_fvarId_3596_);
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_fvarId_3596_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_a_3598_);
v___x_3622_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
lean_object* v___x_3624_; 
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3622_);
v___x_3624_ = v___x_3600_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3622_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
else
{
lean_object* v___x_3631_; 
lean_dec(v_a_3598_);
lean_dec(v_fvarId_3596_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v_code_3433_);
v___x_3631_ = v___x_3600_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_code_3433_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
}
else
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
lean_dec(v_fvarId_3596_);
lean_dec_ref_known(v_code_3433_, 2);
v_a_3634_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v___x_3597_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3597_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3634_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
else
{
lean_object* v___x_3642_; 
lean_dec_ref_known(v_code_3433_, 2);
v___x_3642_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3431_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
return v___x_3642_;
}
}
case 4:
{
lean_object* v_cases_3643_; lean_object* v_typeName_3644_; lean_object* v_resultType_3645_; lean_object* v_discr_3646_; lean_object* v_alts_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3692_; 
v_cases_3643_ = lean_ctor_get(v_code_3433_, 0);
lean_inc_ref(v_cases_3643_);
v_typeName_3644_ = lean_ctor_get(v_cases_3643_, 0);
v_resultType_3645_ = lean_ctor_get(v_cases_3643_, 1);
v_discr_3646_ = lean_ctor_get(v_cases_3643_, 2);
v_alts_3647_ = lean_ctor_get(v_cases_3643_, 3);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_cases_3643_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3649_ = v_cases_3643_;
v_isShared_3650_ = v_isSharedCheck_3692_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_alts_3647_);
lean_inc(v_discr_3646_);
lean_inc(v_resultType_3645_);
lean_inc(v_typeName_3644_);
lean_dec(v_cases_3643_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3692_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; 
lean_inc_ref(v_resultType_3645_);
v___x_3651_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3431_, v_a_3434_, v_t_3432_, v_resultType_3645_);
lean_inc(v_discr_3646_);
v___x_3652_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3434_, v_discr_3646_, v_t_3432_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_fvarId_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3690_; 
v_fvarId_3653_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3655_ = v___x_3652_;
v_isShared_3656_ = v_isSharedCheck_3690_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_fvarId_3653_);
lean_dec(v___x_3652_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3690_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3647_);
v___x_3658_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_3431_, v_t_3432_, v___x_3657_, v_alts_3647_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3681_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3661_ = v___x_3658_;
v_isShared_3662_ = v_isSharedCheck_3681_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3658_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3681_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
size_t v___x_3673_; size_t v___x_3674_; uint8_t v___x_3675_; 
v___x_3673_ = lean_ptr_addr(v_alts_3647_);
lean_dec_ref(v_alts_3647_);
v___x_3674_ = lean_ptr_addr(v_a_3659_);
v___x_3675_ = lean_usize_dec_eq(v___x_3673_, v___x_3674_);
if (v___x_3675_ == 0)
{
lean_dec(v_discr_3646_);
lean_dec_ref(v_resultType_3645_);
lean_dec_ref_known(v_code_3433_, 1);
goto v___jp_3663_;
}
else
{
size_t v___x_3676_; size_t v___x_3677_; uint8_t v___x_3678_; 
v___x_3676_ = lean_ptr_addr(v_resultType_3645_);
lean_dec_ref(v_resultType_3645_);
v___x_3677_ = lean_ptr_addr(v___x_3651_);
v___x_3678_ = lean_usize_dec_eq(v___x_3676_, v___x_3677_);
if (v___x_3678_ == 0)
{
lean_dec(v_discr_3646_);
lean_dec_ref_known(v_code_3433_, 1);
goto v___jp_3663_;
}
else
{
uint8_t v___x_3679_; 
v___x_3679_ = l_Lean_instBEqFVarId_beq(v_discr_3646_, v_fvarId_3653_);
lean_dec(v_discr_3646_);
if (v___x_3679_ == 0)
{
lean_dec_ref_known(v_code_3433_, 1);
goto v___jp_3663_;
}
else
{
lean_object* v___x_3680_; 
lean_del_object(v___x_3661_);
lean_dec(v_a_3659_);
lean_del_object(v___x_3655_);
lean_dec(v_fvarId_3653_);
lean_dec_ref(v___x_3651_);
lean_del_object(v___x_3649_);
lean_dec(v_typeName_3644_);
v___x_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3680_, 0, v_code_3433_);
return v___x_3680_;
}
}
}
v___jp_3663_:
{
lean_object* v___x_3665_; 
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 3, v_a_3659_);
lean_ctor_set(v___x_3649_, 2, v_fvarId_3653_);
lean_ctor_set(v___x_3649_, 1, v___x_3651_);
v___x_3665_ = v___x_3649_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_typeName_3644_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v___x_3651_);
lean_ctor_set(v_reuseFailAlloc_3672_, 2, v_fvarId_3653_);
lean_ctor_set(v_reuseFailAlloc_3672_, 3, v_a_3659_);
v___x_3665_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3667_; 
if (v_isShared_3656_ == 0)
{
lean_ctor_set_tag(v___x_3655_, 4);
lean_ctor_set(v___x_3655_, 0, v___x_3665_);
v___x_3667_ = v___x_3655_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3665_);
v___x_3667_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
lean_object* v___x_3669_; 
if (v_isShared_3662_ == 0)
{
lean_ctor_set(v___x_3661_, 0, v___x_3667_);
v___x_3669_ = v___x_3661_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3667_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_del_object(v___x_3655_);
lean_dec(v_fvarId_3653_);
lean_dec_ref(v___x_3651_);
lean_del_object(v___x_3649_);
lean_dec_ref(v_alts_3647_);
lean_dec(v_discr_3646_);
lean_dec_ref(v_resultType_3645_);
lean_dec(v_typeName_3644_);
lean_dec_ref_known(v_code_3433_, 1);
v_a_3682_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3658_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3658_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
}
else
{
lean_object* v___x_3691_; 
lean_dec_ref(v___x_3651_);
lean_del_object(v___x_3649_);
lean_dec_ref(v_alts_3647_);
lean_dec(v_discr_3646_);
lean_dec_ref(v_resultType_3645_);
lean_dec(v_typeName_3644_);
lean_dec_ref_known(v_code_3433_, 1);
v___x_3691_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3431_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
return v___x_3691_;
}
}
}
case 5:
{
lean_object* v_fvarId_3693_; lean_object* v___x_3694_; 
v_fvarId_3693_ = lean_ctor_get(v_code_3433_, 0);
lean_inc(v_fvarId_3693_);
v___x_3694_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3434_, v_fvarId_3693_, v_t_3432_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_fvarId_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3714_; 
v_fvarId_3695_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3697_ = v___x_3694_;
v_isShared_3698_ = v_isSharedCheck_3714_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_fvarId_3695_);
lean_dec(v___x_3694_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3714_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
uint8_t v___x_3699_; 
v___x_3699_ = l_Lean_instBEqFVarId_beq(v_fvarId_3693_, v_fvarId_3695_);
if (v___x_3699_ == 0)
{
lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3709_; 
v_isSharedCheck_3709_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3709_ == 0)
{
lean_object* v_unused_3710_; 
v_unused_3710_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3710_);
v___x_3701_ = v_code_3433_;
v_isShared_3702_ = v_isSharedCheck_3709_;
goto v_resetjp_3700_;
}
else
{
lean_dec(v_code_3433_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3709_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 0, v_fvarId_3695_);
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_fvarId_3695_);
v___x_3704_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3706_; 
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v___x_3704_);
v___x_3706_ = v___x_3697_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
else
{
lean_object* v___x_3712_; 
lean_dec(v_fvarId_3695_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v_code_3433_);
v___x_3712_ = v___x_3697_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_code_3433_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
}
else
{
lean_object* v___x_3715_; 
lean_dec_ref_known(v_code_3433_, 1);
v___x_3715_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3431_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
return v___x_3715_;
}
}
case 6:
{
lean_object* v_type_3716_; lean_object* v___x_3717_; size_t v___x_3718_; size_t v___x_3719_; uint8_t v___x_3720_; 
v_type_3716_ = lean_ctor_get(v_code_3433_, 0);
lean_inc_ref(v_type_3716_);
v___x_3717_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3431_, v_a_3434_, v_t_3432_, v_type_3716_);
v___x_3718_ = lean_ptr_addr(v_type_3716_);
v___x_3719_ = lean_ptr_addr(v___x_3717_);
v___x_3720_ = lean_usize_dec_eq(v___x_3718_, v___x_3719_);
if (v___x_3720_ == 0)
{
lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3728_; 
v_isSharedCheck_3728_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3728_ == 0)
{
lean_object* v_unused_3729_; 
v_unused_3729_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3729_);
v___x_3722_ = v_code_3433_;
v_isShared_3723_ = v_isSharedCheck_3728_;
goto v_resetjp_3721_;
}
else
{
lean_dec(v_code_3433_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3728_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v___x_3717_);
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3717_);
v___x_3725_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
lean_object* v___x_3726_; 
v___x_3726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
return v___x_3726_;
}
}
}
else
{
lean_object* v___x_3730_; 
lean_dec_ref(v___x_3717_);
v___x_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3730_, 0, v_code_3433_);
return v___x_3730_;
}
}
case 7:
{
lean_object* v_fvarId_3731_; lean_object* v_i_3732_; lean_object* v_y_3733_; lean_object* v_k_3734_; lean_object* v___x_3735_; 
v_fvarId_3731_ = lean_ctor_get(v_code_3433_, 0);
v_i_3732_ = lean_ctor_get(v_code_3433_, 1);
v_y_3733_ = lean_ctor_get(v_code_3433_, 2);
v_k_3734_ = lean_ctor_get(v_code_3433_, 3);
lean_inc(v_fvarId_3731_);
v___x_3735_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3434_, v_fvarId_3731_, v_t_3432_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_fvarId_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v_fvarId_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_fvarId_3736_);
lean_dec_ref_known(v___x_3735_, 1);
lean_inc(v_y_3733_);
v___x_3737_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_3431_, v_a_3434_, v_y_3733_, v_t_3432_);
lean_inc_ref(v_k_3734_);
v___x_3738_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3431_, v_t_3432_, v_k_3734_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3812_; 
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3741_ = v___x_3738_;
v_isShared_3742_ = v_isSharedCheck_3812_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3738_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3812_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
size_t v___x_3743_; size_t v___x_3744_; uint8_t v___x_3745_; 
v___x_3743_ = lean_ptr_addr(v_fvarId_3731_);
v___x_3744_ = lean_ptr_addr(v_fvarId_3736_);
v___x_3745_ = lean_usize_dec_eq(v___x_3743_, v___x_3744_);
if (v___x_3745_ == 0)
{
lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3755_; 
lean_inc(v_i_3732_);
v_isSharedCheck_3755_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3755_ == 0)
{
lean_object* v_unused_3756_; lean_object* v_unused_3757_; lean_object* v_unused_3758_; lean_object* v_unused_3759_; 
v_unused_3756_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_3756_);
v_unused_3757_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_3757_);
v_unused_3758_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3759_);
v___x_3747_ = v_code_3433_;
v_isShared_3748_ = v_isSharedCheck_3755_;
goto v_resetjp_3746_;
}
else
{
lean_dec(v_code_3433_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3755_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 3, v_a_3739_);
lean_ctor_set(v___x_3747_, 2, v___x_3737_);
lean_ctor_set(v___x_3747_, 0, v_fvarId_3736_);
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_fvarId_3736_);
lean_ctor_set(v_reuseFailAlloc_3754_, 1, v_i_3732_);
lean_ctor_set(v_reuseFailAlloc_3754_, 2, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3754_, 3, v_a_3739_);
v___x_3750_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
lean_object* v___x_3752_; 
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 0, v___x_3750_);
v___x_3752_ = v___x_3741_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3750_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
else
{
uint8_t v___x_3760_; 
v___x_3760_ = lean_nat_dec_eq(v_i_3732_, v_i_3732_);
if (v___x_3760_ == 0)
{
lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3770_; 
lean_inc(v_i_3732_);
v_isSharedCheck_3770_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3770_ == 0)
{
lean_object* v_unused_3771_; lean_object* v_unused_3772_; lean_object* v_unused_3773_; lean_object* v_unused_3774_; 
v_unused_3771_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_3771_);
v_unused_3772_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_3772_);
v_unused_3773_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3773_);
v_unused_3774_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3774_);
v___x_3762_ = v_code_3433_;
v_isShared_3763_ = v_isSharedCheck_3770_;
goto v_resetjp_3761_;
}
else
{
lean_dec(v_code_3433_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3770_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 3, v_a_3739_);
lean_ctor_set(v___x_3762_, 2, v___x_3737_);
lean_ctor_set(v___x_3762_, 0, v_fvarId_3736_);
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_fvarId_3736_);
lean_ctor_set(v_reuseFailAlloc_3769_, 1, v_i_3732_);
lean_ctor_set(v_reuseFailAlloc_3769_, 2, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3769_, 3, v_a_3739_);
v___x_3765_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
lean_object* v___x_3767_; 
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 0, v___x_3765_);
v___x_3767_ = v___x_3741_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3765_);
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
else
{
size_t v___x_3775_; size_t v___x_3776_; uint8_t v___x_3777_; 
v___x_3775_ = lean_ptr_addr(v_y_3733_);
v___x_3776_ = lean_ptr_addr(v___x_3737_);
v___x_3777_ = lean_usize_dec_eq(v___x_3775_, v___x_3776_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3787_; 
lean_inc(v_i_3732_);
v_isSharedCheck_3787_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3787_ == 0)
{
lean_object* v_unused_3788_; lean_object* v_unused_3789_; lean_object* v_unused_3790_; lean_object* v_unused_3791_; 
v_unused_3788_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_3788_);
v_unused_3789_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_3789_);
v_unused_3790_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3790_);
v_unused_3791_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3791_);
v___x_3779_ = v_code_3433_;
v_isShared_3780_ = v_isSharedCheck_3787_;
goto v_resetjp_3778_;
}
else
{
lean_dec(v_code_3433_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3787_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 3, v_a_3739_);
lean_ctor_set(v___x_3779_, 2, v___x_3737_);
lean_ctor_set(v___x_3779_, 0, v_fvarId_3736_);
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_fvarId_3736_);
lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_i_3732_);
lean_ctor_set(v_reuseFailAlloc_3786_, 2, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3786_, 3, v_a_3739_);
v___x_3782_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3784_; 
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 0, v___x_3782_);
v___x_3784_ = v___x_3741_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3782_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
else
{
size_t v___x_3792_; size_t v___x_3793_; uint8_t v___x_3794_; 
v___x_3792_ = lean_ptr_addr(v_k_3734_);
v___x_3793_ = lean_ptr_addr(v_a_3739_);
v___x_3794_ = lean_usize_dec_eq(v___x_3792_, v___x_3793_);
if (v___x_3794_ == 0)
{
lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3804_; 
lean_inc(v_i_3732_);
v_isSharedCheck_3804_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3804_ == 0)
{
lean_object* v_unused_3805_; lean_object* v_unused_3806_; lean_object* v_unused_3807_; lean_object* v_unused_3808_; 
v_unused_3805_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_3805_);
v_unused_3806_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_3806_);
v_unused_3807_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3807_);
v_unused_3808_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3808_);
v___x_3796_ = v_code_3433_;
v_isShared_3797_ = v_isSharedCheck_3804_;
goto v_resetjp_3795_;
}
else
{
lean_dec(v_code_3433_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3804_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 3, v_a_3739_);
lean_ctor_set(v___x_3796_, 2, v___x_3737_);
lean_ctor_set(v___x_3796_, 0, v_fvarId_3736_);
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_fvarId_3736_);
lean_ctor_set(v_reuseFailAlloc_3803_, 1, v_i_3732_);
lean_ctor_set(v_reuseFailAlloc_3803_, 2, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3803_, 3, v_a_3739_);
v___x_3799_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
lean_object* v___x_3801_; 
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 0, v___x_3799_);
v___x_3801_ = v___x_3741_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___x_3799_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
else
{
lean_object* v___x_3810_; 
lean_dec(v_a_3739_);
lean_dec(v___x_3737_);
lean_dec(v_fvarId_3736_);
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 0, v_code_3433_);
v___x_3810_ = v___x_3741_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_code_3433_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3737_);
lean_dec(v_fvarId_3736_);
lean_dec_ref_known(v_code_3433_, 4);
return v___x_3738_;
}
}
else
{
lean_object* v___x_3813_; 
lean_dec_ref_known(v_code_3433_, 4);
v___x_3813_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3431_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
return v___x_3813_;
}
}
case 8:
{
lean_object* v_fvarId_3814_; lean_object* v_i_3815_; lean_object* v_y_3816_; lean_object* v_k_3817_; lean_object* v___x_3818_; 
v_fvarId_3814_ = lean_ctor_get(v_code_3433_, 0);
v_i_3815_ = lean_ctor_get(v_code_3433_, 1);
v_y_3816_ = lean_ctor_get(v_code_3433_, 2);
v_k_3817_ = lean_ctor_get(v_code_3433_, 3);
lean_inc(v_fvarId_3814_);
v___x_3818_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3434_, v_fvarId_3814_, v_t_3432_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v_fvarId_3819_; lean_object* v___x_3820_; 
v_fvarId_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_fvarId_3819_);
lean_dec_ref_known(v___x_3818_, 1);
lean_inc(v_y_3816_);
v___x_3820_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3434_, v_y_3816_, v_t_3432_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v_fvarId_3821_; lean_object* v___x_3822_; 
v_fvarId_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_fvarId_3821_);
lean_dec_ref_known(v___x_3820_, 1);
lean_inc_ref(v_k_3817_);
v___x_3822_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3431_, v_t_3432_, v_k_3817_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3896_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3825_ = v___x_3822_;
v_isShared_3826_ = v_isSharedCheck_3896_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3822_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3896_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
size_t v___x_3827_; size_t v___x_3828_; uint8_t v___x_3829_; 
v___x_3827_ = lean_ptr_addr(v_fvarId_3814_);
v___x_3828_ = lean_ptr_addr(v_fvarId_3819_);
v___x_3829_ = lean_usize_dec_eq(v___x_3827_, v___x_3828_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3839_; 
lean_inc(v_i_3815_);
v_isSharedCheck_3839_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3839_ == 0)
{
lean_object* v_unused_3840_; lean_object* v_unused_3841_; lean_object* v_unused_3842_; lean_object* v_unused_3843_; 
v_unused_3840_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_3840_);
v_unused_3841_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_3841_);
v_unused_3842_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3842_);
v_unused_3843_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3843_);
v___x_3831_ = v_code_3433_;
v_isShared_3832_ = v_isSharedCheck_3839_;
goto v_resetjp_3830_;
}
else
{
lean_dec(v_code_3433_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3839_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 3, v_a_3823_);
lean_ctor_set(v___x_3831_, 2, v_fvarId_3821_);
lean_ctor_set(v___x_3831_, 0, v_fvarId_3819_);
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_fvarId_3819_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_i_3815_);
lean_ctor_set(v_reuseFailAlloc_3838_, 2, v_fvarId_3821_);
lean_ctor_set(v_reuseFailAlloc_3838_, 3, v_a_3823_);
v___x_3834_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
lean_object* v___x_3836_; 
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v___x_3834_);
v___x_3836_ = v___x_3825_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3834_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
else
{
uint8_t v___x_3844_; 
v___x_3844_ = lean_nat_dec_eq(v_i_3815_, v_i_3815_);
if (v___x_3844_ == 0)
{
lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3854_; 
lean_inc(v_i_3815_);
v_isSharedCheck_3854_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3854_ == 0)
{
lean_object* v_unused_3855_; lean_object* v_unused_3856_; lean_object* v_unused_3857_; lean_object* v_unused_3858_; 
v_unused_3855_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_3855_);
v_unused_3856_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_3856_);
v_unused_3857_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3857_);
v_unused_3858_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3858_);
v___x_3846_ = v_code_3433_;
v_isShared_3847_ = v_isSharedCheck_3854_;
goto v_resetjp_3845_;
}
else
{
lean_dec(v_code_3433_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3854_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 3, v_a_3823_);
lean_ctor_set(v___x_3846_, 2, v_fvarId_3821_);
lean_ctor_set(v___x_3846_, 0, v_fvarId_3819_);
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_fvarId_3819_);
lean_ctor_set(v_reuseFailAlloc_3853_, 1, v_i_3815_);
lean_ctor_set(v_reuseFailAlloc_3853_, 2, v_fvarId_3821_);
lean_ctor_set(v_reuseFailAlloc_3853_, 3, v_a_3823_);
v___x_3849_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
lean_object* v___x_3851_; 
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v___x_3849_);
v___x_3851_ = v___x_3825_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3849_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
else
{
size_t v___x_3859_; size_t v___x_3860_; uint8_t v___x_3861_; 
v___x_3859_ = lean_ptr_addr(v_y_3816_);
v___x_3860_ = lean_ptr_addr(v_fvarId_3821_);
v___x_3861_ = lean_usize_dec_eq(v___x_3859_, v___x_3860_);
if (v___x_3861_ == 0)
{
lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3871_; 
lean_inc(v_i_3815_);
v_isSharedCheck_3871_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3871_ == 0)
{
lean_object* v_unused_3872_; lean_object* v_unused_3873_; lean_object* v_unused_3874_; lean_object* v_unused_3875_; 
v_unused_3872_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_3872_);
v_unused_3873_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_3873_);
v_unused_3874_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3874_);
v_unused_3875_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3875_);
v___x_3863_ = v_code_3433_;
v_isShared_3864_ = v_isSharedCheck_3871_;
goto v_resetjp_3862_;
}
else
{
lean_dec(v_code_3433_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3871_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 3, v_a_3823_);
lean_ctor_set(v___x_3863_, 2, v_fvarId_3821_);
lean_ctor_set(v___x_3863_, 0, v_fvarId_3819_);
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_fvarId_3819_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v_i_3815_);
lean_ctor_set(v_reuseFailAlloc_3870_, 2, v_fvarId_3821_);
lean_ctor_set(v_reuseFailAlloc_3870_, 3, v_a_3823_);
v___x_3866_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
lean_object* v___x_3868_; 
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v___x_3866_);
v___x_3868_ = v___x_3825_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3866_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
else
{
size_t v___x_3876_; size_t v___x_3877_; uint8_t v___x_3878_; 
v___x_3876_ = lean_ptr_addr(v_k_3817_);
v___x_3877_ = lean_ptr_addr(v_a_3823_);
v___x_3878_ = lean_usize_dec_eq(v___x_3876_, v___x_3877_);
if (v___x_3878_ == 0)
{
lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3888_; 
lean_inc(v_i_3815_);
v_isSharedCheck_3888_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3888_ == 0)
{
lean_object* v_unused_3889_; lean_object* v_unused_3890_; lean_object* v_unused_3891_; lean_object* v_unused_3892_; 
v_unused_3889_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_3889_);
v_unused_3890_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_3890_);
v_unused_3891_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3891_);
v_unused_3892_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3892_);
v___x_3880_ = v_code_3433_;
v_isShared_3881_ = v_isSharedCheck_3888_;
goto v_resetjp_3879_;
}
else
{
lean_dec(v_code_3433_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3888_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 3, v_a_3823_);
lean_ctor_set(v___x_3880_, 2, v_fvarId_3821_);
lean_ctor_set(v___x_3880_, 0, v_fvarId_3819_);
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_fvarId_3819_);
lean_ctor_set(v_reuseFailAlloc_3887_, 1, v_i_3815_);
lean_ctor_set(v_reuseFailAlloc_3887_, 2, v_fvarId_3821_);
lean_ctor_set(v_reuseFailAlloc_3887_, 3, v_a_3823_);
v___x_3883_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
lean_object* v___x_3885_; 
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v___x_3883_);
v___x_3885_ = v___x_3825_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3883_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
else
{
lean_object* v___x_3894_; 
lean_dec(v_a_3823_);
lean_dec(v_fvarId_3821_);
lean_dec(v_fvarId_3819_);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v_code_3433_);
v___x_3894_ = v___x_3825_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_code_3433_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_3821_);
lean_dec(v_fvarId_3819_);
lean_dec_ref_known(v_code_3433_, 4);
return v___x_3822_;
}
}
else
{
lean_object* v___x_3897_; 
lean_dec(v_fvarId_3819_);
lean_dec_ref_known(v_code_3433_, 4);
v___x_3897_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3431_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
return v___x_3897_;
}
}
else
{
lean_object* v___x_3898_; 
lean_dec_ref_known(v_code_3433_, 4);
v___x_3898_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3431_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
return v___x_3898_;
}
}
case 9:
{
lean_object* v_fvarId_3899_; lean_object* v_i_3900_; lean_object* v_offset_3901_; lean_object* v_y_3902_; lean_object* v_ty_3903_; lean_object* v_k_3904_; lean_object* v___x_3905_; 
v_fvarId_3899_ = lean_ctor_get(v_code_3433_, 0);
v_i_3900_ = lean_ctor_get(v_code_3433_, 1);
v_offset_3901_ = lean_ctor_get(v_code_3433_, 2);
v_y_3902_ = lean_ctor_get(v_code_3433_, 3);
v_ty_3903_ = lean_ctor_get(v_code_3433_, 4);
v_k_3904_ = lean_ctor_get(v_code_3433_, 5);
lean_inc(v_fvarId_3899_);
v___x_3905_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3434_, v_fvarId_3899_, v_t_3432_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_fvarId_3906_; lean_object* v___x_3907_; 
v_fvarId_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_fvarId_3906_);
lean_dec_ref_known(v___x_3905_, 1);
lean_inc(v_y_3902_);
v___x_3907_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3434_, v_y_3902_, v_t_3432_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_fvarId_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v_fvarId_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_fvarId_3908_);
lean_dec_ref_known(v___x_3907_, 1);
lean_inc_ref(v_ty_3903_);
v___x_3909_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3431_, v_a_3434_, v_t_3432_, v_ty_3903_);
lean_inc_ref(v_k_3904_);
v___x_3910_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3431_, v_t_3432_, v_k_3904_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_4028_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_3913_ = v___x_3910_;
v_isShared_3914_ = v_isSharedCheck_4028_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3910_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_4028_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
size_t v___x_3915_; size_t v___x_3916_; uint8_t v___x_3917_; 
v___x_3915_ = lean_ptr_addr(v_fvarId_3899_);
v___x_3916_ = lean_ptr_addr(v_fvarId_3906_);
v___x_3917_ = lean_usize_dec_eq(v___x_3915_, v___x_3916_);
if (v___x_3917_ == 0)
{
lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3927_; 
lean_inc(v_offset_3901_);
lean_inc(v_i_3900_);
v_isSharedCheck_3927_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3927_ == 0)
{
lean_object* v_unused_3928_; lean_object* v_unused_3929_; lean_object* v_unused_3930_; lean_object* v_unused_3931_; lean_object* v_unused_3932_; lean_object* v_unused_3933_; 
v_unused_3928_ = lean_ctor_get(v_code_3433_, 5);
lean_dec(v_unused_3928_);
v_unused_3929_ = lean_ctor_get(v_code_3433_, 4);
lean_dec(v_unused_3929_);
v_unused_3930_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_3930_);
v_unused_3931_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_3931_);
v_unused_3932_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3932_);
v_unused_3933_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3933_);
v___x_3919_ = v_code_3433_;
v_isShared_3920_ = v_isSharedCheck_3927_;
goto v_resetjp_3918_;
}
else
{
lean_dec(v_code_3433_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3927_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 5, v_a_3911_);
lean_ctor_set(v___x_3919_, 4, v___x_3909_);
lean_ctor_set(v___x_3919_, 3, v_fvarId_3908_);
lean_ctor_set(v___x_3919_, 0, v_fvarId_3906_);
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_fvarId_3906_);
lean_ctor_set(v_reuseFailAlloc_3926_, 1, v_i_3900_);
lean_ctor_set(v_reuseFailAlloc_3926_, 2, v_offset_3901_);
lean_ctor_set(v_reuseFailAlloc_3926_, 3, v_fvarId_3908_);
lean_ctor_set(v_reuseFailAlloc_3926_, 4, v___x_3909_);
lean_ctor_set(v_reuseFailAlloc_3926_, 5, v_a_3911_);
v___x_3922_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
lean_object* v___x_3924_; 
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3922_);
v___x_3924_ = v___x_3913_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3922_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
else
{
uint8_t v___x_3934_; 
v___x_3934_ = lean_nat_dec_eq(v_i_3900_, v_i_3900_);
if (v___x_3934_ == 0)
{
lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3944_; 
lean_inc(v_offset_3901_);
lean_inc(v_i_3900_);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3944_ == 0)
{
lean_object* v_unused_3945_; lean_object* v_unused_3946_; lean_object* v_unused_3947_; lean_object* v_unused_3948_; lean_object* v_unused_3949_; lean_object* v_unused_3950_; 
v_unused_3945_ = lean_ctor_get(v_code_3433_, 5);
lean_dec(v_unused_3945_);
v_unused_3946_ = lean_ctor_get(v_code_3433_, 4);
lean_dec(v_unused_3946_);
v_unused_3947_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_3947_);
v_unused_3948_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_3948_);
v_unused_3949_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3949_);
v_unused_3950_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3950_);
v___x_3936_ = v_code_3433_;
v_isShared_3937_ = v_isSharedCheck_3944_;
goto v_resetjp_3935_;
}
else
{
lean_dec(v_code_3433_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3944_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
lean_ctor_set(v___x_3936_, 5, v_a_3911_);
lean_ctor_set(v___x_3936_, 4, v___x_3909_);
lean_ctor_set(v___x_3936_, 3, v_fvarId_3908_);
lean_ctor_set(v___x_3936_, 0, v_fvarId_3906_);
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_fvarId_3906_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v_i_3900_);
lean_ctor_set(v_reuseFailAlloc_3943_, 2, v_offset_3901_);
lean_ctor_set(v_reuseFailAlloc_3943_, 3, v_fvarId_3908_);
lean_ctor_set(v_reuseFailAlloc_3943_, 4, v___x_3909_);
lean_ctor_set(v_reuseFailAlloc_3943_, 5, v_a_3911_);
v___x_3939_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
lean_object* v___x_3941_; 
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3939_);
v___x_3941_ = v___x_3913_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3939_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
else
{
uint8_t v___x_3951_; 
v___x_3951_ = lean_nat_dec_eq(v_offset_3901_, v_offset_3901_);
if (v___x_3951_ == 0)
{
lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3961_; 
lean_inc(v_offset_3901_);
lean_inc(v_i_3900_);
v_isSharedCheck_3961_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3961_ == 0)
{
lean_object* v_unused_3962_; lean_object* v_unused_3963_; lean_object* v_unused_3964_; lean_object* v_unused_3965_; lean_object* v_unused_3966_; lean_object* v_unused_3967_; 
v_unused_3962_ = lean_ctor_get(v_code_3433_, 5);
lean_dec(v_unused_3962_);
v_unused_3963_ = lean_ctor_get(v_code_3433_, 4);
lean_dec(v_unused_3963_);
v_unused_3964_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_3964_);
v_unused_3965_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_3965_);
v_unused_3966_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3966_);
v_unused_3967_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3967_);
v___x_3953_ = v_code_3433_;
v_isShared_3954_ = v_isSharedCheck_3961_;
goto v_resetjp_3952_;
}
else
{
lean_dec(v_code_3433_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3961_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
lean_ctor_set(v___x_3953_, 5, v_a_3911_);
lean_ctor_set(v___x_3953_, 4, v___x_3909_);
lean_ctor_set(v___x_3953_, 3, v_fvarId_3908_);
lean_ctor_set(v___x_3953_, 0, v_fvarId_3906_);
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_fvarId_3906_);
lean_ctor_set(v_reuseFailAlloc_3960_, 1, v_i_3900_);
lean_ctor_set(v_reuseFailAlloc_3960_, 2, v_offset_3901_);
lean_ctor_set(v_reuseFailAlloc_3960_, 3, v_fvarId_3908_);
lean_ctor_set(v_reuseFailAlloc_3960_, 4, v___x_3909_);
lean_ctor_set(v_reuseFailAlloc_3960_, 5, v_a_3911_);
v___x_3956_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
lean_object* v___x_3958_; 
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3956_);
v___x_3958_ = v___x_3913_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3956_);
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
else
{
size_t v___x_3968_; size_t v___x_3969_; uint8_t v___x_3970_; 
v___x_3968_ = lean_ptr_addr(v_y_3902_);
v___x_3969_ = lean_ptr_addr(v_fvarId_3908_);
v___x_3970_ = lean_usize_dec_eq(v___x_3968_, v___x_3969_);
if (v___x_3970_ == 0)
{
lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3980_; 
lean_inc(v_offset_3901_);
lean_inc(v_i_3900_);
v_isSharedCheck_3980_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3980_ == 0)
{
lean_object* v_unused_3981_; lean_object* v_unused_3982_; lean_object* v_unused_3983_; lean_object* v_unused_3984_; lean_object* v_unused_3985_; lean_object* v_unused_3986_; 
v_unused_3981_ = lean_ctor_get(v_code_3433_, 5);
lean_dec(v_unused_3981_);
v_unused_3982_ = lean_ctor_get(v_code_3433_, 4);
lean_dec(v_unused_3982_);
v_unused_3983_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_3983_);
v_unused_3984_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_3984_);
v_unused_3985_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_3985_);
v_unused_3986_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_3986_);
v___x_3972_ = v_code_3433_;
v_isShared_3973_ = v_isSharedCheck_3980_;
goto v_resetjp_3971_;
}
else
{
lean_dec(v_code_3433_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3980_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 5, v_a_3911_);
lean_ctor_set(v___x_3972_, 4, v___x_3909_);
lean_ctor_set(v___x_3972_, 3, v_fvarId_3908_);
lean_ctor_set(v___x_3972_, 0, v_fvarId_3906_);
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_fvarId_3906_);
lean_ctor_set(v_reuseFailAlloc_3979_, 1, v_i_3900_);
lean_ctor_set(v_reuseFailAlloc_3979_, 2, v_offset_3901_);
lean_ctor_set(v_reuseFailAlloc_3979_, 3, v_fvarId_3908_);
lean_ctor_set(v_reuseFailAlloc_3979_, 4, v___x_3909_);
lean_ctor_set(v_reuseFailAlloc_3979_, 5, v_a_3911_);
v___x_3975_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
lean_object* v___x_3977_; 
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3975_);
v___x_3977_ = v___x_3913_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3975_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
else
{
size_t v___x_3987_; size_t v___x_3988_; uint8_t v___x_3989_; 
v___x_3987_ = lean_ptr_addr(v_ty_3903_);
v___x_3988_ = lean_ptr_addr(v___x_3909_);
v___x_3989_ = lean_usize_dec_eq(v___x_3987_, v___x_3988_);
if (v___x_3989_ == 0)
{
lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3999_; 
lean_inc(v_offset_3901_);
lean_inc(v_i_3900_);
v_isSharedCheck_3999_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_3999_ == 0)
{
lean_object* v_unused_4000_; lean_object* v_unused_4001_; lean_object* v_unused_4002_; lean_object* v_unused_4003_; lean_object* v_unused_4004_; lean_object* v_unused_4005_; 
v_unused_4000_ = lean_ctor_get(v_code_3433_, 5);
lean_dec(v_unused_4000_);
v_unused_4001_ = lean_ctor_get(v_code_3433_, 4);
lean_dec(v_unused_4001_);
v_unused_4002_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_4002_);
v_unused_4003_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_4003_);
v_unused_4004_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_4004_);
v_unused_4005_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_4005_);
v___x_3991_ = v_code_3433_;
v_isShared_3992_ = v_isSharedCheck_3999_;
goto v_resetjp_3990_;
}
else
{
lean_dec(v_code_3433_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3999_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
lean_ctor_set(v___x_3991_, 5, v_a_3911_);
lean_ctor_set(v___x_3991_, 4, v___x_3909_);
lean_ctor_set(v___x_3991_, 3, v_fvarId_3908_);
lean_ctor_set(v___x_3991_, 0, v_fvarId_3906_);
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_fvarId_3906_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v_i_3900_);
lean_ctor_set(v_reuseFailAlloc_3998_, 2, v_offset_3901_);
lean_ctor_set(v_reuseFailAlloc_3998_, 3, v_fvarId_3908_);
lean_ctor_set(v_reuseFailAlloc_3998_, 4, v___x_3909_);
lean_ctor_set(v_reuseFailAlloc_3998_, 5, v_a_3911_);
v___x_3994_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
lean_object* v___x_3996_; 
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3994_);
v___x_3996_ = v___x_3913_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___x_3994_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
else
{
size_t v___x_4006_; size_t v___x_4007_; uint8_t v___x_4008_; 
v___x_4006_ = lean_ptr_addr(v_k_3904_);
v___x_4007_ = lean_ptr_addr(v_a_3911_);
v___x_4008_ = lean_usize_dec_eq(v___x_4006_, v___x_4007_);
if (v___x_4008_ == 0)
{
lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4018_; 
lean_inc(v_offset_3901_);
lean_inc(v_i_3900_);
v_isSharedCheck_4018_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_4018_ == 0)
{
lean_object* v_unused_4019_; lean_object* v_unused_4020_; lean_object* v_unused_4021_; lean_object* v_unused_4022_; lean_object* v_unused_4023_; lean_object* v_unused_4024_; 
v_unused_4019_ = lean_ctor_get(v_code_3433_, 5);
lean_dec(v_unused_4019_);
v_unused_4020_ = lean_ctor_get(v_code_3433_, 4);
lean_dec(v_unused_4020_);
v_unused_4021_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_4021_);
v_unused_4022_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_4022_);
v_unused_4023_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_4023_);
v_unused_4024_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_4024_);
v___x_4010_ = v_code_3433_;
v_isShared_4011_ = v_isSharedCheck_4018_;
goto v_resetjp_4009_;
}
else
{
lean_dec(v_code_3433_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4018_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
lean_ctor_set(v___x_4010_, 5, v_a_3911_);
lean_ctor_set(v___x_4010_, 4, v___x_3909_);
lean_ctor_set(v___x_4010_, 3, v_fvarId_3908_);
lean_ctor_set(v___x_4010_, 0, v_fvarId_3906_);
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_fvarId_3906_);
lean_ctor_set(v_reuseFailAlloc_4017_, 1, v_i_3900_);
lean_ctor_set(v_reuseFailAlloc_4017_, 2, v_offset_3901_);
lean_ctor_set(v_reuseFailAlloc_4017_, 3, v_fvarId_3908_);
lean_ctor_set(v_reuseFailAlloc_4017_, 4, v___x_3909_);
lean_ctor_set(v_reuseFailAlloc_4017_, 5, v_a_3911_);
v___x_4013_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
lean_object* v___x_4015_; 
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_4013_);
v___x_4015_ = v___x_3913_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v___x_4013_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
else
{
lean_object* v___x_4026_; 
lean_dec(v_a_3911_);
lean_dec_ref(v___x_3909_);
lean_dec(v_fvarId_3908_);
lean_dec(v_fvarId_3906_);
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v_code_3433_);
v___x_4026_ = v___x_3913_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_code_3433_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
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
lean_dec_ref(v___x_3909_);
lean_dec(v_fvarId_3908_);
lean_dec(v_fvarId_3906_);
lean_dec_ref_known(v_code_3433_, 6);
return v___x_3910_;
}
}
else
{
lean_object* v___x_4029_; 
lean_dec(v_fvarId_3906_);
lean_dec_ref_known(v_code_3433_, 6);
v___x_4029_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3431_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
return v___x_4029_;
}
}
else
{
lean_object* v___x_4030_; 
lean_dec_ref_known(v_code_3433_, 6);
v___x_4030_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3431_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
return v___x_4030_;
}
}
case 10:
{
lean_object* v_fvarId_4031_; lean_object* v_cidx_4032_; lean_object* v_k_4033_; lean_object* v___x_4034_; 
v_fvarId_4031_ = lean_ctor_get(v_code_3433_, 0);
v_cidx_4032_ = lean_ctor_get(v_code_3433_, 1);
v_k_4033_ = lean_ctor_get(v_code_3433_, 2);
lean_inc(v_fvarId_4031_);
v___x_4034_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3434_, v_fvarId_4031_, v_t_3432_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_fvarId_4035_; lean_object* v___x_4036_; 
v_fvarId_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_fvarId_4035_);
lean_dec_ref_known(v___x_4034_, 1);
lean_inc_ref(v_k_4033_);
v___x_4036_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3431_, v_t_3432_, v_k_4033_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4090_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4039_ = v___x_4036_;
v_isShared_4040_ = v_isSharedCheck_4090_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4036_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4090_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
size_t v___x_4041_; size_t v___x_4042_; uint8_t v___x_4043_; 
v___x_4041_ = lean_ptr_addr(v_fvarId_4031_);
v___x_4042_ = lean_ptr_addr(v_fvarId_4035_);
v___x_4043_ = lean_usize_dec_eq(v___x_4041_, v___x_4042_);
if (v___x_4043_ == 0)
{
lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4053_; 
lean_inc(v_cidx_4032_);
v_isSharedCheck_4053_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_4053_ == 0)
{
lean_object* v_unused_4054_; lean_object* v_unused_4055_; lean_object* v_unused_4056_; 
v_unused_4054_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_4054_);
v_unused_4055_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_4055_);
v_unused_4056_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_4056_);
v___x_4045_ = v_code_3433_;
v_isShared_4046_ = v_isSharedCheck_4053_;
goto v_resetjp_4044_;
}
else
{
lean_dec(v_code_3433_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4053_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
lean_ctor_set(v___x_4045_, 2, v_a_4037_);
lean_ctor_set(v___x_4045_, 0, v_fvarId_4035_);
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_fvarId_4035_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v_cidx_4032_);
lean_ctor_set(v_reuseFailAlloc_4052_, 2, v_a_4037_);
v___x_4048_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
lean_object* v___x_4050_; 
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 0, v___x_4048_);
v___x_4050_ = v___x_4039_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v___x_4048_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
else
{
uint8_t v___x_4057_; 
v___x_4057_ = lean_nat_dec_eq(v_cidx_4032_, v_cidx_4032_);
if (v___x_4057_ == 0)
{
lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4067_; 
lean_inc(v_cidx_4032_);
v_isSharedCheck_4067_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_4067_ == 0)
{
lean_object* v_unused_4068_; lean_object* v_unused_4069_; lean_object* v_unused_4070_; 
v_unused_4068_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_4068_);
v_unused_4069_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_4069_);
v_unused_4070_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_4070_);
v___x_4059_ = v_code_3433_;
v_isShared_4060_ = v_isSharedCheck_4067_;
goto v_resetjp_4058_;
}
else
{
lean_dec(v_code_3433_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4067_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 2, v_a_4037_);
lean_ctor_set(v___x_4059_, 0, v_fvarId_4035_);
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_fvarId_4035_);
lean_ctor_set(v_reuseFailAlloc_4066_, 1, v_cidx_4032_);
lean_ctor_set(v_reuseFailAlloc_4066_, 2, v_a_4037_);
v___x_4062_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
lean_object* v___x_4064_; 
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 0, v___x_4062_);
v___x_4064_ = v___x_4039_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4062_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
else
{
size_t v___x_4071_; size_t v___x_4072_; uint8_t v___x_4073_; 
v___x_4071_ = lean_ptr_addr(v_k_4033_);
v___x_4072_ = lean_ptr_addr(v_a_4037_);
v___x_4073_ = lean_usize_dec_eq(v___x_4071_, v___x_4072_);
if (v___x_4073_ == 0)
{
lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4083_; 
lean_inc(v_cidx_4032_);
v_isSharedCheck_4083_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_4083_ == 0)
{
lean_object* v_unused_4084_; lean_object* v_unused_4085_; lean_object* v_unused_4086_; 
v_unused_4084_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_4084_);
v_unused_4085_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_4085_);
v_unused_4086_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_4086_);
v___x_4075_ = v_code_3433_;
v_isShared_4076_ = v_isSharedCheck_4083_;
goto v_resetjp_4074_;
}
else
{
lean_dec(v_code_3433_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4083_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
lean_ctor_set(v___x_4075_, 2, v_a_4037_);
lean_ctor_set(v___x_4075_, 0, v_fvarId_4035_);
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_fvarId_4035_);
lean_ctor_set(v_reuseFailAlloc_4082_, 1, v_cidx_4032_);
lean_ctor_set(v_reuseFailAlloc_4082_, 2, v_a_4037_);
v___x_4078_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
lean_object* v___x_4080_; 
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 0, v___x_4078_);
v___x_4080_ = v___x_4039_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___x_4078_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
}
else
{
lean_object* v___x_4088_; 
lean_dec(v_a_4037_);
lean_dec(v_fvarId_4035_);
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 0, v_code_3433_);
v___x_4088_ = v___x_4039_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_code_3433_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4035_);
lean_dec_ref_known(v_code_3433_, 3);
return v___x_4036_;
}
}
else
{
lean_object* v___x_4091_; 
lean_dec_ref_known(v_code_3433_, 3);
v___x_4091_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3431_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
return v___x_4091_;
}
}
case 11:
{
lean_object* v_fvarId_4092_; lean_object* v_n_4093_; uint8_t v_check_4094_; uint8_t v_persistent_4095_; lean_object* v_k_4096_; lean_object* v___x_4097_; 
v_fvarId_4092_ = lean_ctor_get(v_code_3433_, 0);
v_n_4093_ = lean_ctor_get(v_code_3433_, 1);
v_check_4094_ = lean_ctor_get_uint8(v_code_3433_, sizeof(void*)*3);
v_persistent_4095_ = lean_ctor_get_uint8(v_code_3433_, sizeof(void*)*3 + 1);
v_k_4096_ = lean_ctor_get(v_code_3433_, 2);
lean_inc(v_fvarId_4092_);
v___x_4097_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3434_, v_fvarId_4092_, v_t_3432_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_fvarId_4098_; lean_object* v___x_4099_; 
v_fvarId_4098_ = lean_ctor_get(v___x_4097_, 0);
lean_inc(v_fvarId_4098_);
lean_dec_ref_known(v___x_4097_, 1);
lean_inc_ref(v_k_4096_);
v___x_4099_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3431_, v_t_3432_, v_k_4096_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4153_; 
v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4099_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4102_ = v___x_4099_;
v_isShared_4103_ = v_isSharedCheck_4153_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4099_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4153_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
size_t v___x_4104_; size_t v___x_4105_; uint8_t v___x_4106_; 
v___x_4104_ = lean_ptr_addr(v_fvarId_4092_);
v___x_4105_ = lean_ptr_addr(v_fvarId_4098_);
v___x_4106_ = lean_usize_dec_eq(v___x_4104_, v___x_4105_);
if (v___x_4106_ == 0)
{
lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4116_; 
lean_inc(v_n_4093_);
v_isSharedCheck_4116_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_4116_ == 0)
{
lean_object* v_unused_4117_; lean_object* v_unused_4118_; lean_object* v_unused_4119_; 
v_unused_4117_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_4117_);
v_unused_4118_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_4118_);
v_unused_4119_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_4119_);
v___x_4108_ = v_code_3433_;
v_isShared_4109_ = v_isSharedCheck_4116_;
goto v_resetjp_4107_;
}
else
{
lean_dec(v_code_3433_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4116_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
lean_object* v___x_4111_; 
if (v_isShared_4109_ == 0)
{
lean_ctor_set(v___x_4108_, 2, v_a_4100_);
lean_ctor_set(v___x_4108_, 0, v_fvarId_4098_);
v___x_4111_ = v___x_4108_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_fvarId_4098_);
lean_ctor_set(v_reuseFailAlloc_4115_, 1, v_n_4093_);
lean_ctor_set(v_reuseFailAlloc_4115_, 2, v_a_4100_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, sizeof(void*)*3, v_check_4094_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, sizeof(void*)*3 + 1, v_persistent_4095_);
v___x_4111_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
lean_object* v___x_4113_; 
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 0, v___x_4111_);
v___x_4113_ = v___x_4102_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v___x_4111_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
else
{
uint8_t v___x_4120_; 
v___x_4120_ = lean_nat_dec_eq(v_n_4093_, v_n_4093_);
if (v___x_4120_ == 0)
{
lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4130_; 
lean_inc(v_n_4093_);
v_isSharedCheck_4130_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_4130_ == 0)
{
lean_object* v_unused_4131_; lean_object* v_unused_4132_; lean_object* v_unused_4133_; 
v_unused_4131_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_4131_);
v_unused_4132_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_4132_);
v_unused_4133_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_4133_);
v___x_4122_ = v_code_3433_;
v_isShared_4123_ = v_isSharedCheck_4130_;
goto v_resetjp_4121_;
}
else
{
lean_dec(v_code_3433_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4130_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
lean_ctor_set(v___x_4122_, 2, v_a_4100_);
lean_ctor_set(v___x_4122_, 0, v_fvarId_4098_);
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_fvarId_4098_);
lean_ctor_set(v_reuseFailAlloc_4129_, 1, v_n_4093_);
lean_ctor_set(v_reuseFailAlloc_4129_, 2, v_a_4100_);
lean_ctor_set_uint8(v_reuseFailAlloc_4129_, sizeof(void*)*3, v_check_4094_);
lean_ctor_set_uint8(v_reuseFailAlloc_4129_, sizeof(void*)*3 + 1, v_persistent_4095_);
v___x_4125_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
lean_object* v___x_4127_; 
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 0, v___x_4125_);
v___x_4127_ = v___x_4102_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v___x_4125_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
}
else
{
size_t v___x_4134_; size_t v___x_4135_; uint8_t v___x_4136_; 
v___x_4134_ = lean_ptr_addr(v_k_4096_);
v___x_4135_ = lean_ptr_addr(v_a_4100_);
v___x_4136_ = lean_usize_dec_eq(v___x_4134_, v___x_4135_);
if (v___x_4136_ == 0)
{
lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4146_; 
lean_inc(v_n_4093_);
v_isSharedCheck_4146_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_4146_ == 0)
{
lean_object* v_unused_4147_; lean_object* v_unused_4148_; lean_object* v_unused_4149_; 
v_unused_4147_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_4147_);
v_unused_4148_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_4148_);
v_unused_4149_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_4149_);
v___x_4138_ = v_code_3433_;
v_isShared_4139_ = v_isSharedCheck_4146_;
goto v_resetjp_4137_;
}
else
{
lean_dec(v_code_3433_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4146_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
lean_ctor_set(v___x_4138_, 2, v_a_4100_);
lean_ctor_set(v___x_4138_, 0, v_fvarId_4098_);
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_fvarId_4098_);
lean_ctor_set(v_reuseFailAlloc_4145_, 1, v_n_4093_);
lean_ctor_set(v_reuseFailAlloc_4145_, 2, v_a_4100_);
lean_ctor_set_uint8(v_reuseFailAlloc_4145_, sizeof(void*)*3, v_check_4094_);
lean_ctor_set_uint8(v_reuseFailAlloc_4145_, sizeof(void*)*3 + 1, v_persistent_4095_);
v___x_4141_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
lean_object* v___x_4143_; 
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 0, v___x_4141_);
v___x_4143_ = v___x_4102_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v___x_4141_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
else
{
lean_object* v___x_4151_; 
lean_dec(v_a_4100_);
lean_dec(v_fvarId_4098_);
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 0, v_code_3433_);
v___x_4151_ = v___x_4102_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_code_3433_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4098_);
lean_dec_ref_known(v_code_3433_, 3);
return v___x_4099_;
}
}
else
{
lean_object* v___x_4154_; 
lean_dec_ref_known(v_code_3433_, 3);
v___x_4154_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3431_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
return v___x_4154_;
}
}
case 12:
{
lean_object* v_fvarId_4155_; lean_object* v_n_4156_; uint8_t v_check_4157_; uint8_t v_persistent_4158_; lean_object* v_objs_x3f_4159_; lean_object* v_k_4160_; lean_object* v___x_4161_; 
v_fvarId_4155_ = lean_ctor_get(v_code_3433_, 0);
v_n_4156_ = lean_ctor_get(v_code_3433_, 1);
v_check_4157_ = lean_ctor_get_uint8(v_code_3433_, sizeof(void*)*4);
v_persistent_4158_ = lean_ctor_get_uint8(v_code_3433_, sizeof(void*)*4 + 1);
v_objs_x3f_4159_ = lean_ctor_get(v_code_3433_, 2);
v_k_4160_ = lean_ctor_get(v_code_3433_, 3);
lean_inc(v_fvarId_4155_);
v___x_4161_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3434_, v_fvarId_4155_, v_t_3432_);
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_fvarId_4162_; lean_object* v___x_4163_; 
v_fvarId_4162_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_fvarId_4162_);
lean_dec_ref_known(v___x_4161_, 1);
lean_inc_ref(v_k_4160_);
v___x_4163_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3431_, v_t_3432_, v_k_4160_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4236_; 
v_a_4164_ = lean_ctor_get(v___x_4163_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4166_ = v___x_4163_;
v_isShared_4167_ = v_isSharedCheck_4236_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_4163_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4236_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
size_t v___x_4168_; size_t v___x_4169_; uint8_t v___x_4170_; 
v___x_4168_ = lean_ptr_addr(v_fvarId_4155_);
v___x_4169_ = lean_ptr_addr(v_fvarId_4162_);
v___x_4170_ = lean_usize_dec_eq(v___x_4168_, v___x_4169_);
if (v___x_4170_ == 0)
{
lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4180_; 
lean_inc(v_objs_x3f_4159_);
lean_inc(v_n_4156_);
v_isSharedCheck_4180_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_4180_ == 0)
{
lean_object* v_unused_4181_; lean_object* v_unused_4182_; lean_object* v_unused_4183_; lean_object* v_unused_4184_; 
v_unused_4181_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_4181_);
v_unused_4182_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_4182_);
v_unused_4183_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_4183_);
v_unused_4184_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_4184_);
v___x_4172_ = v_code_3433_;
v_isShared_4173_ = v_isSharedCheck_4180_;
goto v_resetjp_4171_;
}
else
{
lean_dec(v_code_3433_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4180_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4175_; 
if (v_isShared_4173_ == 0)
{
lean_ctor_set(v___x_4172_, 3, v_a_4164_);
lean_ctor_set(v___x_4172_, 0, v_fvarId_4162_);
v___x_4175_ = v___x_4172_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_fvarId_4162_);
lean_ctor_set(v_reuseFailAlloc_4179_, 1, v_n_4156_);
lean_ctor_set(v_reuseFailAlloc_4179_, 2, v_objs_x3f_4159_);
lean_ctor_set(v_reuseFailAlloc_4179_, 3, v_a_4164_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, sizeof(void*)*4, v_check_4157_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, sizeof(void*)*4 + 1, v_persistent_4158_);
v___x_4175_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
lean_object* v___x_4177_; 
if (v_isShared_4167_ == 0)
{
lean_ctor_set(v___x_4166_, 0, v___x_4175_);
v___x_4177_ = v___x_4166_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4175_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
else
{
uint8_t v___x_4185_; 
v___x_4185_ = lean_nat_dec_eq(v_n_4156_, v_n_4156_);
if (v___x_4185_ == 0)
{
lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4195_; 
lean_inc(v_objs_x3f_4159_);
lean_inc(v_n_4156_);
v_isSharedCheck_4195_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_4195_ == 0)
{
lean_object* v_unused_4196_; lean_object* v_unused_4197_; lean_object* v_unused_4198_; lean_object* v_unused_4199_; 
v_unused_4196_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_4196_);
v_unused_4197_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_4197_);
v_unused_4198_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_4198_);
v_unused_4199_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_4199_);
v___x_4187_ = v_code_3433_;
v_isShared_4188_ = v_isSharedCheck_4195_;
goto v_resetjp_4186_;
}
else
{
lean_dec(v_code_3433_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4195_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4190_; 
if (v_isShared_4188_ == 0)
{
lean_ctor_set(v___x_4187_, 3, v_a_4164_);
lean_ctor_set(v___x_4187_, 0, v_fvarId_4162_);
v___x_4190_ = v___x_4187_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_fvarId_4162_);
lean_ctor_set(v_reuseFailAlloc_4194_, 1, v_n_4156_);
lean_ctor_set(v_reuseFailAlloc_4194_, 2, v_objs_x3f_4159_);
lean_ctor_set(v_reuseFailAlloc_4194_, 3, v_a_4164_);
lean_ctor_set_uint8(v_reuseFailAlloc_4194_, sizeof(void*)*4, v_check_4157_);
lean_ctor_set_uint8(v_reuseFailAlloc_4194_, sizeof(void*)*4 + 1, v_persistent_4158_);
v___x_4190_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
lean_object* v___x_4192_; 
if (v_isShared_4167_ == 0)
{
lean_ctor_set(v___x_4166_, 0, v___x_4190_);
v___x_4192_ = v___x_4166_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v___x_4190_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
else
{
size_t v___x_4200_; uint8_t v___x_4201_; 
v___x_4200_ = lean_ptr_addr(v_objs_x3f_4159_);
v___x_4201_ = lean_usize_dec_eq(v___x_4200_, v___x_4200_);
if (v___x_4201_ == 0)
{
lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4211_; 
lean_inc(v_objs_x3f_4159_);
lean_inc(v_n_4156_);
v_isSharedCheck_4211_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_4211_ == 0)
{
lean_object* v_unused_4212_; lean_object* v_unused_4213_; lean_object* v_unused_4214_; lean_object* v_unused_4215_; 
v_unused_4212_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_4212_);
v_unused_4213_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_4213_);
v_unused_4214_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_4214_);
v_unused_4215_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_4215_);
v___x_4203_ = v_code_3433_;
v_isShared_4204_ = v_isSharedCheck_4211_;
goto v_resetjp_4202_;
}
else
{
lean_dec(v_code_3433_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4211_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
lean_ctor_set(v___x_4203_, 3, v_a_4164_);
lean_ctor_set(v___x_4203_, 0, v_fvarId_4162_);
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_fvarId_4162_);
lean_ctor_set(v_reuseFailAlloc_4210_, 1, v_n_4156_);
lean_ctor_set(v_reuseFailAlloc_4210_, 2, v_objs_x3f_4159_);
lean_ctor_set(v_reuseFailAlloc_4210_, 3, v_a_4164_);
lean_ctor_set_uint8(v_reuseFailAlloc_4210_, sizeof(void*)*4, v_check_4157_);
lean_ctor_set_uint8(v_reuseFailAlloc_4210_, sizeof(void*)*4 + 1, v_persistent_4158_);
v___x_4206_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
lean_object* v___x_4208_; 
if (v_isShared_4167_ == 0)
{
lean_ctor_set(v___x_4166_, 0, v___x_4206_);
v___x_4208_ = v___x_4166_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4206_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
else
{
size_t v___x_4216_; size_t v___x_4217_; uint8_t v___x_4218_; 
v___x_4216_ = lean_ptr_addr(v_k_4160_);
v___x_4217_ = lean_ptr_addr(v_a_4164_);
v___x_4218_ = lean_usize_dec_eq(v___x_4216_, v___x_4217_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4228_; 
lean_inc(v_objs_x3f_4159_);
lean_inc(v_n_4156_);
v_isSharedCheck_4228_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_4228_ == 0)
{
lean_object* v_unused_4229_; lean_object* v_unused_4230_; lean_object* v_unused_4231_; lean_object* v_unused_4232_; 
v_unused_4229_ = lean_ctor_get(v_code_3433_, 3);
lean_dec(v_unused_4229_);
v_unused_4230_ = lean_ctor_get(v_code_3433_, 2);
lean_dec(v_unused_4230_);
v_unused_4231_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_4231_);
v_unused_4232_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_4232_);
v___x_4220_ = v_code_3433_;
v_isShared_4221_ = v_isSharedCheck_4228_;
goto v_resetjp_4219_;
}
else
{
lean_dec(v_code_3433_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4228_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 3, v_a_4164_);
lean_ctor_set(v___x_4220_, 0, v_fvarId_4162_);
v___x_4223_ = v___x_4220_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_fvarId_4162_);
lean_ctor_set(v_reuseFailAlloc_4227_, 1, v_n_4156_);
lean_ctor_set(v_reuseFailAlloc_4227_, 2, v_objs_x3f_4159_);
lean_ctor_set(v_reuseFailAlloc_4227_, 3, v_a_4164_);
lean_ctor_set_uint8(v_reuseFailAlloc_4227_, sizeof(void*)*4, v_check_4157_);
lean_ctor_set_uint8(v_reuseFailAlloc_4227_, sizeof(void*)*4 + 1, v_persistent_4158_);
v___x_4223_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
lean_object* v___x_4225_; 
if (v_isShared_4167_ == 0)
{
lean_ctor_set(v___x_4166_, 0, v___x_4223_);
v___x_4225_ = v___x_4166_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4223_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
}
else
{
lean_object* v___x_4234_; 
lean_dec(v_a_4164_);
lean_dec(v_fvarId_4162_);
if (v_isShared_4167_ == 0)
{
lean_ctor_set(v___x_4166_, 0, v_code_3433_);
v___x_4234_ = v___x_4166_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_code_3433_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4162_);
lean_dec_ref_known(v_code_3433_, 4);
return v___x_4163_;
}
}
else
{
lean_object* v___x_4237_; 
lean_dec_ref_known(v_code_3433_, 4);
v___x_4237_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3431_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
return v___x_4237_;
}
}
default: 
{
lean_object* v_fvarId_4238_; lean_object* v_k_4239_; lean_object* v___x_4240_; 
v_fvarId_4238_ = lean_ctor_get(v_code_3433_, 0);
v_k_4239_ = lean_ctor_get(v_code_3433_, 1);
lean_inc(v_fvarId_4238_);
v___x_4240_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3434_, v_fvarId_4238_, v_t_3432_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_fvarId_4241_; lean_object* v___x_4242_; 
v_fvarId_4241_ = lean_ctor_get(v___x_4240_, 0);
lean_inc(v_fvarId_4241_);
lean_dec_ref_known(v___x_4240_, 1);
lean_inc_ref(v_k_4239_);
v___x_4242_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3431_, v_t_3432_, v_k_4239_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4280_; 
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4245_ = v___x_4242_;
v_isShared_4246_ = v_isSharedCheck_4280_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4242_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4280_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
size_t v___x_4247_; size_t v___x_4248_; uint8_t v___x_4249_; 
v___x_4247_ = lean_ptr_addr(v_fvarId_4238_);
v___x_4248_ = lean_ptr_addr(v_fvarId_4241_);
v___x_4249_ = lean_usize_dec_eq(v___x_4247_, v___x_4248_);
if (v___x_4249_ == 0)
{
lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4259_; 
v_isSharedCheck_4259_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_4259_ == 0)
{
lean_object* v_unused_4260_; lean_object* v_unused_4261_; 
v_unused_4260_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_4260_);
v_unused_4261_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_4261_);
v___x_4251_ = v_code_3433_;
v_isShared_4252_ = v_isSharedCheck_4259_;
goto v_resetjp_4250_;
}
else
{
lean_dec(v_code_3433_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4259_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 1, v_a_4243_);
lean_ctor_set(v___x_4251_, 0, v_fvarId_4241_);
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_fvarId_4241_);
lean_ctor_set(v_reuseFailAlloc_4258_, 1, v_a_4243_);
v___x_4254_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
lean_object* v___x_4256_; 
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 0, v___x_4254_);
v___x_4256_ = v___x_4245_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v___x_4254_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
else
{
size_t v___x_4262_; size_t v___x_4263_; uint8_t v___x_4264_; 
v___x_4262_ = lean_ptr_addr(v_k_4239_);
v___x_4263_ = lean_ptr_addr(v_a_4243_);
v___x_4264_ = lean_usize_dec_eq(v___x_4262_, v___x_4263_);
if (v___x_4264_ == 0)
{
lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4274_; 
v_isSharedCheck_4274_ = !lean_is_exclusive(v_code_3433_);
if (v_isSharedCheck_4274_ == 0)
{
lean_object* v_unused_4275_; lean_object* v_unused_4276_; 
v_unused_4275_ = lean_ctor_get(v_code_3433_, 1);
lean_dec(v_unused_4275_);
v_unused_4276_ = lean_ctor_get(v_code_3433_, 0);
lean_dec(v_unused_4276_);
v___x_4266_ = v_code_3433_;
v_isShared_4267_ = v_isSharedCheck_4274_;
goto v_resetjp_4265_;
}
else
{
lean_dec(v_code_3433_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4274_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
lean_ctor_set(v___x_4266_, 1, v_a_4243_);
lean_ctor_set(v___x_4266_, 0, v_fvarId_4241_);
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_fvarId_4241_);
lean_ctor_set(v_reuseFailAlloc_4273_, 1, v_a_4243_);
v___x_4269_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
lean_object* v___x_4271_; 
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 0, v___x_4269_);
v___x_4271_ = v___x_4245_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v___x_4269_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
}
else
{
lean_object* v___x_4278_; 
lean_dec(v_a_4243_);
lean_dec(v_fvarId_4241_);
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 0, v_code_3433_);
v___x_4278_ = v___x_4245_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_code_3433_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_4241_);
lean_dec_ref_known(v_code_3433_, 2);
return v___x_4242_;
}
}
else
{
lean_object* v___x_4281_; 
lean_dec_ref_known(v_code_3433_, 2);
v___x_4281_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3431_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
return v___x_4281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t v_pu_4282_, uint8_t v_t_4283_, lean_object* v_decl_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_){
_start:
{
lean_object* v_params_4291_; lean_object* v_type_4292_; lean_object* v_value_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v_params_4291_ = lean_ctor_get(v_decl_4284_, 2);
v_type_4292_ = lean_ctor_get(v_decl_4284_, 3);
v_value_4293_ = lean_ctor_get(v_decl_4284_, 4);
lean_inc_ref(v_type_4292_);
v___x_4294_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4282_, v_a_4285_, v_t_4283_, v_type_4292_);
lean_inc_ref(v_params_4291_);
v___x_4295_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4282_, v_t_4283_, v_params_4291_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; lean_object* v___x_4297_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4296_);
lean_dec_ref_known(v___x_4295_, 1);
lean_inc_ref(v_value_4293_);
v___x_4297_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4282_, v_t_4283_, v_value_4293_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; lean_object* v___x_4299_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
lean_inc(v_a_4298_);
lean_dec_ref_known(v___x_4297_, 1);
v___x_4299_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_4282_, v_decl_4284_, v___x_4294_, v_a_4296_, v_a_4298_, v_a_4287_);
return v___x_4299_;
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
lean_dec(v_a_4296_);
lean_dec_ref(v___x_4294_);
lean_dec_ref(v_decl_4284_);
v_a_4300_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___x_4297_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4297_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
lean_dec_ref(v___x_4294_);
lean_dec_ref(v_decl_4284_);
v_a_4308_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4295_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4295_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp___boxed(lean_object* v_pu_4316_, lean_object* v_t_4317_, lean_object* v_decl_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_){
_start:
{
uint8_t v_pu_boxed_4325_; uint8_t v_t_boxed_4326_; lean_object* v_res_4327_; 
v_pu_boxed_4325_ = lean_unbox(v_pu_4316_);
v_t_boxed_4326_ = lean_unbox(v_t_4317_);
v_res_4327_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_boxed_4325_, v_t_boxed_4326_, v_decl_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_);
lean_dec(v_a_4323_);
lean_dec_ref(v_a_4322_);
lean_dec(v_a_4321_);
lean_dec_ref(v_a_4320_);
lean_dec_ref(v_a_4319_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(lean_object* v_pu_4328_, lean_object* v_t_4329_, lean_object* v_i_4330_, lean_object* v_as_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_){
_start:
{
uint8_t v_pu_boxed_4338_; uint8_t v_t_boxed_4339_; lean_object* v_res_4340_; 
v_pu_boxed_4338_ = lean_unbox(v_pu_4328_);
v_t_boxed_4339_ = lean_unbox(v_t_4329_);
v_res_4340_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_boxed_4338_, v_t_boxed_4339_, v_i_4330_, v_as_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
lean_dec(v___y_4334_);
lean_dec_ref(v___y_4333_);
lean_dec_ref(v___y_4332_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp___boxed(lean_object* v_pu_4341_, lean_object* v_t_4342_, lean_object* v_code_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_){
_start:
{
uint8_t v_pu_boxed_4350_; uint8_t v_t_boxed_4351_; lean_object* v_res_4352_; 
v_pu_boxed_4350_ = lean_unbox(v_pu_4341_);
v_t_boxed_4351_ = lean_unbox(v_t_4342_);
v_res_4352_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_boxed_4350_, v_t_boxed_4351_, v_code_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
lean_dec(v_a_4348_);
lean_dec_ref(v_a_4347_);
lean_dec(v_a_4346_);
lean_dec_ref(v_a_4345_);
lean_dec_ref(v_a_4344_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(uint8_t v_pu_4353_, uint8_t v_t_4354_, uint8_t v_pu_4355_, uint8_t v_t_4356_, lean_object* v_decl_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_){
_start:
{
lean_object* v___x_4364_; 
v___x_4364_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_4355_, v_t_4356_, v_decl_4357_, v___y_4358_, v___y_4360_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(lean_object* v_pu_4365_, lean_object* v_t_4366_, lean_object* v_pu_4367_, lean_object* v_t_4368_, lean_object* v_decl_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_){
_start:
{
uint8_t v_pu_boxed_4376_; uint8_t v_t_boxed_4377_; uint8_t v_pu_boxed_4378_; uint8_t v_t_boxed_4379_; lean_object* v_res_4380_; 
v_pu_boxed_4376_ = lean_unbox(v_pu_4365_);
v_t_boxed_4377_ = lean_unbox(v_t_4366_);
v_pu_boxed_4378_ = lean_unbox(v_pu_4367_);
v_t_boxed_4379_ = lean_unbox(v_t_4368_);
v_res_4380_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(v_pu_boxed_4376_, v_t_boxed_4377_, v_pu_boxed_4378_, v_t_boxed_4379_, v_decl_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec_ref(v___y_4370_);
return v_res_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(uint8_t v_pu_4381_, uint8_t v_t_4382_, uint8_t v_pu_4383_, uint8_t v_t_4384_, lean_object* v_args_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v___x_4392_; 
v___x_4392_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_4383_, v_t_4384_, v_args_4385_, v___y_4386_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(lean_object* v_pu_4393_, lean_object* v_t_4394_, lean_object* v_pu_4395_, lean_object* v_t_4396_, lean_object* v_args_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
uint8_t v_pu_boxed_4404_; uint8_t v_t_boxed_4405_; uint8_t v_pu_boxed_4406_; uint8_t v_t_boxed_4407_; lean_object* v_res_4408_; 
v_pu_boxed_4404_ = lean_unbox(v_pu_4393_);
v_t_boxed_4405_ = lean_unbox(v_t_4394_);
v_pu_boxed_4406_ = lean_unbox(v_pu_4395_);
v_t_boxed_4407_ = lean_unbox(v_t_4396_);
v_res_4408_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(v_pu_boxed_4404_, v_t_boxed_4405_, v_pu_boxed_4406_, v_t_boxed_4407_, v_args_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4399_);
lean_dec_ref(v___y_4398_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(uint8_t v_pu_4409_, uint8_t v_t_4410_, uint8_t v_pu_4411_, uint8_t v_t_4412_, lean_object* v_ps_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v___x_4420_; 
v___x_4420_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4411_, v_t_4412_, v_ps_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(lean_object* v_pu_4421_, lean_object* v_t_4422_, lean_object* v_pu_4423_, lean_object* v_t_4424_, lean_object* v_ps_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_){
_start:
{
uint8_t v_pu_boxed_4432_; uint8_t v_t_boxed_4433_; uint8_t v_pu_boxed_4434_; uint8_t v_t_boxed_4435_; lean_object* v_res_4436_; 
v_pu_boxed_4432_ = lean_unbox(v_pu_4421_);
v_t_boxed_4433_ = lean_unbox(v_t_4422_);
v_pu_boxed_4434_ = lean_unbox(v_pu_4423_);
v_t_boxed_4435_ = lean_unbox(v_t_4424_);
v_res_4436_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(v_pu_boxed_4432_, v_t_boxed_4433_, v_pu_boxed_4434_, v_t_boxed_4435_, v_ps_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
lean_dec_ref(v___y_4426_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(uint8_t v_pu_4437_, uint8_t v_t_4438_, lean_object* v_i_4439_, lean_object* v_as_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
lean_object* v___x_4447_; 
v___x_4447_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_4437_, v_t_4438_, v_i_4439_, v_as_4440_, v___y_4441_, v___y_4443_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(lean_object* v_pu_4448_, lean_object* v_t_4449_, lean_object* v_i_4450_, lean_object* v_as_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_){
_start:
{
uint8_t v_pu_boxed_4458_; uint8_t v_t_boxed_4459_; lean_object* v_res_4460_; 
v_pu_boxed_4458_ = lean_unbox(v_pu_4448_);
v_t_boxed_4459_ = lean_unbox(v_t_4449_);
v_res_4460_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_boxed_4458_, v_t_boxed_4459_, v_i_4450_, v_as_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec_ref(v___y_4452_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(uint8_t v_pu_4461_, uint8_t v_t_4462_, lean_object* v_decl_4463_, lean_object* v_inst_4464_, lean_object* v_____do__lift_4465_){
_start:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4466_ = lean_box(v_pu_4461_);
v___x_4467_ = lean_box(v_t_4462_);
v___x_4468_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDeclImp___boxed), 9, 4);
lean_closure_set(v___x_4468_, 0, v___x_4466_);
lean_closure_set(v___x_4468_, 1, v___x_4467_);
lean_closure_set(v___x_4468_, 2, v_decl_4463_);
lean_closure_set(v___x_4468_, 3, v_____do__lift_4465_);
v___x_4469_ = lean_apply_2(v_inst_4464_, lean_box(0), v___x_4468_);
return v___x_4469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(lean_object* v_pu_4470_, lean_object* v_t_4471_, lean_object* v_decl_4472_, lean_object* v_inst_4473_, lean_object* v_____do__lift_4474_){
_start:
{
uint8_t v_pu_boxed_4475_; uint8_t v_t_boxed_4476_; lean_object* v_res_4477_; 
v_pu_boxed_4475_ = lean_unbox(v_pu_4470_);
v_t_boxed_4476_ = lean_unbox(v_t_4471_);
v_res_4477_ = l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(v_pu_boxed_4475_, v_t_boxed_4476_, v_decl_4472_, v_inst_4473_, v_____do__lift_4474_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg(uint8_t v_pu_4478_, uint8_t v_t_4479_, lean_object* v_inst_4480_, lean_object* v_inst_4481_, lean_object* v_inst_4482_, lean_object* v_decl_4483_){
_start:
{
lean_object* v_toBind_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___f_4487_; lean_object* v___x_4488_; 
v_toBind_4484_ = lean_ctor_get(v_inst_4481_, 1);
lean_inc(v_toBind_4484_);
lean_dec_ref(v_inst_4481_);
v___x_4485_ = lean_box(v_pu_4478_);
v___x_4486_ = lean_box(v_t_4479_);
v___f_4487_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4487_, 0, v___x_4485_);
lean_closure_set(v___f_4487_, 1, v___x_4486_);
lean_closure_set(v___f_4487_, 2, v_decl_4483_);
lean_closure_set(v___f_4487_, 3, v_inst_4480_);
v___x_4488_ = lean_apply_4(v_toBind_4484_, lean_box(0), lean_box(0), v_inst_4482_, v___f_4487_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(lean_object* v_pu_4489_, lean_object* v_t_4490_, lean_object* v_inst_4491_, lean_object* v_inst_4492_, lean_object* v_inst_4493_, lean_object* v_decl_4494_){
_start:
{
uint8_t v_pu_boxed_4495_; uint8_t v_t_boxed_4496_; lean_object* v_res_4497_; 
v_pu_boxed_4495_ = lean_unbox(v_pu_4489_);
v_t_boxed_4496_ = lean_unbox(v_t_4490_);
v_res_4497_ = l_Lean_Compiler_LCNF_normFunDecl___redArg(v_pu_boxed_4495_, v_t_boxed_4496_, v_inst_4491_, v_inst_4492_, v_inst_4493_, v_decl_4494_);
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl(lean_object* v_m_4498_, uint8_t v_pu_4499_, uint8_t v_t_4500_, lean_object* v_inst_4501_, lean_object* v_inst_4502_, lean_object* v_inst_4503_, lean_object* v_decl_4504_){
_start:
{
lean_object* v_toBind_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___f_4508_; lean_object* v___x_4509_; 
v_toBind_4505_ = lean_ctor_get(v_inst_4502_, 1);
lean_inc(v_toBind_4505_);
lean_dec_ref(v_inst_4502_);
v___x_4506_ = lean_box(v_pu_4499_);
v___x_4507_ = lean_box(v_t_4500_);
v___f_4508_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4508_, 0, v___x_4506_);
lean_closure_set(v___f_4508_, 1, v___x_4507_);
lean_closure_set(v___f_4508_, 2, v_decl_4504_);
lean_closure_set(v___f_4508_, 3, v_inst_4501_);
v___x_4509_ = lean_apply_4(v_toBind_4505_, lean_box(0), lean_box(0), v_inst_4503_, v___f_4508_);
return v___x_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___boxed(lean_object* v_m_4510_, lean_object* v_pu_4511_, lean_object* v_t_4512_, lean_object* v_inst_4513_, lean_object* v_inst_4514_, lean_object* v_inst_4515_, lean_object* v_decl_4516_){
_start:
{
uint8_t v_pu_boxed_4517_; uint8_t v_t_boxed_4518_; lean_object* v_res_4519_; 
v_pu_boxed_4517_ = lean_unbox(v_pu_4511_);
v_t_boxed_4518_ = lean_unbox(v_t_4512_);
v_res_4519_ = l_Lean_Compiler_LCNF_normFunDecl(v_m_4510_, v_pu_boxed_4517_, v_t_boxed_4518_, v_inst_4513_, v_inst_4514_, v_inst_4515_, v_decl_4516_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0(uint8_t v_pu_4520_, uint8_t v_t_4521_, lean_object* v_code_4522_, lean_object* v_inst_4523_, lean_object* v_____do__lift_4524_){
_start:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4525_ = lean_box(v_pu_4520_);
v___x_4526_ = lean_box(v_t_4521_);
v___x_4527_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCodeImp___boxed), 9, 4);
lean_closure_set(v___x_4527_, 0, v___x_4525_);
lean_closure_set(v___x_4527_, 1, v___x_4526_);
lean_closure_set(v___x_4527_, 2, v_code_4522_);
lean_closure_set(v___x_4527_, 3, v_____do__lift_4524_);
v___x_4528_ = lean_apply_2(v_inst_4523_, lean_box(0), v___x_4527_);
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(lean_object* v_pu_4529_, lean_object* v_t_4530_, lean_object* v_code_4531_, lean_object* v_inst_4532_, lean_object* v_____do__lift_4533_){
_start:
{
uint8_t v_pu_boxed_4534_; uint8_t v_t_boxed_4535_; lean_object* v_res_4536_; 
v_pu_boxed_4534_ = lean_unbox(v_pu_4529_);
v_t_boxed_4535_ = lean_unbox(v_t_4530_);
v_res_4536_ = l_Lean_Compiler_LCNF_normCode___redArg___lam__0(v_pu_boxed_4534_, v_t_boxed_4535_, v_code_4531_, v_inst_4532_, v_____do__lift_4533_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg(uint8_t v_pu_4537_, uint8_t v_t_4538_, lean_object* v_inst_4539_, lean_object* v_inst_4540_, lean_object* v_inst_4541_, lean_object* v_code_4542_){
_start:
{
lean_object* v_toBind_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___f_4546_; lean_object* v___x_4547_; 
v_toBind_4543_ = lean_ctor_get(v_inst_4540_, 1);
lean_inc(v_toBind_4543_);
lean_dec_ref(v_inst_4540_);
v___x_4544_ = lean_box(v_pu_4537_);
v___x_4545_ = lean_box(v_t_4538_);
v___f_4546_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4546_, 0, v___x_4544_);
lean_closure_set(v___f_4546_, 1, v___x_4545_);
lean_closure_set(v___f_4546_, 2, v_code_4542_);
lean_closure_set(v___f_4546_, 3, v_inst_4539_);
v___x_4547_ = lean_apply_4(v_toBind_4543_, lean_box(0), lean_box(0), v_inst_4541_, v___f_4546_);
return v___x_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___boxed(lean_object* v_pu_4548_, lean_object* v_t_4549_, lean_object* v_inst_4550_, lean_object* v_inst_4551_, lean_object* v_inst_4552_, lean_object* v_code_4553_){
_start:
{
uint8_t v_pu_boxed_4554_; uint8_t v_t_boxed_4555_; lean_object* v_res_4556_; 
v_pu_boxed_4554_ = lean_unbox(v_pu_4548_);
v_t_boxed_4555_ = lean_unbox(v_t_4549_);
v_res_4556_ = l_Lean_Compiler_LCNF_normCode___redArg(v_pu_boxed_4554_, v_t_boxed_4555_, v_inst_4550_, v_inst_4551_, v_inst_4552_, v_code_4553_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode(lean_object* v_m_4557_, uint8_t v_pu_4558_, uint8_t v_t_4559_, lean_object* v_inst_4560_, lean_object* v_inst_4561_, lean_object* v_inst_4562_, lean_object* v_code_4563_){
_start:
{
lean_object* v_toBind_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___f_4567_; lean_object* v___x_4568_; 
v_toBind_4564_ = lean_ctor_get(v_inst_4561_, 1);
lean_inc(v_toBind_4564_);
lean_dec_ref(v_inst_4561_);
v___x_4565_ = lean_box(v_pu_4558_);
v___x_4566_ = lean_box(v_t_4559_);
v___f_4567_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4567_, 0, v___x_4565_);
lean_closure_set(v___f_4567_, 1, v___x_4566_);
lean_closure_set(v___f_4567_, 2, v_code_4563_);
lean_closure_set(v___f_4567_, 3, v_inst_4560_);
v___x_4568_ = lean_apply_4(v_toBind_4564_, lean_box(0), lean_box(0), v_inst_4562_, v___f_4567_);
return v___x_4568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___boxed(lean_object* v_m_4569_, lean_object* v_pu_4570_, lean_object* v_t_4571_, lean_object* v_inst_4572_, lean_object* v_inst_4573_, lean_object* v_inst_4574_, lean_object* v_code_4575_){
_start:
{
uint8_t v_pu_boxed_4576_; uint8_t v_t_boxed_4577_; lean_object* v_res_4578_; 
v_pu_boxed_4576_ = lean_unbox(v_pu_4570_);
v_t_boxed_4577_ = lean_unbox(v_t_4571_);
v_res_4578_ = l_Lean_Compiler_LCNF_normCode(v_m_4569_, v_pu_boxed_4576_, v_t_boxed_4577_, v_inst_4572_, v_inst_4573_, v_inst_4574_, v_code_4575_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t v_pu_4579_, lean_object* v_e_4580_, lean_object* v_s_4581_, uint8_t v_translator_4582_){
_start:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4584_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4579_, v_s_4581_, v_translator_4582_, v_e_4580_);
v___x_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(lean_object* v_pu_4586_, lean_object* v_e_4587_, lean_object* v_s_4588_, lean_object* v_translator_4589_, lean_object* v_a_4590_){
_start:
{
uint8_t v_pu_boxed_4591_; uint8_t v_translator_boxed_4592_; lean_object* v_res_4593_; 
v_pu_boxed_4591_ = lean_unbox(v_pu_4586_);
v_translator_boxed_4592_ = lean_unbox(v_translator_4589_);
v_res_4593_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_boxed_4591_, v_e_4587_, v_s_4588_, v_translator_boxed_4592_);
lean_dec_ref(v_s_4588_);
return v_res_4593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(uint8_t v_pu_4594_, lean_object* v_e_4595_, lean_object* v_s_4596_, uint8_t v_translator_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_){
_start:
{
lean_object* v___x_4603_; 
v___x_4603_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_4594_, v_e_4595_, v_s_4596_, v_translator_4597_);
return v___x_4603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___boxed(lean_object* v_pu_4604_, lean_object* v_e_4605_, lean_object* v_s_4606_, lean_object* v_translator_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_){
_start:
{
uint8_t v_pu_boxed_4613_; uint8_t v_translator_boxed_4614_; lean_object* v_res_4615_; 
v_pu_boxed_4613_ = lean_unbox(v_pu_4604_);
v_translator_boxed_4614_ = lean_unbox(v_translator_4607_);
v_res_4615_ = l_Lean_Compiler_LCNF_replaceExprFVars(v_pu_boxed_4613_, v_e_4605_, v_s_4606_, v_translator_boxed_4614_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_);
lean_dec(v_a_4611_);
lean_dec_ref(v_a_4610_);
lean_dec(v_a_4609_);
lean_dec_ref(v_a_4608_);
lean_dec_ref(v_s_4606_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t v_pu_4616_, lean_object* v_code_4617_, lean_object* v_s_4618_, uint8_t v_translator_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_){
_start:
{
lean_object* v___x_4625_; 
v___x_4625_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4616_, v_translator_4619_, v_code_4617_, v_s_4618_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_);
return v___x_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars___boxed(lean_object* v_pu_4626_, lean_object* v_code_4627_, lean_object* v_s_4628_, lean_object* v_translator_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_){
_start:
{
uint8_t v_pu_boxed_4635_; uint8_t v_translator_boxed_4636_; lean_object* v_res_4637_; 
v_pu_boxed_4635_ = lean_unbox(v_pu_4626_);
v_translator_boxed_4636_ = lean_unbox(v_translator_4629_);
v_res_4637_ = l_Lean_Compiler_LCNF_replaceFVars(v_pu_boxed_4635_, v_code_4627_, v_s_4628_, v_translator_boxed_4636_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_);
lean_dec(v_a_4633_);
lean_dec_ref(v_a_4632_);
lean_dec(v_a_4631_);
lean_dec_ref(v_a_4630_);
lean_dec_ref(v_s_4628_);
return v_res_4637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object* v_a_4641_){
_start:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4643_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1));
v___x_4644_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4643_, v_a_4641_);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(lean_object* v_a_4645_, lean_object* v_a_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4645_);
lean_dec(v_a_4645_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_){
_start:
{
lean_object* v___x_4653_; 
v___x_4653_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4649_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___boxed(lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_){
_start:
{
lean_object* v_res_4659_; 
v_res_4659_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_);
lean_dec(v_a_4657_);
lean_dec_ref(v_a_4656_);
lean_dec(v_a_4655_);
lean_dec_ref(v_a_4654_);
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t v_pu_4660_, lean_object* v_type_4661_, uint8_t v_borrow_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_){
_start:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v_a_4670_; lean_object* v___x_4671_; 
v___x_4668_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_4669_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4668_, v_a_4664_);
v_a_4670_ = lean_ctor_get(v___x_4669_, 0);
lean_inc(v_a_4670_);
lean_dec_ref(v___x_4669_);
v___x_4671_ = l_Lean_Compiler_LCNF_mkParam(v_pu_4660_, v_a_4670_, v_type_4661_, v_borrow_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam___boxed(lean_object* v_pu_4672_, lean_object* v_type_4673_, lean_object* v_borrow_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_){
_start:
{
uint8_t v_pu_boxed_4680_; uint8_t v_borrow_boxed_4681_; lean_object* v_res_4682_; 
v_pu_boxed_4680_ = lean_unbox(v_pu_4672_);
v_borrow_boxed_4681_ = lean_unbox(v_borrow_4674_);
v_res_4682_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_boxed_4680_, v_type_4673_, v_borrow_boxed_4681_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_);
lean_dec(v_a_4678_);
lean_dec_ref(v_a_4677_);
lean_dec(v_a_4676_);
lean_dec_ref(v_a_4675_);
return v_res_4682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object* v_a_4683_){
_start:
{
lean_object* v_config_4685_; lean_object* v___x_4686_; 
v_config_4685_ = lean_ctor_get(v_a_4683_, 0);
lean_inc_ref(v_config_4685_);
v___x_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4686_, 0, v_config_4685_);
return v___x_4686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg___boxed(lean_object* v_a_4687_, lean_object* v_a_4688_){
_start:
{
lean_object* v_res_4689_; 
v_res_4689_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4687_);
lean_dec_ref(v_a_4687_);
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_){
_start:
{
lean_object* v___x_4695_; 
v___x_4695_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4690_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___boxed(lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l_Lean_Compiler_LCNF_getConfig(v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_);
lean_dec(v_a_4699_);
lean_dec_ref(v_a_4698_);
lean_dec(v_a_4697_);
lean_dec_ref(v_a_4696_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object* v_x_4702_, lean_object* v_s_4703_, uint8_t v_phase_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_){
_start:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; 
v___x_4708_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4705_);
v___x_4709_ = l_Lean_Compiler_LCNF_toConfigOptions(v___x_4708_);
lean_dec_ref(v___x_4708_);
v___x_4710_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4710_, 0, v___x_4709_);
lean_ctor_set_uint8(v___x_4710_, sizeof(void*)*1, v_phase_4704_);
v___x_4711_ = lean_st_mk_ref(v_s_4703_);
lean_inc(v_a_4706_);
lean_inc_ref(v_a_4705_);
lean_inc(v___x_4711_);
v___x_4712_ = lean_apply_5(v_x_4702_, v___x_4710_, v___x_4711_, v_a_4705_, v_a_4706_, lean_box(0));
if (lean_obj_tag(v___x_4712_) == 0)
{
lean_object* v_a_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4721_; 
v_a_4713_ = lean_ctor_get(v___x_4712_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4712_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4715_ = v___x_4712_;
v_isShared_4716_ = v_isSharedCheck_4721_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_a_4713_);
lean_dec(v___x_4712_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4721_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4717_; lean_object* v___x_4719_; 
v___x_4717_ = lean_st_ref_get(v___x_4711_);
lean_dec(v___x_4711_);
lean_dec(v___x_4717_);
if (v_isShared_4716_ == 0)
{
v___x_4719_ = v___x_4715_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_a_4713_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
}
else
{
lean_dec(v___x_4711_);
return v___x_4712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(lean_object* v_x_4722_, lean_object* v_s_4723_, lean_object* v_phase_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_){
_start:
{
uint8_t v_phase_boxed_4728_; lean_object* v_res_4729_; 
v_phase_boxed_4728_ = lean_unbox(v_phase_4724_);
v_res_4729_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4722_, v_s_4723_, v_phase_boxed_4728_, v_a_4725_, v_a_4726_);
lean_dec(v_a_4726_);
lean_dec_ref(v_a_4725_);
return v_res_4729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run(lean_object* v_00_u03b1_4730_, lean_object* v_x_4731_, lean_object* v_s_4732_, uint8_t v_phase_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_){
_start:
{
lean_object* v___x_4737_; 
v___x_4737_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4731_, v_s_4732_, v_phase_4733_, v_a_4734_, v_a_4735_);
return v___x_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object* v_00_u03b1_4738_, lean_object* v_x_4739_, lean_object* v_s_4740_, lean_object* v_phase_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_){
_start:
{
uint8_t v_phase_boxed_4745_; lean_object* v_res_4746_; 
v_phase_boxed_4745_ = lean_unbox(v_phase_4741_);
v_res_4746_ = l_Lean_Compiler_LCNF_CompilerM_run(v_00_u03b1_4738_, v_x_4739_, v_s_4740_, v_phase_boxed_4745_, v_a_4742_, v_a_4743_);
lean_dec(v_a_4743_);
lean_dec_ref(v_a_4742_);
return v_res_4746_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_4747_; 
v___x_4747_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_4747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg(){
_start:
{
lean_object* v___x_4749_; 
v___x_4749_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___boxed(lean_object* v___dummy_4750_){
_start:
{
lean_object* v_res_4751_; 
v_res_4751_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg();
return v_res_4751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object* v_00_u03b1_4752_, lean_object* v_00_u03b2_4753_, lean_object* v_inst_4754_, lean_object* v_inst_4755_){
_start:
{
lean_object* v___x_4756_; 
v___x_4756_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object* v_00_u03b1_4757_, lean_object* v_00_u03b2_4758_, lean_object* v_inst_4759_, lean_object* v_inst_4760_){
_start:
{
lean_object* v_res_4761_; 
v_res_4761_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(v_00_u03b1_4757_, v_00_u03b2_4758_, v_inst_4759_, v_inst_4760_);
lean_dec_ref(v_inst_4760_);
lean_dec_ref(v_inst_4759_);
return v_res_4761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg(){
_start:
{
lean_object* v___x_4763_; 
v___x_4763_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg___boxed(lean_object* v___dummy_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg();
return v_res_4765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension(lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v___x_4770_; 
v___x_4770_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension(v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_);
lean_dec_ref(v_a_4774_);
lean_dec_ref(v_a_4773_);
return v_res_4775_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4779_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2));
v___x_4780_ = lean_unsigned_to_nat(14u);
v___x_4781_ = lean_unsigned_to_nat(178u);
v___x_4782_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1));
v___x_4783_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0));
v___x_4784_ = l_mkPanicMessageWithDecl(v___x_4783_, v___x_4782_, v___x_4781_, v___x_4780_, v___x_4779_);
return v___x_4784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(lean_object* v_inst_4785_, lean_object* v_inst_4786_, lean_object* v_snd_4787_, lean_object* v_inst_4788_, lean_object* v_s_4789_, lean_object* v_e_4790_){
_start:
{
lean_object* v_fst_4791_; lean_object* v_snd_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4807_; 
v_fst_4791_ = lean_ctor_get(v_s_4789_, 0);
v_snd_4792_ = lean_ctor_get(v_s_4789_, 1);
v_isSharedCheck_4807_ = !lean_is_exclusive(v_s_4789_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4794_ = v_s_4789_;
v_isShared_4795_ = v_isSharedCheck_4807_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_snd_4792_);
lean_inc(v_fst_4791_);
lean_dec(v_s_4789_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4807_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4796_; lean_object* v___y_4798_; lean_object* v___x_4803_; 
lean_inc_n(v_e_4790_, 2);
v___x_4796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4796_, 0, v_e_4790_);
lean_ctor_set(v___x_4796_, 1, v_fst_4791_);
lean_inc_ref(v_inst_4786_);
lean_inc_ref(v_inst_4785_);
v___x_4803_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4785_, v_inst_4786_, v_snd_4787_, v_e_4790_);
if (lean_obj_tag(v___x_4803_) == 0)
{
lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4804_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3);
v___x_4805_ = l_panic___redArg(v_inst_4788_, v___x_4804_);
v___y_4798_ = v___x_4805_;
goto v___jp_4797_;
}
else
{
lean_object* v_val_4806_; 
v_val_4806_ = lean_ctor_get(v___x_4803_, 0);
lean_inc(v_val_4806_);
lean_dec_ref_known(v___x_4803_, 1);
v___y_4798_ = v_val_4806_;
goto v___jp_4797_;
}
v___jp_4797_:
{
lean_object* v___x_4799_; lean_object* v___x_4801_; 
v___x_4799_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4785_, v_inst_4786_, v_snd_4792_, v_e_4790_, v___y_4798_);
if (v_isShared_4795_ == 0)
{
lean_ctor_set(v___x_4794_, 1, v___x_4799_);
lean_ctor_set(v___x_4794_, 0, v___x_4796_);
v___x_4801_ = v___x_4794_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v___x_4796_);
lean_ctor_set(v_reuseFailAlloc_4802_, 1, v___x_4799_);
v___x_4801_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
return v___x_4801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed(lean_object* v_inst_4808_, lean_object* v_inst_4809_, lean_object* v_snd_4810_, lean_object* v_inst_4811_, lean_object* v_s_4812_, lean_object* v_e_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(v_inst_4808_, v_inst_4809_, v_snd_4810_, v_inst_4811_, v_s_4812_, v_e_4813_);
lean_dec(v_inst_4811_);
lean_dec(v_snd_4810_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object* v_inst_4815_, lean_object* v_inst_4816_, lean_object* v_inst_4817_, lean_object* v_oldState_4818_, lean_object* v_newState_4819_, lean_object* v_x_4820_, lean_object* v_s_4821_){
_start:
{
lean_object* v_fst_4822_; lean_object* v_snd_4823_; lean_object* v_fst_4824_; lean_object* v___f_4825_; lean_object* v_newEntries_4826_; lean_object* v___x_4827_; 
v_fst_4822_ = lean_ctor_get(v_newState_4819_, 0);
lean_inc(v_fst_4822_);
v_snd_4823_ = lean_ctor_get(v_newState_4819_, 1);
lean_inc(v_snd_4823_);
lean_dec_ref(v_newState_4819_);
v_fst_4824_ = lean_ctor_get(v_oldState_4818_, 0);
v___f_4825_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_4825_, 0, v_inst_4815_);
lean_closure_set(v___f_4825_, 1, v_inst_4816_);
lean_closure_set(v___f_4825_, 2, v_snd_4823_);
lean_closure_set(v___f_4825_, 3, v_inst_4817_);
v_newEntries_4826_ = l_Lean_takeNewEntries___redArg(v_fst_4822_, v_fst_4824_);
v___x_4827_ = l_List_foldl___redArg(v___f_4825_, v_s_4821_, v_newEntries_4826_);
return v___x_4827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object* v_inst_4828_, lean_object* v_inst_4829_, lean_object* v_inst_4830_, lean_object* v_oldState_4831_, lean_object* v_newState_4832_, lean_object* v_x_4833_, lean_object* v_s_4834_){
_start:
{
lean_object* v_res_4835_; 
v_res_4835_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(v_inst_4828_, v_inst_4829_, v_inst_4830_, v_oldState_4831_, v_newState_4832_, v_x_4833_, v_s_4834_);
lean_dec(v_x_4833_);
lean_dec_ref(v_oldState_4831_);
return v_res_4835_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0(void){
_start:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; 
v___x_4836_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_4837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4837_, 0, v___x_4836_);
return v___x_4837_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1(void){
_start:
{
lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4838_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0);
v___x_4839_ = lean_box(0);
v___x_4840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4840_, 0, v___x_4839_);
lean_ctor_set(v___x_4840_, 1, v___x_4838_);
return v___x_4840_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2(void){
_start:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4841_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1);
v___x_4842_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_4842_, 0, lean_box(0));
lean_closure_set(v___x_4842_, 1, lean_box(0));
lean_closure_set(v___x_4842_, 2, v___x_4841_);
return v___x_4842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object* v_inst_4854_, lean_object* v_inst_4855_, lean_object* v_inst_4856_){
_start:
{
lean_object* v___f_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; uint8_t v___x_4863_; lean_object* v___x_4864_; 
v___f_4858_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4858_, 0, v_inst_4854_);
lean_closure_set(v___f_4858_, 1, v_inst_4855_);
lean_closure_set(v___f_4858_, 2, v_inst_4856_);
v___x_4859_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2);
v___x_4860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4860_, 0, v___f_4858_);
v___x_4861_ = lean_box(0);
v___x_4862_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8));
v___x_4863_ = 0;
v___x_4864_ = l_Lean_registerEnvExtension___redArg(v___x_4859_, v___x_4860_, v___x_4861_, v___x_4862_, v___x_4863_, v___x_4863_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v_a_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4872_; 
v_a_4865_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4872_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4872_ == 0)
{
v___x_4867_ = v___x_4864_;
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_a_4865_);
lean_dec(v___x_4864_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
lean_object* v___x_4870_; 
if (v_isShared_4868_ == 0)
{
v___x_4870_ = v___x_4867_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4865_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
return v___x_4870_;
}
}
}
else
{
lean_object* v_a_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4880_; 
v_a_4873_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4880_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4880_ == 0)
{
v___x_4875_ = v___x_4864_;
v_isShared_4876_ = v_isSharedCheck_4880_;
goto v_resetjp_4874_;
}
else
{
lean_inc(v_a_4873_);
lean_dec(v___x_4864_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4880_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v___x_4878_; 
if (v_isShared_4876_ == 0)
{
v___x_4878_ = v___x_4875_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_a_4873_);
v___x_4878_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
return v___x_4878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object* v_inst_4881_, lean_object* v_inst_4882_, lean_object* v_inst_4883_, lean_object* v_a_4884_){
_start:
{
lean_object* v_res_4885_; 
v_res_4885_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4881_, v_inst_4882_, v_inst_4883_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object* v_00_u03b1_4886_, lean_object* v_00_u03b2_4887_, lean_object* v_inst_4888_, lean_object* v_inst_4889_, lean_object* v_inst_4890_){
_start:
{
lean_object* v___x_4892_; 
v___x_4892_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_4888_, v_inst_4889_, v_inst_4890_);
return v___x_4892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object* v_00_u03b1_4893_, lean_object* v_00_u03b2_4894_, lean_object* v_inst_4895_, lean_object* v_inst_4896_, lean_object* v_inst_4897_, lean_object* v_a_4898_){
_start:
{
lean_object* v_res_4899_; 
v_res_4899_ = l_Lean_Compiler_LCNF_CacheExtension_register(v_00_u03b1_4893_, v_00_u03b2_4894_, v_inst_4895_, v_inst_4896_, v_inst_4897_);
return v_res_4899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object* v_a_4900_, lean_object* v_inst_4901_, lean_object* v_inst_4902_, lean_object* v_b_4903_, lean_object* v_x_4904_){
_start:
{
lean_object* v_fst_4905_; lean_object* v_snd_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4915_; 
v_fst_4905_ = lean_ctor_get(v_x_4904_, 0);
v_snd_4906_ = lean_ctor_get(v_x_4904_, 1);
v_isSharedCheck_4915_ = !lean_is_exclusive(v_x_4904_);
if (v_isSharedCheck_4915_ == 0)
{
v___x_4908_ = v_x_4904_;
v_isShared_4909_ = v_isSharedCheck_4915_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_snd_4906_);
lean_inc(v_fst_4905_);
lean_dec(v_x_4904_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4915_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4913_; 
lean_inc(v_a_4900_);
v___x_4910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4910_, 0, v_a_4900_);
lean_ctor_set(v___x_4910_, 1, v_fst_4905_);
v___x_4911_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4901_, v_inst_4902_, v_snd_4906_, v_a_4900_, v_b_4903_);
if (v_isShared_4909_ == 0)
{
lean_ctor_set(v___x_4908_, 1, v___x_4911_);
lean_ctor_set(v___x_4908_, 0, v___x_4910_);
v___x_4913_ = v___x_4908_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v___x_4910_);
lean_ctor_set(v_reuseFailAlloc_4914_, 1, v___x_4911_);
v___x_4913_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4912_;
}
v_reusejp_4912_:
{
return v___x_4913_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; 
v___x_4916_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_4917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4917_, 0, v___x_4916_);
return v___x_4917_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; 
v___x_4918_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0);
v___x_4919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4919_, 0, v___x_4918_);
lean_ctor_set(v___x_4919_, 1, v___x_4918_);
return v___x_4919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object* v_inst_4920_, lean_object* v_inst_4921_, lean_object* v_ext_4922_, lean_object* v_a_4923_, lean_object* v_b_4924_, lean_object* v_a_4925_){
_start:
{
lean_object* v___f_4927_; lean_object* v___x_4928_; lean_object* v_env_4929_; lean_object* v_nextMacroScope_4930_; lean_object* v_ngen_4931_; lean_object* v_auxDeclNGen_4932_; lean_object* v_traceState_4933_; lean_object* v_recordedDeps_4934_; lean_object* v_messages_4935_; lean_object* v_infoState_4936_; lean_object* v_snapshotTasks_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4957_; 
v___f_4927_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4927_, 0, v_a_4923_);
lean_closure_set(v___f_4927_, 1, v_inst_4920_);
lean_closure_set(v___f_4927_, 2, v_inst_4921_);
lean_closure_set(v___f_4927_, 3, v_b_4924_);
v___x_4928_ = lean_st_ref_take(v_a_4925_);
v_env_4929_ = lean_ctor_get(v___x_4928_, 0);
v_nextMacroScope_4930_ = lean_ctor_get(v___x_4928_, 1);
v_ngen_4931_ = lean_ctor_get(v___x_4928_, 2);
v_auxDeclNGen_4932_ = lean_ctor_get(v___x_4928_, 3);
v_traceState_4933_ = lean_ctor_get(v___x_4928_, 4);
v_recordedDeps_4934_ = lean_ctor_get(v___x_4928_, 6);
v_messages_4935_ = lean_ctor_get(v___x_4928_, 7);
v_infoState_4936_ = lean_ctor_get(v___x_4928_, 8);
v_snapshotTasks_4937_ = lean_ctor_get(v___x_4928_, 9);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4957_ == 0)
{
lean_object* v_unused_4958_; 
v_unused_4958_ = lean_ctor_get(v___x_4928_, 5);
lean_dec(v_unused_4958_);
v___x_4939_ = v___x_4928_;
v_isShared_4940_ = v_isSharedCheck_4957_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_snapshotTasks_4937_);
lean_inc(v_infoState_4936_);
lean_inc(v_messages_4935_);
lean_inc(v_recordedDeps_4934_);
lean_inc(v_traceState_4933_);
lean_inc(v_auxDeclNGen_4932_);
lean_inc(v_ngen_4931_);
lean_inc(v_nextMacroScope_4930_);
lean_inc(v_env_4929_);
lean_dec(v___x_4928_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4957_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v_asyncMode_4941_; uint8_t v_logWrites_4942_; lean_object* v___x_4943_; lean_object* v___y_4945_; lean_object* v___x_4952_; uint8_t v___x_4953_; 
v_asyncMode_4941_ = lean_ctor_get(v_ext_4922_, 2);
lean_inc(v_asyncMode_4941_);
v_logWrites_4942_ = lean_ctor_get_uint8(v_ext_4922_, sizeof(void*)*6);
v___x_4943_ = lean_box(0);
v___x_4952_ = lean_box(0);
v___x_4953_ = 1;
if (v_logWrites_4942_ == 0)
{
lean_object* v___x_4954_; 
v___x_4954_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_ext_4922_, v_env_4929_, v___f_4927_, v_asyncMode_4941_, v___x_4952_, v___x_4953_);
lean_dec(v_asyncMode_4941_);
v___y_4945_ = v___x_4954_;
goto v___jp_4944_;
}
else
{
lean_object* v___x_4955_; lean_object* v___x_4956_; 
lean_inc_ref(v_ext_4922_);
v___x_4955_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_ext_4922_, v_env_4929_);
lean_dec_ref(v_env_4929_);
v___x_4956_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_ext_4922_, v___x_4955_, v___f_4927_, v_asyncMode_4941_, v___x_4952_, v___x_4953_);
lean_dec(v_asyncMode_4941_);
v___y_4945_ = v___x_4956_;
goto v___jp_4944_;
}
v___jp_4944_:
{
lean_object* v___x_4946_; lean_object* v___x_4948_; 
v___x_4946_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 5, v___x_4946_);
lean_ctor_set(v___x_4939_, 0, v___y_4945_);
v___x_4948_ = v___x_4939_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___y_4945_);
lean_ctor_set(v_reuseFailAlloc_4951_, 1, v_nextMacroScope_4930_);
lean_ctor_set(v_reuseFailAlloc_4951_, 2, v_ngen_4931_);
lean_ctor_set(v_reuseFailAlloc_4951_, 3, v_auxDeclNGen_4932_);
lean_ctor_set(v_reuseFailAlloc_4951_, 4, v_traceState_4933_);
lean_ctor_set(v_reuseFailAlloc_4951_, 5, v___x_4946_);
lean_ctor_set(v_reuseFailAlloc_4951_, 6, v_recordedDeps_4934_);
lean_ctor_set(v_reuseFailAlloc_4951_, 7, v_messages_4935_);
lean_ctor_set(v_reuseFailAlloc_4951_, 8, v_infoState_4936_);
lean_ctor_set(v_reuseFailAlloc_4951_, 9, v_snapshotTasks_4937_);
v___x_4948_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
lean_object* v___x_4949_; lean_object* v___x_4950_; 
v___x_4949_ = lean_st_ref_put(v_a_4925_, v___x_4948_);
v___x_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4943_);
return v___x_4950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object* v_inst_4959_, lean_object* v_inst_4960_, lean_object* v_ext_4961_, lean_object* v_a_4962_, lean_object* v_b_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4959_, v_inst_4960_, v_ext_4961_, v_a_4962_, v_b_4963_, v_a_4964_);
lean_dec(v_a_4964_);
return v_res_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object* v_00_u03b1_4967_, lean_object* v_00_u03b2_4968_, lean_object* v_inst_4969_, lean_object* v_inst_4970_, lean_object* v_inst_4971_, lean_object* v_ext_4972_, lean_object* v_a_4973_, lean_object* v_b_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_){
_start:
{
lean_object* v___x_4978_; 
v___x_4978_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_4969_, v_inst_4970_, v_ext_4972_, v_a_4973_, v_b_4974_, v_a_4976_);
return v___x_4978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object* v_00_u03b1_4979_, lean_object* v_00_u03b2_4980_, lean_object* v_inst_4981_, lean_object* v_inst_4982_, lean_object* v_inst_4983_, lean_object* v_ext_4984_, lean_object* v_a_4985_, lean_object* v_b_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_){
_start:
{
lean_object* v_res_4990_; 
v_res_4990_ = l_Lean_Compiler_LCNF_CacheExtension_insert(v_00_u03b1_4979_, v_00_u03b2_4980_, v_inst_4981_, v_inst_4982_, v_inst_4983_, v_ext_4984_, v_a_4985_, v_b_4986_, v_a_4987_, v_a_4988_);
lean_dec(v_a_4988_);
lean_dec_ref(v_a_4987_);
lean_dec(v_inst_4983_);
return v_res_4990_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_4991_; 
v___x_4991_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_4991_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4992_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0);
v___x_4993_ = lean_box(0);
v___x_4994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4993_);
lean_ctor_set(v___x_4994_, 1, v___x_4992_);
return v___x_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object* v_inst_4995_, lean_object* v_inst_4996_, lean_object* v_ext_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_){
_start:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v_env_5003_; lean_object* v_asyncMode_5004_; lean_object* v___x_5005_; uint8_t v___x_5006_; lean_object* v___x_5007_; lean_object* v_snd_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
v___x_5001_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1);
v___x_5002_ = lean_st_ref_get(v_a_4999_);
v_env_5003_ = lean_ctor_get(v___x_5002_, 0);
lean_inc_ref(v_env_5003_);
lean_dec(v___x_5002_);
v_asyncMode_5004_ = lean_ctor_get(v_ext_4997_, 2);
v___x_5005_ = lean_box(0);
v___x_5006_ = 0;
v___x_5007_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5001_, v_ext_4997_, v_env_5003_, v_asyncMode_5004_, v___x_5005_, v___x_5006_);
v_snd_5008_ = lean_ctor_get(v___x_5007_, 1);
lean_inc(v_snd_5008_);
lean_dec(v___x_5007_);
v___x_5009_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4995_, v_inst_4996_, v_snd_5008_, v_a_4998_);
lean_dec(v_snd_5008_);
v___x_5010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5009_);
return v___x_5010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object* v_inst_5011_, lean_object* v_inst_5012_, lean_object* v_ext_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_){
_start:
{
lean_object* v_res_5017_; 
v_res_5017_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_5011_, v_inst_5012_, v_ext_5013_, v_a_5014_, v_a_5015_);
lean_dec(v_a_5015_);
lean_dec_ref(v_ext_5013_);
return v_res_5017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object* v_00_u03b1_5018_, lean_object* v_00_u03b2_5019_, lean_object* v_inst_5020_, lean_object* v_inst_5021_, lean_object* v_inst_5022_, lean_object* v_ext_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_){
_start:
{
lean_object* v___x_5028_; 
v___x_5028_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_5020_, v_inst_5021_, v_ext_5023_, v_a_5024_, v_a_5026_);
return v___x_5028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object* v_00_u03b1_5029_, lean_object* v_00_u03b2_5030_, lean_object* v_inst_5031_, lean_object* v_inst_5032_, lean_object* v_inst_5033_, lean_object* v_ext_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_){
_start:
{
lean_object* v_res_5039_; 
v_res_5039_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(v_00_u03b1_5029_, v_00_u03b2_5030_, v_inst_5031_, v_inst_5032_, v_inst_5033_, v_ext_5034_, v_a_5035_, v_a_5036_, v_a_5037_);
lean_dec(v_a_5037_);
lean_dec_ref(v_a_5036_);
lean_dec_ref(v_ext_5034_);
lean_dec(v_inst_5033_);
return v_res_5039_;
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
