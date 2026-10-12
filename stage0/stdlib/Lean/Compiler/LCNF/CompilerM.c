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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Phase_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Compiler_LCNF_Phase_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Compiler_LCNF_Phase_ctorIdx___impl(v_x_4__boxed_6_);
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
lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Phase_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Compiler_LCNF_Phase_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Compiler_LCNF_Phase_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg(lean_object* v_base_24_){
_start:
{
lean_inc(v_base_24_);
return v_base_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___redArg___boxed(lean_object* v_base_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Compiler_LCNF_Phase_base_elim___redArg(v_base_25_);
lean_dec(v_base_25_);
return v_res_26_;
}
}
lean_object* l_Lean_Compiler_LCNF_Phase_base_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_base_30_){
_start:
{
lean_inc(v_base_30_);
return v_base_30_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Phase_base_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_base_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Compiler_LCNF_Phase_base_elim(lean_box(0), v_t_28_, lean_box(0), v_base_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_base_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_base_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Compiler_LCNF_Phase_base_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_base_35_);
lean_dec(v_base_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(lean_object* v_mono_38_){
_start:
{
lean_inc(v_mono_38_);
return v_mono_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___redArg___boxed(lean_object* v_mono_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(v_mono_39_);
lean_dec(v_mono_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_mono_44_){
_start:
{
lean_inc(v_mono_44_);
return v_mono_44_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Phase_mono_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_mono_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Compiler_LCNF_Phase_mono_elim(lean_box(0), v_t_42_, lean_box(0), v_mono_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_mono_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_mono_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Compiler_LCNF_Phase_mono_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_mono_49_);
lean_dec(v_mono_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(lean_object* v_impure_52_){
_start:
{
lean_inc(v_impure_52_);
return v_impure_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___redArg___boxed(lean_object* v_impure_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(v_impure_53_);
lean_dec(v_impure_53_);
return v_res_54_;
}
}
lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_impure_58_){
_start:
{
lean_inc(v_impure_58_);
return v_impure_58_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Phase_impure_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_impure_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Compiler_LCNF_Phase_impure_elim(lean_box(0), v_t_56_, lean_box(0), v_impure_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_impure_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_impure_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_Compiler_LCNF_Phase_impure_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_impure_63_);
lean_dec(v_impure_63_);
return v_res_65_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_instInhabitedPhase_default(void){
_start:
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_instInhabitedPhase(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
uint8_t l_Lean_Compiler_LCNF_Phase_ofNat(lean_object* v_n_68_){
_start:
{
lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_nat_dec_le(v_n_68_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(1u);
v___x_72_ = lean_nat_dec_le(v_n_68_, v___x_71_);
if (v___x_72_ == 0)
{
uint8_t v___x_73_; 
v___x_73_ = 2;
return v___x_73_;
}
else
{
uint8_t v___x_74_; 
v___x_74_ = 1;
return v___x_74_;
}
}
else
{
uint8_t v___x_75_; 
v___x_75_ = 0;
return v___x_75_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Phase_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_68_ = stack[0].m_obj;
uint8_t v_res_76_;
v_res_76_ = l_Lean_Compiler_LCNF_Phase_ofNat(v_n_68_);
stack->m_num = v_res_76_;
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
uint8_t l_Lean_Compiler_LCNF_instDecidableEqPhase(uint8_t v_x_80_, uint8_t v_y_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_82_ = lean_box(v_x_80_);
v___x_83_ = lean_obj_tag_nat(v___x_82_);
lean_dec(v___x_82_);
v___x_84_ = lean_box(v_y_81_);
v___x_85_ = lean_obj_tag_nat(v___x_84_);
lean_dec(v___x_84_);
v___x_86_ = lean_nat_dec_eq(v___x_83_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instDecidableEqPhase_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_80_ = stack[0].m_num;
uint8_t v_y_81_ = stack[1].m_num;
uint8_t v_res_87_;
v_res_87_ = l_Lean_Compiler_LCNF_instDecidableEqPhase(v_x_80_, v_y_81_);
stack->m_num = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableEqPhase___boxed(lean_object* v_x_88_, lean_object* v_y_89_){
_start:
{
uint8_t v_x_23__boxed_90_; uint8_t v_y_24__boxed_91_; uint8_t v_res_92_; lean_object* v_r_93_; 
v_x_23__boxed_90_ = lean_unbox(v_x_88_);
v_y_24__boxed_91_ = lean_unbox(v_y_89_);
v_res_92_ = l_Lean_Compiler_LCNF_instDecidableEqPhase(v_x_23__boxed_90_, v_y_24__boxed_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t v_x_94_){
_start:
{
if (v_x_94_ == 2)
{
uint8_t v___x_95_; 
v___x_95_ = 1;
return v___x_95_;
}
else
{
uint8_t v___x_96_; 
v___x_96_ = 0;
return v___x_96_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Phase_toPurity_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_94_ = stack[0].m_num;
uint8_t v_res_97_;
v_res_97_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_x_94_);
stack->m_num = v_res_97_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toPurity___boxed(lean_object* v_x_98_){
_start:
{
uint8_t v_x_23__boxed_99_; uint8_t v_res_100_; lean_object* v_r_101_; 
v_x_23__boxed_99_ = lean_unbox(v_x_98_);
v_res_100_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_x_23__boxed_99_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_box(0);
v___x_103_ = lean_unsigned_to_nat(16u);
v___x_104_ = lean_mk_array(v___x_103_, v___x_102_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0);
v___x_106_ = lean_unsigned_to_nat(0u);
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v___x_105_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1);
v___x_109_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
lean_ctor_set(v___x_109_, 2, v___x_108_);
lean_ctor_set(v___x_109_, 3, v___x_108_);
lean_ctor_set(v___x_109_, 4, v___x_108_);
lean_ctor_set(v___x_109_, 5, v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2);
v___x_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v___x_110_);
return v___x_112_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default(void){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default;
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0(void){
_start:
{
lean_object* v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; 
v___x_115_ = l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default;
v___x_116_ = 0;
v___x_117_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_116_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0, &l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0_once, _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext(void){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default;
return v___x_119_;
}
}
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(lean_object* v_00_u03b1_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_127_, 0, v___y_121_);
return v___x_127_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_121_ = stack[1].m_obj;
lean_object* v___y_122_ = stack[2].m_obj;
lean_object* v___y_123_ = stack[3].m_obj;
lean_object* v___y_124_ = stack[4].m_obj;
lean_object* v___y_125_ = stack[5].m_obj;
lean_object* v_res_128_;
v_res_128_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(lean_box(0), v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object* v_00_u03b1_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(v_00_u03b1_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_136_;
}
}
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object* v_00_u03b1_137_, lean_object* v_00_u03b2_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v___x_146_; 
lean_inc(v___y_144_);
lean_inc_ref(v___y_143_);
lean_inc(v___y_142_);
lean_inc_ref(v___y_141_);
v___x_146_ = lean_apply_5(v___y_139_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, lean_box(0));
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_148_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_a_147_);
lean_dec_ref_known(v___x_146_, 1);
lean_inc(v___y_144_);
lean_inc_ref(v___y_143_);
lean_inc(v___y_142_);
lean_inc_ref(v___y_141_);
v___x_148_ = lean_apply_6(v___y_140_, v_a_147_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, lean_box(0));
return v___x_148_;
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
lean_dec_ref(v___y_140_);
v_a_149_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_146_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_146_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_139_ = stack[2].m_obj;
lean_object* v___y_140_ = stack[3].m_obj;
lean_object* v___y_141_ = stack[4].m_obj;
lean_object* v___y_142_ = stack[5].m_obj;
lean_object* v___y_143_ = stack[6].m_obj;
lean_object* v___y_144_ = stack[7].m_obj;
lean_object* v_res_157_;
v_res_157_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_box(0), lean_box(0), v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
stack->m_obj
 = v_res_157_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object* v_00_u03b1_158_, lean_object* v_00_u03b2_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(v_00_u03b1_158_, v_00_u03b2_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
return v_res_167_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0(void){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_instMonadEIO___redArg();
return v___x_168_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0);
v___x_170_ = l_StateRefT_x27_instMonad___redArg(v___x_169_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadCompilerM(void){
_start:
{
lean_object* v___x_175_; lean_object* v_toApplicative_176_; lean_object* v_toFunctor_177_; lean_object* v_toSeq_178_; lean_object* v_toSeqLeft_179_; lean_object* v_toSeqRight_180_; lean_object* v___f_181_; lean_object* v___f_182_; lean_object* v___f_183_; lean_object* v___f_184_; lean_object* v___x_185_; lean_object* v___f_186_; lean_object* v___f_187_; lean_object* v___f_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v_toApplicative_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_219_; 
v___x_175_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_176_ = lean_ctor_get(v___x_175_, 0);
v_toFunctor_177_ = lean_ctor_get(v_toApplicative_176_, 0);
v_toSeq_178_ = lean_ctor_get(v_toApplicative_176_, 2);
v_toSeqLeft_179_ = lean_ctor_get(v_toApplicative_176_, 3);
v_toSeqRight_180_ = lean_ctor_get(v_toApplicative_176_, 4);
v___f_181_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_182_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_177_, 2);
v___f_183_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_183_, 0, v_toFunctor_177_);
v___f_184_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_184_, 0, v_toFunctor_177_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___f_183_);
lean_ctor_set(v___x_185_, 1, v___f_184_);
lean_inc(v_toSeqRight_180_);
v___f_186_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_186_, 0, v_toSeqRight_180_);
lean_inc(v_toSeqLeft_179_);
v___f_187_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_187_, 0, v_toSeqLeft_179_);
lean_inc(v_toSeq_178_);
v___f_188_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_188_, 0, v_toSeq_178_);
v___x_189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_189_, 0, v___x_185_);
lean_ctor_set(v___x_189_, 1, v___f_181_);
lean_ctor_set(v___x_189_, 2, v___f_188_);
lean_ctor_set(v___x_189_, 3, v___f_187_);
lean_ctor_set(v___x_189_, 4, v___f_186_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v___f_182_);
v___x_191_ = l_StateRefT_x27_instMonad___redArg(v___x_190_);
v_toApplicative_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; 
v_unused_220_ = lean_ctor_get(v___x_191_, 1);
lean_dec(v_unused_220_);
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_219_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_toApplicative_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_219_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v_toFunctor_196_; lean_object* v_toSeq_197_; lean_object* v_toSeqLeft_198_; lean_object* v_toSeqRight_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_217_; 
v_toFunctor_196_ = lean_ctor_get(v_toApplicative_192_, 0);
v_toSeq_197_ = lean_ctor_get(v_toApplicative_192_, 2);
v_toSeqLeft_198_ = lean_ctor_get(v_toApplicative_192_, 3);
v_toSeqRight_199_ = lean_ctor_get(v_toApplicative_192_, 4);
v_isSharedCheck_217_ = !lean_is_exclusive(v_toApplicative_192_);
if (v_isSharedCheck_217_ == 0)
{
lean_object* v_unused_218_; 
v_unused_218_ = lean_ctor_get(v_toApplicative_192_, 1);
lean_dec(v_unused_218_);
v___x_201_ = v_toApplicative_192_;
v_isShared_202_ = v_isSharedCheck_217_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_toSeqRight_199_);
lean_inc(v_toSeqLeft_198_);
lean_inc(v_toSeq_197_);
lean_inc(v_toFunctor_196_);
lean_dec(v_toApplicative_192_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_217_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___f_203_; lean_object* v___f_204_; lean_object* v___f_205_; lean_object* v___f_206_; lean_object* v___x_207_; lean_object* v___f_208_; lean_object* v___f_209_; lean_object* v___f_210_; lean_object* v___x_212_; 
v___f_203_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_204_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_196_);
v___f_205_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_205_, 0, v_toFunctor_196_);
v___f_206_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_206_, 0, v_toFunctor_196_);
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v___f_205_);
lean_ctor_set(v___x_207_, 1, v___f_206_);
v___f_208_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_208_, 0, v_toSeqRight_199_);
v___f_209_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_209_, 0, v_toSeqLeft_198_);
v___f_210_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_210_, 0, v_toSeq_197_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 4, v___f_208_);
lean_ctor_set(v___x_201_, 3, v___f_209_);
lean_ctor_set(v___x_201_, 2, v___f_210_);
lean_ctor_set(v___x_201_, 1, v___f_203_);
lean_ctor_set(v___x_201_, 0, v___x_207_);
v___x_212_ = v___x_201_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___f_203_);
lean_ctor_set(v_reuseFailAlloc_216_, 2, v___f_210_);
lean_ctor_set(v_reuseFailAlloc_216_, 3, v___f_209_);
lean_ctor_set(v_reuseFailAlloc_216_, 4, v___f_208_);
v___x_212_ = v_reuseFailAlloc_216_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_214_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 1, v___f_204_);
lean_ctor_set(v___x_194_, 0, v___x_212_);
v___x_214_ = v___x_194_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___f_204_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_withPhase___redArg(uint8_t v_phase_221_, lean_object* v_x_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_config_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_config_228_ = lean_ctor_get(v_a_223_, 0);
lean_inc_ref(v_config_228_);
v___x_229_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_229_, 0, v_config_228_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*1, v_phase_221_);
lean_inc(v_a_226_);
lean_inc_ref(v_a_225_);
lean_inc(v_a_224_);
v___x_230_ = lean_apply_5(v_x_222_, v___x_229_, v_a_224_, v_a_225_, v_a_226_, lean_box(0));
return v___x_230_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_withPhase___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_221_ = stack[0].m_num;
lean_object* v_x_222_ = stack[1].m_obj;
lean_object* v_a_223_ = stack[2].m_obj;
lean_object* v_a_224_ = stack[3].m_obj;
lean_object* v_a_225_ = stack[4].m_obj;
lean_object* v_a_226_ = stack[5].m_obj;
lean_object* v_res_231_;
v_res_231_ = l_Lean_Compiler_LCNF_withPhase___redArg(v_phase_221_, v_x_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
stack->m_obj
 = v_res_231_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___redArg___boxed(lean_object* v_phase_232_, lean_object* v_x_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
uint8_t v_phase_boxed_239_; lean_object* v_res_240_; 
v_phase_boxed_239_ = lean_unbox(v_phase_232_);
v_res_240_ = l_Lean_Compiler_LCNF_withPhase___redArg(v_phase_boxed_239_, v_x_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
return v_res_240_;
}
}
lean_object* l_Lean_Compiler_LCNF_withPhase(lean_object* v_00_u03b1_241_, uint8_t v_phase_242_, lean_object* v_x_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_config_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_config_249_ = lean_ctor_get(v_a_244_, 0);
lean_inc_ref(v_config_249_);
v___x_250_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_250_, 0, v_config_249_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*1, v_phase_242_);
lean_inc(v_a_247_);
lean_inc_ref(v_a_246_);
lean_inc(v_a_245_);
v___x_251_ = lean_apply_5(v_x_243_, v___x_250_, v_a_245_, v_a_246_, v_a_247_, lean_box(0));
return v___x_251_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_withPhase_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_242_ = stack[1].m_num;
lean_object* v_x_243_ = stack[2].m_obj;
lean_object* v_a_244_ = stack[3].m_obj;
lean_object* v_a_245_ = stack[4].m_obj;
lean_object* v_a_246_ = stack[5].m_obj;
lean_object* v_a_247_ = stack[6].m_obj;
lean_object* v_res_252_;
v_res_252_ = l_Lean_Compiler_LCNF_withPhase(lean_box(0), v_phase_242_, v_x_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
stack->m_obj
 = v_res_252_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withPhase___boxed(lean_object* v_00_u03b1_253_, lean_object* v_phase_254_, lean_object* v_x_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
uint8_t v_phase_boxed_261_; lean_object* v_res_262_; 
v_phase_boxed_261_ = lean_unbox(v_phase_254_);
v_res_262_ = l_Lean_Compiler_LCNF_withPhase(v_00_u03b1_253_, v_phase_boxed_261_, v_x_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
return v_res_262_;
}
}
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object* v_a_263_){
_start:
{
uint8_t v_phase_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v_phase_265_ = lean_ctor_get_uint8(v_a_263_, sizeof(void*)*1);
v___x_266_ = lean_box(v_phase_265_);
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_getPhase___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_263_ = stack[0].m_obj;
lean_object* v_res_268_;
v_res_268_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_263_);
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___redArg___boxed(lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_269_);
lean_dec_ref(v_a_269_);
return v_res_271_;
}
}
lean_object* l_Lean_Compiler_LCNF_getPhase(lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_272_);
return v___x_277_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_getPhase_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_272_ = stack[0].m_obj;
lean_object* v_a_273_ = stack[1].m_obj;
lean_object* v_a_274_ = stack[2].m_obj;
lean_object* v_a_275_ = stack[3].m_obj;
lean_object* v_res_278_;
v_res_278_ = l_Lean_Compiler_LCNF_getPhase(v_a_272_, v_a_273_, v_a_274_, v_a_275_);
stack->m_obj
 = v_res_278_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPhase___boxed(lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Compiler_LCNF_getPhase(v_a_279_, v_a_280_, v_a_281_, v_a_282_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
return v_res_284_;
}
}
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object* v_a_285_){
_start:
{
lean_object* v___x_287_; lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_298_; 
v___x_287_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_285_);
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_298_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_298_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_298_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
uint8_t v___x_292_; uint8_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_292_ = lean_unbox(v_a_288_);
lean_dec(v_a_288_);
v___x_293_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_292_);
v___x_294_ = lean_box(v___x_293_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_294_);
v___x_296_ = v___x_290_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_getPurity___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_285_ = stack[0].m_obj;
lean_object* v_res_299_;
v_res_299_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_285_);
stack->m_obj
 = v_res_299_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___redArg___boxed(lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_300_);
lean_dec_ref(v_a_300_);
return v_res_302_;
}
}
lean_object* l_Lean_Compiler_LCNF_getPurity(lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_303_);
return v___x_308_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_getPurity_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_303_ = stack[0].m_obj;
lean_object* v_a_304_ = stack[1].m_obj;
lean_object* v_a_305_ = stack[2].m_obj;
lean_object* v_a_306_ = stack[3].m_obj;
lean_object* v_res_309_;
v_res_309_ = l_Lean_Compiler_LCNF_getPurity(v_a_303_, v_a_304_, v_a_305_, v_a_306_);
stack->m_obj
 = v_res_309_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPurity___boxed(lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Compiler_LCNF_getPurity(v_a_310_, v_a_311_, v_a_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
return v_res_315_;
}
}
lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg(lean_object* v_a_316_){
_start:
{
lean_object* v___x_318_; lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_334_; 
v___x_318_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_316_);
v_a_319_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_334_ == 0)
{
v___x_321_ = v___x_318_;
v_isShared_322_ = v_isSharedCheck_334_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_318_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_334_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
uint8_t v___x_323_; 
v___x_323_ = lean_unbox(v_a_319_);
lean_dec(v_a_319_);
if (v___x_323_ == 0)
{
uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_324_ = 1;
v___x_325_ = lean_box(v___x_324_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_325_);
v___x_327_ = v___x_321_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
else
{
uint8_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_329_ = 0;
v___x_330_ = lean_box(v___x_329_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_330_);
v___x_332_ = v___x_321_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_inBasePhase___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_316_ = stack[0].m_obj;
lean_object* v_res_335_;
v_res_335_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_316_);
stack->m_obj
 = v_res_335_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___redArg___boxed(lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_336_);
lean_dec_ref(v_a_336_);
return v_res_338_;
}
}
lean_object* l_Lean_Compiler_LCNF_inBasePhase(lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_339_);
return v___x_344_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_inBasePhase_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_339_ = stack[0].m_obj;
lean_object* v_a_340_ = stack[1].m_obj;
lean_object* v_a_341_ = stack[2].m_obj;
lean_object* v_a_342_ = stack[3].m_obj;
lean_object* v_res_345_;
v_res_345_ = l_Lean_Compiler_LCNF_inBasePhase(v_a_339_, v_a_340_, v_a_341_, v_a_342_);
stack->m_obj
 = v_res_345_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inBasePhase___boxed(lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Compiler_LCNF_inBasePhase(v_a_346_, v_a_347_, v_a_348_, v_a_349_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
return v_res_351_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0(void){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_352_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_355_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_356_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
lean_ctor_set(v___x_358_, 2, v___x_357_);
lean_ctor_set(v___x_358_, 3, v___x_357_);
lean_ctor_set(v___x_358_, 4, v___x_356_);
lean_ctor_set(v___x_358_, 5, v___x_356_);
lean_ctor_set(v___x_358_, 6, v___x_356_);
lean_ctor_set(v___x_358_, 7, v___x_356_);
lean_ctor_set(v___x_358_, 8, v___x_356_);
lean_ctor_set(v___x_358_, 9, v___x_356_);
lean_ctor_set(v___x_358_, 10, v___x_356_);
lean_ctor_set(v___x_358_, 11, v___x_355_);
return v___x_358_;
}
}
lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(lean_object* v_msgData_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; lean_object* v_env_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_365_ = lean_st_ref_get(v___y_363_);
v_env_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc_ref(v_env_366_);
lean_dec(v___x_365_);
v___x_367_ = lean_st_ref_get(v___y_361_);
v___x_368_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_360_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_390_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_390_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_390_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_390_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v_lctx_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_388_; 
v_lctx_373_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_388_ == 0)
{
lean_object* v_unused_389_; 
v_unused_389_ = lean_ctor_get(v___x_367_, 1);
lean_dec(v_unused_389_);
v___x_375_ = v___x_367_;
v_isShared_376_ = v_isSharedCheck_388_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_lctx_373_);
lean_dec(v___x_367_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_388_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_377_ = lean_unbox(v_a_369_);
lean_dec(v_a_369_);
v___x_378_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_373_, v___x_377_);
lean_dec_ref(v_lctx_373_);
v___x_379_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_362_);
v___x_380_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
v___x_381_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_381_, 0, v_env_366_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
lean_ctor_set(v___x_381_, 2, v___x_378_);
lean_ctor_set(v___x_381_, 3, v___x_379_);
if (v_isShared_376_ == 0)
{
lean_ctor_set_tag(v___x_375_, 3);
lean_ctor_set(v___x_375_, 1, v_msgData_359_);
lean_ctor_set(v___x_375_, 0, v___x_381_);
v___x_383_ = v___x_375_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_msgData_359_);
v___x_383_ = v_reuseFailAlloc_387_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_385_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_383_);
v___x_385_ = v___x_371_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec(v___x_367_);
lean_dec_ref(v_env_366_);
lean_dec_ref(v_msgData_359_);
v_a_391_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_368_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_368_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_359_ = stack[0].m_obj;
lean_object* v___y_360_ = stack[1].m_obj;
lean_object* v___y_361_ = stack[2].m_obj;
lean_object* v___y_362_ = stack[3].m_obj;
lean_object* v___y_363_ = stack[4].m_obj;
lean_object* v_res_399_;
v_res_399_ = l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(v_msgData_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
stack->m_obj
 = v_res_399_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed(lean_object* v_msgData_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(v_msgData_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
return v_res_406_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(lean_object* v_msg_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_ref_415_; lean_object* v___x_416_; lean_object* v_env_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_ref_415_ = lean_ctor_get(v___y_412_, 2);
v___x_416_ = lean_st_ref_get(v___y_413_);
v_env_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc_ref(v_env_417_);
lean_dec(v___x_416_);
v___x_418_ = lean_st_ref_get(v___y_411_);
v___x_419_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_410_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_442_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_442_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_442_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_442_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v_lctx_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_440_; 
v_lctx_424_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; 
v_unused_441_ = lean_ctor_get(v___x_418_, 1);
lean_dec(v_unused_441_);
v___x_426_ = v___x_418_;
v_isShared_427_ = v_isSharedCheck_440_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_lctx_424_);
lean_dec(v___x_418_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_440_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_428_ = lean_unbox(v_a_420_);
lean_dec(v_a_420_);
v___x_429_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_424_, v___x_428_);
lean_dec_ref(v_lctx_424_);
v___x_430_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_412_);
v___x_431_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
v___x_432_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_432_, 0, v_env_417_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
lean_ctor_set(v___x_432_, 2, v___x_429_);
lean_ctor_set(v___x_432_, 3, v___x_430_);
if (v_isShared_427_ == 0)
{
lean_ctor_set_tag(v___x_426_, 3);
lean_ctor_set(v___x_426_, 1, v_msg_409_);
lean_ctor_set(v___x_426_, 0, v___x_432_);
v___x_434_ = v___x_426_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_msg_409_);
v___x_434_ = v_reuseFailAlloc_439_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
lean_inc(v_ref_415_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v_ref_415_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
if (v_isShared_423_ == 0)
{
lean_ctor_set_tag(v___x_422_, 1);
lean_ctor_set(v___x_422_, 0, v___x_435_);
v___x_437_ = v___x_422_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec(v___x_418_);
lean_dec_ref(v_env_417_);
lean_dec_ref(v_msg_409_);
v_a_443_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_419_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_419_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_409_ = stack[0].m_obj;
lean_object* v___y_410_ = stack[1].m_obj;
lean_object* v___y_411_ = stack[2].m_obj;
lean_object* v___y_412_ = stack[3].m_obj;
lean_object* v___y_413_ = stack[4].m_obj;
lean_object* v_res_451_;
v_res_451_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
stack->m_obj
 = v_res_451_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg___boxed(lean_object* v_msg_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
return v_res_458_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(lean_object* v_00_u03b1_459_, lean_object* v_msg_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v_msg_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
return v___x_466_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_460_ = stack[1].m_obj;
lean_object* v___y_461_ = stack[2].m_obj;
lean_object* v___y_462_ = stack[3].m_obj;
lean_object* v___y_463_ = stack[4].m_obj;
lean_object* v___y_464_ = stack[5].m_obj;
lean_object* v_res_467_;
v_res_467_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(lean_box(0), v_msg_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
stack->m_obj
 = v_res_467_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___boxed(lean_object* v_00_u03b1_468_, lean_object* v_msg_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(v_00_u03b1_468_, v_msg_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(lean_object* v_a_476_, lean_object* v_x_477_){
_start:
{
if (lean_obj_tag(v_x_477_) == 0)
{
lean_object* v___x_478_; 
v___x_478_ = lean_box(0);
return v___x_478_;
}
else
{
lean_object* v_key_479_; lean_object* v_value_480_; lean_object* v_tail_481_; uint8_t v___x_482_; 
v_key_479_ = lean_ctor_get(v_x_477_, 0);
v_value_480_ = lean_ctor_get(v_x_477_, 1);
v_tail_481_ = lean_ctor_get(v_x_477_, 2);
v___x_482_ = l_Lean_instBEqFVarId_beq(v_key_479_, v_a_476_);
if (v___x_482_ == 0)
{
v_x_477_ = v_tail_481_;
goto _start;
}
else
{
lean_object* v___x_484_; 
lean_inc(v_value_480_);
v___x_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_484_, 0, v_value_480_);
return v___x_484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg___boxed(lean_object* v_a_485_, lean_object* v_x_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_485_, v_x_486_);
lean_dec(v_x_486_);
lean_dec(v_a_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object* v_m_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_buckets_490_; lean_object* v___x_491_; uint64_t v___x_492_; uint64_t v___x_493_; uint64_t v___x_494_; uint64_t v_fold_495_; uint64_t v___x_496_; uint64_t v___x_497_; uint64_t v___x_498_; size_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_buckets_490_ = lean_ctor_get(v_m_488_, 1);
v___x_491_ = lean_array_get_size(v_buckets_490_);
v___x_492_ = l_Lean_instHashableFVarId_hash(v_a_489_);
v___x_493_ = 32ULL;
v___x_494_ = lean_uint64_shift_right(v___x_492_, v___x_493_);
v_fold_495_ = lean_uint64_xor(v___x_492_, v___x_494_);
v___x_496_ = 16ULL;
v___x_497_ = lean_uint64_shift_right(v_fold_495_, v___x_496_);
v___x_498_ = lean_uint64_xor(v_fold_495_, v___x_497_);
v___x_499_ = lean_uint64_to_usize(v___x_498_);
v___x_500_ = lean_usize_of_nat(v___x_491_);
v___x_501_ = ((size_t)1ULL);
v___x_502_ = lean_usize_sub(v___x_500_, v___x_501_);
v___x_503_ = lean_usize_land(v___x_499_, v___x_502_);
v___x_504_ = lean_array_uget_borrowed(v_buckets_490_, v___x_503_);
v___x_505_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_489_, v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg___boxed(lean_object* v_m_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_506_, v_a_507_);
lean_dec(v_a_507_);
lean_dec_ref(v_m_506_);
return v_res_508_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getType___closed__1(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = ((lean_object*)(l_Lean_Compiler_LCNF_getType___closed__0));
v___x_511_ = l_Lean_stringToMessageData(v___x_510_);
return v___x_511_;
}
}
lean_object* l_Lean_Compiler_LCNF_getType(lean_object* v_fvarId_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_518_; lean_object* v_lctx_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_584_; 
v___x_518_ = lean_st_ref_get(v_a_514_);
v_lctx_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v___x_518_, 1);
lean_dec(v_unused_585_);
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_584_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_lctx_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_584_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_513_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_575_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_575_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_575_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_575_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___y_529_; lean_object* v___y_543_; lean_object* v___y_558_; uint8_t v___x_572_; 
v___x_572_ = lean_unbox(v_a_524_);
if (v___x_572_ == 0)
{
lean_object* v_letDeclsPure_573_; 
v_letDeclsPure_573_ = lean_ctor_get(v_lctx_519_, 2);
lean_inc_ref(v_letDeclsPure_573_);
v___y_558_ = v_letDeclsPure_573_;
goto v___jp_557_;
}
else
{
lean_object* v_letDeclsImpure_574_; 
v_letDeclsImpure_574_ = lean_ctor_get(v_lctx_519_, 3);
lean_inc_ref(v_letDeclsImpure_574_);
v___y_558_ = v_letDeclsImpure_574_;
goto v___jp_557_;
}
v___jp_528_:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_529_, v_fvarId_512_);
lean_dec_ref(v___y_529_);
if (lean_obj_tag(v___x_530_) == 1)
{
lean_object* v_val_531_; lean_object* v_type_532_; lean_object* v___x_534_; 
lean_del_object(v___x_521_);
lean_dec(v_fvarId_512_);
v_val_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_val_531_);
lean_dec_ref_known(v___x_530_, 1);
v_type_532_ = lean_ctor_get(v_val_531_, 3);
lean_inc_ref(v_type_532_);
lean_dec(v_val_531_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v_type_532_);
v___x_534_ = v___x_526_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_type_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
lean_dec(v___x_530_);
lean_del_object(v___x_526_);
v___x_536_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_537_ = l_Lean_MessageData_ofName(v_fvarId_512_);
if (v_isShared_522_ == 0)
{
lean_ctor_set_tag(v___x_521_, 7);
lean_ctor_set(v___x_521_, 1, v___x_537_);
lean_ctor_set(v___x_521_, 0, v___x_536_);
v___x_539_ = v___x_521_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_537_);
v___x_539_ = v_reuseFailAlloc_541_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_539_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
return v___x_540_;
}
}
}
v___jp_542_:
{
lean_object* v___x_544_; 
v___x_544_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_543_, v_fvarId_512_);
lean_dec_ref(v___y_543_);
if (lean_obj_tag(v___x_544_) == 1)
{
lean_object* v_val_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_553_; 
lean_del_object(v___x_526_);
lean_dec(v_a_524_);
lean_del_object(v___x_521_);
lean_dec_ref(v_lctx_519_);
lean_dec(v_fvarId_512_);
v_val_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_553_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_553_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_val_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_553_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v_type_549_; lean_object* v___x_551_; 
v_type_549_ = lean_ctor_get(v_val_545_, 2);
lean_inc_ref(v_type_549_);
lean_dec(v_val_545_);
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 0);
lean_ctor_set(v___x_547_, 0, v_type_549_);
v___x_551_ = v___x_547_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_type_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
else
{
uint8_t v___x_554_; 
lean_dec(v___x_544_);
v___x_554_ = lean_unbox(v_a_524_);
lean_dec(v_a_524_);
if (v___x_554_ == 0)
{
lean_object* v_funDeclsPure_555_; 
v_funDeclsPure_555_ = lean_ctor_get(v_lctx_519_, 4);
lean_inc_ref(v_funDeclsPure_555_);
lean_dec_ref(v_lctx_519_);
v___y_529_ = v_funDeclsPure_555_;
goto v___jp_528_;
}
else
{
lean_object* v_funDeclsImpure_556_; 
v_funDeclsImpure_556_ = lean_ctor_get(v_lctx_519_, 5);
lean_inc_ref(v_funDeclsImpure_556_);
lean_dec_ref(v_lctx_519_);
v___y_529_ = v_funDeclsImpure_556_;
goto v___jp_528_;
}
}
}
v___jp_557_:
{
lean_object* v___x_559_; 
v___x_559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_558_, v_fvarId_512_);
lean_dec_ref(v___y_558_);
if (lean_obj_tag(v___x_559_) == 1)
{
lean_object* v_val_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_568_; 
lean_del_object(v___x_526_);
lean_dec(v_a_524_);
lean_del_object(v___x_521_);
lean_dec_ref(v_lctx_519_);
lean_dec(v_fvarId_512_);
v_val_560_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_568_ == 0)
{
v___x_562_ = v___x_559_;
v_isShared_563_ = v_isSharedCheck_568_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_val_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_568_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v_type_564_; lean_object* v___x_566_; 
v_type_564_ = lean_ctor_get(v_val_560_, 2);
lean_inc_ref(v_type_564_);
lean_dec(v_val_560_);
if (v_isShared_563_ == 0)
{
lean_ctor_set_tag(v___x_562_, 0);
lean_ctor_set(v___x_562_, 0, v_type_564_);
v___x_566_ = v___x_562_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_type_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
else
{
uint8_t v___x_569_; 
lean_dec(v___x_559_);
v___x_569_ = lean_unbox(v_a_524_);
if (v___x_569_ == 0)
{
lean_object* v_paramsPure_570_; 
v_paramsPure_570_ = lean_ctor_get(v_lctx_519_, 0);
lean_inc_ref(v_paramsPure_570_);
v___y_543_ = v_paramsPure_570_;
goto v___jp_542_;
}
else
{
lean_object* v_paramsImpure_571_; 
v_paramsImpure_571_ = lean_ctor_get(v_lctx_519_, 1);
lean_inc_ref(v_paramsImpure_571_);
v___y_543_ = v_paramsImpure_571_;
goto v___jp_542_;
}
}
}
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_del_object(v___x_521_);
lean_dec_ref(v_lctx_519_);
lean_dec(v_fvarId_512_);
v_a_576_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_523_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_523_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_getType_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_512_ = stack[0].m_obj;
lean_object* v_a_513_ = stack[1].m_obj;
lean_object* v_a_514_ = stack[2].m_obj;
lean_object* v_a_515_ = stack[3].m_obj;
lean_object* v_a_516_ = stack[4].m_obj;
lean_object* v_res_586_;
v_res_586_ = l_Lean_Compiler_LCNF_getType(v_fvarId_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
stack->m_obj
 = v_res_586_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getType___boxed(lean_object* v_fvarId_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Compiler_LCNF_getType(v_fvarId_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(lean_object* v_00_u03b2_594_, lean_object* v_m_595_, lean_object* v_a_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_595_, v_a_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(lean_object* v_00_u03b2_598_, lean_object* v_m_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(v_00_u03b2_598_, v_m_599_, v_a_600_);
lean_dec(v_a_600_);
lean_dec_ref(v_m_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(lean_object* v_00_u03b2_602_, lean_object* v_a_603_, lean_object* v_x_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_603_, v_x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_606_, lean_object* v_a_607_, lean_object* v_x_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(v_00_u03b2_606_, v_a_607_, v_x_608_);
lean_dec(v_x_608_);
lean_dec(v_a_607_);
return v_res_609_;
}
}
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object* v_fvarId_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v___x_616_; lean_object* v_lctx_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_682_; 
v___x_616_ = lean_st_ref_get(v_a_612_);
v_lctx_617_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; 
v_unused_683_ = lean_ctor_get(v___x_616_, 1);
lean_dec(v_unused_683_);
v___x_619_ = v___x_616_;
v_isShared_620_ = v_isSharedCheck_682_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_lctx_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_682_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_611_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_673_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_673_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_673_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_673_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___y_627_; lean_object* v___y_641_; lean_object* v___y_656_; uint8_t v___x_670_; 
v___x_670_ = lean_unbox(v_a_622_);
if (v___x_670_ == 0)
{
lean_object* v_letDeclsPure_671_; 
v_letDeclsPure_671_ = lean_ctor_get(v_lctx_617_, 2);
lean_inc_ref(v_letDeclsPure_671_);
v___y_656_ = v_letDeclsPure_671_;
goto v___jp_655_;
}
else
{
lean_object* v_letDeclsImpure_672_; 
v_letDeclsImpure_672_ = lean_ctor_get(v_lctx_617_, 3);
lean_inc_ref(v_letDeclsImpure_672_);
v___y_656_ = v_letDeclsImpure_672_;
goto v___jp_655_;
}
v___jp_626_:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_627_, v_fvarId_610_);
lean_dec_ref(v___y_627_);
if (lean_obj_tag(v___x_628_) == 1)
{
lean_object* v_val_629_; lean_object* v_binderName_630_; lean_object* v___x_632_; 
lean_del_object(v___x_619_);
lean_dec(v_fvarId_610_);
v_val_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_val_629_);
lean_dec_ref_known(v___x_628_, 1);
v_binderName_630_ = lean_ctor_get(v_val_629_, 1);
lean_inc(v_binderName_630_);
lean_dec(v_val_629_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v_binderName_630_);
v___x_632_ = v___x_624_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_binderName_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
lean_dec(v___x_628_);
lean_del_object(v___x_624_);
v___x_634_ = lean_obj_once(&l_Lean_Compiler_LCNF_getType___closed__1, &l_Lean_Compiler_LCNF_getType___closed__1_once, _init_l_Lean_Compiler_LCNF_getType___closed__1);
v___x_635_ = l_Lean_MessageData_ofName(v_fvarId_610_);
if (v_isShared_620_ == 0)
{
lean_ctor_set_tag(v___x_619_, 7);
lean_ctor_set(v___x_619_, 1, v___x_635_);
lean_ctor_set(v___x_619_, 0, v___x_634_);
v___x_637_ = v___x_619_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___x_635_);
v___x_637_ = v_reuseFailAlloc_639_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_637_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
return v___x_638_;
}
}
}
v___jp_640_:
{
lean_object* v___x_642_; 
v___x_642_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_641_, v_fvarId_610_);
lean_dec_ref(v___y_641_);
if (lean_obj_tag(v___x_642_) == 1)
{
lean_object* v_val_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_651_; 
lean_del_object(v___x_624_);
lean_dec(v_a_622_);
lean_del_object(v___x_619_);
lean_dec_ref(v_lctx_617_);
lean_dec(v_fvarId_610_);
v_val_643_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_651_ == 0)
{
v___x_645_ = v___x_642_;
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_val_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v_binderName_647_; lean_object* v___x_649_; 
v_binderName_647_ = lean_ctor_get(v_val_643_, 1);
lean_inc(v_binderName_647_);
lean_dec(v_val_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 0);
lean_ctor_set(v___x_645_, 0, v_binderName_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_binderName_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
else
{
uint8_t v___x_652_; 
lean_dec(v___x_642_);
v___x_652_ = lean_unbox(v_a_622_);
lean_dec(v_a_622_);
if (v___x_652_ == 0)
{
lean_object* v_funDeclsPure_653_; 
v_funDeclsPure_653_ = lean_ctor_get(v_lctx_617_, 4);
lean_inc_ref(v_funDeclsPure_653_);
lean_dec_ref(v_lctx_617_);
v___y_627_ = v_funDeclsPure_653_;
goto v___jp_626_;
}
else
{
lean_object* v_funDeclsImpure_654_; 
v_funDeclsImpure_654_ = lean_ctor_get(v_lctx_617_, 5);
lean_inc_ref(v_funDeclsImpure_654_);
lean_dec_ref(v_lctx_617_);
v___y_627_ = v_funDeclsImpure_654_;
goto v___jp_626_;
}
}
}
v___jp_655_:
{
lean_object* v___x_657_; 
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_656_, v_fvarId_610_);
lean_dec_ref(v___y_656_);
if (lean_obj_tag(v___x_657_) == 1)
{
lean_object* v_val_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_666_; 
lean_del_object(v___x_624_);
lean_dec(v_a_622_);
lean_del_object(v___x_619_);
lean_dec_ref(v_lctx_617_);
lean_dec(v_fvarId_610_);
v_val_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_666_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_val_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_binderName_662_; lean_object* v___x_664_; 
v_binderName_662_ = lean_ctor_get(v_val_658_, 1);
lean_inc(v_binderName_662_);
lean_dec(v_val_658_);
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 0);
lean_ctor_set(v___x_660_, 0, v_binderName_662_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_binderName_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
else
{
uint8_t v___x_667_; 
lean_dec(v___x_657_);
v___x_667_ = lean_unbox(v_a_622_);
if (v___x_667_ == 0)
{
lean_object* v_paramsPure_668_; 
v_paramsPure_668_ = lean_ctor_get(v_lctx_617_, 0);
lean_inc_ref(v_paramsPure_668_);
v___y_641_ = v_paramsPure_668_;
goto v___jp_640_;
}
else
{
lean_object* v_paramsImpure_669_; 
v_paramsImpure_669_ = lean_ctor_get(v_lctx_617_, 1);
lean_inc_ref(v_paramsImpure_669_);
v___y_641_ = v_paramsImpure_669_;
goto v___jp_640_;
}
}
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_del_object(v___x_619_);
lean_dec_ref(v_lctx_617_);
lean_dec(v_fvarId_610_);
v_a_674_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_621_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_621_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_getBinderName_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_610_ = stack[0].m_obj;
lean_object* v_a_611_ = stack[1].m_obj;
lean_object* v_a_612_ = stack[2].m_obj;
lean_object* v_a_613_ = stack[3].m_obj;
lean_object* v_a_614_ = stack[4].m_obj;
lean_object* v_res_684_;
v_res_684_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
stack->m_obj
 = v_res_684_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBinderName___boxed(lean_object* v_fvarId_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
return v_res_691_;
}
}
lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t v_pu_692_, lean_object* v_fvarId_693_, lean_object* v_a_694_){
_start:
{
lean_object* v___x_696_; lean_object* v___y_698_; 
v___x_696_ = lean_st_ref_get(v_a_694_);
if (v_pu_692_ == 0)
{
lean_object* v_lctx_701_; lean_object* v_paramsPure_702_; 
v_lctx_701_ = lean_ctor_get(v___x_696_, 0);
lean_inc_ref(v_lctx_701_);
lean_dec(v___x_696_);
v_paramsPure_702_ = lean_ctor_get(v_lctx_701_, 0);
lean_inc_ref(v_paramsPure_702_);
lean_dec_ref(v_lctx_701_);
v___y_698_ = v_paramsPure_702_;
goto v___jp_697_;
}
else
{
lean_object* v_lctx_703_; lean_object* v_paramsImpure_704_; 
v_lctx_703_ = lean_ctor_get(v___x_696_, 0);
lean_inc_ref(v_lctx_703_);
lean_dec(v___x_696_);
v_paramsImpure_704_ = lean_ctor_get(v_lctx_703_, 1);
lean_inc_ref(v_paramsImpure_704_);
lean_dec_ref(v_lctx_703_);
v___y_698_ = v_paramsImpure_704_;
goto v___jp_697_;
}
v___jp_697_:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_698_, v_fvarId_693_);
lean_dec_ref(v___y_698_);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_findParam_x3f___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_692_ = stack[0].m_num;
lean_object* v_fvarId_693_ = stack[1].m_obj;
lean_object* v_a_694_ = stack[2].m_obj;
lean_object* v_res_705_;
v_res_705_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_692_, v_fvarId_693_, v_a_694_);
stack->m_obj
 = v_res_705_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(lean_object* v_pu_706_, lean_object* v_fvarId_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
uint8_t v_pu_boxed_710_; lean_object* v_res_711_; 
v_pu_boxed_710_ = lean_unbox(v_pu_706_);
v_res_711_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_boxed_710_, v_fvarId_707_, v_a_708_);
lean_dec(v_a_708_);
lean_dec(v_fvarId_707_);
return v_res_711_;
}
}
lean_object* l_Lean_Compiler_LCNF_findParam_x3f(uint8_t v_pu_712_, lean_object* v_fvarId_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_712_, v_fvarId_713_, v_a_715_);
return v___x_719_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_findParam_x3f_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_712_ = stack[0].m_num;
lean_object* v_fvarId_713_ = stack[1].m_obj;
lean_object* v_a_714_ = stack[2].m_obj;
lean_object* v_a_715_ = stack[3].m_obj;
lean_object* v_a_716_ = stack[4].m_obj;
lean_object* v_a_717_ = stack[5].m_obj;
lean_object* v_res_720_;
v_res_720_ = l_Lean_Compiler_LCNF_findParam_x3f(v_pu_712_, v_fvarId_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
stack->m_obj
 = v_res_720_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findParam_x3f___boxed(lean_object* v_pu_721_, lean_object* v_fvarId_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
uint8_t v_pu_boxed_728_; lean_object* v_res_729_; 
v_pu_boxed_728_ = lean_unbox(v_pu_721_);
v_res_729_ = l_Lean_Compiler_LCNF_findParam_x3f(v_pu_boxed_728_, v_fvarId_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_fvarId_722_);
return v_res_729_;
}
}
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t v_pu_730_, lean_object* v_fvarId_731_, lean_object* v_a_732_){
_start:
{
lean_object* v___x_734_; lean_object* v___y_736_; 
v___x_734_ = lean_st_ref_get(v_a_732_);
if (v_pu_730_ == 0)
{
lean_object* v_lctx_739_; lean_object* v_letDeclsPure_740_; 
v_lctx_739_ = lean_ctor_get(v___x_734_, 0);
lean_inc_ref(v_lctx_739_);
lean_dec(v___x_734_);
v_letDeclsPure_740_ = lean_ctor_get(v_lctx_739_, 2);
lean_inc_ref(v_letDeclsPure_740_);
lean_dec_ref(v_lctx_739_);
v___y_736_ = v_letDeclsPure_740_;
goto v___jp_735_;
}
else
{
lean_object* v_lctx_741_; lean_object* v_letDeclsImpure_742_; 
v_lctx_741_ = lean_ctor_get(v___x_734_, 0);
lean_inc_ref(v_lctx_741_);
lean_dec(v___x_734_);
v_letDeclsImpure_742_ = lean_ctor_get(v_lctx_741_, 3);
lean_inc_ref(v_letDeclsImpure_742_);
lean_dec_ref(v_lctx_741_);
v___y_736_ = v_letDeclsImpure_742_;
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_730_ = stack[0].m_num;
lean_object* v_fvarId_731_ = stack[1].m_obj;
lean_object* v_a_732_ = stack[2].m_obj;
lean_object* v_res_743_;
v_res_743_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_730_, v_fvarId_731_, v_a_732_);
stack->m_obj
 = v_res_743_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(lean_object* v_pu_744_, lean_object* v_fvarId_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
uint8_t v_pu_boxed_748_; lean_object* v_res_749_; 
v_pu_boxed_748_ = lean_unbox(v_pu_744_);
v_res_749_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_boxed_748_, v_fvarId_745_, v_a_746_);
lean_dec(v_a_746_);
lean_dec(v_fvarId_745_);
return v_res_749_;
}
}
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(uint8_t v_pu_750_, lean_object* v_fvarId_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_750_, v_fvarId_751_, v_a_753_);
return v___x_757_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_findLetDecl_x3f_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_750_ = stack[0].m_num;
lean_object* v_fvarId_751_ = stack[1].m_obj;
lean_object* v_a_752_ = stack[2].m_obj;
lean_object* v_a_753_ = stack[3].m_obj;
lean_object* v_a_754_ = stack[4].m_obj;
lean_object* v_a_755_ = stack[5].m_obj;
lean_object* v_res_758_;
v_res_758_ = l_Lean_Compiler_LCNF_findLetDecl_x3f(v_pu_750_, v_fvarId_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
stack->m_obj
 = v_res_758_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(lean_object* v_pu_759_, lean_object* v_fvarId_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
uint8_t v_pu_boxed_766_; lean_object* v_res_767_; 
v_pu_boxed_766_ = lean_unbox(v_pu_759_);
v_res_767_ = l_Lean_Compiler_LCNF_findLetDecl_x3f(v_pu_boxed_766_, v_fvarId_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_fvarId_760_);
return v_res_767_;
}
}
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t v_pu_768_, lean_object* v_fvarId_769_, lean_object* v_a_770_){
_start:
{
lean_object* v___x_772_; lean_object* v___y_774_; 
v___x_772_ = lean_st_ref_get(v_a_770_);
if (v_pu_768_ == 0)
{
lean_object* v_lctx_777_; lean_object* v_funDeclsPure_778_; 
v_lctx_777_ = lean_ctor_get(v___x_772_, 0);
lean_inc_ref(v_lctx_777_);
lean_dec(v___x_772_);
v_funDeclsPure_778_ = lean_ctor_get(v_lctx_777_, 4);
lean_inc_ref(v_funDeclsPure_778_);
lean_dec_ref(v_lctx_777_);
v___y_774_ = v_funDeclsPure_778_;
goto v___jp_773_;
}
else
{
lean_object* v_lctx_779_; lean_object* v_funDeclsImpure_780_; 
v_lctx_779_ = lean_ctor_get(v___x_772_, 0);
lean_inc_ref(v_lctx_779_);
lean_dec(v___x_772_);
v_funDeclsImpure_780_ = lean_ctor_get(v_lctx_779_, 5);
lean_inc_ref(v_funDeclsImpure_780_);
lean_dec_ref(v_lctx_779_);
v___y_774_ = v_funDeclsImpure_780_;
goto v___jp_773_;
}
v___jp_773_:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_774_, v_fvarId_769_);
lean_dec_ref(v___y_774_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_768_ = stack[0].m_num;
lean_object* v_fvarId_769_ = stack[1].m_obj;
lean_object* v_a_770_ = stack[2].m_obj;
lean_object* v_res_781_;
v_res_781_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_768_, v_fvarId_769_, v_a_770_);
stack->m_obj
 = v_res_781_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(lean_object* v_pu_782_, lean_object* v_fvarId_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
uint8_t v_pu_boxed_786_; lean_object* v_res_787_; 
v_pu_boxed_786_ = lean_unbox(v_pu_782_);
v_res_787_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_boxed_786_, v_fvarId_783_, v_a_784_);
lean_dec(v_a_784_);
lean_dec(v_fvarId_783_);
return v_res_787_;
}
}
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(uint8_t v_pu_788_, lean_object* v_fvarId_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_788_, v_fvarId_789_, v_a_791_);
return v___x_795_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_findFunDecl_x3f_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_788_ = stack[0].m_num;
lean_object* v_fvarId_789_ = stack[1].m_obj;
lean_object* v_a_790_ = stack[2].m_obj;
lean_object* v_a_791_ = stack[3].m_obj;
lean_object* v_a_792_ = stack[4].m_obj;
lean_object* v_a_793_ = stack[5].m_obj;
lean_object* v_res_796_;
v_res_796_ = l_Lean_Compiler_LCNF_findFunDecl_x3f(v_pu_788_, v_fvarId_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
stack->m_obj
 = v_res_796_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(lean_object* v_pu_797_, lean_object* v_fvarId_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
uint8_t v_pu_boxed_804_; lean_object* v_res_805_; 
v_pu_boxed_804_ = lean_unbox(v_pu_797_);
v_res_805_ = l_Lean_Compiler_LCNF_findFunDecl_x3f(v_pu_boxed_804_, v_fvarId_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_fvarId_798_);
return v_res_805_;
}
}
lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t v_pu_806_, lean_object* v_fvarId_807_, lean_object* v_a_808_){
_start:
{
lean_object* v___x_810_; lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_831_; 
v___x_810_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_806_, v_fvarId_807_, v_a_808_);
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_831_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_831_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_831_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
if (lean_obj_tag(v_a_811_) == 1)
{
lean_object* v_val_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_826_; 
v_val_815_ = lean_ctor_get(v_a_811_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v_a_811_);
if (v_isSharedCheck_826_ == 0)
{
v___x_817_ = v_a_811_;
v_isShared_818_ = v_isSharedCheck_826_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_val_815_);
lean_dec(v_a_811_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_826_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v_value_819_; lean_object* v___x_821_; 
v_value_819_ = lean_ctor_get(v_val_815_, 3);
lean_inc(v_value_819_);
lean_dec(v_val_815_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v_value_819_);
v___x_821_ = v___x_817_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_value_819_);
v___x_821_ = v_reuseFailAlloc_825_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_823_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_821_);
v___x_823_ = v___x_813_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_829_; 
lean_dec(v_a_811_);
v___x_827_ = lean_box(0);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_827_);
v___x_829_ = v___x_813_;
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
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_findLetValue_x3f___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_806_ = stack[0].m_num;
lean_object* v_fvarId_807_ = stack[1].m_obj;
lean_object* v_a_808_ = stack[2].m_obj;
lean_object* v_res_832_;
v_res_832_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_806_, v_fvarId_807_, v_a_808_);
stack->m_obj
 = v_res_832_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg___boxed(lean_object* v_pu_833_, lean_object* v_fvarId_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
uint8_t v_pu_boxed_837_; lean_object* v_res_838_; 
v_pu_boxed_837_ = lean_unbox(v_pu_833_);
v_res_838_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_boxed_837_, v_fvarId_834_, v_a_835_);
lean_dec(v_a_835_);
lean_dec(v_fvarId_834_);
return v_res_838_;
}
}
lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f(uint8_t v_pu_839_, lean_object* v_fvarId_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_839_, v_fvarId_840_, v_a_842_);
return v___x_846_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_findLetValue_x3f_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_839_ = stack[0].m_num;
lean_object* v_fvarId_840_ = stack[1].m_obj;
lean_object* v_a_841_ = stack[2].m_obj;
lean_object* v_a_842_ = stack[3].m_obj;
lean_object* v_a_843_ = stack[4].m_obj;
lean_object* v_a_844_ = stack[5].m_obj;
lean_object* v_res_847_;
v_res_847_ = l_Lean_Compiler_LCNF_findLetValue_x3f(v_pu_839_, v_fvarId_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
stack->m_obj
 = v_res_847_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(lean_object* v_pu_848_, lean_object* v_fvarId_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
uint8_t v_pu_boxed_855_; lean_object* v_res_856_; 
v_pu_boxed_855_ = lean_unbox(v_pu_848_);
v_res_856_ = l_Lean_Compiler_LCNF_findLetValue_x3f(v_pu_boxed_855_, v_fvarId_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_fvarId_849_);
return v_res_856_;
}
}
lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg(lean_object* v_fvarId_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
uint8_t v___x_865_; lean_object* v___x_866_; 
v___x_865_ = 0;
v___x_866_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_865_, v_fvarId_857_, v_a_858_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_894_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_894_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_894_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_894_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
if (lean_obj_tag(v_a_867_) == 1)
{
lean_object* v_val_871_; 
v_val_871_ = lean_ctor_get(v_a_867_, 0);
lean_inc(v_val_871_);
lean_dec_ref_known(v_a_867_, 1);
if (lean_obj_tag(v_val_871_) == 3)
{
lean_object* v_declName_872_; lean_object* v___x_873_; lean_object* v_env_880_; uint8_t v___x_881_; lean_object* v___x_882_; 
v_declName_872_ = lean_ctor_get(v_val_871_, 0);
lean_inc(v_declName_872_);
lean_dec_ref_known(v_val_871_, 3);
v___x_873_ = lean_st_ref_get(v_a_859_);
v_env_880_ = lean_ctor_get(v___x_873_, 0);
lean_inc_ref(v_env_880_);
lean_dec(v___x_873_);
v___x_881_ = 0;
v___x_882_ = l_Lean_Environment_find_x3f(v_env_880_, v_declName_872_, v___x_881_);
if (lean_obj_tag(v___x_882_) == 1)
{
lean_object* v_val_883_; 
v_val_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_val_883_);
lean_dec_ref_known(v___x_882_, 1);
if (lean_obj_tag(v_val_883_) == 6)
{
lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_892_; 
lean_del_object(v___x_869_);
v_isSharedCheck_892_ = !lean_is_exclusive(v_val_883_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_val_883_, 0);
lean_dec(v_unused_893_);
v___x_885_ = v_val_883_;
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
else
{
lean_dec(v_val_883_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_887_ = 1;
v___x_888_ = lean_box(v___x_887_);
if (v_isShared_886_ == 0)
{
lean_ctor_set_tag(v___x_885_, 0);
lean_ctor_set(v___x_885_, 0, v___x_888_);
v___x_890_ = v___x_885_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
else
{
lean_dec(v_val_883_);
goto v___jp_874_;
}
}
else
{
lean_dec(v___x_882_);
goto v___jp_874_;
}
v___jp_874_:
{
uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_875_ = 0;
v___x_876_ = lean_box(v___x_875_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_876_);
v___x_878_ = v___x_869_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
else
{
lean_dec(v_val_871_);
lean_del_object(v___x_869_);
goto v___jp_861_;
}
}
else
{
lean_del_object(v___x_869_);
lean_dec(v_a_867_);
goto v___jp_861_;
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v_a_895_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_866_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_866_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
v___jp_861_:
{
uint8_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = 0;
v___x_863_ = lean_box(v___x_862_);
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
return v___x_864_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_isConstructorApp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_857_ = stack[0].m_obj;
lean_object* v_a_858_ = stack[1].m_obj;
lean_object* v_a_859_ = stack[2].m_obj;
lean_object* v_res_903_;
v_res_903_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_857_, v_a_858_, v_a_859_);
stack->m_obj
 = v_res_903_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___redArg___boxed(lean_object* v_fvarId_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_904_, v_a_905_, v_a_906_);
lean_dec(v_a_906_);
lean_dec(v_a_905_);
lean_dec(v_fvarId_904_);
return v_res_908_;
}
}
lean_object* l_Lean_Compiler_LCNF_isConstructorApp(lean_object* v_fvarId_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_909_, v_a_911_, v_a_913_);
return v___x_915_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_isConstructorApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_909_ = stack[0].m_obj;
lean_object* v_a_910_ = stack[1].m_obj;
lean_object* v_a_911_ = stack[2].m_obj;
lean_object* v_a_912_ = stack[3].m_obj;
lean_object* v_a_913_ = stack[4].m_obj;
lean_object* v_res_916_;
v_res_916_ = l_Lean_Compiler_LCNF_isConstructorApp(v_fvarId_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
stack->m_obj
 = v_res_916_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isConstructorApp___boxed(lean_object* v_fvarId_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Compiler_LCNF_isConstructorApp(v_fvarId_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec(v_fvarId_917_);
return v_res_923_;
}
}
lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(lean_object* v_arg_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
if (lean_obj_tag(v_arg_924_) == 1)
{
lean_object* v_fvarId_928_; lean_object* v___x_929_; 
v_fvarId_928_ = lean_ctor_get(v_arg_924_, 0);
v___x_929_ = l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_928_, v_a_925_, v_a_926_);
return v___x_929_;
}
else
{
uint8_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = 0;
v___x_931_ = lean_box(v___x_930_);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_924_ = stack[0].m_obj;
lean_object* v_a_925_ = stack[1].m_obj;
lean_object* v_a_926_ = stack[2].m_obj;
lean_object* v_res_933_;
v_res_933_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_924_, v_a_925_, v_a_926_);
stack->m_obj
 = v_res_933_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(lean_object* v_arg_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec(v_a_935_);
lean_dec(v_arg_934_);
return v_res_938_;
}
}
lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp(uint8_t v_pu_939_, lean_object* v_arg_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_940_, v_a_942_, v_a_944_);
return v___x_946_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Arg_isConstructorApp_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_939_ = stack[0].m_num;
lean_object* v_arg_940_ = stack[1].m_obj;
lean_object* v_a_941_ = stack[2].m_obj;
lean_object* v_a_942_ = stack[3].m_obj;
lean_object* v_a_943_ = stack[4].m_obj;
lean_object* v_a_944_ = stack[5].m_obj;
lean_object* v_res_947_;
v_res_947_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp(v_pu_939_, v_arg_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
stack->m_obj
 = v_res_947_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(lean_object* v_pu_948_, lean_object* v_arg_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
uint8_t v_pu_boxed_955_; lean_object* v_res_956_; 
v_pu_boxed_955_ = lean_unbox(v_pu_948_);
v_res_956_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp(v_pu_boxed_955_, v_arg_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_arg_949_);
return v_res_956_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getParam___closed__1(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l_Lean_Compiler_LCNF_getParam___closed__0));
v___x_959_ = l_Lean_stringToMessageData(v___x_958_);
return v___x_959_;
}
}
lean_object* l_Lean_Compiler_LCNF_getParam(uint8_t v_pu_960_, lean_object* v_fvarId_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_980_; 
v___x_967_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_960_, v_fvarId_961_, v_a_963_);
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_980_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_980_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_980_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
if (lean_obj_tag(v_a_968_) == 1)
{
lean_object* v_val_972_; lean_object* v___x_974_; 
lean_dec(v_fvarId_961_);
v_val_972_ = lean_ctor_get(v_a_968_, 0);
lean_inc(v_val_972_);
lean_dec_ref_known(v_a_968_, 1);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v_val_972_);
v___x_974_ = v___x_970_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_val_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
lean_del_object(v___x_970_);
lean_dec(v_a_968_);
v___x_976_ = lean_obj_once(&l_Lean_Compiler_LCNF_getParam___closed__1, &l_Lean_Compiler_LCNF_getParam___closed__1_once, _init_l_Lean_Compiler_LCNF_getParam___closed__1);
v___x_977_ = l_Lean_MessageData_ofName(v_fvarId_961_);
v___x_978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_978_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_979_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_getParam_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_960_ = stack[0].m_num;
lean_object* v_fvarId_961_ = stack[1].m_obj;
lean_object* v_a_962_ = stack[2].m_obj;
lean_object* v_a_963_ = stack[3].m_obj;
lean_object* v_a_964_ = stack[4].m_obj;
lean_object* v_a_965_ = stack[5].m_obj;
lean_object* v_res_981_;
v_res_981_ = l_Lean_Compiler_LCNF_getParam(v_pu_960_, v_fvarId_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
stack->m_obj
 = v_res_981_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParam___boxed(lean_object* v_pu_982_, lean_object* v_fvarId_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
uint8_t v_pu_boxed_989_; lean_object* v_res_990_; 
v_pu_boxed_989_ = lean_unbox(v_pu_982_);
v_res_990_ = l_Lean_Compiler_LCNF_getParam(v_pu_boxed_989_, v_fvarId_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
return v_res_990_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_Compiler_LCNF_getLetDecl___closed__0));
v___x_993_ = l_Lean_stringToMessageData(v___x_992_);
return v___x_993_;
}
}
lean_object* l_Lean_Compiler_LCNF_getLetDecl(uint8_t v_pu_994_, lean_object* v_fvarId_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v___x_1001_; lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1014_; 
v___x_1001_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_994_, v_fvarId_995_, v_a_997_);
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1014_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1014_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
if (lean_obj_tag(v_a_1002_) == 1)
{
lean_object* v_val_1006_; lean_object* v___x_1008_; 
lean_dec(v_fvarId_995_);
v_val_1006_ = lean_ctor_get(v_a_1002_, 0);
lean_inc(v_val_1006_);
lean_dec_ref_known(v_a_1002_, 1);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v_val_1006_);
v___x_1008_ = v___x_1004_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_val_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_del_object(v___x_1004_);
lean_dec(v_a_1002_);
v___x_1010_ = lean_obj_once(&l_Lean_Compiler_LCNF_getLetDecl___closed__1, &l_Lean_Compiler_LCNF_getLetDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1);
v___x_1011_ = l_Lean_MessageData_ofName(v_fvarId_995_);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_1012_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
return v___x_1013_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_getLetDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_994_ = stack[0].m_num;
lean_object* v_fvarId_995_ = stack[1].m_obj;
lean_object* v_a_996_ = stack[2].m_obj;
lean_object* v_a_997_ = stack[3].m_obj;
lean_object* v_a_998_ = stack[4].m_obj;
lean_object* v_a_999_ = stack[5].m_obj;
lean_object* v_res_1015_;
v_res_1015_ = l_Lean_Compiler_LCNF_getLetDecl(v_pu_994_, v_fvarId_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
stack->m_obj
 = v_res_1015_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLetDecl___boxed(lean_object* v_pu_1016_, lean_object* v_fvarId_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
uint8_t v_pu_boxed_1023_; lean_object* v_res_1024_; 
v_pu_boxed_1023_ = lean_unbox(v_pu_1016_);
v_res_1024_ = l_Lean_Compiler_LCNF_getLetDecl(v_pu_boxed_1023_, v_fvarId_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
return v_res_1024_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = ((lean_object*)(l_Lean_Compiler_LCNF_getFunDecl___closed__0));
v___x_1027_ = l_Lean_stringToMessageData(v___x_1026_);
return v___x_1027_;
}
}
lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t v_pu_1028_, lean_object* v_fvarId_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___x_1035_; lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1048_; 
v___x_1035_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_1028_, v_fvarId_1029_, v_a_1031_);
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1048_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1048_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
if (lean_obj_tag(v_a_1036_) == 1)
{
lean_object* v_val_1040_; lean_object* v___x_1042_; 
lean_dec(v_fvarId_1029_);
v_val_1040_ = lean_ctor_get(v_a_1036_, 0);
lean_inc(v_val_1040_);
lean_dec_ref_known(v_a_1036_, 1);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v_val_1040_);
v___x_1042_ = v___x_1038_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_val_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_del_object(v___x_1038_);
lean_dec(v_a_1036_);
v___x_1044_ = lean_obj_once(&l_Lean_Compiler_LCNF_getFunDecl___closed__1, &l_Lean_Compiler_LCNF_getFunDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1);
v___x_1045_ = l_Lean_MessageData_ofName(v_fvarId_1029_);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(v___x_1046_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
return v___x_1047_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_getFunDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1028_ = stack[0].m_num;
lean_object* v_fvarId_1029_ = stack[1].m_obj;
lean_object* v_a_1030_ = stack[2].m_obj;
lean_object* v_a_1031_ = stack[3].m_obj;
lean_object* v_a_1032_ = stack[4].m_obj;
lean_object* v_a_1033_ = stack[5].m_obj;
lean_object* v_res_1049_;
v_res_1049_ = l_Lean_Compiler_LCNF_getFunDecl(v_pu_1028_, v_fvarId_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
stack->m_obj
 = v_res_1049_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getFunDecl___boxed(lean_object* v_pu_1050_, lean_object* v_fvarId_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
uint8_t v_pu_boxed_1057_; lean_object* v_res_1058_; 
v_pu_boxed_1057_ = lean_unbox(v_pu_1050_);
v_res_1058_ = l_Lean_Compiler_LCNF_getFunDecl(v_pu_boxed_1057_, v_fvarId_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
return v_res_1058_;
}
}
lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg(lean_object* v_f_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v___x_1062_; lean_object* v_lctx_1063_; lean_object* v_nextIdx_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1075_; 
v___x_1062_ = lean_st_ref_take(v_a_1060_);
v_lctx_1063_ = lean_ctor_get(v___x_1062_, 0);
v_nextIdx_1064_ = lean_ctor_get(v___x_1062_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1066_ = v___x_1062_;
v_isShared_1067_ = v_isSharedCheck_1075_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_nextIdx_1064_);
lean_inc(v_lctx_1063_);
lean_dec(v___x_1062_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1075_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1068_ = lean_box(0);
v___x_1069_ = lean_apply_1(v_f_1059_, v_lctx_1063_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1069_);
v___x_1071_ = v___x_1066_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_nextIdx_1064_);
v___x_1071_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_st_ref_put(v_a_1060_, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1068_);
return v___x_1073_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_modifyLCtx___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1059_ = stack[0].m_obj;
lean_object* v_a_1060_ = stack[1].m_obj;
lean_object* v_res_1076_;
v_res_1076_ = l_Lean_Compiler_LCNF_modifyLCtx___redArg(v_f_1059_, v_a_1060_);
stack->m_obj
 = v_res_1076_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(lean_object* v_f_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_Compiler_LCNF_modifyLCtx___redArg(v_f_1077_, v_a_1078_);
lean_dec(v_a_1078_);
return v_res_1080_;
}
}
lean_object* l_Lean_Compiler_LCNF_modifyLCtx(lean_object* v_f_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v___x_1087_; lean_object* v_lctx_1088_; lean_object* v_nextIdx_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1100_; 
v___x_1087_ = lean_st_ref_take(v_a_1083_);
v_lctx_1088_ = lean_ctor_get(v___x_1087_, 0);
v_nextIdx_1089_ = lean_ctor_get(v___x_1087_, 1);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1091_ = v___x_1087_;
v_isShared_1092_ = v_isSharedCheck_1100_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_nextIdx_1089_);
lean_inc(v_lctx_1088_);
lean_dec(v___x_1087_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1100_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_apply_1(v_f_1081_, v_lctx_1088_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1094_);
v___x_1096_ = v___x_1091_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_nextIdx_1089_);
v___x_1096_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_st_ref_put(v_a_1083_, v___x_1096_);
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1093_);
return v___x_1098_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_modifyLCtx_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1081_ = stack[0].m_obj;
lean_object* v_a_1082_ = stack[1].m_obj;
lean_object* v_a_1083_ = stack[2].m_obj;
lean_object* v_a_1084_ = stack[3].m_obj;
lean_object* v_a_1085_ = stack[4].m_obj;
lean_object* v_res_1101_;
v_res_1101_ = l_Lean_Compiler_LCNF_modifyLCtx(v_f_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
stack->m_obj
 = v_res_1101_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_modifyLCtx___boxed(lean_object* v_f_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_Compiler_LCNF_modifyLCtx(v_f_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
return v_res_1108_;
}
}
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t v_pu_1109_, lean_object* v_decl_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v___x_1113_; lean_object* v_lctx_1114_; lean_object* v_nextIdx_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1126_; 
v___x_1113_ = lean_st_ref_take(v_a_1111_);
v_lctx_1114_ = lean_ctor_get(v___x_1113_, 0);
v_nextIdx_1115_ = lean_ctor_get(v___x_1113_, 1);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1117_ = v___x_1113_;
v_isShared_1118_ = v_isSharedCheck_1126_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_nextIdx_1115_);
lean_inc(v_lctx_1114_);
lean_dec(v___x_1113_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1126_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1119_ = lean_box(0);
v___x_1120_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_1109_, v_lctx_1114_, v_decl_1110_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1120_);
v___x_1122_ = v___x_1117_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_nextIdx_1115_);
v___x_1122_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_st_ref_put(v_a_1111_, v___x_1122_);
v___x_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1119_);
return v___x_1124_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_eraseLetDecl___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1109_ = stack[0].m_num;
lean_object* v_decl_1110_ = stack[1].m_obj;
lean_object* v_a_1111_ = stack[2].m_obj;
lean_object* v_res_1127_;
v_res_1127_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1109_, v_decl_1110_, v_a_1111_);
stack->m_obj
 = v_res_1127_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(lean_object* v_pu_1128_, lean_object* v_decl_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
uint8_t v_pu_boxed_1132_; lean_object* v_res_1133_; 
v_pu_boxed_1132_ = lean_unbox(v_pu_1128_);
v_res_1133_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_boxed_1132_, v_decl_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_decl_1129_);
return v_res_1133_;
}
}
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(uint8_t v_pu_1134_, lean_object* v_decl_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1134_, v_decl_1135_, v_a_1137_);
return v___x_1141_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_eraseLetDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1134_ = stack[0].m_num;
lean_object* v_decl_1135_ = stack[1].m_obj;
lean_object* v_a_1136_ = stack[2].m_obj;
lean_object* v_a_1137_ = stack[3].m_obj;
lean_object* v_a_1138_ = stack[4].m_obj;
lean_object* v_a_1139_ = stack[5].m_obj;
lean_object* v_res_1142_;
v_res_1142_ = l_Lean_Compiler_LCNF_eraseLetDecl(v_pu_1134_, v_decl_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
stack->m_obj
 = v_res_1142_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___boxed(lean_object* v_pu_1143_, lean_object* v_decl_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
uint8_t v_pu_boxed_1150_; lean_object* v_res_1151_; 
v_pu_boxed_1150_ = lean_unbox(v_pu_1143_);
v_res_1151_ = l_Lean_Compiler_LCNF_eraseLetDecl(v_pu_boxed_1150_, v_decl_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec_ref(v_decl_1144_);
return v_res_1151_;
}
}
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t v_pu_1152_, lean_object* v_decl_1153_, uint8_t v_recursive_1154_, lean_object* v_a_1155_){
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
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1163_ = lean_box(0);
v___x_1164_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_1152_, v_lctx_1158_, v_decl_1153_, v_recursive_1154_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1164_);
v___x_1166_ = v___x_1161_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_nextIdx_1159_);
v___x_1166_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_st_ref_put(v_a_1155_, v___x_1166_);
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1163_);
return v___x_1168_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_eraseFunDecl___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1152_ = stack[0].m_num;
lean_object* v_decl_1153_ = stack[1].m_obj;
uint8_t v_recursive_1154_ = stack[2].m_num;
lean_object* v_a_1155_ = stack[3].m_obj;
lean_object* v_res_1171_;
v_res_1171_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1152_, v_decl_1153_, v_recursive_1154_, v_a_1155_);
stack->m_obj
 = v_res_1171_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(lean_object* v_pu_1172_, lean_object* v_decl_1173_, lean_object* v_recursive_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
uint8_t v_pu_boxed_1177_; uint8_t v_recursive_boxed_1178_; lean_object* v_res_1179_; 
v_pu_boxed_1177_ = lean_unbox(v_pu_1172_);
v_recursive_boxed_1178_ = lean_unbox(v_recursive_1174_);
v_res_1179_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_boxed_1177_, v_decl_1173_, v_recursive_boxed_1178_, v_a_1175_);
lean_dec(v_a_1175_);
lean_dec_ref(v_decl_1173_);
return v_res_1179_;
}
}
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(uint8_t v_pu_1180_, lean_object* v_decl_1181_, uint8_t v_recursive_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1180_, v_decl_1181_, v_recursive_1182_, v_a_1184_);
return v___x_1188_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_eraseFunDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1180_ = stack[0].m_num;
lean_object* v_decl_1181_ = stack[1].m_obj;
uint8_t v_recursive_1182_ = stack[2].m_num;
lean_object* v_a_1183_ = stack[3].m_obj;
lean_object* v_a_1184_ = stack[4].m_obj;
lean_object* v_a_1185_ = stack[5].m_obj;
lean_object* v_a_1186_ = stack[6].m_obj;
lean_object* v_res_1189_;
v_res_1189_ = l_Lean_Compiler_LCNF_eraseFunDecl(v_pu_1180_, v_decl_1181_, v_recursive_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
stack->m_obj
 = v_res_1189_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___boxed(lean_object* v_pu_1190_, lean_object* v_decl_1191_, lean_object* v_recursive_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
uint8_t v_pu_boxed_1198_; uint8_t v_recursive_boxed_1199_; lean_object* v_res_1200_; 
v_pu_boxed_1198_ = lean_unbox(v_pu_1190_);
v_recursive_boxed_1199_ = lean_unbox(v_recursive_1192_);
v_res_1200_ = l_Lean_Compiler_LCNF_eraseFunDecl(v_pu_boxed_1198_, v_decl_1191_, v_recursive_boxed_1199_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
lean_dec(v_a_1196_);
lean_dec_ref(v_a_1195_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec_ref(v_decl_1191_);
return v_res_1200_;
}
}
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t v_pu_1201_, lean_object* v_code_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v___x_1205_; lean_object* v_lctx_1206_; lean_object* v_nextIdx_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1218_; 
v___x_1205_ = lean_st_ref_take(v_a_1203_);
v_lctx_1206_ = lean_ctor_get(v___x_1205_, 0);
v_nextIdx_1207_ = lean_ctor_get(v___x_1205_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1209_ = v___x_1205_;
v_isShared_1210_ = v_isSharedCheck_1218_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_nextIdx_1207_);
lean_inc(v_lctx_1206_);
lean_dec(v___x_1205_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1218_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1211_ = lean_box(0);
v___x_1212_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1201_, v_code_1202_, v_lctx_1206_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v___x_1212_);
v___x_1214_ = v___x_1209_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_nextIdx_1207_);
v___x_1214_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_st_ref_put(v_a_1203_, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1211_);
return v___x_1216_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_eraseCode___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1201_ = stack[0].m_num;
lean_object* v_code_1202_ = stack[1].m_obj;
lean_object* v_a_1203_ = stack[2].m_obj;
lean_object* v_res_1219_;
v_res_1219_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_1201_, v_code_1202_, v_a_1203_);
stack->m_obj
 = v_res_1219_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(lean_object* v_pu_1220_, lean_object* v_code_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
uint8_t v_pu_boxed_1224_; lean_object* v_res_1225_; 
v_pu_boxed_1224_ = lean_unbox(v_pu_1220_);
v_res_1225_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_boxed_1224_, v_code_1221_, v_a_1222_);
lean_dec(v_a_1222_);
lean_dec_ref(v_code_1221_);
return v_res_1225_;
}
}
lean_object* l_Lean_Compiler_LCNF_eraseCode(uint8_t v_pu_1226_, lean_object* v_code_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_1226_, v_code_1227_, v_a_1229_);
return v___x_1233_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_eraseCode_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1226_ = stack[0].m_num;
lean_object* v_code_1227_ = stack[1].m_obj;
lean_object* v_a_1228_ = stack[2].m_obj;
lean_object* v_a_1229_ = stack[3].m_obj;
lean_object* v_a_1230_ = stack[4].m_obj;
lean_object* v_a_1231_ = stack[5].m_obj;
lean_object* v_res_1234_;
v_res_1234_ = l_Lean_Compiler_LCNF_eraseCode(v_pu_1226_, v_code_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
stack->m_obj
 = v_res_1234_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCode___boxed(lean_object* v_pu_1235_, lean_object* v_code_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
uint8_t v_pu_boxed_1242_; lean_object* v_res_1243_; 
v_pu_boxed_1242_ = lean_unbox(v_pu_1235_);
v_res_1243_ = l_Lean_Compiler_LCNF_eraseCode(v_pu_boxed_1242_, v_code_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec_ref(v_code_1236_);
return v_res_1243_;
}
}
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t v_pu_1244_, lean_object* v_param_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v___x_1248_; lean_object* v_lctx_1249_; lean_object* v_nextIdx_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1261_; 
v___x_1248_ = lean_st_ref_take(v_a_1246_);
v_lctx_1249_ = lean_ctor_get(v___x_1248_, 0);
v_nextIdx_1250_ = lean_ctor_get(v___x_1248_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1252_ = v___x_1248_;
v_isShared_1253_ = v_isSharedCheck_1261_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_nextIdx_1250_);
lean_inc(v_lctx_1249_);
lean_dec(v___x_1248_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1261_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1254_ = lean_box(0);
v___x_1255_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_1244_, v_lctx_1249_, v_param_1245_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v___x_1255_);
v___x_1257_ = v___x_1252_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_nextIdx_1250_);
v___x_1257_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_st_ref_put(v_a_1246_, v___x_1257_);
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1254_);
return v___x_1259_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_eraseParam___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1244_ = stack[0].m_num;
lean_object* v_param_1245_ = stack[1].m_obj;
lean_object* v_a_1246_ = stack[2].m_obj;
lean_object* v_res_1262_;
v_res_1262_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_1244_, v_param_1245_, v_a_1246_);
stack->m_obj
 = v_res_1262_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(lean_object* v_pu_1263_, lean_object* v_param_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
uint8_t v_pu_boxed_1267_; lean_object* v_res_1268_; 
v_pu_boxed_1267_ = lean_unbox(v_pu_1263_);
v_res_1268_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_boxed_1267_, v_param_1264_, v_a_1265_);
lean_dec(v_a_1265_);
lean_dec_ref(v_param_1264_);
return v_res_1268_;
}
}
lean_object* l_Lean_Compiler_LCNF_eraseParam(uint8_t v_pu_1269_, lean_object* v_param_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_1269_, v_param_1270_, v_a_1272_);
return v___x_1276_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_eraseParam_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1269_ = stack[0].m_num;
lean_object* v_param_1270_ = stack[1].m_obj;
lean_object* v_a_1271_ = stack[2].m_obj;
lean_object* v_a_1272_ = stack[3].m_obj;
lean_object* v_a_1273_ = stack[4].m_obj;
lean_object* v_a_1274_ = stack[5].m_obj;
lean_object* v_res_1277_;
v_res_1277_ = l_Lean_Compiler_LCNF_eraseParam(v_pu_1269_, v_param_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
stack->m_obj
 = v_res_1277_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParam___boxed(lean_object* v_pu_1278_, lean_object* v_param_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
uint8_t v_pu_boxed_1285_; lean_object* v_res_1286_; 
v_pu_boxed_1285_ = lean_unbox(v_pu_1278_);
v_res_1286_ = l_Lean_Compiler_LCNF_eraseParam(v_pu_boxed_1285_, v_param_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec_ref(v_param_1279_);
return v_res_1286_;
}
}
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t v_pu_1287_, lean_object* v_params_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v___x_1291_; lean_object* v_lctx_1292_; lean_object* v_nextIdx_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1304_; 
v___x_1291_ = lean_st_ref_take(v_a_1289_);
v_lctx_1292_ = lean_ctor_get(v___x_1291_, 0);
v_nextIdx_1293_ = lean_ctor_get(v___x_1291_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1295_ = v___x_1291_;
v_isShared_1296_ = v_isSharedCheck_1304_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_nextIdx_1293_);
lean_inc(v_lctx_1292_);
lean_dec(v___x_1291_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1304_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1297_ = lean_box(0);
v___x_1298_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_1287_, v_lctx_1292_, v_params_1288_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1298_);
v___x_1300_ = v___x_1295_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_nextIdx_1293_);
v___x_1300_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_st_ref_put(v_a_1289_, v___x_1300_);
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1297_);
return v___x_1302_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_eraseParams___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1287_ = stack[0].m_num;
lean_object* v_params_1288_ = stack[1].m_obj;
lean_object* v_a_1289_ = stack[2].m_obj;
lean_object* v_res_1305_;
v_res_1305_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1287_, v_params_1288_, v_a_1289_);
stack->m_obj
 = v_res_1305_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(lean_object* v_pu_1306_, lean_object* v_params_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
uint8_t v_pu_boxed_1310_; lean_object* v_res_1311_; 
v_pu_boxed_1310_ = lean_unbox(v_pu_1306_);
v_res_1311_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_boxed_1310_, v_params_1307_, v_a_1308_);
lean_dec(v_a_1308_);
lean_dec_ref(v_params_1307_);
return v_res_1311_;
}
}
lean_object* l_Lean_Compiler_LCNF_eraseParams(uint8_t v_pu_1312_, lean_object* v_params_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1312_, v_params_1313_, v_a_1315_);
return v___x_1319_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_eraseParams_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1312_ = stack[0].m_num;
lean_object* v_params_1313_ = stack[1].m_obj;
lean_object* v_a_1314_ = stack[2].m_obj;
lean_object* v_a_1315_ = stack[3].m_obj;
lean_object* v_a_1316_ = stack[4].m_obj;
lean_object* v_a_1317_ = stack[5].m_obj;
lean_object* v_res_1320_;
v_res_1320_ = l_Lean_Compiler_LCNF_eraseParams(v_pu_1312_, v_params_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
stack->m_obj
 = v_res_1320_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseParams___boxed(lean_object* v_pu_1321_, lean_object* v_params_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
uint8_t v_pu_boxed_1328_; lean_object* v_res_1329_; 
v_pu_boxed_1328_ = lean_unbox(v_pu_1321_);
v_res_1329_ = l_Lean_Compiler_LCNF_eraseParams(v_pu_boxed_1328_, v_params_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec_ref(v_params_1322_);
return v_res_1329_;
}
}
lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t v_pu_1330_, lean_object* v_decl_1331_, lean_object* v_a_1332_){
_start:
{
switch(lean_obj_tag(v_decl_1331_))
{
case 0:
{
lean_object* v_decl_1334_; lean_object* v___x_1335_; 
v_decl_1334_ = lean_ctor_get(v_decl_1331_, 0);
v___x_1335_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_1330_, v_decl_1334_, v_a_1332_);
return v___x_1335_;
}
case 1:
{
lean_object* v_decl_1336_; uint8_t v___x_1337_; lean_object* v___x_1338_; 
v_decl_1336_ = lean_ctor_get(v_decl_1331_, 0);
v___x_1337_ = 1;
v___x_1338_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1330_, v_decl_1336_, v___x_1337_, v_a_1332_);
return v___x_1338_;
}
case 2:
{
lean_object* v_decl_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; 
v_decl_1339_ = lean_ctor_get(v_decl_1331_, 0);
v___x_1340_ = 1;
v___x_1341_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_1330_, v_decl_1339_, v___x_1340_, v_a_1332_);
return v___x_1341_;
}
default: 
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = lean_box(0);
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
return v___x_1343_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_eraseCodeDecl___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1330_ = stack[0].m_num;
lean_object* v_decl_1331_ = stack[1].m_obj;
lean_object* v_a_1332_ = stack[2].m_obj;
lean_object* v_res_1344_;
v_res_1344_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1330_, v_decl_1331_, v_a_1332_);
stack->m_obj
 = v_res_1344_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(lean_object* v_pu_1345_, lean_object* v_decl_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
uint8_t v_pu_boxed_1349_; lean_object* v_res_1350_; 
v_pu_boxed_1349_ = lean_unbox(v_pu_1345_);
v_res_1350_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_boxed_1349_, v_decl_1346_, v_a_1347_);
lean_dec(v_a_1347_);
lean_dec_ref(v_decl_1346_);
return v_res_1350_;
}
}
lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(uint8_t v_pu_1351_, lean_object* v_decl_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1351_, v_decl_1352_, v_a_1354_);
return v___x_1358_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_eraseCodeDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1351_ = stack[0].m_num;
lean_object* v_decl_1352_ = stack[1].m_obj;
lean_object* v_a_1353_ = stack[2].m_obj;
lean_object* v_a_1354_ = stack[3].m_obj;
lean_object* v_a_1355_ = stack[4].m_obj;
lean_object* v_a_1356_ = stack[5].m_obj;
lean_object* v_res_1359_;
v_res_1359_ = l_Lean_Compiler_LCNF_eraseCodeDecl(v_pu_1351_, v_decl_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
stack->m_obj
 = v_res_1359_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(lean_object* v_pu_1360_, lean_object* v_decl_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
uint8_t v_pu_boxed_1367_; lean_object* v_res_1368_; 
v_pu_boxed_1367_ = lean_unbox(v_pu_1360_);
v_res_1368_ = l_Lean_Compiler_LCNF_eraseCodeDecl(v_pu_boxed_1367_, v_decl_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec_ref(v_decl_1361_);
return v_res_1368_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(uint8_t v_pu_1369_, lean_object* v_as_1370_, size_t v_i_1371_, size_t v_stop_1372_, lean_object* v_b_1373_, lean_object* v___y_1374_){
_start:
{
uint8_t v___x_1376_; 
v___x_1376_ = lean_usize_dec_eq(v_i_1371_, v_stop_1372_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = lean_array_uget_borrowed(v_as_1370_, v_i_1371_);
v___x_1378_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_1369_, v___x_1377_, v___y_1374_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; size_t v___x_1380_; size_t v___x_1381_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_add(v_i_1371_, v___x_1380_);
v_i_1371_ = v___x_1381_;
v_b_1373_ = v_a_1379_;
goto _start;
}
else
{
return v___x_1378_;
}
}
else
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1383_, 0, v_b_1373_);
return v___x_1383_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1369_ = stack[0].m_num;
lean_object* v_as_1370_ = stack[1].m_obj;
size_t v_i_1371_ = stack[2].m_num;
size_t v_stop_1372_ = stack[3].m_num;
lean_object* v_b_1373_ = stack[4].m_obj;
lean_object* v___y_1374_ = stack[5].m_obj;
lean_object* v_res_1384_;
v_res_1384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1369_, v_as_1370_, v_i_1371_, v_stop_1372_, v_b_1373_, v___y_1374_);
stack->m_obj
 = v_res_1384_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(lean_object* v_pu_1385_, lean_object* v_as_1386_, lean_object* v_i_1387_, lean_object* v_stop_1388_, lean_object* v_b_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
uint8_t v_pu_boxed_1392_; size_t v_i_boxed_1393_; size_t v_stop_boxed_1394_; lean_object* v_res_1395_; 
v_pu_boxed_1392_ = lean_unbox(v_pu_1385_);
v_i_boxed_1393_ = lean_unbox_usize(v_i_1387_);
lean_dec(v_i_1387_);
v_stop_boxed_1394_ = lean_unbox_usize(v_stop_1388_);
lean_dec(v_stop_1388_);
v_res_1395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_boxed_1392_, v_as_1386_, v_i_boxed_1393_, v_stop_boxed_1394_, v_b_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v_as_1386_);
return v_res_1395_;
}
}
lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(uint8_t v_pu_1396_, lean_object* v_decls_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1403_ = lean_unsigned_to_nat(0u);
v___x_1404_ = lean_array_get_size(v_decls_1397_);
v___x_1405_ = lean_box(0);
v___x_1406_ = lean_nat_dec_lt(v___x_1403_, v___x_1404_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1405_);
return v___x_1407_;
}
else
{
uint8_t v___x_1408_; 
v___x_1408_ = lean_nat_dec_le(v___x_1404_, v___x_1404_);
if (v___x_1408_ == 0)
{
if (v___x_1406_ == 0)
{
lean_object* v___x_1409_; 
v___x_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1405_);
return v___x_1409_;
}
else
{
size_t v___x_1410_; size_t v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = ((size_t)0ULL);
v___x_1411_ = lean_usize_of_nat(v___x_1404_);
v___x_1412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1396_, v_decls_1397_, v___x_1410_, v___x_1411_, v___x_1405_, v_a_1399_);
return v___x_1412_;
}
}
else
{
size_t v___x_1413_; size_t v___x_1414_; lean_object* v___x_1415_; 
v___x_1413_ = ((size_t)0ULL);
v___x_1414_ = lean_usize_of_nat(v___x_1404_);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1396_, v_decls_1397_, v___x_1413_, v___x_1414_, v___x_1405_, v_a_1399_);
return v___x_1415_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_eraseCodeDecls_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1396_ = stack[0].m_num;
lean_object* v_decls_1397_ = stack[1].m_obj;
lean_object* v_a_1398_ = stack[2].m_obj;
lean_object* v_a_1399_ = stack[3].m_obj;
lean_object* v_a_1400_ = stack[4].m_obj;
lean_object* v_a_1401_ = stack[5].m_obj;
lean_object* v_res_1416_;
v_res_1416_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v_pu_1396_, v_decls_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_);
stack->m_obj
 = v_res_1416_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(lean_object* v_pu_1417_, lean_object* v_decls_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
uint8_t v_pu_boxed_1424_; lean_object* v_res_1425_; 
v_pu_boxed_1424_ = lean_unbox(v_pu_1417_);
v_res_1425_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v_pu_boxed_1424_, v_decls_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
lean_dec_ref(v_decls_1418_);
return v_res_1425_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(uint8_t v_pu_1426_, lean_object* v_as_1427_, size_t v_i_1428_, size_t v_stop_1429_, lean_object* v_b_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_1426_, v_as_1427_, v_i_1428_, v_stop_1429_, v_b_1430_, v___y_1432_);
return v___x_1436_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1426_ = stack[0].m_num;
lean_object* v_as_1427_ = stack[1].m_obj;
size_t v_i_1428_ = stack[2].m_num;
size_t v_stop_1429_ = stack[3].m_num;
lean_object* v_b_1430_ = stack[4].m_obj;
lean_object* v___y_1431_ = stack[5].m_obj;
lean_object* v___y_1432_ = stack[6].m_obj;
lean_object* v___y_1433_ = stack[7].m_obj;
lean_object* v___y_1434_ = stack[8].m_obj;
lean_object* v_res_1437_;
v_res_1437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(v_pu_1426_, v_as_1427_, v_i_1428_, v_stop_1429_, v_b_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
stack->m_obj
 = v_res_1437_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(lean_object* v_pu_1438_, lean_object* v_as_1439_, lean_object* v_i_1440_, lean_object* v_stop_1441_, lean_object* v_b_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
uint8_t v_pu_boxed_1448_; size_t v_i_boxed_1449_; size_t v_stop_boxed_1450_; lean_object* v_res_1451_; 
v_pu_boxed_1448_ = lean_unbox(v_pu_1438_);
v_i_boxed_1449_ = lean_unbox_usize(v_i_1440_);
lean_dec(v_i_1440_);
v_stop_boxed_1450_ = lean_unbox_usize(v_stop_1441_);
lean_dec(v_stop_1441_);
v_res_1451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(v_pu_boxed_1448_, v_as_1439_, v_i_boxed_1449_, v_stop_boxed_1450_, v_b_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec_ref(v_as_1439_);
return v_res_1451_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(lean_object* v_f_1452_, lean_object* v_v_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
if (lean_obj_tag(v_v_1453_) == 0)
{
lean_object* v_code_1459_; lean_object* v___x_1460_; 
v_code_1459_ = lean_ctor_get(v_v_1453_, 0);
lean_inc_ref(v_code_1459_);
lean_dec_ref_known(v_v_1453_, 1);
lean_inc(v___y_1457_);
lean_inc_ref(v___y_1456_);
lean_inc(v___y_1455_);
lean_inc_ref(v___y_1454_);
v___x_1460_ = lean_apply_6(v_f_1452_, v_code_1459_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, lean_box(0));
return v___x_1460_;
}
else
{
lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1468_; 
lean_dec_ref(v_f_1452_);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_v_1453_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; 
v_unused_1469_ = lean_ctor_get(v_v_1453_, 0);
lean_dec(v_unused_1469_);
v___x_1462_ = v_v_1453_;
v_isShared_1463_ = v_isSharedCheck_1468_;
goto v_resetjp_1461_;
}
else
{
lean_dec(v_v_1453_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1468_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1464_ = lean_box(0);
if (v_isShared_1463_ == 0)
{
lean_ctor_set_tag(v___x_1462_, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1464_);
v___x_1466_ = v___x_1462_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1452_ = stack[0].m_obj;
lean_object* v_v_1453_ = stack[1].m_obj;
lean_object* v___y_1454_ = stack[2].m_obj;
lean_object* v___y_1455_ = stack[3].m_obj;
lean_object* v___y_1456_ = stack[4].m_obj;
lean_object* v___y_1457_ = stack[5].m_obj;
lean_object* v_res_1470_;
v_res_1470_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1452_, v_v_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
stack->m_obj
 = v_res_1470_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg___boxed(lean_object* v_f_1471_, lean_object* v_v_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1471_, v_v_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
return v_res_1478_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(uint8_t v_pu_1479_, lean_object* v_f_1480_, lean_object* v_v_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_1480_, v_v_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
return v___x_1487_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1479_ = stack[0].m_num;
lean_object* v_f_1480_ = stack[1].m_obj;
lean_object* v_v_1481_ = stack[2].m_obj;
lean_object* v___y_1482_ = stack[3].m_obj;
lean_object* v___y_1483_ = stack[4].m_obj;
lean_object* v___y_1484_ = stack[5].m_obj;
lean_object* v___y_1485_ = stack[6].m_obj;
lean_object* v_res_1488_;
v_res_1488_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(v_pu_1479_, v_f_1480_, v_v_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
stack->m_obj
 = v_res_1488_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(lean_object* v_pu_1489_, lean_object* v_f_1490_, lean_object* v_v_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
uint8_t v_pu_boxed_1497_; lean_object* v_res_1498_; 
v_pu_boxed_1497_ = lean_unbox(v_pu_1489_);
v_res_1498_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(v_pu_boxed_1497_, v_f_1490_, v_v_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
return v_res_1498_;
}
}
lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t v_pu_1499_, lean_object* v_decl_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_toSignature_1506_; lean_object* v_value_1507_; lean_object* v_params_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v_toSignature_1506_ = lean_ctor_get(v_decl_1500_, 0);
lean_inc_ref(v_toSignature_1506_);
v_value_1507_ = lean_ctor_get(v_decl_1500_, 1);
lean_inc_ref(v_value_1507_);
lean_dec_ref(v_decl_1500_);
v_params_1508_ = lean_ctor_get(v_toSignature_1506_, 3);
lean_inc_ref(v_params_1508_);
lean_dec_ref(v_toSignature_1506_);
v___x_1509_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_1499_, v_params_1508_, v_a_1502_);
lean_dec_ref(v_params_1508_);
lean_dec_ref(v___x_1509_);
v___x_1510_ = lean_box(v_pu_1499_);
v___x_1511_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_eraseCode___boxed), 7, 1);
lean_closure_set(v___x_1511_, 0, v___x_1510_);
v___x_1512_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v___x_1511_, v_value_1507_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
return v___x_1512_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_eraseDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1499_ = stack[0].m_num;
lean_object* v_decl_1500_ = stack[1].m_obj;
lean_object* v_a_1501_ = stack[2].m_obj;
lean_object* v_a_1502_ = stack[3].m_obj;
lean_object* v_a_1503_ = stack[4].m_obj;
lean_object* v_a_1504_ = stack[5].m_obj;
lean_object* v_res_1513_;
v_res_1513_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_1499_, v_decl_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
stack->m_obj
 = v_res_1513_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eraseDecl___boxed(lean_object* v_pu_1514_, lean_object* v_decl_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
uint8_t v_pu_boxed_1521_; lean_object* v_res_1522_; 
v_pu_boxed_1521_ = lean_unbox(v_pu_1514_);
v_res_1522_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_boxed_1521_, v_decl_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
return v_res_1522_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_erase(uint8_t v_pu_1523_, lean_object* v_decl_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_Compiler_LCNF_eraseDecl(v_pu_1523_, v_decl_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_erase_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1523_ = stack[0].m_num;
lean_object* v_decl_1524_ = stack[1].m_obj;
lean_object* v_a_1525_ = stack[2].m_obj;
lean_object* v_a_1526_ = stack[3].m_obj;
lean_object* v_a_1527_ = stack[4].m_obj;
lean_object* v_a_1528_ = stack[5].m_obj;
lean_object* v_res_1531_;
v_res_1531_ = l_Lean_Compiler_LCNF_Decl_erase(v_pu_1523_, v_decl_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
stack->m_obj
 = v_res_1531_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_erase___boxed(lean_object* v_pu_1532_, lean_object* v_decl_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
uint8_t v_pu_boxed_1539_; lean_object* v_res_1540_; 
v_pu_boxed_1539_ = lean_unbox(v_pu_1532_);
v_res_1540_ = l_Lean_Compiler_LCNF_Decl_erase(v_pu_boxed_1539_, v_decl_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(lean_object* v_msg_1541_){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = l_Lean_instInhabitedExpr;
v___x_1543_ = lean_panic_fn_borrowed(v___x_1542_, v_msg_1541_);
return v___x_1543_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1547_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2));
v___x_1548_ = lean_unsigned_to_nat(20u);
v___x_1549_ = lean_unsigned_to_nat(215u);
v___x_1550_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1));
v___x_1551_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0));
v___x_1552_ = l_mkPanicMessageWithDecl(v___x_1551_, v___x_1550_, v___x_1549_, v___x_1548_, v___x_1547_);
return v___x_1552_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t v_pu_1553_, lean_object* v_s_1554_, uint8_t v_translator_1555_, lean_object* v_e_1556_){
_start:
{
uint8_t v___x_1557_; 
v___x_1557_ = l_Lean_Expr_hasFVar(v_e_1556_);
if (v___x_1557_ == 0)
{
return v_e_1556_;
}
else
{
switch(lean_obj_tag(v_e_1556_))
{
case 1:
{
lean_object* v_fvarId_1558_; lean_object* v___x_1559_; 
v_fvarId_1558_ = lean_ctor_get(v_e_1556_, 0);
v___x_1559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1554_, v_fvarId_1558_);
if (lean_obj_tag(v___x_1559_) == 0)
{
return v_e_1556_;
}
else
{
lean_object* v_val_1560_; 
lean_dec_ref_known(v_e_1556_, 1);
v_val_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_val_1560_);
lean_dec_ref_known(v___x_1559_, 1);
switch(lean_obj_tag(v_val_1560_))
{
case 0:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_Compiler_LCNF_erasedExpr;
return v___x_1561_;
}
case 1:
{
if (v_translator_1555_ == 0)
{
lean_object* v_fvarId_1562_; lean_object* v___x_1563_; 
v_fvarId_1562_ = lean_ctor_get(v_val_1560_, 0);
lean_inc(v_fvarId_1562_);
lean_dec_ref_known(v_val_1560_, 1);
v___x_1563_ = l_Lean_Expr_fvar___override(v_fvarId_1562_);
v_e_1556_ = v___x_1563_;
goto _start;
}
else
{
lean_object* v_fvarId_1565_; lean_object* v___x_1566_; 
v_fvarId_1565_ = lean_ctor_get(v_val_1560_, 0);
lean_inc(v_fvarId_1565_);
lean_dec_ref_known(v_val_1560_, 1);
v___x_1566_ = l_Lean_Expr_fvar___override(v_fvarId_1565_);
return v___x_1566_;
}
}
default: 
{
if (v_translator_1555_ == 0)
{
lean_object* v_expr_1567_; 
v_expr_1567_ = lean_ctor_get(v_val_1560_, 0);
lean_inc_ref(v_expr_1567_);
lean_dec_ref_known(v_val_1560_, 1);
v_e_1556_ = v_expr_1567_;
goto _start;
}
else
{
lean_object* v_expr_1569_; 
v_expr_1569_ = lean_ctor_get(v_val_1560_, 0);
lean_inc_ref(v_expr_1569_);
lean_dec_ref_known(v_val_1560_, 1);
return v_expr_1569_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_1570_; lean_object* v_arg_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; size_t v___x_1574_; size_t v___x_1575_; uint8_t v___x_1576_; 
v_fn_1570_ = lean_ctor_get(v_e_1556_, 0);
v_arg_1571_ = lean_ctor_get(v_e_1556_, 1);
lean_inc_ref(v_fn_1570_);
v___x_1572_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1553_, v_s_1554_, v_translator_1555_, v_fn_1570_);
lean_inc_ref(v_arg_1571_);
v___x_1573_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1553_, v_s_1554_, v_translator_1555_, v_arg_1571_);
v___x_1574_ = lean_ptr_addr(v_fn_1570_);
v___x_1575_ = lean_ptr_addr(v___x_1572_);
v___x_1576_ = lean_usize_dec_eq(v___x_1574_, v___x_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_dec_ref_known(v_e_1556_, 2);
v___x_1577_ = l_Lean_Expr_app___override(v___x_1572_, v___x_1573_);
v___x_1578_ = l_Lean_Expr_headBeta(v___x_1577_);
return v___x_1578_;
}
else
{
size_t v___x_1579_; size_t v___x_1580_; uint8_t v___x_1581_; 
v___x_1579_ = lean_ptr_addr(v_arg_1571_);
v___x_1580_ = lean_ptr_addr(v___x_1573_);
v___x_1581_ = lean_usize_dec_eq(v___x_1579_, v___x_1580_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec_ref_known(v_e_1556_, 2);
v___x_1582_ = l_Lean_Expr_app___override(v___x_1572_, v___x_1573_);
v___x_1583_ = l_Lean_Expr_headBeta(v___x_1582_);
return v___x_1583_;
}
else
{
lean_object* v___x_1584_; 
lean_dec_ref(v___x_1573_);
lean_dec_ref(v___x_1572_);
v___x_1584_ = l_Lean_Expr_headBeta(v_e_1556_);
return v___x_1584_;
}
}
}
case 6:
{
lean_object* v_binderName_1585_; lean_object* v_binderType_1586_; lean_object* v_body_1587_; uint8_t v_binderInfo_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; size_t v___x_1591_; size_t v___x_1592_; uint8_t v___x_1593_; 
v_binderName_1585_ = lean_ctor_get(v_e_1556_, 0);
v_binderType_1586_ = lean_ctor_get(v_e_1556_, 1);
v_body_1587_ = lean_ctor_get(v_e_1556_, 2);
v_binderInfo_1588_ = lean_ctor_get_uint8(v_e_1556_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1586_);
v___x_1589_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1553_, v_s_1554_, v_translator_1555_, v_binderType_1586_);
lean_inc_ref(v_body_1587_);
v___x_1590_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1553_, v_s_1554_, v_translator_1555_, v_body_1587_);
v___x_1591_ = lean_ptr_addr(v_binderType_1586_);
v___x_1592_ = lean_ptr_addr(v___x_1589_);
v___x_1593_ = lean_usize_dec_eq(v___x_1591_, v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; 
lean_inc(v_binderName_1585_);
lean_dec_ref_known(v_e_1556_, 3);
v___x_1594_ = l_Lean_Expr_lam___override(v_binderName_1585_, v___x_1589_, v___x_1590_, v_binderInfo_1588_);
return v___x_1594_;
}
else
{
size_t v___x_1595_; size_t v___x_1596_; uint8_t v___x_1597_; 
v___x_1595_ = lean_ptr_addr(v_body_1587_);
v___x_1596_ = lean_ptr_addr(v___x_1590_);
v___x_1597_ = lean_usize_dec_eq(v___x_1595_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
lean_inc(v_binderName_1585_);
lean_dec_ref_known(v_e_1556_, 3);
v___x_1598_ = l_Lean_Expr_lam___override(v_binderName_1585_, v___x_1589_, v___x_1590_, v_binderInfo_1588_);
return v___x_1598_;
}
else
{
uint8_t v___x_1599_; 
v___x_1599_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1588_, v_binderInfo_1588_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; 
lean_inc(v_binderName_1585_);
lean_dec_ref_known(v_e_1556_, 3);
v___x_1600_ = l_Lean_Expr_lam___override(v_binderName_1585_, v___x_1589_, v___x_1590_, v_binderInfo_1588_);
return v___x_1600_;
}
else
{
lean_dec_ref(v___x_1590_);
lean_dec_ref(v___x_1589_);
return v_e_1556_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1601_; lean_object* v_binderType_1602_; lean_object* v_body_1603_; uint8_t v_binderInfo_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; size_t v___x_1607_; size_t v___x_1608_; uint8_t v___x_1609_; 
v_binderName_1601_ = lean_ctor_get(v_e_1556_, 0);
v_binderType_1602_ = lean_ctor_get(v_e_1556_, 1);
v_body_1603_ = lean_ctor_get(v_e_1556_, 2);
v_binderInfo_1604_ = lean_ctor_get_uint8(v_e_1556_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1602_);
v___x_1605_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1553_, v_s_1554_, v_translator_1555_, v_binderType_1602_);
lean_inc_ref(v_body_1603_);
v___x_1606_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1553_, v_s_1554_, v_translator_1555_, v_body_1603_);
v___x_1607_ = lean_ptr_addr(v_binderType_1602_);
v___x_1608_ = lean_ptr_addr(v___x_1605_);
v___x_1609_ = lean_usize_dec_eq(v___x_1607_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; 
lean_inc(v_binderName_1601_);
lean_dec_ref_known(v_e_1556_, 3);
v___x_1610_ = l_Lean_Expr_forallE___override(v_binderName_1601_, v___x_1605_, v___x_1606_, v_binderInfo_1604_);
return v___x_1610_;
}
else
{
size_t v___x_1611_; size_t v___x_1612_; uint8_t v___x_1613_; 
v___x_1611_ = lean_ptr_addr(v_body_1603_);
v___x_1612_ = lean_ptr_addr(v___x_1606_);
v___x_1613_ = lean_usize_dec_eq(v___x_1611_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; 
lean_inc(v_binderName_1601_);
lean_dec_ref_known(v_e_1556_, 3);
v___x_1614_ = l_Lean_Expr_forallE___override(v_binderName_1601_, v___x_1605_, v___x_1606_, v_binderInfo_1604_);
return v___x_1614_;
}
else
{
uint8_t v___x_1615_; 
v___x_1615_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1604_, v_binderInfo_1604_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; 
lean_inc(v_binderName_1601_);
lean_dec_ref_known(v_e_1556_, 3);
v___x_1616_ = l_Lean_Expr_forallE___override(v_binderName_1601_, v___x_1605_, v___x_1606_, v_binderInfo_1604_);
return v___x_1616_;
}
else
{
lean_dec_ref(v___x_1606_);
lean_dec_ref(v___x_1605_);
return v_e_1556_;
}
}
}
}
case 8:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
lean_dec_ref_known(v_e_1556_, 4);
v___x_1617_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3, &l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
v___x_1618_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_1617_);
return v___x_1618_;
}
case 10:
{
lean_object* v_data_1619_; lean_object* v_expr_1620_; lean_object* v___x_1621_; size_t v___x_1622_; size_t v___x_1623_; uint8_t v___x_1624_; 
v_data_1619_ = lean_ctor_get(v_e_1556_, 0);
v_expr_1620_ = lean_ctor_get(v_e_1556_, 1);
lean_inc_ref(v_expr_1620_);
v___x_1621_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1553_, v_s_1554_, v_translator_1555_, v_expr_1620_);
v___x_1622_ = lean_ptr_addr(v_expr_1620_);
v___x_1623_ = lean_ptr_addr(v___x_1621_);
v___x_1624_ = lean_usize_dec_eq(v___x_1622_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; 
lean_inc(v_data_1619_);
lean_dec_ref_known(v_e_1556_, 2);
v___x_1625_ = l_Lean_Expr_mdata___override(v_data_1619_, v___x_1621_);
return v___x_1625_;
}
else
{
lean_dec_ref(v___x_1621_);
return v_e_1556_;
}
}
case 11:
{
lean_object* v_typeName_1626_; lean_object* v_idx_1627_; lean_object* v_struct_1628_; lean_object* v___x_1629_; size_t v___x_1630_; size_t v___x_1631_; uint8_t v___x_1632_; 
v_typeName_1626_ = lean_ctor_get(v_e_1556_, 0);
v_idx_1627_ = lean_ctor_get(v_e_1556_, 1);
v_struct_1628_ = lean_ctor_get(v_e_1556_, 2);
lean_inc_ref(v_struct_1628_);
v___x_1629_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1553_, v_s_1554_, v_translator_1555_, v_struct_1628_);
v___x_1630_ = lean_ptr_addr(v_struct_1628_);
v___x_1631_ = lean_ptr_addr(v___x_1629_);
v___x_1632_ = lean_usize_dec_eq(v___x_1630_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; 
lean_inc(v_idx_1627_);
lean_inc(v_typeName_1626_);
lean_dec_ref_known(v_e_1556_, 3);
v___x_1633_ = l_Lean_Expr_proj___override(v_typeName_1626_, v_idx_1627_, v___x_1629_);
return v___x_1633_;
}
else
{
lean_dec_ref(v___x_1629_);
return v_e_1556_;
}
}
default: 
{
return v_e_1556_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1553_ = stack[0].m_num;
lean_object* v_s_1554_ = stack[1].m_obj;
uint8_t v_translator_1555_ = stack[2].m_num;
lean_object* v_e_1556_ = stack[3].m_obj;
lean_object* v_res_1634_;
v_res_1634_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1553_, v_s_1554_, v_translator_1555_, v_e_1556_);
stack->m_obj
 = v_res_1634_;
}
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(uint8_t v_pu_1635_, lean_object* v_s_1636_, uint8_t v_translator_1637_, lean_object* v_e_1638_){
_start:
{
if (lean_obj_tag(v_e_1638_) == 5)
{
lean_object* v_fn_1639_; lean_object* v_arg_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; size_t v___x_1643_; size_t v___x_1644_; uint8_t v___x_1645_; 
v_fn_1639_ = lean_ctor_get(v_e_1638_, 0);
v_arg_1640_ = lean_ctor_get(v_e_1638_, 1);
lean_inc_ref(v_fn_1639_);
v___x_1641_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1635_, v_s_1636_, v_translator_1637_, v_fn_1639_);
lean_inc_ref(v_arg_1640_);
v___x_1642_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1635_, v_s_1636_, v_translator_1637_, v_arg_1640_);
v___x_1643_ = lean_ptr_addr(v_fn_1639_);
v___x_1644_ = lean_ptr_addr(v___x_1641_);
v___x_1645_ = lean_usize_dec_eq(v___x_1643_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
lean_dec_ref_known(v_e_1638_, 2);
v___x_1646_ = l_Lean_Expr_app___override(v___x_1641_, v___x_1642_);
return v___x_1646_;
}
else
{
size_t v___x_1647_; size_t v___x_1648_; uint8_t v___x_1649_; 
v___x_1647_ = lean_ptr_addr(v_arg_1640_);
v___x_1648_ = lean_ptr_addr(v___x_1642_);
v___x_1649_ = lean_usize_dec_eq(v___x_1647_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; 
lean_dec_ref_known(v_e_1638_, 2);
v___x_1650_ = l_Lean_Expr_app___override(v___x_1641_, v___x_1642_);
return v___x_1650_;
}
else
{
lean_dec_ref(v___x_1642_);
lean_dec_ref(v___x_1641_);
return v_e_1638_;
}
}
}
else
{
lean_object* v___x_1651_; 
v___x_1651_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1635_, v_s_1636_, v_translator_1637_, v_e_1638_);
return v___x_1651_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1635_ = stack[0].m_num;
lean_object* v_s_1636_ = stack[1].m_obj;
uint8_t v_translator_1637_ = stack[2].m_num;
lean_object* v_e_1638_ = stack[3].m_obj;
lean_object* v_res_1652_;
v_res_1652_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_1635_, v_s_1636_, v_translator_1637_, v_e_1638_);
stack->m_obj
 = v_res_1652_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(lean_object* v_pu_1653_, lean_object* v_s_1654_, lean_object* v_translator_1655_, lean_object* v_e_1656_){
_start:
{
uint8_t v_pu_boxed_1657_; uint8_t v_translator_boxed_1658_; lean_object* v_res_1659_; 
v_pu_boxed_1657_ = lean_unbox(v_pu_1653_);
v_translator_boxed_1658_ = lean_unbox(v_translator_1655_);
v_res_1659_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_boxed_1657_, v_s_1654_, v_translator_boxed_1658_, v_e_1656_);
lean_dec_ref(v_s_1654_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(lean_object* v_pu_1660_, lean_object* v_s_1661_, lean_object* v_translator_1662_, lean_object* v_e_1663_){
_start:
{
uint8_t v_pu_boxed_1664_; uint8_t v_translator_boxed_1665_; lean_object* v_res_1666_; 
v_pu_boxed_1664_ = lean_unbox(v_pu_1660_);
v_translator_boxed_1665_ = lean_unbox(v_translator_1662_);
v_res_1666_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_boxed_1664_, v_s_1661_, v_translator_boxed_1665_, v_e_1663_);
lean_dec_ref(v_s_1661_);
return v_res_1666_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(uint8_t v_pu_1667_, lean_object* v_s_1668_, lean_object* v_e_1669_, uint8_t v_translator_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1667_, v_s_1668_, v_translator_1670_, v_e_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1667_ = stack[0].m_num;
lean_object* v_s_1668_ = stack[1].m_obj;
lean_object* v_e_1669_ = stack[2].m_obj;
uint8_t v_translator_1670_ = stack[3].m_num;
lean_object* v_res_1672_;
v_res_1672_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(v_pu_1667_, v_s_1668_, v_e_1669_, v_translator_1670_);
stack->m_obj
 = v_res_1672_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(lean_object* v_pu_1673_, lean_object* v_s_1674_, lean_object* v_e_1675_, lean_object* v_translator_1676_){
_start:
{
uint8_t v_pu_boxed_1677_; uint8_t v_translator_boxed_1678_; lean_object* v_res_1679_; 
v_pu_boxed_1677_ = lean_unbox(v_pu_1673_);
v_translator_boxed_1678_ = lean_unbox(v_translator_1676_);
v_res_1679_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(v_pu_boxed_1677_, v_s_1674_, v_e_1675_, v_translator_boxed_1678_);
lean_dec_ref(v_s_1674_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___impl(lean_object* v_x_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_obj_tag_nat(v_x_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___impl___boxed(lean_object* v_x_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___impl(v_x_1682_);
lean_dec(v_x_1682_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(lean_object* v_t_1684_, lean_object* v_k_1685_){
_start:
{
if (lean_obj_tag(v_t_1684_) == 0)
{
lean_object* v_fvarId_1686_; lean_object* v___x_1687_; 
v_fvarId_1686_ = lean_ctor_get(v_t_1684_, 0);
lean_inc(v_fvarId_1686_);
lean_dec_ref_known(v_t_1684_, 1);
v___x_1687_ = lean_apply_1(v_k_1685_, v_fvarId_1686_);
return v___x_1687_;
}
else
{
return v_k_1685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(lean_object* v_motive_1688_, lean_object* v_ctorIdx_1689_, lean_object* v_t_1690_, lean_object* v_h_1691_, lean_object* v_k_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1690_, v_k_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(lean_object* v_motive_1694_, lean_object* v_ctorIdx_1695_, lean_object* v_t_1696_, lean_object* v_h_1697_, lean_object* v_k_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(v_motive_1694_, v_ctorIdx_1695_, v_t_1696_, v_h_1697_, v_k_1698_);
lean_dec(v_ctorIdx_1695_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(lean_object* v_t_1700_, lean_object* v_fvar_1701_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1700_, v_fvar_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(lean_object* v_motive_1703_, lean_object* v_t_1704_, lean_object* v_h_1705_, lean_object* v_fvar_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1704_, v_fvar_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(lean_object* v_t_1708_, lean_object* v_erased_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1708_, v_erased_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(lean_object* v_motive_1711_, lean_object* v_t_1712_, lean_object* v_h_1713_, lean_object* v_erased_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_1712_, v_erased_1714_);
return v___x_1715_;
}
}
lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object* v_s_1720_, lean_object* v_fvarId_1721_, uint8_t v_translator_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1720_, v_fvarId_1721_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1724_, 0, v_fvarId_1721_);
return v___x_1724_;
}
else
{
lean_object* v_val_1725_; 
lean_dec(v_fvarId_1721_);
v_val_1725_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_val_1725_);
lean_dec_ref_known(v___x_1723_, 1);
if (lean_obj_tag(v_val_1725_) == 1)
{
if (v_translator_1722_ == 0)
{
lean_object* v_fvarId_1726_; 
v_fvarId_1726_ = lean_ctor_get(v_val_1725_, 0);
lean_inc(v_fvarId_1726_);
lean_dec_ref_known(v_val_1725_, 1);
v_fvarId_1721_ = v_fvarId_1726_;
goto _start;
}
else
{
lean_object* v_fvarId_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
v_fvarId_1728_ = lean_ctor_get(v_val_1725_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_val_1725_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v_val_1725_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_fvarId_1728_);
lean_dec(v_val_1725_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
lean_ctor_set_tag(v___x_1730_, 0);
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_fvarId_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
else
{
lean_object* v___x_1736_; 
lean_dec(v_val_1725_);
v___x_1736_ = lean_box(1);
return v___x_1736_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normFVarImp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1720_ = stack[0].m_obj;
lean_object* v_fvarId_1721_ = stack[1].m_obj;
uint8_t v_translator_1722_ = stack[2].m_num;
lean_object* v_res_1737_;
v_res_1737_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1720_, v_fvarId_1721_, v_translator_1722_);
stack->m_obj
 = v_res_1737_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg___boxed(lean_object* v_s_1738_, lean_object* v_fvarId_1739_, lean_object* v_translator_1740_){
_start:
{
uint8_t v_translator_boxed_1741_; lean_object* v_res_1742_; 
v_translator_boxed_1741_ = lean_unbox(v_translator_1740_);
v_res_1742_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1738_, v_fvarId_1739_, v_translator_boxed_1741_);
lean_dec_ref(v_s_1738_);
return v_res_1742_;
}
}
lean_object* l_Lean_Compiler_LCNF_normFVarImp(uint8_t v_pu_1743_, lean_object* v_s_1744_, lean_object* v_fvarId_1745_, uint8_t v_translator_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1744_, v_fvarId_1745_, v_translator_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normFVarImp_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1743_ = stack[0].m_num;
lean_object* v_s_1744_ = stack[1].m_obj;
lean_object* v_fvarId_1745_ = stack[2].m_obj;
uint8_t v_translator_1746_ = stack[3].m_num;
lean_object* v_res_1748_;
v_res_1748_ = l_Lean_Compiler_LCNF_normFVarImp(v_pu_1743_, v_s_1744_, v_fvarId_1745_, v_translator_1746_);
stack->m_obj
 = v_res_1748_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVarImp___boxed(lean_object* v_pu_1749_, lean_object* v_s_1750_, lean_object* v_fvarId_1751_, lean_object* v_translator_1752_){
_start:
{
uint8_t v_pu_boxed_1753_; uint8_t v_translator_boxed_1754_; lean_object* v_res_1755_; 
v_pu_boxed_1753_ = lean_unbox(v_pu_1749_);
v_translator_boxed_1754_ = lean_unbox(v_translator_1752_);
v_res_1755_ = l_Lean_Compiler_LCNF_normFVarImp(v_pu_boxed_1753_, v_s_1750_, v_fvarId_1751_, v_translator_boxed_1754_);
lean_dec_ref(v_s_1750_);
return v_res_1755_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t v_pu_1756_, lean_object* v_s_1757_, lean_object* v_arg_1758_, uint8_t v_translator_1759_){
_start:
{
switch(lean_obj_tag(v_arg_1758_))
{
case 0:
{
return v_arg_1758_;
}
case 1:
{
lean_object* v_fvarId_1760_; lean_object* v___x_1761_; 
v_fvarId_1760_ = lean_ctor_get(v_arg_1758_, 0);
v___x_1761_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_1757_, v_fvarId_1760_);
if (lean_obj_tag(v___x_1761_) == 0)
{
return v_arg_1758_;
}
else
{
lean_object* v_val_1762_; 
lean_dec_ref_known(v_arg_1758_, 1);
v_val_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_val_1762_);
lean_dec_ref_known(v___x_1761_, 1);
switch(lean_obj_tag(v_val_1762_))
{
case 0:
{
lean_object* v___x_1763_; 
v___x_1763_ = lean_box(0);
return v___x_1763_;
}
case 1:
{
lean_object* v_fvarId_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1772_; 
v_fvarId_1764_ = lean_ctor_get(v_val_1762_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v_val_1762_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1766_ = v_val_1762_;
v_isShared_1767_ = v_isSharedCheck_1772_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_fvarId_1764_);
lean_dec(v_val_1762_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1772_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_fvarId_1764_);
v___x_1769_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
if (v_translator_1759_ == 0)
{
v_arg_1758_ = v___x_1769_;
goto _start;
}
else
{
return v___x_1769_;
}
}
}
}
default: 
{
lean_object* v_expr_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
v_expr_1773_ = lean_ctor_get(v_val_1762_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_val_1762_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v_val_1762_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_expr_1773_);
lean_dec(v_val_1762_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_expr_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
}
default: 
{
lean_object* v_expr_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_expr_1781_ = lean_ctor_get(v_arg_1758_, 0);
lean_inc_ref(v_expr_1781_);
v___x_1782_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1756_, v_s_1757_, v_translator_1759_, v_expr_1781_);
v___x_1783_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_1756_, v_arg_1758_, v___x_1782_);
return v___x_1783_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1756_ = stack[0].m_num;
lean_object* v_s_1757_ = stack[1].m_obj;
lean_object* v_arg_1758_ = stack[2].m_obj;
uint8_t v_translator_1759_ = stack[3].m_num;
lean_object* v_res_1784_;
v_res_1784_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1756_, v_s_1757_, v_arg_1758_, v_translator_1759_);
stack->m_obj
 = v_res_1784_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp___boxed(lean_object* v_pu_1785_, lean_object* v_s_1786_, lean_object* v_arg_1787_, lean_object* v_translator_1788_){
_start:
{
uint8_t v_pu_boxed_1789_; uint8_t v_translator_boxed_1790_; lean_object* v_res_1791_; 
v_pu_boxed_1789_ = lean_unbox(v_pu_1785_);
v_translator_boxed_1790_ = lean_unbox(v_translator_1788_);
v_res_1791_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_boxed_1789_, v_s_1786_, v_arg_1787_, v_translator_boxed_1790_);
lean_dec_ref(v_s_1786_);
return v_res_1791_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(uint8_t v_pu_1792_, lean_object* v_s_1793_, uint8_t v_translator_1794_, lean_object* v_i_1795_, lean_object* v_as_1796_){
_start:
{
lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1797_ = lean_array_get_size(v_as_1796_);
v___x_1798_ = lean_nat_dec_lt(v_i_1795_, v___x_1797_);
if (v___x_1798_ == 0)
{
lean_dec(v_i_1795_);
return v_as_1796_;
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1800_; size_t v___x_1801_; size_t v___x_1802_; uint8_t v___x_1803_; 
v_a_1799_ = lean_array_fget_borrowed(v_as_1796_, v_i_1795_);
lean_inc(v_a_1799_);
v___x_1800_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_1792_, v_s_1793_, v_a_1799_, v_translator_1794_);
v___x_1801_ = lean_ptr_addr(v_a_1799_);
v___x_1802_ = lean_ptr_addr(v___x_1800_);
v___x_1803_ = lean_usize_dec_eq(v___x_1801_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = lean_unsigned_to_nat(1u);
v___x_1805_ = lean_nat_add(v_i_1795_, v___x_1804_);
v___x_1806_ = lean_array_fset(v_as_1796_, v_i_1795_, v___x_1800_);
lean_dec(v_i_1795_);
v_i_1795_ = v___x_1805_;
v_as_1796_ = v___x_1806_;
goto _start;
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec(v___x_1800_);
v___x_1808_ = lean_unsigned_to_nat(1u);
v___x_1809_ = lean_nat_add(v_i_1795_, v___x_1808_);
lean_dec(v_i_1795_);
v_i_1795_ = v___x_1809_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1792_ = stack[0].m_num;
lean_object* v_s_1793_ = stack[1].m_obj;
uint8_t v_translator_1794_ = stack[2].m_num;
lean_object* v_i_1795_ = stack[3].m_obj;
lean_object* v_as_1796_ = stack[4].m_obj;
lean_object* v_res_1811_;
v_res_1811_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_1792_, v_s_1793_, v_translator_1794_, v_i_1795_, v_as_1796_);
stack->m_obj
 = v_res_1811_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0___boxed(lean_object* v_pu_1812_, lean_object* v_s_1813_, lean_object* v_translator_1814_, lean_object* v_i_1815_, lean_object* v_as_1816_){
_start:
{
uint8_t v_pu_boxed_1817_; uint8_t v_translator_boxed_1818_; lean_object* v_res_1819_; 
v_pu_boxed_1817_ = lean_unbox(v_pu_1812_);
v_translator_boxed_1818_ = lean_unbox(v_translator_1814_);
v_res_1819_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_boxed_1817_, v_s_1813_, v_translator_boxed_1818_, v_i_1815_, v_as_1816_);
lean_dec_ref(v_s_1813_);
return v_res_1819_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t v_pu_1820_, lean_object* v_s_1821_, lean_object* v_args_1822_, uint8_t v_translator_1823_){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = lean_unsigned_to_nat(0u);
v___x_1825_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_1820_, v_s_1821_, v_translator_1823_, v___x_1824_, v_args_1822_);
return v___x_1825_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1820_ = stack[0].m_num;
lean_object* v_s_1821_ = stack[1].m_obj;
lean_object* v_args_1822_ = stack[2].m_obj;
uint8_t v_translator_1823_ = stack[3].m_num;
lean_object* v_res_1826_;
v_res_1826_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1820_, v_s_1821_, v_args_1822_, v_translator_1823_);
stack->m_obj
 = v_res_1826_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(lean_object* v_pu_1827_, lean_object* v_s_1828_, lean_object* v_args_1829_, lean_object* v_translator_1830_){
_start:
{
uint8_t v_pu_boxed_1831_; uint8_t v_translator_boxed_1832_; lean_object* v_res_1833_; 
v_pu_boxed_1831_ = lean_unbox(v_pu_1827_);
v_translator_boxed_1832_ = lean_unbox(v_translator_1830_);
v_res_1833_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_boxed_1831_, v_s_1828_, v_args_1829_, v_translator_boxed_1832_);
lean_dec_ref(v_s_1828_);
return v_res_1833_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t v_pu_1834_, lean_object* v_s_1835_, lean_object* v_e_1836_, uint8_t v_translator_1837_){
_start:
{
lean_object* v_fvarId_1839_; lean_object* v_args_1845_; 
switch(lean_obj_tag(v_e_1836_))
{
case 2:
{
lean_object* v_struct_1848_; lean_object* v___x_1849_; 
v_struct_1848_ = lean_ctor_get(v_e_1836_, 2);
lean_inc(v_struct_1848_);
v___x_1849_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1835_, v_struct_1848_, v_translator_1837_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_fvarId_1850_; lean_object* v___x_1851_; 
v_fvarId_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_fvarId_1850_);
lean_dec_ref_known(v___x_1849_, 1);
v___x_1851_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1834_, v_e_1836_, v_fvarId_1850_);
return v___x_1851_;
}
else
{
lean_object* v___x_1852_; 
lean_dec_ref_known(v_e_1836_, 3);
v___x_1852_ = lean_box(1);
return v___x_1852_;
}
}
case 3:
{
lean_object* v_args_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v_args_1853_ = lean_ctor_get(v_e_1836_, 2);
lean_inc_ref(v_args_1853_);
v___x_1854_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1834_, v_s_1835_, v_args_1853_, v_translator_1837_);
v___x_1855_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1836_, v___x_1854_);
return v___x_1855_;
}
case 4:
{
lean_object* v_fvarId_1856_; lean_object* v_args_1857_; lean_object* v___x_1858_; 
v_fvarId_1856_ = lean_ctor_get(v_e_1836_, 0);
v_args_1857_ = lean_ctor_get(v_e_1836_, 1);
lean_inc(v_fvarId_1856_);
v___x_1858_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1835_, v_fvarId_1856_, v_translator_1837_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_fvarId_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v_fvarId_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_fvarId_1859_);
lean_dec_ref_known(v___x_1858_, 1);
lean_inc_ref(v_args_1857_);
v___x_1860_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1834_, v_s_1835_, v_args_1857_, v_translator_1837_);
v___x_1861_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___redArg(v_e_1836_, v_fvarId_1859_, v___x_1860_);
lean_dec_ref_known(v_e_1836_, 2);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; 
lean_dec_ref_known(v_e_1836_, 2);
v___x_1862_ = lean_box(1);
return v___x_1862_;
}
}
case 5:
{
lean_object* v_args_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v_args_1863_ = lean_ctor_get(v_e_1836_, 1);
lean_inc_ref(v_args_1863_);
v___x_1864_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1834_, v_s_1835_, v_args_1863_, v_translator_1837_);
v___x_1865_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1836_, v___x_1864_);
return v___x_1865_;
}
case 6:
{
lean_object* v_var_1866_; 
v_var_1866_ = lean_ctor_get(v_e_1836_, 1);
lean_inc(v_var_1866_);
v_fvarId_1839_ = v_var_1866_;
goto v___jp_1838_;
}
case 7:
{
lean_object* v_var_1867_; 
v_var_1867_ = lean_ctor_get(v_e_1836_, 1);
lean_inc(v_var_1867_);
v_fvarId_1839_ = v_var_1867_;
goto v___jp_1838_;
}
case 8:
{
lean_object* v_var_1868_; lean_object* v___x_1869_; 
v_var_1868_ = lean_ctor_get(v_e_1836_, 2);
lean_inc(v_var_1868_);
v___x_1869_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1835_, v_var_1868_, v_translator_1837_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_fvarId_1870_; lean_object* v___x_1871_; 
v_fvarId_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_fvarId_1870_);
lean_dec_ref_known(v___x_1869_, 1);
v___x_1871_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1834_, v_e_1836_, v_fvarId_1870_);
return v___x_1871_;
}
else
{
lean_object* v___x_1872_; 
lean_dec_ref_known(v_e_1836_, 3);
v___x_1872_ = lean_box(1);
return v___x_1872_;
}
}
case 9:
{
lean_object* v_args_1873_; 
v_args_1873_ = lean_ctor_get(v_e_1836_, 1);
lean_inc_ref(v_args_1873_);
v_args_1845_ = v_args_1873_;
goto v___jp_1844_;
}
case 10:
{
lean_object* v_args_1874_; 
v_args_1874_ = lean_ctor_get(v_e_1836_, 1);
lean_inc_ref(v_args_1874_);
v_args_1845_ = v_args_1874_;
goto v___jp_1844_;
}
case 11:
{
lean_object* v_n_1875_; lean_object* v_var_1876_; lean_object* v___x_1877_; 
v_n_1875_ = lean_ctor_get(v_e_1836_, 0);
lean_inc(v_n_1875_);
v_var_1876_ = lean_ctor_get(v_e_1836_, 1);
lean_inc(v_var_1876_);
v___x_1877_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1835_, v_var_1876_, v_translator_1837_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_fvarId_1878_; lean_object* v___x_1879_; 
v_fvarId_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_fvarId_1878_);
lean_dec_ref_known(v___x_1877_, 1);
v___x_1879_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp___redArg(v_e_1836_, v_n_1875_, v_fvarId_1878_);
return v___x_1879_;
}
else
{
lean_object* v___x_1880_; 
lean_dec(v_n_1875_);
lean_dec_ref_known(v_e_1836_, 2);
v___x_1880_ = lean_box(1);
return v___x_1880_;
}
}
case 12:
{
lean_object* v_var_1881_; lean_object* v_i_1882_; uint8_t v_updateHeader_1883_; lean_object* v_args_1884_; lean_object* v___x_1885_; 
v_var_1881_ = lean_ctor_get(v_e_1836_, 0);
v_i_1882_ = lean_ctor_get(v_e_1836_, 1);
lean_inc_ref(v_i_1882_);
v_updateHeader_1883_ = lean_ctor_get_uint8(v_e_1836_, sizeof(void*)*3);
v_args_1884_ = lean_ctor_get(v_e_1836_, 2);
lean_inc(v_var_1881_);
v___x_1885_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1835_, v_var_1881_, v_translator_1837_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_fvarId_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v_fvarId_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_fvarId_1886_);
lean_dec_ref_known(v___x_1885_, 1);
lean_inc_ref(v_args_1884_);
v___x_1887_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1834_, v_s_1835_, v_args_1884_, v_translator_1837_);
v___x_1888_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp___redArg(v_e_1836_, v_fvarId_1886_, v_i_1882_, v_updateHeader_1883_, v___x_1887_);
return v___x_1888_;
}
else
{
lean_object* v___x_1889_; 
lean_dec_ref(v_i_1882_);
lean_dec_ref_known(v_e_1836_, 3);
v___x_1889_ = lean_box(1);
return v___x_1889_;
}
}
case 13:
{
lean_object* v_ty_1890_; lean_object* v_fvarId_1891_; lean_object* v___x_1892_; 
v_ty_1890_ = lean_ctor_get(v_e_1836_, 0);
lean_inc_ref(v_ty_1890_);
v_fvarId_1891_ = lean_ctor_get(v_e_1836_, 1);
lean_inc(v_fvarId_1891_);
v___x_1892_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1835_, v_fvarId_1891_, v_translator_1837_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_fvarId_1893_; lean_object* v___x_1894_; 
v_fvarId_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_fvarId_1893_);
lean_dec_ref_known(v___x_1892_, 1);
v___x_1894_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp___redArg(v_e_1836_, v_ty_1890_, v_fvarId_1893_);
return v___x_1894_;
}
else
{
lean_object* v___x_1895_; 
lean_dec_ref_known(v_e_1836_, 2);
lean_dec_ref(v_ty_1890_);
v___x_1895_ = lean_box(1);
return v___x_1895_;
}
}
case 14:
{
lean_object* v_fvarId_1896_; lean_object* v___x_1897_; 
v_fvarId_1896_ = lean_ctor_get(v_e_1836_, 0);
lean_inc(v_fvarId_1896_);
v___x_1897_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1835_, v_fvarId_1896_, v_translator_1837_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_fvarId_1898_; lean_object* v___x_1899_; 
v_fvarId_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_fvarId_1898_);
lean_dec_ref_known(v___x_1897_, 1);
v___x_1899_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp___redArg(v_e_1836_, v_fvarId_1898_);
return v___x_1899_;
}
else
{
lean_object* v___x_1900_; 
lean_dec_ref_known(v_e_1836_, 1);
v___x_1900_ = lean_box(1);
return v___x_1900_;
}
}
case 15:
{
lean_object* v_fvarId_1901_; lean_object* v___x_1902_; 
v_fvarId_1901_ = lean_ctor_get(v_e_1836_, 0);
lean_inc(v_fvarId_1901_);
v___x_1902_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1835_, v_fvarId_1901_, v_translator_1837_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_fvarId_1903_; lean_object* v___x_1904_; 
v_fvarId_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_fvarId_1903_);
lean_dec_ref_known(v___x_1902_, 1);
v___x_1904_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp___redArg(v_e_1836_, v_fvarId_1903_);
return v___x_1904_;
}
else
{
lean_object* v___x_1905_; 
lean_dec_ref_known(v_e_1836_, 1);
v___x_1905_ = lean_box(1);
return v___x_1905_;
}
}
default: 
{
return v_e_1836_;
}
}
v___jp_1838_:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_1835_, v_fvarId_1839_, v_translator_1837_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_fvarId_1841_; lean_object* v___x_1842_; 
v_fvarId_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_fvarId_1841_);
lean_dec_ref_known(v___x_1840_, 1);
v___x_1842_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_1834_, v_e_1836_, v_fvarId_1841_);
return v___x_1842_;
}
else
{
lean_object* v___x_1843_; 
lean_dec(v_e_1836_);
v___x_1843_ = lean_box(1);
return v___x_1843_;
}
}
v___jp_1844_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1834_, v_s_1835_, v_args_1845_, v_translator_1837_);
v___x_1847_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_e_1836_, v___x_1846_);
return v___x_1847_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1834_ = stack[0].m_num;
lean_object* v_s_1835_ = stack[1].m_obj;
lean_object* v_e_1836_ = stack[2].m_obj;
uint8_t v_translator_1837_ = stack[3].m_num;
lean_object* v_res_1906_;
v_res_1906_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_1834_, v_s_1835_, v_e_1836_, v_translator_1837_);
stack->m_obj
 = v_res_1906_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp___boxed(lean_object* v_pu_1907_, lean_object* v_s_1908_, lean_object* v_e_1909_, lean_object* v_translator_1910_){
_start:
{
uint8_t v_pu_boxed_1911_; uint8_t v_translator_boxed_1912_; lean_object* v_res_1913_; 
v_pu_boxed_1911_ = lean_unbox(v_pu_1907_);
v_translator_boxed_1912_ = lean_unbox(v_translator_1910_);
v_res_1913_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_boxed_1911_, v_s_1908_, v_e_1909_, v_translator_boxed_1912_);
lean_dec_ref(v_s_1908_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(lean_object* v_inst_1914_, lean_object* v_inst_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_apply_2(v_inst_1914_, lean_box(0), v_inst_1915_);
return v___x_1916_;
}
}
lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(uint8_t v_pu_1917_, uint8_t v_t_1918_, lean_object* v_m_1919_, lean_object* v_n_1920_, lean_object* v_inst_1921_, lean_object* v_inst_1922_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_apply_2(v_inst_1921_, lean_box(0), v_inst_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1917_ = stack[0].m_num;
uint8_t v_t_1918_ = stack[1].m_num;
lean_object* v_inst_1921_ = stack[4].m_obj;
lean_object* v_inst_1922_ = stack[5].m_obj;
lean_object* v_res_1924_;
v_res_1924_ = l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(v_pu_1917_, v_t_1918_, lean_box(0), lean_box(0), v_inst_1921_, v_inst_1922_);
stack->m_obj
 = v_res_1924_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(lean_object* v_pu_1925_, lean_object* v_t_1926_, lean_object* v_m_1927_, lean_object* v_n_1928_, lean_object* v_inst_1929_, lean_object* v_inst_1930_){
_start:
{
uint8_t v_pu_boxed_1931_; uint8_t v_t_boxed_1932_; lean_object* v_res_1933_; 
v_pu_boxed_1931_ = lean_unbox(v_pu_1925_);
v_t_boxed_1932_ = lean_unbox(v_t_1926_);
v_res_1933_ = l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(v_pu_boxed_1931_, v_t_boxed_1932_, v_m_1927_, v_n_1928_, v_inst_1929_, v_inst_1930_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0(lean_object* v_inst_1934_, lean_object* v_inst_1935_, lean_object* v_f_1936_){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = lean_apply_1(v_inst_1934_, v_f_1936_);
v___x_1938_ = lean_apply_2(v_inst_1935_, lean_box(0), v___x_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(lean_object* v_inst_1939_, lean_object* v_inst_1940_){
_start:
{
lean_object* v___f_1941_; 
v___f_1941_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1941_, 0, v_inst_1940_);
lean_closure_set(v___f_1941_, 1, v_inst_1939_);
return v___f_1941_;
}
}
lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(uint8_t v_pu_1942_, lean_object* v_m_1943_, lean_object* v_n_1944_, lean_object* v_inst_1945_, lean_object* v_inst_1946_){
_start:
{
lean_object* v___f_1947_; 
v___f_1947_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1947_, 0, v_inst_1946_);
lean_closure_set(v___f_1947_, 1, v_inst_1945_);
return v___f_1947_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1942_ = stack[0].m_num;
lean_object* v_inst_1945_ = stack[3].m_obj;
lean_object* v_inst_1946_ = stack[4].m_obj;
lean_object* v_res_1948_;
v_res_1948_ = l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(v_pu_1942_, lean_box(0), lean_box(0), v_inst_1945_, v_inst_1946_);
stack->m_obj
 = v_res_1948_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(lean_object* v_pu_1949_, lean_object* v_m_1950_, lean_object* v_n_1951_, lean_object* v_inst_1952_, lean_object* v_inst_1953_){
_start:
{
uint8_t v_pu_boxed_1954_; lean_object* v_res_1955_; 
v_pu_boxed_1954_ = lean_unbox(v_pu_1949_);
v_res_1955_ = l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(v_pu_boxed_1954_, v_m_1950_, v_n_1951_, v_inst_1952_, v_inst_1953_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg___lam__0(lean_object* v___x_1956_, lean_object* v___x_1957_, lean_object* v_fvarId_1958_, lean_object* v_arg_1959_, lean_object* v_s_1960_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1956_, v___x_1957_, v_s_1960_, v_fvarId_1958_, v_arg_1959_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___redArg(lean_object* v_inst_1964_, lean_object* v_fvarId_1965_, lean_object* v_arg_1966_){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___f_1969_; lean_object* v___x_1970_; 
v___x_1967_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1968_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1969_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1969_, 0, v___x_1967_);
lean_closure_set(v___f_1969_, 1, v___x_1968_);
lean_closure_set(v___f_1969_, 2, v_fvarId_1965_);
lean_closure_set(v___f_1969_, 3, v_arg_1966_);
v___x_1970_ = lean_apply_1(v_inst_1964_, v___f_1969_);
return v___x_1970_;
}
}
lean_object* l_Lean_Compiler_LCNF_addSubst(lean_object* v_m_1971_, uint8_t v_pu_1972_, lean_object* v_inst_1973_, lean_object* v_fvarId_1974_, lean_object* v_arg_1975_){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___f_1978_; lean_object* v___x_1979_; 
v___x_1976_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1977_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_1978_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1978_, 0, v___x_1976_);
lean_closure_set(v___f_1978_, 1, v___x_1977_);
lean_closure_set(v___f_1978_, 2, v_fvarId_1974_);
lean_closure_set(v___f_1978_, 3, v_arg_1975_);
v___x_1979_ = lean_apply_1(v_inst_1973_, v___f_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_addSubst_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1972_ = stack[1].m_num;
lean_object* v_inst_1973_ = stack[2].m_obj;
lean_object* v_fvarId_1974_ = stack[3].m_obj;
lean_object* v_arg_1975_ = stack[4].m_obj;
lean_object* v_res_1980_;
v_res_1980_ = l_Lean_Compiler_LCNF_addSubst(lean_box(0), v_pu_1972_, v_inst_1973_, v_fvarId_1974_, v_arg_1975_);
stack->m_obj
 = v_res_1980_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addSubst___boxed(lean_object* v_m_1981_, lean_object* v_pu_1982_, lean_object* v_inst_1983_, lean_object* v_fvarId_1984_, lean_object* v_arg_1985_){
_start:
{
uint8_t v_pu_boxed_1986_; lean_object* v_res_1987_; 
v_pu_boxed_1986_ = lean_unbox(v_pu_1982_);
v_res_1987_ = l_Lean_Compiler_LCNF_addSubst(v_m_1981_, v_pu_boxed_1986_, v_inst_1983_, v_fvarId_1984_, v_arg_1985_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0(lean_object* v_fvarId_x27_1988_, lean_object* v___x_1989_, lean_object* v___x_1990_, lean_object* v_fvarId_1991_, lean_object* v_s_1992_){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1993_, 0, v_fvarId_x27_1988_);
v___x_1994_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1989_, v___x_1990_, v_s_1992_, v_fvarId_1991_, v___x_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___redArg(lean_object* v_inst_1995_, lean_object* v_fvarId_1996_, lean_object* v_fvarId_x27_1997_){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___f_2000_; lean_object* v___x_2001_; 
v___x_1998_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_1999_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_2000_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2000_, 0, v_fvarId_x27_1997_);
lean_closure_set(v___f_2000_, 1, v___x_1998_);
lean_closure_set(v___f_2000_, 2, v___x_1999_);
lean_closure_set(v___f_2000_, 3, v_fvarId_1996_);
v___x_2001_ = lean_apply_1(v_inst_1995_, v___f_2000_);
return v___x_2001_;
}
}
lean_object* l_Lean_Compiler_LCNF_addFVarSubst(lean_object* v_m_2002_, uint8_t v_ph_2003_, lean_object* v_inst_2004_, lean_object* v_fvarId_2005_, lean_object* v_fvarId_x27_2006_){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___f_2009_; lean_object* v___x_2010_; 
v___x_2007_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0));
v___x_2008_ = ((lean_object*)(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1));
v___f_2009_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2009_, 0, v_fvarId_x27_2006_);
lean_closure_set(v___f_2009_, 1, v___x_2007_);
lean_closure_set(v___f_2009_, 2, v___x_2008_);
lean_closure_set(v___f_2009_, 3, v_fvarId_2005_);
v___x_2010_ = lean_apply_1(v_inst_2004_, v___f_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_addFVarSubst_0interp(lean_interpreter_value* stack)
{
uint8_t v_ph_2003_ = stack[1].m_num;
lean_object* v_inst_2004_ = stack[2].m_obj;
lean_object* v_fvarId_2005_ = stack[3].m_obj;
lean_object* v_fvarId_x27_2006_ = stack[4].m_obj;
lean_object* v_res_2011_;
v_res_2011_ = l_Lean_Compiler_LCNF_addFVarSubst(lean_box(0), v_ph_2003_, v_inst_2004_, v_fvarId_2005_, v_fvarId_x27_2006_);
stack->m_obj
 = v_res_2011_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addFVarSubst___boxed(lean_object* v_m_2012_, lean_object* v_ph_2013_, lean_object* v_inst_2014_, lean_object* v_fvarId_2015_, lean_object* v_fvarId_x27_2016_){
_start:
{
uint8_t v_ph_boxed_2017_; lean_object* v_res_2018_; 
v_ph_boxed_2017_ = lean_unbox(v_ph_2013_);
v_res_2018_ = l_Lean_Compiler_LCNF_addFVarSubst(v_m_2012_, v_ph_boxed_2017_, v_inst_2014_, v_fvarId_2015_, v_fvarId_x27_2016_);
return v_res_2018_;
}
}
lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(lean_object* v_fvarId_2019_, uint8_t v_t_2020_, lean_object* v_toPure_2021_, lean_object* v_____do__lift_2022_){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_____do__lift_2022_, v_fvarId_2019_, v_t_2020_);
v___x_2024_ = lean_apply_2(v_toPure_2021_, lean_box(0), v___x_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normFVar___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2019_ = stack[0].m_obj;
uint8_t v_t_2020_ = stack[1].m_num;
lean_object* v_toPure_2021_ = stack[2].m_obj;
lean_object* v_____do__lift_2022_ = stack[3].m_obj;
lean_object* v_res_2025_;
v_res_2025_ = l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(v_fvarId_2019_, v_t_2020_, v_toPure_2021_, v_____do__lift_2022_);
stack->m_obj
 = v_res_2025_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(lean_object* v_fvarId_2026_, lean_object* v_t_2027_, lean_object* v_toPure_2028_, lean_object* v_____do__lift_2029_){
_start:
{
uint8_t v_t_boxed_2030_; lean_object* v_res_2031_; 
v_t_boxed_2030_ = lean_unbox(v_t_2027_);
v_res_2031_ = l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(v_fvarId_2026_, v_t_boxed_2030_, v_toPure_2028_, v_____do__lift_2029_);
lean_dec_ref(v_____do__lift_2029_);
return v_res_2031_;
}
}
lean_object* l_Lean_Compiler_LCNF_normFVar___redArg(uint8_t v_t_2032_, lean_object* v_inst_2033_, lean_object* v_inst_2034_, lean_object* v_fvarId_2035_){
_start:
{
lean_object* v_toApplicative_2036_; lean_object* v_toBind_2037_; lean_object* v_toPure_2038_; lean_object* v___x_2039_; lean_object* v___f_2040_; lean_object* v___x_2041_; 
v_toApplicative_2036_ = lean_ctor_get(v_inst_2034_, 0);
lean_inc_ref(v_toApplicative_2036_);
v_toBind_2037_ = lean_ctor_get(v_inst_2034_, 1);
lean_inc(v_toBind_2037_);
lean_dec_ref(v_inst_2034_);
v_toPure_2038_ = lean_ctor_get(v_toApplicative_2036_, 1);
lean_inc(v_toPure_2038_);
lean_dec_ref(v_toApplicative_2036_);
v___x_2039_ = lean_box(v_t_2032_);
v___f_2040_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2040_, 0, v_fvarId_2035_);
lean_closure_set(v___f_2040_, 1, v___x_2039_);
lean_closure_set(v___f_2040_, 2, v_toPure_2038_);
v___x_2041_ = lean_apply_4(v_toBind_2037_, lean_box(0), lean_box(0), v_inst_2033_, v___f_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normFVar___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2032_ = stack[0].m_num;
lean_object* v_inst_2033_ = stack[1].m_obj;
lean_object* v_inst_2034_ = stack[2].m_obj;
lean_object* v_fvarId_2035_ = stack[3].m_obj;
lean_object* v_res_2042_;
v_res_2042_ = l_Lean_Compiler_LCNF_normFVar___redArg(v_t_2032_, v_inst_2033_, v_inst_2034_, v_fvarId_2035_);
stack->m_obj
 = v_res_2042_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___redArg___boxed(lean_object* v_t_2043_, lean_object* v_inst_2044_, lean_object* v_inst_2045_, lean_object* v_fvarId_2046_){
_start:
{
uint8_t v_t_boxed_2047_; lean_object* v_res_2048_; 
v_t_boxed_2047_ = lean_unbox(v_t_2043_);
v_res_2048_ = l_Lean_Compiler_LCNF_normFVar___redArg(v_t_boxed_2047_, v_inst_2044_, v_inst_2045_, v_fvarId_2046_);
return v_res_2048_;
}
}
lean_object* l_Lean_Compiler_LCNF_normFVar(lean_object* v_m_2049_, uint8_t v_pu_2050_, uint8_t v_t_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_fvarId_2054_){
_start:
{
lean_object* v_toApplicative_2055_; lean_object* v_toBind_2056_; lean_object* v_toPure_2057_; lean_object* v___x_2058_; lean_object* v___f_2059_; lean_object* v___x_2060_; 
v_toApplicative_2055_ = lean_ctor_get(v_inst_2053_, 0);
lean_inc_ref(v_toApplicative_2055_);
v_toBind_2056_ = lean_ctor_get(v_inst_2053_, 1);
lean_inc(v_toBind_2056_);
lean_dec_ref(v_inst_2053_);
v_toPure_2057_ = lean_ctor_get(v_toApplicative_2055_, 1);
lean_inc(v_toPure_2057_);
lean_dec_ref(v_toApplicative_2055_);
v___x_2058_ = lean_box(v_t_2051_);
v___f_2059_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2059_, 0, v_fvarId_2054_);
lean_closure_set(v___f_2059_, 1, v___x_2058_);
lean_closure_set(v___f_2059_, 2, v_toPure_2057_);
v___x_2060_ = lean_apply_4(v_toBind_2056_, lean_box(0), lean_box(0), v_inst_2052_, v___f_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normFVar_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2050_ = stack[1].m_num;
uint8_t v_t_2051_ = stack[2].m_num;
lean_object* v_inst_2052_ = stack[3].m_obj;
lean_object* v_inst_2053_ = stack[4].m_obj;
lean_object* v_fvarId_2054_ = stack[5].m_obj;
lean_object* v_res_2061_;
v_res_2061_ = l_Lean_Compiler_LCNF_normFVar(lean_box(0), v_pu_2050_, v_t_2051_, v_inst_2052_, v_inst_2053_, v_fvarId_2054_);
stack->m_obj
 = v_res_2061_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFVar___boxed(lean_object* v_m_2062_, lean_object* v_pu_2063_, lean_object* v_t_2064_, lean_object* v_inst_2065_, lean_object* v_inst_2066_, lean_object* v_fvarId_2067_){
_start:
{
uint8_t v_pu_boxed_2068_; uint8_t v_t_boxed_2069_; lean_object* v_res_2070_; 
v_pu_boxed_2068_ = lean_unbox(v_pu_2063_);
v_t_boxed_2069_ = lean_unbox(v_t_2064_);
v_res_2070_ = l_Lean_Compiler_LCNF_normFVar(v_m_2062_, v_pu_boxed_2068_, v_t_boxed_2069_, v_inst_2065_, v_inst_2066_, v_fvarId_2067_);
return v_res_2070_;
}
}
lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(uint8_t v_pu_2071_, uint8_t v_t_2072_, lean_object* v_e_2073_, lean_object* v_toPure_2074_, lean_object* v_____do__lift_2075_){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2071_, v_____do__lift_2075_, v_t_2072_, v_e_2073_);
v___x_2077_ = lean_apply_2(v_toPure_2074_, lean_box(0), v___x_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normExpr___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2071_ = stack[0].m_num;
uint8_t v_t_2072_ = stack[1].m_num;
lean_object* v_e_2073_ = stack[2].m_obj;
lean_object* v_toPure_2074_ = stack[3].m_obj;
lean_object* v_____do__lift_2075_ = stack[4].m_obj;
lean_object* v_res_2078_;
v_res_2078_ = l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(v_pu_2071_, v_t_2072_, v_e_2073_, v_toPure_2074_, v_____do__lift_2075_);
stack->m_obj
 = v_res_2078_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(lean_object* v_pu_2079_, lean_object* v_t_2080_, lean_object* v_e_2081_, lean_object* v_toPure_2082_, lean_object* v_____do__lift_2083_){
_start:
{
uint8_t v_pu_boxed_2084_; uint8_t v_t_boxed_2085_; lean_object* v_res_2086_; 
v_pu_boxed_2084_ = lean_unbox(v_pu_2079_);
v_t_boxed_2085_ = lean_unbox(v_t_2080_);
v_res_2086_ = l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(v_pu_boxed_2084_, v_t_boxed_2085_, v_e_2081_, v_toPure_2082_, v_____do__lift_2083_);
lean_dec_ref(v_____do__lift_2083_);
return v_res_2086_;
}
}
lean_object* l_Lean_Compiler_LCNF_normExpr___redArg(uint8_t v_pu_2087_, uint8_t v_t_2088_, lean_object* v_inst_2089_, lean_object* v_inst_2090_, lean_object* v_e_2091_){
_start:
{
lean_object* v_toApplicative_2092_; lean_object* v_toBind_2093_; lean_object* v_toPure_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___f_2097_; lean_object* v___x_2098_; 
v_toApplicative_2092_ = lean_ctor_get(v_inst_2090_, 0);
lean_inc_ref(v_toApplicative_2092_);
v_toBind_2093_ = lean_ctor_get(v_inst_2090_, 1);
lean_inc(v_toBind_2093_);
lean_dec_ref(v_inst_2090_);
v_toPure_2094_ = lean_ctor_get(v_toApplicative_2092_, 1);
lean_inc(v_toPure_2094_);
lean_dec_ref(v_toApplicative_2092_);
v___x_2095_ = lean_box(v_pu_2087_);
v___x_2096_ = lean_box(v_t_2088_);
v___f_2097_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2097_, 0, v___x_2095_);
lean_closure_set(v___f_2097_, 1, v___x_2096_);
lean_closure_set(v___f_2097_, 2, v_e_2091_);
lean_closure_set(v___f_2097_, 3, v_toPure_2094_);
v___x_2098_ = lean_apply_4(v_toBind_2093_, lean_box(0), lean_box(0), v_inst_2089_, v___f_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normExpr___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2087_ = stack[0].m_num;
uint8_t v_t_2088_ = stack[1].m_num;
lean_object* v_inst_2089_ = stack[2].m_obj;
lean_object* v_inst_2090_ = stack[3].m_obj;
lean_object* v_e_2091_ = stack[4].m_obj;
lean_object* v_res_2099_;
v_res_2099_ = l_Lean_Compiler_LCNF_normExpr___redArg(v_pu_2087_, v_t_2088_, v_inst_2089_, v_inst_2090_, v_e_2091_);
stack->m_obj
 = v_res_2099_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___redArg___boxed(lean_object* v_pu_2100_, lean_object* v_t_2101_, lean_object* v_inst_2102_, lean_object* v_inst_2103_, lean_object* v_e_2104_){
_start:
{
uint8_t v_pu_boxed_2105_; uint8_t v_t_boxed_2106_; lean_object* v_res_2107_; 
v_pu_boxed_2105_ = lean_unbox(v_pu_2100_);
v_t_boxed_2106_ = lean_unbox(v_t_2101_);
v_res_2107_ = l_Lean_Compiler_LCNF_normExpr___redArg(v_pu_boxed_2105_, v_t_boxed_2106_, v_inst_2102_, v_inst_2103_, v_e_2104_);
return v_res_2107_;
}
}
lean_object* l_Lean_Compiler_LCNF_normExpr(lean_object* v_m_2108_, uint8_t v_pu_2109_, uint8_t v_t_2110_, lean_object* v_inst_2111_, lean_object* v_inst_2112_, lean_object* v_e_2113_){
_start:
{
lean_object* v_toApplicative_2114_; lean_object* v_toBind_2115_; lean_object* v_toPure_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___f_2119_; lean_object* v___x_2120_; 
v_toApplicative_2114_ = lean_ctor_get(v_inst_2112_, 0);
lean_inc_ref(v_toApplicative_2114_);
v_toBind_2115_ = lean_ctor_get(v_inst_2112_, 1);
lean_inc(v_toBind_2115_);
lean_dec_ref(v_inst_2112_);
v_toPure_2116_ = lean_ctor_get(v_toApplicative_2114_, 1);
lean_inc(v_toPure_2116_);
lean_dec_ref(v_toApplicative_2114_);
v___x_2117_ = lean_box(v_pu_2109_);
v___x_2118_ = lean_box(v_t_2110_);
v___f_2119_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2119_, 0, v___x_2117_);
lean_closure_set(v___f_2119_, 1, v___x_2118_);
lean_closure_set(v___f_2119_, 2, v_e_2113_);
lean_closure_set(v___f_2119_, 3, v_toPure_2116_);
v___x_2120_ = lean_apply_4(v_toBind_2115_, lean_box(0), lean_box(0), v_inst_2111_, v___f_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normExpr_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2109_ = stack[1].m_num;
uint8_t v_t_2110_ = stack[2].m_num;
lean_object* v_inst_2111_ = stack[3].m_obj;
lean_object* v_inst_2112_ = stack[4].m_obj;
lean_object* v_e_2113_ = stack[5].m_obj;
lean_object* v_res_2121_;
v_res_2121_ = l_Lean_Compiler_LCNF_normExpr(lean_box(0), v_pu_2109_, v_t_2110_, v_inst_2111_, v_inst_2112_, v_e_2113_);
stack->m_obj
 = v_res_2121_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___boxed(lean_object* v_m_2122_, lean_object* v_pu_2123_, lean_object* v_t_2124_, lean_object* v_inst_2125_, lean_object* v_inst_2126_, lean_object* v_e_2127_){
_start:
{
uint8_t v_pu_boxed_2128_; uint8_t v_t_boxed_2129_; lean_object* v_res_2130_; 
v_pu_boxed_2128_ = lean_unbox(v_pu_2123_);
v_t_boxed_2129_ = lean_unbox(v_t_2124_);
v_res_2130_ = l_Lean_Compiler_LCNF_normExpr(v_m_2122_, v_pu_boxed_2128_, v_t_boxed_2129_, v_inst_2125_, v_inst_2126_, v_e_2127_);
return v_res_2130_;
}
}
lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0(uint8_t v_pu_2131_, lean_object* v_arg_2132_, uint8_t v_t_2133_, lean_object* v_toPure_2134_, lean_object* v_____do__lift_2135_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_2131_, v_____do__lift_2135_, v_arg_2132_, v_t_2133_);
v___x_2137_ = lean_apply_2(v_toPure_2134_, lean_box(0), v___x_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normArg___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2131_ = stack[0].m_num;
lean_object* v_arg_2132_ = stack[1].m_obj;
uint8_t v_t_2133_ = stack[2].m_num;
lean_object* v_toPure_2134_ = stack[3].m_obj;
lean_object* v_____do__lift_2135_ = stack[4].m_obj;
lean_object* v_res_2138_;
v_res_2138_ = l_Lean_Compiler_LCNF_normArg___redArg___lam__0(v_pu_2131_, v_arg_2132_, v_t_2133_, v_toPure_2134_, v_____do__lift_2135_);
stack->m_obj
 = v_res_2138_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(lean_object* v_pu_2139_, lean_object* v_arg_2140_, lean_object* v_t_2141_, lean_object* v_toPure_2142_, lean_object* v_____do__lift_2143_){
_start:
{
uint8_t v_pu_boxed_2144_; uint8_t v_t_boxed_2145_; lean_object* v_res_2146_; 
v_pu_boxed_2144_ = lean_unbox(v_pu_2139_);
v_t_boxed_2145_ = lean_unbox(v_t_2141_);
v_res_2146_ = l_Lean_Compiler_LCNF_normArg___redArg___lam__0(v_pu_boxed_2144_, v_arg_2140_, v_t_boxed_2145_, v_toPure_2142_, v_____do__lift_2143_);
lean_dec_ref(v_____do__lift_2143_);
return v_res_2146_;
}
}
lean_object* l_Lean_Compiler_LCNF_normArg___redArg(uint8_t v_pu_2147_, uint8_t v_t_2148_, lean_object* v_inst_2149_, lean_object* v_inst_2150_, lean_object* v_arg_2151_){
_start:
{
lean_object* v_toApplicative_2152_; lean_object* v_toBind_2153_; lean_object* v_toPure_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___f_2157_; lean_object* v___x_2158_; 
v_toApplicative_2152_ = lean_ctor_get(v_inst_2150_, 0);
lean_inc_ref(v_toApplicative_2152_);
v_toBind_2153_ = lean_ctor_get(v_inst_2150_, 1);
lean_inc(v_toBind_2153_);
lean_dec_ref(v_inst_2150_);
v_toPure_2154_ = lean_ctor_get(v_toApplicative_2152_, 1);
lean_inc(v_toPure_2154_);
lean_dec_ref(v_toApplicative_2152_);
v___x_2155_ = lean_box(v_pu_2147_);
v___x_2156_ = lean_box(v_t_2148_);
v___f_2157_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2157_, 0, v___x_2155_);
lean_closure_set(v___f_2157_, 1, v_arg_2151_);
lean_closure_set(v___f_2157_, 2, v___x_2156_);
lean_closure_set(v___f_2157_, 3, v_toPure_2154_);
v___x_2158_ = lean_apply_4(v_toBind_2153_, lean_box(0), lean_box(0), v_inst_2149_, v___f_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normArg___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2147_ = stack[0].m_num;
uint8_t v_t_2148_ = stack[1].m_num;
lean_object* v_inst_2149_ = stack[2].m_obj;
lean_object* v_inst_2150_ = stack[3].m_obj;
lean_object* v_arg_2151_ = stack[4].m_obj;
lean_object* v_res_2159_;
v_res_2159_ = l_Lean_Compiler_LCNF_normArg___redArg(v_pu_2147_, v_t_2148_, v_inst_2149_, v_inst_2150_, v_arg_2151_);
stack->m_obj
 = v_res_2159_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___redArg___boxed(lean_object* v_pu_2160_, lean_object* v_t_2161_, lean_object* v_inst_2162_, lean_object* v_inst_2163_, lean_object* v_arg_2164_){
_start:
{
uint8_t v_pu_boxed_2165_; uint8_t v_t_boxed_2166_; lean_object* v_res_2167_; 
v_pu_boxed_2165_ = lean_unbox(v_pu_2160_);
v_t_boxed_2166_ = lean_unbox(v_t_2161_);
v_res_2167_ = l_Lean_Compiler_LCNF_normArg___redArg(v_pu_boxed_2165_, v_t_boxed_2166_, v_inst_2162_, v_inst_2163_, v_arg_2164_);
return v_res_2167_;
}
}
lean_object* l_Lean_Compiler_LCNF_normArg(lean_object* v_m_2168_, uint8_t v_pu_2169_, uint8_t v_t_2170_, lean_object* v_inst_2171_, lean_object* v_inst_2172_, lean_object* v_arg_2173_){
_start:
{
lean_object* v_toApplicative_2174_; lean_object* v_toBind_2175_; lean_object* v_toPure_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___f_2179_; lean_object* v___x_2180_; 
v_toApplicative_2174_ = lean_ctor_get(v_inst_2172_, 0);
lean_inc_ref(v_toApplicative_2174_);
v_toBind_2175_ = lean_ctor_get(v_inst_2172_, 1);
lean_inc(v_toBind_2175_);
lean_dec_ref(v_inst_2172_);
v_toPure_2176_ = lean_ctor_get(v_toApplicative_2174_, 1);
lean_inc(v_toPure_2176_);
lean_dec_ref(v_toApplicative_2174_);
v___x_2177_ = lean_box(v_pu_2169_);
v___x_2178_ = lean_box(v_t_2170_);
v___f_2179_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2179_, 0, v___x_2177_);
lean_closure_set(v___f_2179_, 1, v_arg_2173_);
lean_closure_set(v___f_2179_, 2, v___x_2178_);
lean_closure_set(v___f_2179_, 3, v_toPure_2176_);
v___x_2180_ = lean_apply_4(v_toBind_2175_, lean_box(0), lean_box(0), v_inst_2171_, v___f_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2169_ = stack[1].m_num;
uint8_t v_t_2170_ = stack[2].m_num;
lean_object* v_inst_2171_ = stack[3].m_obj;
lean_object* v_inst_2172_ = stack[4].m_obj;
lean_object* v_arg_2173_ = stack[5].m_obj;
lean_object* v_res_2181_;
v_res_2181_ = l_Lean_Compiler_LCNF_normArg(lean_box(0), v_pu_2169_, v_t_2170_, v_inst_2171_, v_inst_2172_, v_arg_2173_);
stack->m_obj
 = v_res_2181_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArg___boxed(lean_object* v_m_2182_, lean_object* v_pu_2183_, lean_object* v_t_2184_, lean_object* v_inst_2185_, lean_object* v_inst_2186_, lean_object* v_arg_2187_){
_start:
{
uint8_t v_pu_boxed_2188_; uint8_t v_t_boxed_2189_; lean_object* v_res_2190_; 
v_pu_boxed_2188_ = lean_unbox(v_pu_2183_);
v_t_boxed_2189_ = lean_unbox(v_t_2184_);
v_res_2190_ = l_Lean_Compiler_LCNF_normArg(v_m_2182_, v_pu_boxed_2188_, v_t_boxed_2189_, v_inst_2185_, v_inst_2186_, v_arg_2187_);
return v_res_2190_;
}
}
lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(uint8_t v_pu_2191_, lean_object* v_e_2192_, uint8_t v_t_2193_, lean_object* v_toPure_2194_, lean_object* v_____do__lift_2195_){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_2191_, v_____do__lift_2195_, v_e_2192_, v_t_2193_);
v___x_2197_ = lean_apply_2(v_toPure_2194_, lean_box(0), v___x_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2191_ = stack[0].m_num;
lean_object* v_e_2192_ = stack[1].m_obj;
uint8_t v_t_2193_ = stack[2].m_num;
lean_object* v_toPure_2194_ = stack[3].m_obj;
lean_object* v_____do__lift_2195_ = stack[4].m_obj;
lean_object* v_res_2198_;
v_res_2198_ = l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(v_pu_2191_, v_e_2192_, v_t_2193_, v_toPure_2194_, v_____do__lift_2195_);
stack->m_obj
 = v_res_2198_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(lean_object* v_pu_2199_, lean_object* v_e_2200_, lean_object* v_t_2201_, lean_object* v_toPure_2202_, lean_object* v_____do__lift_2203_){
_start:
{
uint8_t v_pu_boxed_2204_; uint8_t v_t_boxed_2205_; lean_object* v_res_2206_; 
v_pu_boxed_2204_ = lean_unbox(v_pu_2199_);
v_t_boxed_2205_ = lean_unbox(v_t_2201_);
v_res_2206_ = l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(v_pu_boxed_2204_, v_e_2200_, v_t_boxed_2205_, v_toPure_2202_, v_____do__lift_2203_);
lean_dec_ref(v_____do__lift_2203_);
return v_res_2206_;
}
}
lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg(uint8_t v_pu_2207_, uint8_t v_t_2208_, lean_object* v_inst_2209_, lean_object* v_inst_2210_, lean_object* v_e_2211_){
_start:
{
lean_object* v_toApplicative_2212_; lean_object* v_toBind_2213_; lean_object* v_toPure_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___f_2217_; lean_object* v___x_2218_; 
v_toApplicative_2212_ = lean_ctor_get(v_inst_2210_, 0);
lean_inc_ref(v_toApplicative_2212_);
v_toBind_2213_ = lean_ctor_get(v_inst_2210_, 1);
lean_inc(v_toBind_2213_);
lean_dec_ref(v_inst_2210_);
v_toPure_2214_ = lean_ctor_get(v_toApplicative_2212_, 1);
lean_inc(v_toPure_2214_);
lean_dec_ref(v_toApplicative_2212_);
v___x_2215_ = lean_box(v_pu_2207_);
v___x_2216_ = lean_box(v_t_2208_);
v___f_2217_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2217_, 0, v___x_2215_);
lean_closure_set(v___f_2217_, 1, v_e_2211_);
lean_closure_set(v___f_2217_, 2, v___x_2216_);
lean_closure_set(v___f_2217_, 3, v_toPure_2214_);
v___x_2218_ = lean_apply_4(v_toBind_2213_, lean_box(0), lean_box(0), v_inst_2209_, v___f_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normLetValue___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2207_ = stack[0].m_num;
uint8_t v_t_2208_ = stack[1].m_num;
lean_object* v_inst_2209_ = stack[2].m_obj;
lean_object* v_inst_2210_ = stack[3].m_obj;
lean_object* v_e_2211_ = stack[4].m_obj;
lean_object* v_res_2219_;
v_res_2219_ = l_Lean_Compiler_LCNF_normLetValue___redArg(v_pu_2207_, v_t_2208_, v_inst_2209_, v_inst_2210_, v_e_2211_);
stack->m_obj
 = v_res_2219_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(lean_object* v_pu_2220_, lean_object* v_t_2221_, lean_object* v_inst_2222_, lean_object* v_inst_2223_, lean_object* v_e_2224_){
_start:
{
uint8_t v_pu_boxed_2225_; uint8_t v_t_boxed_2226_; lean_object* v_res_2227_; 
v_pu_boxed_2225_ = lean_unbox(v_pu_2220_);
v_t_boxed_2226_ = lean_unbox(v_t_2221_);
v_res_2227_ = l_Lean_Compiler_LCNF_normLetValue___redArg(v_pu_boxed_2225_, v_t_boxed_2226_, v_inst_2222_, v_inst_2223_, v_e_2224_);
return v_res_2227_;
}
}
lean_object* l_Lean_Compiler_LCNF_normLetValue(lean_object* v_m_2228_, uint8_t v_pu_2229_, uint8_t v_t_2230_, lean_object* v_inst_2231_, lean_object* v_inst_2232_, lean_object* v_e_2233_){
_start:
{
lean_object* v_toApplicative_2234_; lean_object* v_toBind_2235_; lean_object* v_toPure_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___f_2239_; lean_object* v___x_2240_; 
v_toApplicative_2234_ = lean_ctor_get(v_inst_2232_, 0);
lean_inc_ref(v_toApplicative_2234_);
v_toBind_2235_ = lean_ctor_get(v_inst_2232_, 1);
lean_inc(v_toBind_2235_);
lean_dec_ref(v_inst_2232_);
v_toPure_2236_ = lean_ctor_get(v_toApplicative_2234_, 1);
lean_inc(v_toPure_2236_);
lean_dec_ref(v_toApplicative_2234_);
v___x_2237_ = lean_box(v_pu_2229_);
v___x_2238_ = lean_box(v_t_2230_);
v___f_2239_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2239_, 0, v___x_2237_);
lean_closure_set(v___f_2239_, 1, v_e_2233_);
lean_closure_set(v___f_2239_, 2, v___x_2238_);
lean_closure_set(v___f_2239_, 3, v_toPure_2236_);
v___x_2240_ = lean_apply_4(v_toBind_2235_, lean_box(0), lean_box(0), v_inst_2231_, v___f_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normLetValue_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2229_ = stack[1].m_num;
uint8_t v_t_2230_ = stack[2].m_num;
lean_object* v_inst_2231_ = stack[3].m_obj;
lean_object* v_inst_2232_ = stack[4].m_obj;
lean_object* v_e_2233_ = stack[5].m_obj;
lean_object* v_res_2241_;
v_res_2241_ = l_Lean_Compiler_LCNF_normLetValue(lean_box(0), v_pu_2229_, v_t_2230_, v_inst_2231_, v_inst_2232_, v_e_2233_);
stack->m_obj
 = v_res_2241_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetValue___boxed(lean_object* v_m_2242_, lean_object* v_pu_2243_, lean_object* v_t_2244_, lean_object* v_inst_2245_, lean_object* v_inst_2246_, lean_object* v_e_2247_){
_start:
{
uint8_t v_pu_boxed_2248_; uint8_t v_t_boxed_2249_; lean_object* v_res_2250_; 
v_pu_boxed_2248_ = lean_unbox(v_pu_2243_);
v_t_boxed_2249_ = lean_unbox(v_t_2244_);
v_res_2250_ = l_Lean_Compiler_LCNF_normLetValue(v_m_2242_, v_pu_boxed_2248_, v_t_boxed_2249_, v_inst_2245_, v_inst_2246_, v_e_2247_);
return v_res_2250_;
}
}
lean_object* l_Lean_Compiler_LCNF_normExprCore(uint8_t v_pu_2251_, lean_object* v_s_2252_, lean_object* v_e_2253_, uint8_t v_translator_2254_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2251_, v_s_2252_, v_translator_2254_, v_e_2253_);
return v___x_2255_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normExprCore_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2251_ = stack[0].m_num;
lean_object* v_s_2252_ = stack[1].m_obj;
lean_object* v_e_2253_ = stack[2].m_obj;
uint8_t v_translator_2254_ = stack[3].m_num;
lean_object* v_res_2256_;
v_res_2256_ = l_Lean_Compiler_LCNF_normExprCore(v_pu_2251_, v_s_2252_, v_e_2253_, v_translator_2254_);
stack->m_obj
 = v_res_2256_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprCore___boxed(lean_object* v_pu_2257_, lean_object* v_s_2258_, lean_object* v_e_2259_, lean_object* v_translator_2260_){
_start:
{
uint8_t v_pu_boxed_2261_; uint8_t v_translator_boxed_2262_; lean_object* v_res_2263_; 
v_pu_boxed_2261_ = lean_unbox(v_pu_2257_);
v_translator_boxed_2262_ = lean_unbox(v_translator_2260_);
v_res_2263_ = l_Lean_Compiler_LCNF_normExprCore(v_pu_boxed_2261_, v_s_2258_, v_e_2259_, v_translator_boxed_2262_);
lean_dec_ref(v_s_2258_);
return v_res_2263_;
}
}
lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(uint8_t v_pu_2264_, lean_object* v_args_2265_, uint8_t v_t_2266_, lean_object* v_toPure_2267_, lean_object* v_____do__lift_2268_){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_2264_, v_____do__lift_2268_, v_args_2265_, v_t_2266_);
v___x_2270_ = lean_apply_2(v_toPure_2267_, lean_box(0), v___x_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normArgs___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2264_ = stack[0].m_num;
lean_object* v_args_2265_ = stack[1].m_obj;
uint8_t v_t_2266_ = stack[2].m_num;
lean_object* v_toPure_2267_ = stack[3].m_obj;
lean_object* v_____do__lift_2268_ = stack[4].m_obj;
lean_object* v_res_2271_;
v_res_2271_ = l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(v_pu_2264_, v_args_2265_, v_t_2266_, v_toPure_2267_, v_____do__lift_2268_);
stack->m_obj
 = v_res_2271_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(lean_object* v_pu_2272_, lean_object* v_args_2273_, lean_object* v_t_2274_, lean_object* v_toPure_2275_, lean_object* v_____do__lift_2276_){
_start:
{
uint8_t v_pu_boxed_2277_; uint8_t v_t_boxed_2278_; lean_object* v_res_2279_; 
v_pu_boxed_2277_ = lean_unbox(v_pu_2272_);
v_t_boxed_2278_ = lean_unbox(v_t_2274_);
v_res_2279_ = l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(v_pu_boxed_2277_, v_args_2273_, v_t_boxed_2278_, v_toPure_2275_, v_____do__lift_2276_);
lean_dec_ref(v_____do__lift_2276_);
return v_res_2279_;
}
}
lean_object* l_Lean_Compiler_LCNF_normArgs___redArg(uint8_t v_pu_2280_, uint8_t v_t_2281_, lean_object* v_inst_2282_, lean_object* v_inst_2283_, lean_object* v_args_2284_){
_start:
{
lean_object* v_toApplicative_2285_; lean_object* v_toBind_2286_; lean_object* v_toPure_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___f_2290_; lean_object* v___x_2291_; 
v_toApplicative_2285_ = lean_ctor_get(v_inst_2283_, 0);
lean_inc_ref(v_toApplicative_2285_);
v_toBind_2286_ = lean_ctor_get(v_inst_2283_, 1);
lean_inc(v_toBind_2286_);
lean_dec_ref(v_inst_2283_);
v_toPure_2287_ = lean_ctor_get(v_toApplicative_2285_, 1);
lean_inc(v_toPure_2287_);
lean_dec_ref(v_toApplicative_2285_);
v___x_2288_ = lean_box(v_pu_2280_);
v___x_2289_ = lean_box(v_t_2281_);
v___f_2290_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2290_, 0, v___x_2288_);
lean_closure_set(v___f_2290_, 1, v_args_2284_);
lean_closure_set(v___f_2290_, 2, v___x_2289_);
lean_closure_set(v___f_2290_, 3, v_toPure_2287_);
v___x_2291_ = lean_apply_4(v_toBind_2286_, lean_box(0), lean_box(0), v_inst_2282_, v___f_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normArgs___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2280_ = stack[0].m_num;
uint8_t v_t_2281_ = stack[1].m_num;
lean_object* v_inst_2282_ = stack[2].m_obj;
lean_object* v_inst_2283_ = stack[3].m_obj;
lean_object* v_args_2284_ = stack[4].m_obj;
lean_object* v_res_2292_;
v_res_2292_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_2280_, v_t_2281_, v_inst_2282_, v_inst_2283_, v_args_2284_);
stack->m_obj
 = v_res_2292_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___redArg___boxed(lean_object* v_pu_2293_, lean_object* v_t_2294_, lean_object* v_inst_2295_, lean_object* v_inst_2296_, lean_object* v_args_2297_){
_start:
{
uint8_t v_pu_boxed_2298_; uint8_t v_t_boxed_2299_; lean_object* v_res_2300_; 
v_pu_boxed_2298_ = lean_unbox(v_pu_2293_);
v_t_boxed_2299_ = lean_unbox(v_t_2294_);
v_res_2300_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_boxed_2298_, v_t_boxed_2299_, v_inst_2295_, v_inst_2296_, v_args_2297_);
return v_res_2300_;
}
}
lean_object* l_Lean_Compiler_LCNF_normArgs(lean_object* v_m_2301_, uint8_t v_pu_2302_, uint8_t v_t_2303_, lean_object* v_inst_2304_, lean_object* v_inst_2305_, lean_object* v_args_2306_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_Compiler_LCNF_normArgs___redArg(v_pu_2302_, v_t_2303_, v_inst_2304_, v_inst_2305_, v_args_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normArgs_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2302_ = stack[1].m_num;
uint8_t v_t_2303_ = stack[2].m_num;
lean_object* v_inst_2304_ = stack[3].m_obj;
lean_object* v_inst_2305_ = stack[4].m_obj;
lean_object* v_args_2306_ = stack[5].m_obj;
lean_object* v_res_2308_;
v_res_2308_ = l_Lean_Compiler_LCNF_normArgs(lean_box(0), v_pu_2302_, v_t_2303_, v_inst_2304_, v_inst_2305_, v_args_2306_);
stack->m_obj
 = v_res_2308_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___boxed(lean_object* v_m_2309_, lean_object* v_pu_2310_, lean_object* v_t_2311_, lean_object* v_inst_2312_, lean_object* v_inst_2313_, lean_object* v_args_2314_){
_start:
{
uint8_t v_pu_boxed_2315_; uint8_t v_t_boxed_2316_; lean_object* v_res_2317_; 
v_pu_boxed_2315_ = lean_unbox(v_pu_2310_);
v_t_boxed_2316_ = lean_unbox(v_t_2311_);
v_res_2317_ = l_Lean_Compiler_LCNF_normArgs(v_m_2309_, v_pu_boxed_2315_, v_t_boxed_2316_, v_inst_2312_, v_inst_2313_, v_args_2314_);
return v_res_2317_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object* v_binderName_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v___x_2321_; lean_object* v_nextIdx_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v_lctx_2325_; lean_object* v_nextIdx_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2337_; 
v___x_2321_ = lean_st_ref_get(v_a_2319_);
v_nextIdx_2322_ = lean_ctor_get(v___x_2321_, 1);
lean_inc(v_nextIdx_2322_);
lean_dec(v___x_2321_);
v___x_2323_ = l_Lean_Name_num___override(v_binderName_2318_, v_nextIdx_2322_);
v___x_2324_ = lean_st_ref_take(v_a_2319_);
v_lctx_2325_ = lean_ctor_get(v___x_2324_, 0);
v_nextIdx_2326_ = lean_ctor_get(v___x_2324_, 1);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2328_ = v___x_2324_;
v_isShared_2329_ = v_isSharedCheck_2337_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_nextIdx_2326_);
lean_inc(v_lctx_2325_);
lean_dec(v___x_2324_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2337_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2330_ = lean_unsigned_to_nat(1u);
v___x_2331_ = lean_nat_add(v_nextIdx_2326_, v___x_2330_);
lean_dec(v_nextIdx_2326_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 1, v___x_2331_);
v___x_2333_ = v___x_2328_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_lctx_2325_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = lean_st_ref_put(v_a_2319_, v___x_2333_);
v___x_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2323_);
return v___x_2335_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkFreshBinderName___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderName_2318_ = stack[0].m_obj;
lean_object* v_a_2319_ = stack[1].m_obj;
lean_object* v_res_2338_;
v_res_2338_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2318_, v_a_2319_);
stack->m_obj
 = v_res_2338_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(lean_object* v_binderName_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2339_, v_a_2340_);
lean_dec(v_a_2340_);
return v_res_2342_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object* v_binderName_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_2343_, v_a_2345_);
return v___x_2349_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkFreshBinderName_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderName_2343_ = stack[0].m_obj;
lean_object* v_a_2344_ = stack[1].m_obj;
lean_object* v_a_2345_ = stack[2].m_obj;
lean_object* v_a_2346_ = stack[3].m_obj;
lean_object* v_a_2347_ = stack[4].m_obj;
lean_object* v_res_2350_;
v_res_2350_ = l_Lean_Compiler_LCNF_mkFreshBinderName(v_binderName_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
stack->m_obj
 = v_res_2350_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(lean_object* v_binderName_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lean_Compiler_LCNF_mkFreshBinderName(v_binderName_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
return v_res_2357_;
}
}
lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(lean_object* v_binderName_2358_, lean_object* v_baseName_2359_, lean_object* v_a_2360_){
_start:
{
uint8_t v___x_2362_; 
v___x_2362_ = l_Lean_Name_isAnonymous(v_binderName_2358_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; 
lean_dec(v_baseName_2359_);
v___x_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2363_, 0, v_binderName_2358_);
return v___x_2363_;
}
else
{
lean_object* v___x_2364_; 
lean_dec(v_binderName_2358_);
v___x_2364_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_baseName_2359_, v_a_2360_);
return v___x_2364_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderName_2358_ = stack[0].m_obj;
lean_object* v_baseName_2359_ = stack[1].m_obj;
lean_object* v_a_2360_ = stack[2].m_obj;
lean_object* v_res_2365_;
v_res_2365_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2358_, v_baseName_2359_, v_a_2360_);
stack->m_obj
 = v_res_2365_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(lean_object* v_binderName_2366_, lean_object* v_baseName_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2366_, v_baseName_2367_, v_a_2368_);
lean_dec(v_a_2368_);
return v_res_2370_;
}
}
lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous(lean_object* v_binderName_2371_, lean_object* v_baseName_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2371_, v_baseName_2372_, v_a_2374_);
return v___x_2378_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ensureNotAnonymous_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderName_2371_ = stack[0].m_obj;
lean_object* v_baseName_2372_ = stack[1].m_obj;
lean_object* v_a_2373_ = stack[2].m_obj;
lean_object* v_a_2374_ = stack[3].m_obj;
lean_object* v_a_2375_ = stack[4].m_obj;
lean_object* v_a_2376_ = stack[5].m_obj;
lean_object* v_res_2379_;
v_res_2379_ = l_Lean_Compiler_LCNF_ensureNotAnonymous(v_binderName_2371_, v_baseName_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
stack->m_obj
 = v_res_2379_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(lean_object* v_binderName_2380_, lean_object* v_baseName_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Lean_Compiler_LCNF_ensureNotAnonymous(v_binderName_2380_, v_baseName_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
return v_res_2387_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(lean_object* v___y_2388_){
_start:
{
lean_object* v___x_2390_; lean_object* v_ngen_2391_; lean_object* v_namePrefix_2392_; lean_object* v_idx_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2423_; 
v___x_2390_ = lean_st_ref_get(v___y_2388_);
v_ngen_2391_ = lean_ctor_get(v___x_2390_, 2);
lean_inc_ref(v_ngen_2391_);
lean_dec(v___x_2390_);
v_namePrefix_2392_ = lean_ctor_get(v_ngen_2391_, 0);
v_idx_2393_ = lean_ctor_get(v_ngen_2391_, 1);
v_isSharedCheck_2423_ = !lean_is_exclusive(v_ngen_2391_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2395_ = v_ngen_2391_;
v_isShared_2396_ = v_isSharedCheck_2423_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_idx_2393_);
lean_inc(v_namePrefix_2392_);
lean_dec(v_ngen_2391_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2423_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v_r_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2401_; 
lean_inc(v_idx_2393_);
lean_inc(v_namePrefix_2392_);
v_r_2397_ = l_Lean_Name_num___override(v_namePrefix_2392_, v_idx_2393_);
v___x_2398_ = lean_unsigned_to_nat(1u);
v___x_2399_ = lean_nat_add(v_idx_2393_, v___x_2398_);
lean_dec(v_idx_2393_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 1, v___x_2399_);
v___x_2401_ = v___x_2395_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_namePrefix_2392_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v___x_2399_);
v___x_2401_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
lean_object* v___x_2402_; lean_object* v_env_2403_; lean_object* v_nextMacroScope_2404_; lean_object* v_auxDeclNGen_2405_; lean_object* v_traceState_2406_; lean_object* v_cache_2407_; lean_object* v_recordedDeps_2408_; lean_object* v_messages_2409_; lean_object* v_infoState_2410_; lean_object* v_snapshotTasks_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2420_; 
v___x_2402_ = lean_st_ref_take(v___y_2388_);
v_env_2403_ = lean_ctor_get(v___x_2402_, 0);
v_nextMacroScope_2404_ = lean_ctor_get(v___x_2402_, 1);
v_auxDeclNGen_2405_ = lean_ctor_get(v___x_2402_, 3);
v_traceState_2406_ = lean_ctor_get(v___x_2402_, 4);
v_cache_2407_ = lean_ctor_get(v___x_2402_, 5);
v_recordedDeps_2408_ = lean_ctor_get(v___x_2402_, 6);
v_messages_2409_ = lean_ctor_get(v___x_2402_, 7);
v_infoState_2410_ = lean_ctor_get(v___x_2402_, 8);
v_snapshotTasks_2411_ = lean_ctor_get(v___x_2402_, 9);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2420_ == 0)
{
lean_object* v_unused_2421_; 
v_unused_2421_ = lean_ctor_get(v___x_2402_, 2);
lean_dec(v_unused_2421_);
v___x_2413_ = v___x_2402_;
v_isShared_2414_ = v_isSharedCheck_2420_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_snapshotTasks_2411_);
lean_inc(v_infoState_2410_);
lean_inc(v_messages_2409_);
lean_inc(v_recordedDeps_2408_);
lean_inc(v_cache_2407_);
lean_inc(v_traceState_2406_);
lean_inc(v_auxDeclNGen_2405_);
lean_inc(v_nextMacroScope_2404_);
lean_inc(v_env_2403_);
lean_dec(v___x_2402_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2420_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 2, v___x_2401_);
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_env_2403_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_nextMacroScope_2404_);
lean_ctor_set(v_reuseFailAlloc_2419_, 2, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2419_, 3, v_auxDeclNGen_2405_);
lean_ctor_set(v_reuseFailAlloc_2419_, 4, v_traceState_2406_);
lean_ctor_set(v_reuseFailAlloc_2419_, 5, v_cache_2407_);
lean_ctor_set(v_reuseFailAlloc_2419_, 6, v_recordedDeps_2408_);
lean_ctor_set(v_reuseFailAlloc_2419_, 7, v_messages_2409_);
lean_ctor_set(v_reuseFailAlloc_2419_, 8, v_infoState_2410_);
lean_ctor_set(v_reuseFailAlloc_2419_, 9, v_snapshotTasks_2411_);
v___x_2416_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = lean_st_ref_put(v___y_2388_, v___x_2416_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v_r_2397_);
return v___x_2418_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2388_ = stack[0].m_obj;
lean_object* v_res_2424_;
v_res_2424_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2388_);
stack->m_obj
 = v_res_2424_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2425_);
lean_dec(v___y_2425_);
return v_res_2427_;
}
}
lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v___x_2433_; lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
v___x_2433_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2431_);
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2433_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2433_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2428_ = stack[0].m_obj;
lean_object* v___y_2429_ = stack[1].m_obj;
lean_object* v___y_2430_ = stack[2].m_obj;
lean_object* v___y_2431_ = stack[3].m_obj;
lean_object* v_res_2442_;
v_res_2442_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
stack->m_obj
 = v_res_2442_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
return v_res_2448_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t v_pu_2452_, lean_object* v_binderName_2453_, lean_object* v_type_2454_, uint8_t v_borrow_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2485_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_a_2462_);
lean_dec_ref_known(v___x_2461_, 1);
v___x_2463_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_2464_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2453_, v___x_2463_, v_a_2457_);
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2467_ = v___x_2464_;
v_isShared_2468_ = v_isSharedCheck_2485_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2464_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2485_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v_lctx_2471_; lean_object* v_nextIdx_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2484_; 
v___x_2469_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2469_, 0, v_a_2462_);
lean_ctor_set(v___x_2469_, 1, v_a_2465_);
lean_ctor_set(v___x_2469_, 2, v_type_2454_);
lean_ctor_set_uint8(v___x_2469_, sizeof(void*)*3, v_borrow_2455_);
v___x_2470_ = lean_st_ref_take(v_a_2457_);
v_lctx_2471_ = lean_ctor_get(v___x_2470_, 0);
v_nextIdx_2472_ = lean_ctor_get(v___x_2470_, 1);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2474_ = v___x_2470_;
v_isShared_2475_ = v_isSharedCheck_2484_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_nextIdx_2472_);
lean_inc(v_lctx_2471_);
lean_dec(v___x_2470_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2484_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2476_; lean_object* v___x_2478_; 
lean_inc_ref(v___x_2469_);
v___x_2476_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2452_, v_lctx_2471_, v___x_2469_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v___x_2476_);
v___x_2478_ = v___x_2474_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2476_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_nextIdx_2472_);
v___x_2478_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2479_ = lean_st_ref_put(v_a_2457_, v___x_2478_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v___x_2469_);
v___x_2481_ = v___x_2467_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2469_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec_ref(v_type_2454_);
lean_dec(v_binderName_2453_);
v_a_2486_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2461_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2461_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkParam_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2452_ = stack[0].m_num;
lean_object* v_binderName_2453_ = stack[1].m_obj;
lean_object* v_type_2454_ = stack[2].m_obj;
uint8_t v_borrow_2455_ = stack[3].m_num;
lean_object* v_a_2456_ = stack[4].m_obj;
lean_object* v_a_2457_ = stack[5].m_obj;
lean_object* v_a_2458_ = stack[6].m_obj;
lean_object* v_a_2459_ = stack[7].m_obj;
lean_object* v_res_2494_;
v_res_2494_ = l_Lean_Compiler_LCNF_mkParam(v_pu_2452_, v_binderName_2453_, v_type_2454_, v_borrow_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
stack->m_obj
 = v_res_2494_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkParam___boxed(lean_object* v_pu_2495_, lean_object* v_binderName_2496_, lean_object* v_type_2497_, lean_object* v_borrow_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
uint8_t v_pu_boxed_2504_; uint8_t v_borrow_boxed_2505_; lean_object* v_res_2506_; 
v_pu_boxed_2504_ = lean_unbox(v_pu_2495_);
v_borrow_boxed_2505_ = lean_unbox(v_borrow_2498_);
v_res_2506_ = l_Lean_Compiler_LCNF_mkParam(v_pu_boxed_2504_, v_binderName_2496_, v_type_2497_, v_borrow_boxed_2505_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_a_2500_);
lean_dec_ref(v_a_2499_);
return v_res_2506_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_2510_);
return v___x_2512_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2507_ = stack[0].m_obj;
lean_object* v___y_2508_ = stack[1].m_obj;
lean_object* v___y_2509_ = stack[2].m_obj;
lean_object* v___y_2510_ = stack[3].m_obj;
lean_object* v_res_2513_;
v_res_2513_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
stack->m_obj
 = v_res_2513_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
return v_res_2519_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t v_pu_2523_, lean_object* v_binderName_2524_, lean_object* v_type_2525_, lean_object* v_value_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2556_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2532_, 1);
v___x_2534_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2535_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2524_, v___x_2534_, v_a_2528_);
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2538_ = v___x_2535_;
v_isShared_2539_ = v_isSharedCheck_2556_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2535_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2556_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v_lctx_2542_; lean_object* v_nextIdx_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2555_; 
v___x_2540_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2540_, 0, v_a_2533_);
lean_ctor_set(v___x_2540_, 1, v_a_2536_);
lean_ctor_set(v___x_2540_, 2, v_type_2525_);
lean_ctor_set(v___x_2540_, 3, v_value_2526_);
v___x_2541_ = lean_st_ref_take(v_a_2528_);
v_lctx_2542_ = lean_ctor_get(v___x_2541_, 0);
v_nextIdx_2543_ = lean_ctor_get(v___x_2541_, 1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2545_ = v___x_2541_;
v_isShared_2546_ = v_isSharedCheck_2555_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_nextIdx_2543_);
lean_inc(v_lctx_2542_);
lean_dec(v___x_2541_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2555_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; lean_object* v___x_2549_; 
lean_inc_ref(v___x_2540_);
v___x_2547_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2523_, v_lctx_2542_, v___x_2540_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2547_);
v___x_2549_ = v___x_2545_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_nextIdx_2543_);
v___x_2549_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2550_; lean_object* v___x_2552_; 
v___x_2550_ = lean_st_ref_put(v_a_2528_, v___x_2549_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 0, v___x_2540_);
v___x_2552_ = v___x_2538_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2540_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_dec(v_value_2526_);
lean_dec_ref(v_type_2525_);
lean_dec(v_binderName_2524_);
v_a_2557_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2532_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2532_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkLetDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2523_ = stack[0].m_num;
lean_object* v_binderName_2524_ = stack[1].m_obj;
lean_object* v_type_2525_ = stack[2].m_obj;
lean_object* v_value_2526_ = stack[3].m_obj;
lean_object* v_a_2527_ = stack[4].m_obj;
lean_object* v_a_2528_ = stack[5].m_obj;
lean_object* v_a_2529_ = stack[6].m_obj;
lean_object* v_a_2530_ = stack[7].m_obj;
lean_object* v_res_2565_;
v_res_2565_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2523_, v_binderName_2524_, v_type_2525_, v_value_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_);
stack->m_obj
 = v_res_2565_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDecl___boxed(lean_object* v_pu_2566_, lean_object* v_binderName_2567_, lean_object* v_type_2568_, lean_object* v_value_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_){
_start:
{
uint8_t v_pu_boxed_2575_; lean_object* v_res_2576_; 
v_pu_boxed_2575_ = lean_unbox(v_pu_2566_);
v_res_2576_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_boxed_2575_, v_binderName_2567_, v_type_2568_, v_value_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
return v_res_2576_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t v_pu_2580_, lean_object* v_binderName_2581_, lean_object* v_type_2582_, lean_object* v_params_2583_, lean_object* v_value_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2614_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___x_2590_, 1);
v___x_2592_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFunDecl___closed__1));
v___x_2593_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(v_binderName_2581_, v___x_2592_, v_a_2586_);
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2614_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2614_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v_lctx_2600_; lean_object* v_nextIdx_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2613_; 
v___x_2598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2598_, 0, v_a_2591_);
lean_ctor_set(v___x_2598_, 1, v_a_2594_);
lean_ctor_set(v___x_2598_, 2, v_params_2583_);
lean_ctor_set(v___x_2598_, 3, v_type_2582_);
lean_ctor_set(v___x_2598_, 4, v_value_2584_);
v___x_2599_ = lean_st_ref_take(v_a_2586_);
v_lctx_2600_ = lean_ctor_get(v___x_2599_, 0);
v_nextIdx_2601_ = lean_ctor_get(v___x_2599_, 1);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2603_ = v___x_2599_;
v_isShared_2604_ = v_isSharedCheck_2613_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_nextIdx_2601_);
lean_inc(v_lctx_2600_);
lean_dec(v___x_2599_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2613_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v___x_2607_; 
lean_inc_ref(v___x_2598_);
v___x_2605_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2580_, v_lctx_2600_, v___x_2598_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2605_);
v___x_2607_ = v___x_2603_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2605_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_nextIdx_2601_);
v___x_2607_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2608_; lean_object* v___x_2610_; 
v___x_2608_ = lean_st_ref_put(v_a_2586_, v___x_2607_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v___x_2598_);
v___x_2610_ = v___x_2596_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2598_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec_ref(v_value_2584_);
lean_dec_ref(v_params_2583_);
lean_dec_ref(v_type_2582_);
lean_dec(v_binderName_2581_);
v_a_2615_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2590_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2590_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkFunDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2580_ = stack[0].m_num;
lean_object* v_binderName_2581_ = stack[1].m_obj;
lean_object* v_type_2582_ = stack[2].m_obj;
lean_object* v_params_2583_ = stack[3].m_obj;
lean_object* v_value_2584_ = stack[4].m_obj;
lean_object* v_a_2585_ = stack[5].m_obj;
lean_object* v_a_2586_ = stack[6].m_obj;
lean_object* v_a_2587_ = stack[7].m_obj;
lean_object* v_a_2588_ = stack[8].m_obj;
lean_object* v_res_2623_;
v_res_2623_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_2580_, v_binderName_2581_, v_type_2582_, v_params_2583_, v_value_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
stack->m_obj
 = v_res_2623_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFunDecl___boxed(lean_object* v_pu_2624_, lean_object* v_binderName_2625_, lean_object* v_type_2626_, lean_object* v_params_2627_, lean_object* v_value_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
uint8_t v_pu_boxed_2634_; lean_object* v_res_2635_; 
v_pu_boxed_2634_ = lean_unbox(v_pu_2624_);
v_res_2635_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_boxed_2634_, v_binderName_2625_, v_type_2626_, v_params_2627_, v_value_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
return v_res_2635_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t v_pu_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v_a_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2642_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkLetDecl___closed__1));
v___x_2643_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2642_, v_a_2638_);
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref(v___x_2643_);
v___x_2645_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2646_ = lean_box(1);
v___x_2647_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2636_, v_a_2644_, v___x_2645_, v___x_2646_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
return v___x_2647_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkLetDeclErased_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2636_ = stack[0].m_num;
lean_object* v_a_2637_ = stack[1].m_obj;
lean_object* v_a_2638_ = stack[2].m_obj;
lean_object* v_a_2639_ = stack[3].m_obj;
lean_object* v_a_2640_ = stack[4].m_obj;
lean_object* v_res_2648_;
v_res_2648_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
stack->m_obj
 = v_res_2648_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(lean_object* v_pu_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_){
_start:
{
uint8_t v_pu_boxed_2655_; lean_object* v_res_2656_; 
v_pu_boxed_2655_ = lean_unbox(v_pu_2649_);
v_res_2656_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_boxed_2655_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec(v_a_2651_);
lean_dec_ref(v_a_2650_);
return v_res_2656_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t v_pu_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v_pu_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2674_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2666_ = v___x_2663_;
v_isShared_2667_ = v_isSharedCheck_2674_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2663_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2674_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v_fvarId_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
v_fvarId_2668_ = lean_ctor_get(v_a_2664_, 0);
lean_inc(v_fvarId_2668_);
v___x_2669_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2669_, 0, v_fvarId_2668_);
v___x_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2670_, 0, v_a_2664_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2670_);
v___x_2672_ = v___x_2666_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
v_a_2675_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2663_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2663_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkReturnErased_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2657_ = stack[0].m_num;
lean_object* v_a_2658_ = stack[1].m_obj;
lean_object* v_a_2659_ = stack[2].m_obj;
lean_object* v_a_2660_ = stack[3].m_obj;
lean_object* v_a_2661_ = stack[4].m_obj;
lean_object* v_res_2683_;
v_res_2683_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
stack->m_obj
 = v_res_2683_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkReturnErased___boxed(lean_object* v_pu_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
uint8_t v_pu_boxed_2690_; lean_object* v_res_2691_; 
v_pu_boxed_2690_ = lean_unbox(v_pu_2684_);
v_res_2691_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_boxed_2690_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
return v_res_2691_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t v_pu_2692_, lean_object* v_p_2693_, lean_object* v_type_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v_fvarId_2697_; lean_object* v_binderName_2698_; lean_object* v_type_2699_; uint8_t v_borrow_2700_; size_t v___x_2701_; size_t v___x_2702_; uint8_t v___x_2703_; 
v_fvarId_2697_ = lean_ctor_get(v_p_2693_, 0);
v_binderName_2698_ = lean_ctor_get(v_p_2693_, 1);
v_type_2699_ = lean_ctor_get(v_p_2693_, 2);
v_borrow_2700_ = lean_ctor_get_uint8(v_p_2693_, sizeof(void*)*3);
v___x_2701_ = lean_ptr_addr(v_type_2694_);
v___x_2702_ = lean_ptr_addr(v_type_2699_);
v___x_2703_ = lean_usize_dec_eq(v___x_2701_, v___x_2702_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2723_; 
lean_inc(v_binderName_2698_);
lean_inc(v_fvarId_2697_);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_p_2693_);
if (v_isSharedCheck_2723_ == 0)
{
lean_object* v_unused_2724_; lean_object* v_unused_2725_; lean_object* v_unused_2726_; 
v_unused_2724_ = lean_ctor_get(v_p_2693_, 2);
lean_dec(v_unused_2724_);
v_unused_2725_ = lean_ctor_get(v_p_2693_, 1);
lean_dec(v_unused_2725_);
v_unused_2726_ = lean_ctor_get(v_p_2693_, 0);
lean_dec(v_unused_2726_);
v___x_2705_ = v_p_2693_;
v_isShared_2706_ = v_isSharedCheck_2723_;
goto v_resetjp_2704_;
}
else
{
lean_dec(v_p_2693_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2723_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v_p_2708_; 
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 2, v_type_2694_);
v_p_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_fvarId_2697_);
lean_ctor_set(v_reuseFailAlloc_2722_, 1, v_binderName_2698_);
lean_ctor_set(v_reuseFailAlloc_2722_, 2, v_type_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, sizeof(void*)*3, v_borrow_2700_);
v_p_2708_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2709_; lean_object* v_lctx_2710_; lean_object* v_nextIdx_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2721_; 
v___x_2709_ = lean_st_ref_take(v_a_2695_);
v_lctx_2710_ = lean_ctor_get(v___x_2709_, 0);
v_nextIdx_2711_ = lean_ctor_get(v___x_2709_, 1);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2713_ = v___x_2709_;
v_isShared_2714_ = v_isSharedCheck_2721_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_nextIdx_2711_);
lean_inc(v_lctx_2710_);
lean_dec(v___x_2709_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2721_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2715_; lean_object* v___x_2717_; 
lean_inc_ref(v_p_2708_);
v___x_2715_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2692_, v_lctx_2710_, v_p_2708_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v___x_2715_);
v___x_2717_ = v___x_2713_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2715_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v_nextIdx_2711_);
v___x_2717_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = lean_st_ref_put(v_a_2695_, v___x_2717_);
v___x_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2719_, 0, v_p_2708_);
return v___x_2719_;
}
}
}
}
}
else
{
lean_object* v___x_2727_; 
lean_dec_ref(v_type_2694_);
v___x_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2727_, 0, v_p_2693_);
return v___x_2727_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2692_ = stack[0].m_num;
lean_object* v_p_2693_ = stack[1].m_obj;
lean_object* v_type_2694_ = stack[2].m_obj;
lean_object* v_a_2695_ = stack[3].m_obj;
lean_object* v_res_2728_;
v_res_2728_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_2692_, v_p_2693_, v_type_2694_, v_a_2695_);
stack->m_obj
 = v_res_2728_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(lean_object* v_pu_2729_, lean_object* v_p_2730_, lean_object* v_type_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_){
_start:
{
uint8_t v_pu_boxed_2734_; lean_object* v_res_2735_; 
v_pu_boxed_2734_ = lean_unbox(v_pu_2729_);
v_res_2735_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_boxed_2734_, v_p_2730_, v_type_2731_, v_a_2732_);
lean_dec(v_a_2732_);
return v_res_2735_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(uint8_t v_pu_2736_, lean_object* v_p_2737_, lean_object* v_type_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_2736_, v_p_2737_, v_type_2738_, v_a_2740_);
return v___x_2744_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2736_ = stack[0].m_num;
lean_object* v_p_2737_ = stack[1].m_obj;
lean_object* v_type_2738_ = stack[2].m_obj;
lean_object* v_a_2739_ = stack[3].m_obj;
lean_object* v_a_2740_ = stack[4].m_obj;
lean_object* v_a_2741_ = stack[5].m_obj;
lean_object* v_a_2742_ = stack[6].m_obj;
lean_object* v_res_2745_;
v_res_2745_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(v_pu_2736_, v_p_2737_, v_type_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
stack->m_obj
 = v_res_2745_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(lean_object* v_pu_2746_, lean_object* v_p_2747_, lean_object* v_type_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
uint8_t v_pu_boxed_2754_; lean_object* v_res_2755_; 
v_pu_boxed_2754_ = lean_unbox(v_pu_2746_);
v_res_2755_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(v_pu_boxed_2754_, v_p_2747_, v_type_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
return v_res_2755_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t v_pu_2756_, lean_object* v_p_2757_, uint8_t v_borrow_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v_fvarId_2761_; lean_object* v_binderName_2762_; lean_object* v_type_2763_; uint8_t v_borrow_2764_; 
v_fvarId_2761_ = lean_ctor_get(v_p_2757_, 0);
v_binderName_2762_ = lean_ctor_get(v_p_2757_, 1);
v_type_2763_ = lean_ctor_get(v_p_2757_, 2);
v_borrow_2764_ = lean_ctor_get_uint8(v_p_2757_, sizeof(void*)*3);
if (v_borrow_2764_ == 0)
{
if (v_borrow_2758_ == 0)
{
lean_object* v___x_2780_; 
v___x_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2780_, 0, v_p_2757_);
return v___x_2780_;
}
else
{
lean_inc_ref(v_type_2763_);
lean_inc(v_binderName_2762_);
lean_inc(v_fvarId_2761_);
lean_dec_ref(v_p_2757_);
goto v___jp_2765_;
}
}
else
{
if (v_borrow_2758_ == 0)
{
lean_inc_ref(v_type_2763_);
lean_inc(v_binderName_2762_);
lean_inc(v_fvarId_2761_);
lean_dec_ref(v_p_2757_);
goto v___jp_2765_;
}
else
{
lean_object* v___x_2781_; 
v___x_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2781_, 0, v_p_2757_);
return v___x_2781_;
}
}
v___jp_2765_:
{
lean_object* v_p_2766_; lean_object* v___x_2767_; lean_object* v_lctx_2768_; lean_object* v_nextIdx_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2779_; 
v_p_2766_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_p_2766_, 0, v_fvarId_2761_);
lean_ctor_set(v_p_2766_, 1, v_binderName_2762_);
lean_ctor_set(v_p_2766_, 2, v_type_2763_);
lean_ctor_set_uint8(v_p_2766_, sizeof(void*)*3, v_borrow_2758_);
v___x_2767_ = lean_st_ref_take(v_a_2759_);
v_lctx_2768_ = lean_ctor_get(v___x_2767_, 0);
v_nextIdx_2769_ = lean_ctor_get(v___x_2767_, 1);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2771_ = v___x_2767_;
v_isShared_2772_ = v_isSharedCheck_2779_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_nextIdx_2769_);
lean_inc(v_lctx_2768_);
lean_dec(v___x_2767_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2779_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; lean_object* v___x_2775_; 
lean_inc_ref(v_p_2766_);
v___x_2773_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_2756_, v_lctx_2768_, v_p_2766_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2773_);
v___x_2775_ = v___x_2771_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2773_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_nextIdx_2769_);
v___x_2775_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = lean_st_ref_put(v_a_2759_, v___x_2775_);
v___x_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2777_, 0, v_p_2766_);
return v___x_2777_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2756_ = stack[0].m_num;
lean_object* v_p_2757_ = stack[1].m_obj;
uint8_t v_borrow_2758_ = stack[2].m_num;
lean_object* v_a_2759_ = stack[3].m_obj;
lean_object* v_res_2782_;
v_res_2782_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_2756_, v_p_2757_, v_borrow_2758_, v_a_2759_);
stack->m_obj
 = v_res_2782_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(lean_object* v_pu_2783_, lean_object* v_p_2784_, lean_object* v_borrow_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_){
_start:
{
uint8_t v_pu_boxed_2788_; uint8_t v_borrow_boxed_2789_; lean_object* v_res_2790_; 
v_pu_boxed_2788_ = lean_unbox(v_pu_2783_);
v_borrow_boxed_2789_ = lean_unbox(v_borrow_2785_);
v_res_2790_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_boxed_2788_, v_p_2784_, v_borrow_boxed_2789_, v_a_2786_);
lean_dec(v_a_2786_);
return v_res_2790_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(uint8_t v_pu_2791_, lean_object* v_p_2792_, uint8_t v_borrow_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_2791_, v_p_2792_, v_borrow_2793_, v_a_2795_);
return v___x_2799_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2791_ = stack[0].m_num;
lean_object* v_p_2792_ = stack[1].m_obj;
uint8_t v_borrow_2793_ = stack[2].m_num;
lean_object* v_a_2794_ = stack[3].m_obj;
lean_object* v_a_2795_ = stack[4].m_obj;
lean_object* v_a_2796_ = stack[5].m_obj;
lean_object* v_a_2797_ = stack[6].m_obj;
lean_object* v_res_2800_;
v_res_2800_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(v_pu_2791_, v_p_2792_, v_borrow_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
stack->m_obj
 = v_res_2800_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(lean_object* v_pu_2801_, lean_object* v_p_2802_, lean_object* v_borrow_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
uint8_t v_pu_boxed_2809_; uint8_t v_borrow_boxed_2810_; lean_object* v_res_2811_; 
v_pu_boxed_2809_ = lean_unbox(v_pu_2801_);
v_borrow_boxed_2810_ = lean_unbox(v_borrow_2803_);
v_res_2811_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(v_pu_boxed_2809_, v_p_2802_, v_borrow_boxed_2810_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
return v_res_2811_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t v_pu_2812_, lean_object* v_decl_2813_, lean_object* v_type_2814_, lean_object* v_value_2815_, lean_object* v_a_2816_){
_start:
{
lean_object* v_fvarId_2818_; lean_object* v_binderName_2819_; lean_object* v_type_2820_; lean_object* v_value_2821_; size_t v___x_2837_; size_t v___x_2838_; uint8_t v___x_2839_; 
v_fvarId_2818_ = lean_ctor_get(v_decl_2813_, 0);
v_binderName_2819_ = lean_ctor_get(v_decl_2813_, 1);
v_type_2820_ = lean_ctor_get(v_decl_2813_, 2);
v_value_2821_ = lean_ctor_get(v_decl_2813_, 3);
v___x_2837_ = lean_ptr_addr(v_type_2814_);
v___x_2838_ = lean_ptr_addr(v_type_2820_);
v___x_2839_ = lean_usize_dec_eq(v___x_2837_, v___x_2838_);
if (v___x_2839_ == 0)
{
lean_inc(v_binderName_2819_);
lean_inc(v_fvarId_2818_);
lean_dec_ref(v_decl_2813_);
goto v___jp_2822_;
}
else
{
size_t v___x_2840_; size_t v___x_2841_; uint8_t v___x_2842_; 
v___x_2840_ = lean_ptr_addr(v_value_2815_);
v___x_2841_ = lean_ptr_addr(v_value_2821_);
v___x_2842_ = lean_usize_dec_eq(v___x_2840_, v___x_2841_);
if (v___x_2842_ == 0)
{
lean_inc(v_binderName_2819_);
lean_inc(v_fvarId_2818_);
lean_dec_ref(v_decl_2813_);
goto v___jp_2822_;
}
else
{
lean_object* v___x_2843_; 
lean_dec(v_value_2815_);
lean_dec_ref(v_type_2814_);
v___x_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2843_, 0, v_decl_2813_);
return v___x_2843_;
}
}
v___jp_2822_:
{
lean_object* v_decl_2823_; lean_object* v___x_2824_; lean_object* v_lctx_2825_; lean_object* v_nextIdx_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2836_; 
v_decl_2823_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_decl_2823_, 0, v_fvarId_2818_);
lean_ctor_set(v_decl_2823_, 1, v_binderName_2819_);
lean_ctor_set(v_decl_2823_, 2, v_type_2814_);
lean_ctor_set(v_decl_2823_, 3, v_value_2815_);
v___x_2824_ = lean_st_ref_take(v_a_2816_);
v_lctx_2825_ = lean_ctor_get(v___x_2824_, 0);
v_nextIdx_2826_ = lean_ctor_get(v___x_2824_, 1);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2828_ = v___x_2824_;
v_isShared_2829_ = v_isSharedCheck_2836_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_nextIdx_2826_);
lean_inc(v_lctx_2825_);
lean_dec(v___x_2824_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2836_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2830_; lean_object* v___x_2832_; 
lean_inc_ref(v_decl_2823_);
v___x_2830_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_2812_, v_lctx_2825_, v_decl_2823_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v___x_2830_);
v___x_2832_ = v___x_2828_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2830_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_nextIdx_2826_);
v___x_2832_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_st_ref_put(v_a_2816_, v___x_2832_);
v___x_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2834_, 0, v_decl_2823_);
return v___x_2834_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2812_ = stack[0].m_num;
lean_object* v_decl_2813_ = stack[1].m_obj;
lean_object* v_type_2814_ = stack[2].m_obj;
lean_object* v_value_2815_ = stack[3].m_obj;
lean_object* v_a_2816_ = stack[4].m_obj;
lean_object* v_res_2844_;
v_res_2844_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2812_, v_decl_2813_, v_type_2814_, v_value_2815_, v_a_2816_);
stack->m_obj
 = v_res_2844_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(lean_object* v_pu_2845_, lean_object* v_decl_2846_, lean_object* v_type_2847_, lean_object* v_value_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
uint8_t v_pu_boxed_2851_; lean_object* v_res_2852_; 
v_pu_boxed_2851_ = lean_unbox(v_pu_2845_);
v_res_2852_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_boxed_2851_, v_decl_2846_, v_type_2847_, v_value_2848_, v_a_2849_);
lean_dec(v_a_2849_);
return v_res_2852_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(uint8_t v_pu_2853_, lean_object* v_decl_2854_, lean_object* v_type_2855_, lean_object* v_value_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2853_, v_decl_2854_, v_type_2855_, v_value_2856_, v_a_2858_);
return v___x_2862_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2853_ = stack[0].m_num;
lean_object* v_decl_2854_ = stack[1].m_obj;
lean_object* v_type_2855_ = stack[2].m_obj;
lean_object* v_value_2856_ = stack[3].m_obj;
lean_object* v_a_2857_ = stack[4].m_obj;
lean_object* v_a_2858_ = stack[5].m_obj;
lean_object* v_a_2859_ = stack[6].m_obj;
lean_object* v_a_2860_ = stack[7].m_obj;
lean_object* v_res_2863_;
v_res_2863_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(v_pu_2853_, v_decl_2854_, v_type_2855_, v_value_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
stack->m_obj
 = v_res_2863_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(lean_object* v_pu_2864_, lean_object* v_decl_2865_, lean_object* v_type_2866_, lean_object* v_value_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
uint8_t v_pu_boxed_2873_; lean_object* v_res_2874_; 
v_pu_boxed_2873_ = lean_unbox(v_pu_2864_);
v_res_2874_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(v_pu_boxed_2873_, v_decl_2865_, v_type_2866_, v_value_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
lean_dec(v_a_2871_);
lean_dec_ref(v_a_2870_);
lean_dec(v_a_2869_);
lean_dec_ref(v_a_2868_);
return v_res_2874_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t v_pu_2875_, lean_object* v_decl_2876_, lean_object* v_value_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v_type_2880_; lean_object* v___x_2881_; 
v_type_2880_ = lean_ctor_get(v_decl_2876_, 2);
lean_inc_ref(v_type_2880_);
v___x_2881_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_2875_, v_decl_2876_, v_type_2880_, v_value_2877_, v_a_2878_);
return v___x_2881_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2875_ = stack[0].m_num;
lean_object* v_decl_2876_ = stack[1].m_obj;
lean_object* v_value_2877_ = stack[2].m_obj;
lean_object* v_a_2878_ = stack[3].m_obj;
lean_object* v_res_2882_;
v_res_2882_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_2875_, v_decl_2876_, v_value_2877_, v_a_2878_);
stack->m_obj
 = v_res_2882_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(lean_object* v_pu_2883_, lean_object* v_decl_2884_, lean_object* v_value_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_){
_start:
{
uint8_t v_pu_boxed_2888_; lean_object* v_res_2889_; 
v_pu_boxed_2888_ = lean_unbox(v_pu_2883_);
v_res_2889_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_boxed_2888_, v_decl_2884_, v_value_2885_, v_a_2886_);
lean_dec(v_a_2886_);
return v_res_2889_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(uint8_t v_pu_2890_, lean_object* v_decl_2891_, lean_object* v_value_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v_pu_2890_, v_decl_2891_, v_value_2892_, v_a_2894_);
return v___x_2898_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetDecl_updateValue_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2890_ = stack[0].m_num;
lean_object* v_decl_2891_ = stack[1].m_obj;
lean_object* v_value_2892_ = stack[2].m_obj;
lean_object* v_a_2893_ = stack[3].m_obj;
lean_object* v_a_2894_ = stack[4].m_obj;
lean_object* v_a_2895_ = stack[5].m_obj;
lean_object* v_a_2896_ = stack[6].m_obj;
lean_object* v_res_2899_;
v_res_2899_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(v_pu_2890_, v_decl_2891_, v_value_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
stack->m_obj
 = v_res_2899_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(lean_object* v_pu_2900_, lean_object* v_decl_2901_, lean_object* v_value_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
uint8_t v_pu_boxed_2908_; lean_object* v_res_2909_; 
v_pu_boxed_2908_ = lean_unbox(v_pu_2900_);
v_res_2909_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(v_pu_boxed_2908_, v_decl_2901_, v_value_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
return v_res_2909_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t v_pu_2910_, lean_object* v_decl_2911_, lean_object* v_type_2912_, lean_object* v_params_2913_, lean_object* v_value_2914_, lean_object* v_a_2915_){
_start:
{
lean_object* v_fvarId_2917_; lean_object* v_binderName_2918_; lean_object* v_params_2919_; lean_object* v_type_2920_; lean_object* v_value_2921_; size_t v___x_2937_; size_t v___x_2938_; uint8_t v___x_2939_; 
v_fvarId_2917_ = lean_ctor_get(v_decl_2911_, 0);
v_binderName_2918_ = lean_ctor_get(v_decl_2911_, 1);
v_params_2919_ = lean_ctor_get(v_decl_2911_, 2);
v_type_2920_ = lean_ctor_get(v_decl_2911_, 3);
v_value_2921_ = lean_ctor_get(v_decl_2911_, 4);
v___x_2937_ = lean_ptr_addr(v_type_2912_);
v___x_2938_ = lean_ptr_addr(v_type_2920_);
v___x_2939_ = lean_usize_dec_eq(v___x_2937_, v___x_2938_);
if (v___x_2939_ == 0)
{
lean_inc(v_binderName_2918_);
lean_inc(v_fvarId_2917_);
lean_dec_ref(v_decl_2911_);
goto v___jp_2922_;
}
else
{
size_t v___x_2940_; size_t v___x_2941_; uint8_t v___x_2942_; 
v___x_2940_ = lean_ptr_addr(v_params_2913_);
v___x_2941_ = lean_ptr_addr(v_params_2919_);
v___x_2942_ = lean_usize_dec_eq(v___x_2940_, v___x_2941_);
if (v___x_2942_ == 0)
{
lean_inc(v_binderName_2918_);
lean_inc(v_fvarId_2917_);
lean_dec_ref(v_decl_2911_);
goto v___jp_2922_;
}
else
{
size_t v___x_2943_; size_t v___x_2944_; uint8_t v___x_2945_; 
v___x_2943_ = lean_ptr_addr(v_value_2914_);
v___x_2944_ = lean_ptr_addr(v_value_2921_);
v___x_2945_ = lean_usize_dec_eq(v___x_2943_, v___x_2944_);
if (v___x_2945_ == 0)
{
lean_inc(v_binderName_2918_);
lean_inc(v_fvarId_2917_);
lean_dec_ref(v_decl_2911_);
goto v___jp_2922_;
}
else
{
lean_object* v___x_2946_; 
lean_dec_ref(v_value_2914_);
lean_dec_ref(v_params_2913_);
lean_dec_ref(v_type_2912_);
v___x_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2946_, 0, v_decl_2911_);
return v___x_2946_;
}
}
}
v___jp_2922_:
{
lean_object* v_decl_2923_; lean_object* v___x_2924_; lean_object* v_lctx_2925_; lean_object* v_nextIdx_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2936_; 
v_decl_2923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_decl_2923_, 0, v_fvarId_2917_);
lean_ctor_set(v_decl_2923_, 1, v_binderName_2918_);
lean_ctor_set(v_decl_2923_, 2, v_params_2913_);
lean_ctor_set(v_decl_2923_, 3, v_type_2912_);
lean_ctor_set(v_decl_2923_, 4, v_value_2914_);
v___x_2924_ = lean_st_ref_take(v_a_2915_);
v_lctx_2925_ = lean_ctor_get(v___x_2924_, 0);
v_nextIdx_2926_ = lean_ctor_get(v___x_2924_, 1);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2928_ = v___x_2924_;
v_isShared_2929_ = v_isSharedCheck_2936_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_nextIdx_2926_);
lean_inc(v_lctx_2925_);
lean_dec(v___x_2924_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2936_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2930_; lean_object* v___x_2932_; 
lean_inc_ref(v_decl_2923_);
v___x_2930_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_2910_, v_lctx_2925_, v_decl_2923_);
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 0, v___x_2930_);
v___x_2932_ = v___x_2928_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v_nextIdx_2926_);
v___x_2932_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = lean_st_ref_put(v_a_2915_, v___x_2932_);
v___x_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2934_, 0, v_decl_2923_);
return v___x_2934_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2910_ = stack[0].m_num;
lean_object* v_decl_2911_ = stack[1].m_obj;
lean_object* v_type_2912_ = stack[2].m_obj;
lean_object* v_params_2913_ = stack[3].m_obj;
lean_object* v_value_2914_ = stack[4].m_obj;
lean_object* v_a_2915_ = stack[5].m_obj;
lean_object* v_res_2947_;
v_res_2947_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2910_, v_decl_2911_, v_type_2912_, v_params_2913_, v_value_2914_, v_a_2915_);
stack->m_obj
 = v_res_2947_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(lean_object* v_pu_2948_, lean_object* v_decl_2949_, lean_object* v_type_2950_, lean_object* v_params_2951_, lean_object* v_value_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
uint8_t v_pu_boxed_2955_; lean_object* v_res_2956_; 
v_pu_boxed_2955_ = lean_unbox(v_pu_2948_);
v_res_2956_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_boxed_2955_, v_decl_2949_, v_type_2950_, v_params_2951_, v_value_2952_, v_a_2953_);
lean_dec(v_a_2953_);
return v_res_2956_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(uint8_t v_pu_2957_, lean_object* v_decl_2958_, lean_object* v_type_2959_, lean_object* v_params_2960_, lean_object* v_value_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2957_, v_decl_2958_, v_type_2959_, v_params_2960_, v_value_2961_, v_a_2963_);
return v___x_2967_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2957_ = stack[0].m_num;
lean_object* v_decl_2958_ = stack[1].m_obj;
lean_object* v_type_2959_ = stack[2].m_obj;
lean_object* v_params_2960_ = stack[3].m_obj;
lean_object* v_value_2961_ = stack[4].m_obj;
lean_object* v_a_2962_ = stack[5].m_obj;
lean_object* v_a_2963_ = stack[6].m_obj;
lean_object* v_a_2964_ = stack[7].m_obj;
lean_object* v_a_2965_ = stack[8].m_obj;
lean_object* v_res_2968_;
v_res_2968_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(v_pu_2957_, v_decl_2958_, v_type_2959_, v_params_2960_, v_value_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
stack->m_obj
 = v_res_2968_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(lean_object* v_pu_2969_, lean_object* v_decl_2970_, lean_object* v_type_2971_, lean_object* v_params_2972_, lean_object* v_value_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_){
_start:
{
uint8_t v_pu_boxed_2979_; lean_object* v_res_2980_; 
v_pu_boxed_2979_ = lean_unbox(v_pu_2969_);
v_res_2980_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(v_pu_boxed_2979_, v_decl_2970_, v_type_2971_, v_params_2972_, v_value_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_);
lean_dec(v_a_2977_);
lean_dec_ref(v_a_2976_);
lean_dec(v_a_2975_);
lean_dec_ref(v_a_2974_);
return v_res_2980_;
}
}
lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(uint8_t v_pu_2981_, lean_object* v_decl_2982_, lean_object* v_type_2983_, lean_object* v_value_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v_params_2987_; lean_object* v___x_2988_; 
v_params_2987_ = lean_ctor_get(v_decl_2982_, 2);
lean_inc_ref(v_params_2987_);
v___x_2988_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2981_, v_decl_2982_, v_type_2983_, v_params_2987_, v_value_2984_, v_a_2985_);
return v___x_2988_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2981_ = stack[0].m_num;
lean_object* v_decl_2982_ = stack[1].m_obj;
lean_object* v_type_2983_ = stack[2].m_obj;
lean_object* v_value_2984_ = stack[3].m_obj;
lean_object* v_a_2985_ = stack[4].m_obj;
lean_object* v_res_2989_;
v_res_2989_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(v_pu_2981_, v_decl_2982_, v_type_2983_, v_value_2984_, v_a_2985_);
stack->m_obj
 = v_res_2989_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(lean_object* v_pu_2990_, lean_object* v_decl_2991_, lean_object* v_type_2992_, lean_object* v_value_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
uint8_t v_pu_boxed_2996_; lean_object* v_res_2997_; 
v_pu_boxed_2996_ = lean_unbox(v_pu_2990_);
v_res_2997_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(v_pu_boxed_2996_, v_decl_2991_, v_type_2992_, v_value_2993_, v_a_2994_);
lean_dec(v_a_2994_);
return v_res_2997_;
}
}
lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27(uint8_t v_pu_2998_, lean_object* v_decl_2999_, lean_object* v_type_3000_, lean_object* v_value_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v_params_3007_; lean_object* v___x_3008_; 
v_params_3007_ = lean_ctor_get(v_decl_2999_, 2);
lean_inc_ref(v_params_3007_);
v___x_3008_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2998_, v_decl_2999_, v_type_3000_, v_params_3007_, v_value_3001_, v_a_3003_);
return v___x_3008_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_update_x27_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2998_ = stack[0].m_num;
lean_object* v_decl_2999_ = stack[1].m_obj;
lean_object* v_type_3000_ = stack[2].m_obj;
lean_object* v_value_3001_ = stack[3].m_obj;
lean_object* v_a_3002_ = stack[4].m_obj;
lean_object* v_a_3003_ = stack[5].m_obj;
lean_object* v_a_3004_ = stack[6].m_obj;
lean_object* v_a_3005_ = stack[7].m_obj;
lean_object* v_res_3009_;
v_res_3009_ = l_Lean_Compiler_LCNF_FunDecl_update_x27(v_pu_2998_, v_decl_2999_, v_type_3000_, v_value_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
stack->m_obj
 = v_res_3009_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(lean_object* v_pu_3010_, lean_object* v_decl_3011_, lean_object* v_type_3012_, lean_object* v_value_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_){
_start:
{
uint8_t v_pu_boxed_3019_; lean_object* v_res_3020_; 
v_pu_boxed_3019_ = lean_unbox(v_pu_3010_);
v_res_3020_ = l_Lean_Compiler_LCNF_FunDecl_update_x27(v_pu_boxed_3019_, v_decl_3011_, v_type_3012_, v_value_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
lean_dec(v_a_3017_);
lean_dec_ref(v_a_3016_);
lean_dec(v_a_3015_);
lean_dec_ref(v_a_3014_);
return v_res_3020_;
}
}
lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(uint8_t v_pu_3021_, lean_object* v_decl_3022_, lean_object* v_value_3023_, lean_object* v_a_3024_){
_start:
{
lean_object* v_params_3026_; lean_object* v_type_3027_; lean_object* v___x_3028_; 
v_params_3026_ = lean_ctor_get(v_decl_3022_, 2);
lean_inc_ref(v_params_3026_);
v_type_3027_ = lean_ctor_get(v_decl_3022_, 3);
lean_inc_ref(v_type_3027_);
v___x_3028_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_3021_, v_decl_3022_, v_type_3027_, v_params_3026_, v_value_3023_, v_a_3024_);
return v___x_3028_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3021_ = stack[0].m_num;
lean_object* v_decl_3022_ = stack[1].m_obj;
lean_object* v_value_3023_ = stack[2].m_obj;
lean_object* v_a_3024_ = stack[3].m_obj;
lean_object* v_res_3029_;
v_res_3029_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(v_pu_3021_, v_decl_3022_, v_value_3023_, v_a_3024_);
stack->m_obj
 = v_res_3029_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(lean_object* v_pu_3030_, lean_object* v_decl_3031_, lean_object* v_value_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_){
_start:
{
uint8_t v_pu_boxed_3035_; lean_object* v_res_3036_; 
v_pu_boxed_3035_ = lean_unbox(v_pu_3030_);
v_res_3036_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(v_pu_boxed_3035_, v_decl_3031_, v_value_3032_, v_a_3033_);
lean_dec(v_a_3033_);
return v_res_3036_;
}
}
lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue(uint8_t v_pu_3037_, lean_object* v_decl_3038_, lean_object* v_value_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v_params_3045_; lean_object* v_type_3046_; lean_object* v___x_3047_; 
v_params_3045_ = lean_ctor_get(v_decl_3038_, 2);
lean_inc_ref(v_params_3045_);
v_type_3046_ = lean_ctor_get(v_decl_3038_, 3);
lean_inc_ref(v_type_3046_);
v___x_3047_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_3037_, v_decl_3038_, v_type_3046_, v_params_3045_, v_value_3039_, v_a_3041_);
return v___x_3047_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_updateValue_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3037_ = stack[0].m_num;
lean_object* v_decl_3038_ = stack[1].m_obj;
lean_object* v_value_3039_ = stack[2].m_obj;
lean_object* v_a_3040_ = stack[3].m_obj;
lean_object* v_a_3041_ = stack[4].m_obj;
lean_object* v_a_3042_ = stack[5].m_obj;
lean_object* v_a_3043_ = stack[6].m_obj;
lean_object* v_res_3048_;
v_res_3048_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(v_pu_3037_, v_decl_3038_, v_value_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
stack->m_obj
 = v_res_3048_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(lean_object* v_pu_3049_, lean_object* v_decl_3050_, lean_object* v_value_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
uint8_t v_pu_boxed_3057_; lean_object* v_res_3058_; 
v_pu_boxed_3057_ = lean_unbox(v_pu_3049_);
v_res_3058_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(v_pu_boxed_3057_, v_decl_3050_, v_value_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
return v_res_3058_;
}
}
lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0(uint8_t v_pu_3059_, lean_object* v_p_3060_, lean_object* v_inst_3061_, lean_object* v_____do__lift_3062_){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3063_ = lean_box(v_pu_3059_);
v___x_3064_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed), 8, 3);
lean_closure_set(v___x_3064_, 0, v___x_3063_);
lean_closure_set(v___x_3064_, 1, v_p_3060_);
lean_closure_set(v___x_3064_, 2, v_____do__lift_3062_);
v___x_3065_ = lean_apply_2(v_inst_3061_, lean_box(0), v___x_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normParam___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3059_ = stack[0].m_num;
lean_object* v_p_3060_ = stack[1].m_obj;
lean_object* v_inst_3061_ = stack[2].m_obj;
lean_object* v_____do__lift_3062_ = stack[3].m_obj;
lean_object* v_res_3066_;
v_res_3066_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__0(v_pu_3059_, v_p_3060_, v_inst_3061_, v_____do__lift_3062_);
stack->m_obj
 = v_res_3066_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(lean_object* v_pu_3067_, lean_object* v_p_3068_, lean_object* v_inst_3069_, lean_object* v_____do__lift_3070_){
_start:
{
uint8_t v_pu_boxed_3071_; lean_object* v_res_3072_; 
v_pu_boxed_3071_ = lean_unbox(v_pu_3067_);
v_res_3072_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__0(v_pu_boxed_3071_, v_p_3068_, v_inst_3069_, v_____do__lift_3070_);
return v_res_3072_;
}
}
lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1(uint8_t v_pu_3073_, uint8_t v_t_3074_, lean_object* v_type_3075_, lean_object* v_toPure_3076_, lean_object* v_____do__lift_3077_){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3073_, v_____do__lift_3077_, v_t_3074_, v_type_3075_);
v___x_3079_ = lean_apply_2(v_toPure_3076_, lean_box(0), v___x_3078_);
return v___x_3079_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normParam___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3073_ = stack[0].m_num;
uint8_t v_t_3074_ = stack[1].m_num;
lean_object* v_type_3075_ = stack[2].m_obj;
lean_object* v_toPure_3076_ = stack[3].m_obj;
lean_object* v_____do__lift_3077_ = stack[4].m_obj;
lean_object* v_res_3080_;
v_res_3080_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(v_pu_3073_, v_t_3074_, v_type_3075_, v_toPure_3076_, v_____do__lift_3077_);
stack->m_obj
 = v_res_3080_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(lean_object* v_pu_3081_, lean_object* v_t_3082_, lean_object* v_type_3083_, lean_object* v_toPure_3084_, lean_object* v_____do__lift_3085_){
_start:
{
uint8_t v_pu_boxed_3086_; uint8_t v_t_boxed_3087_; lean_object* v_res_3088_; 
v_pu_boxed_3086_ = lean_unbox(v_pu_3081_);
v_t_boxed_3087_ = lean_unbox(v_t_3082_);
v_res_3088_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(v_pu_boxed_3086_, v_t_boxed_3087_, v_type_3083_, v_toPure_3084_, v_____do__lift_3085_);
lean_dec_ref(v_____do__lift_3085_);
return v_res_3088_;
}
}
lean_object* l_Lean_Compiler_LCNF_normParam___redArg(uint8_t v_pu_3089_, uint8_t v_t_3090_, lean_object* v_inst_3091_, lean_object* v_inst_3092_, lean_object* v_inst_3093_, lean_object* v_p_3094_){
_start:
{
lean_object* v_toApplicative_3095_; lean_object* v_toBind_3096_; lean_object* v_type_3097_; lean_object* v_toPure_3098_; lean_object* v___x_3099_; lean_object* v___f_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___f_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v_toApplicative_3095_ = lean_ctor_get(v_inst_3092_, 0);
lean_inc_ref(v_toApplicative_3095_);
v_toBind_3096_ = lean_ctor_get(v_inst_3092_, 1);
lean_inc_n(v_toBind_3096_, 2);
lean_dec_ref(v_inst_3092_);
v_type_3097_ = lean_ctor_get(v_p_3094_, 2);
lean_inc_ref(v_type_3097_);
v_toPure_3098_ = lean_ctor_get(v_toApplicative_3095_, 1);
lean_inc(v_toPure_3098_);
lean_dec_ref(v_toApplicative_3095_);
v___x_3099_ = lean_box(v_pu_3089_);
v___f_3100_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3100_, 0, v___x_3099_);
lean_closure_set(v___f_3100_, 1, v_p_3094_);
lean_closure_set(v___f_3100_, 2, v_inst_3091_);
v___x_3101_ = lean_box(v_pu_3089_);
v___x_3102_ = lean_box(v_t_3090_);
v___f_3103_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3103_, 0, v___x_3101_);
lean_closure_set(v___f_3103_, 1, v___x_3102_);
lean_closure_set(v___f_3103_, 2, v_type_3097_);
lean_closure_set(v___f_3103_, 3, v_toPure_3098_);
v___x_3104_ = lean_apply_4(v_toBind_3096_, lean_box(0), lean_box(0), v_inst_3093_, v___f_3103_);
v___x_3105_ = lean_apply_4(v_toBind_3096_, lean_box(0), lean_box(0), v___x_3104_, v___f_3100_);
return v___x_3105_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normParam___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3089_ = stack[0].m_num;
uint8_t v_t_3090_ = stack[1].m_num;
lean_object* v_inst_3091_ = stack[2].m_obj;
lean_object* v_inst_3092_ = stack[3].m_obj;
lean_object* v_inst_3093_ = stack[4].m_obj;
lean_object* v_p_3094_ = stack[5].m_obj;
lean_object* v_res_3106_;
v_res_3106_ = l_Lean_Compiler_LCNF_normParam___redArg(v_pu_3089_, v_t_3090_, v_inst_3091_, v_inst_3092_, v_inst_3093_, v_p_3094_);
stack->m_obj
 = v_res_3106_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___redArg___boxed(lean_object* v_pu_3107_, lean_object* v_t_3108_, lean_object* v_inst_3109_, lean_object* v_inst_3110_, lean_object* v_inst_3111_, lean_object* v_p_3112_){
_start:
{
uint8_t v_pu_boxed_3113_; uint8_t v_t_boxed_3114_; lean_object* v_res_3115_; 
v_pu_boxed_3113_ = lean_unbox(v_pu_3107_);
v_t_boxed_3114_ = lean_unbox(v_t_3108_);
v_res_3115_ = l_Lean_Compiler_LCNF_normParam___redArg(v_pu_boxed_3113_, v_t_boxed_3114_, v_inst_3109_, v_inst_3110_, v_inst_3111_, v_p_3112_);
return v_res_3115_;
}
}
lean_object* l_Lean_Compiler_LCNF_normParam(lean_object* v_m_3116_, uint8_t v_pu_3117_, uint8_t v_t_3118_, lean_object* v_inst_3119_, lean_object* v_inst_3120_, lean_object* v_inst_3121_, lean_object* v_p_3122_){
_start:
{
lean_object* v_toApplicative_3123_; lean_object* v_toBind_3124_; lean_object* v_type_3125_; lean_object* v_toPure_3126_; lean_object* v___x_3127_; lean_object* v___f_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___f_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v_toApplicative_3123_ = lean_ctor_get(v_inst_3120_, 0);
lean_inc_ref(v_toApplicative_3123_);
v_toBind_3124_ = lean_ctor_get(v_inst_3120_, 1);
lean_inc_n(v_toBind_3124_, 2);
lean_dec_ref(v_inst_3120_);
v_type_3125_ = lean_ctor_get(v_p_3122_, 2);
lean_inc_ref(v_type_3125_);
v_toPure_3126_ = lean_ctor_get(v_toApplicative_3123_, 1);
lean_inc(v_toPure_3126_);
lean_dec_ref(v_toApplicative_3123_);
v___x_3127_ = lean_box(v_pu_3117_);
v___f_3128_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3128_, 0, v___x_3127_);
lean_closure_set(v___f_3128_, 1, v_p_3122_);
lean_closure_set(v___f_3128_, 2, v_inst_3119_);
v___x_3129_ = lean_box(v_pu_3117_);
v___x_3130_ = lean_box(v_t_3118_);
v___f_3131_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3131_, 0, v___x_3129_);
lean_closure_set(v___f_3131_, 1, v___x_3130_);
lean_closure_set(v___f_3131_, 2, v_type_3125_);
lean_closure_set(v___f_3131_, 3, v_toPure_3126_);
v___x_3132_ = lean_apply_4(v_toBind_3124_, lean_box(0), lean_box(0), v_inst_3121_, v___f_3131_);
v___x_3133_ = lean_apply_4(v_toBind_3124_, lean_box(0), lean_box(0), v___x_3132_, v___f_3128_);
return v___x_3133_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normParam_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3117_ = stack[1].m_num;
uint8_t v_t_3118_ = stack[2].m_num;
lean_object* v_inst_3119_ = stack[3].m_obj;
lean_object* v_inst_3120_ = stack[4].m_obj;
lean_object* v_inst_3121_ = stack[5].m_obj;
lean_object* v_p_3122_ = stack[6].m_obj;
lean_object* v_res_3134_;
v_res_3134_ = l_Lean_Compiler_LCNF_normParam(lean_box(0), v_pu_3117_, v_t_3118_, v_inst_3119_, v_inst_3120_, v_inst_3121_, v_p_3122_);
stack->m_obj
 = v_res_3134_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___boxed(lean_object* v_m_3135_, lean_object* v_pu_3136_, lean_object* v_t_3137_, lean_object* v_inst_3138_, lean_object* v_inst_3139_, lean_object* v_inst_3140_, lean_object* v_p_3141_){
_start:
{
uint8_t v_pu_boxed_3142_; uint8_t v_t_boxed_3143_; lean_object* v_res_3144_; 
v_pu_boxed_3142_ = lean_unbox(v_pu_3136_);
v_t_boxed_3143_ = lean_unbox(v_t_3137_);
v_res_3144_ = l_Lean_Compiler_LCNF_normParam(v_m_3135_, v_pu_boxed_3142_, v_t_boxed_3143_, v_inst_3138_, v_inst_3139_, v_inst_3140_, v_p_3141_);
return v_res_3144_;
}
}
lean_object* l_Lean_Compiler_LCNF_normParams___redArg(uint8_t v_pu_3145_, uint8_t v_t_3146_, lean_object* v_inst_3147_, lean_object* v_inst_3148_, lean_object* v_inst_3149_, lean_object* v_ps_3150_){
_start:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3151_ = lean_box(v_pu_3145_);
v___x_3152_ = lean_box(v_t_3146_);
lean_inc_ref(v_inst_3148_);
v___x_3153_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___boxed), 7, 6);
lean_closure_set(v___x_3153_, 0, lean_box(0));
lean_closure_set(v___x_3153_, 1, v___x_3151_);
lean_closure_set(v___x_3153_, 2, v___x_3152_);
lean_closure_set(v___x_3153_, 3, v_inst_3147_);
lean_closure_set(v___x_3153_, 4, v_inst_3148_);
lean_closure_set(v___x_3153_, 5, v_inst_3149_);
v___x_3154_ = lean_unsigned_to_nat(0u);
v___x_3155_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_box(0), lean_box(0), v_inst_3148_, v___x_3153_, v___x_3154_, v_ps_3150_);
return v___x_3155_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normParams___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3145_ = stack[0].m_num;
uint8_t v_t_3146_ = stack[1].m_num;
lean_object* v_inst_3147_ = stack[2].m_obj;
lean_object* v_inst_3148_ = stack[3].m_obj;
lean_object* v_inst_3149_ = stack[4].m_obj;
lean_object* v_ps_3150_ = stack[5].m_obj;
lean_object* v_res_3156_;
v_res_3156_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_3145_, v_t_3146_, v_inst_3147_, v_inst_3148_, v_inst_3149_, v_ps_3150_);
stack->m_obj
 = v_res_3156_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___redArg___boxed(lean_object* v_pu_3157_, lean_object* v_t_3158_, lean_object* v_inst_3159_, lean_object* v_inst_3160_, lean_object* v_inst_3161_, lean_object* v_ps_3162_){
_start:
{
uint8_t v_pu_boxed_3163_; uint8_t v_t_boxed_3164_; lean_object* v_res_3165_; 
v_pu_boxed_3163_ = lean_unbox(v_pu_3157_);
v_t_boxed_3164_ = lean_unbox(v_t_3158_);
v_res_3165_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_boxed_3163_, v_t_boxed_3164_, v_inst_3159_, v_inst_3160_, v_inst_3161_, v_ps_3162_);
return v_res_3165_;
}
}
lean_object* l_Lean_Compiler_LCNF_normParams(lean_object* v_m_3166_, uint8_t v_pu_3167_, uint8_t v_t_3168_, lean_object* v_inst_3169_, lean_object* v_inst_3170_, lean_object* v_inst_3171_, lean_object* v_ps_3172_){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = l_Lean_Compiler_LCNF_normParams___redArg(v_pu_3167_, v_t_3168_, v_inst_3169_, v_inst_3170_, v_inst_3171_, v_ps_3172_);
return v___x_3173_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normParams_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3167_ = stack[1].m_num;
uint8_t v_t_3168_ = stack[2].m_num;
lean_object* v_inst_3169_ = stack[3].m_obj;
lean_object* v_inst_3170_ = stack[4].m_obj;
lean_object* v_inst_3171_ = stack[5].m_obj;
lean_object* v_ps_3172_ = stack[6].m_obj;
lean_object* v_res_3174_;
v_res_3174_ = l_Lean_Compiler_LCNF_normParams(lean_box(0), v_pu_3167_, v_t_3168_, v_inst_3169_, v_inst_3170_, v_inst_3171_, v_ps_3172_);
stack->m_obj
 = v_res_3174_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___boxed(lean_object* v_m_3175_, lean_object* v_pu_3176_, lean_object* v_t_3177_, lean_object* v_inst_3178_, lean_object* v_inst_3179_, lean_object* v_inst_3180_, lean_object* v_ps_3181_){
_start:
{
uint8_t v_pu_boxed_3182_; uint8_t v_t_boxed_3183_; lean_object* v_res_3184_; 
v_pu_boxed_3182_ = lean_unbox(v_pu_3176_);
v_t_boxed_3183_ = lean_unbox(v_t_3177_);
v_res_3184_ = l_Lean_Compiler_LCNF_normParams(v_m_3175_, v_pu_boxed_3182_, v_t_boxed_3183_, v_inst_3178_, v_inst_3179_, v_inst_3180_, v_ps_3181_);
return v_res_3184_;
}
}
lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(uint8_t v_pu_3185_, lean_object* v_decl_3186_, lean_object* v_____do__lift_3187_, lean_object* v_inst_3188_, lean_object* v_____do__lift_3189_){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3190_ = lean_box(v_pu_3185_);
v___x_3191_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed), 9, 4);
lean_closure_set(v___x_3191_, 0, v___x_3190_);
lean_closure_set(v___x_3191_, 1, v_decl_3186_);
lean_closure_set(v___x_3191_, 2, v_____do__lift_3187_);
lean_closure_set(v___x_3191_, 3, v_____do__lift_3189_);
v___x_3192_ = lean_apply_2(v_inst_3188_, lean_box(0), v___x_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3185_ = stack[0].m_num;
lean_object* v_decl_3186_ = stack[1].m_obj;
lean_object* v_____do__lift_3187_ = stack[2].m_obj;
lean_object* v_inst_3188_ = stack[3].m_obj;
lean_object* v_____do__lift_3189_ = stack[4].m_obj;
lean_object* v_res_3193_;
v_res_3193_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(v_pu_3185_, v_decl_3186_, v_____do__lift_3187_, v_inst_3188_, v_____do__lift_3189_);
stack->m_obj
 = v_res_3193_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(lean_object* v_pu_3194_, lean_object* v_decl_3195_, lean_object* v_____do__lift_3196_, lean_object* v_inst_3197_, lean_object* v_____do__lift_3198_){
_start:
{
uint8_t v_pu_boxed_3199_; lean_object* v_res_3200_; 
v_pu_boxed_3199_ = lean_unbox(v_pu_3194_);
v_res_3200_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(v_pu_boxed_3199_, v_decl_3195_, v_____do__lift_3196_, v_inst_3197_, v_____do__lift_3198_);
return v_res_3200_;
}
}
lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(uint8_t v_pu_3201_, lean_object* v_value_3202_, uint8_t v_t_3203_, lean_object* v_toPure_3204_, lean_object* v_____do__lift_3205_){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3201_, v_____do__lift_3205_, v_value_3202_, v_t_3203_);
v___x_3207_ = lean_apply_2(v_toPure_3204_, lean_box(0), v___x_3206_);
return v___x_3207_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3201_ = stack[0].m_num;
lean_object* v_value_3202_ = stack[1].m_obj;
uint8_t v_t_3203_ = stack[2].m_num;
lean_object* v_toPure_3204_ = stack[3].m_obj;
lean_object* v_____do__lift_3205_ = stack[4].m_obj;
lean_object* v_res_3208_;
v_res_3208_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(v_pu_3201_, v_value_3202_, v_t_3203_, v_toPure_3204_, v_____do__lift_3205_);
stack->m_obj
 = v_res_3208_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(lean_object* v_pu_3209_, lean_object* v_value_3210_, lean_object* v_t_3211_, lean_object* v_toPure_3212_, lean_object* v_____do__lift_3213_){
_start:
{
uint8_t v_pu_boxed_3214_; uint8_t v_t_boxed_3215_; lean_object* v_res_3216_; 
v_pu_boxed_3214_ = lean_unbox(v_pu_3209_);
v_t_boxed_3215_ = lean_unbox(v_t_3211_);
v_res_3216_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(v_pu_boxed_3214_, v_value_3210_, v_t_boxed_3215_, v_toPure_3212_, v_____do__lift_3213_);
lean_dec_ref(v_____do__lift_3213_);
return v_res_3216_;
}
}
lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(uint8_t v_pu_3217_, lean_object* v_decl_3218_, lean_object* v_inst_3219_, lean_object* v_value_3220_, uint8_t v_t_3221_, lean_object* v_toPure_3222_, lean_object* v_toBind_3223_, lean_object* v_inst_3224_, lean_object* v_____do__lift_3225_){
_start:
{
lean_object* v___x_3226_; lean_object* v___f_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___f_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3226_ = lean_box(v_pu_3217_);
v___f_3227_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3227_, 0, v___x_3226_);
lean_closure_set(v___f_3227_, 1, v_decl_3218_);
lean_closure_set(v___f_3227_, 2, v_____do__lift_3225_);
lean_closure_set(v___f_3227_, 3, v_inst_3219_);
v___x_3228_ = lean_box(v_pu_3217_);
v___x_3229_ = lean_box(v_t_3221_);
v___f_3230_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3230_, 0, v___x_3228_);
lean_closure_set(v___f_3230_, 1, v_value_3220_);
lean_closure_set(v___f_3230_, 2, v___x_3229_);
lean_closure_set(v___f_3230_, 3, v_toPure_3222_);
lean_inc(v_toBind_3223_);
v___x_3231_ = lean_apply_4(v_toBind_3223_, lean_box(0), lean_box(0), v_inst_3224_, v___f_3230_);
v___x_3232_ = lean_apply_4(v_toBind_3223_, lean_box(0), lean_box(0), v___x_3231_, v___f_3227_);
return v___x_3232_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3217_ = stack[0].m_num;
lean_object* v_decl_3218_ = stack[1].m_obj;
lean_object* v_inst_3219_ = stack[2].m_obj;
lean_object* v_value_3220_ = stack[3].m_obj;
uint8_t v_t_3221_ = stack[4].m_num;
lean_object* v_toPure_3222_ = stack[5].m_obj;
lean_object* v_toBind_3223_ = stack[6].m_obj;
lean_object* v_inst_3224_ = stack[7].m_obj;
lean_object* v_____do__lift_3225_ = stack[8].m_obj;
lean_object* v_res_3233_;
v_res_3233_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(v_pu_3217_, v_decl_3218_, v_inst_3219_, v_value_3220_, v_t_3221_, v_toPure_3222_, v_toBind_3223_, v_inst_3224_, v_____do__lift_3225_);
stack->m_obj
 = v_res_3233_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(lean_object* v_pu_3234_, lean_object* v_decl_3235_, lean_object* v_inst_3236_, lean_object* v_value_3237_, lean_object* v_t_3238_, lean_object* v_toPure_3239_, lean_object* v_toBind_3240_, lean_object* v_inst_3241_, lean_object* v_____do__lift_3242_){
_start:
{
uint8_t v_pu_boxed_3243_; uint8_t v_t_boxed_3244_; lean_object* v_res_3245_; 
v_pu_boxed_3243_ = lean_unbox(v_pu_3234_);
v_t_boxed_3244_ = lean_unbox(v_t_3238_);
v_res_3245_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(v_pu_boxed_3243_, v_decl_3235_, v_inst_3236_, v_value_3237_, v_t_boxed_3244_, v_toPure_3239_, v_toBind_3240_, v_inst_3241_, v_____do__lift_3242_);
return v_res_3245_;
}
}
lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg(uint8_t v_pu_3246_, uint8_t v_t_3247_, lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v_inst_3250_, lean_object* v_decl_3251_){
_start:
{
lean_object* v_toApplicative_3252_; lean_object* v_toBind_3253_; lean_object* v_type_3254_; lean_object* v_value_3255_; lean_object* v_toPure_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___f_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___f_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v_toApplicative_3252_ = lean_ctor_get(v_inst_3249_, 0);
lean_inc_ref(v_toApplicative_3252_);
v_toBind_3253_ = lean_ctor_get(v_inst_3249_, 1);
lean_inc_n(v_toBind_3253_, 3);
lean_dec_ref(v_inst_3249_);
v_type_3254_ = lean_ctor_get(v_decl_3251_, 2);
lean_inc_ref(v_type_3254_);
v_value_3255_ = lean_ctor_get(v_decl_3251_, 3);
lean_inc(v_value_3255_);
v_toPure_3256_ = lean_ctor_get(v_toApplicative_3252_, 1);
lean_inc_n(v_toPure_3256_, 2);
lean_dec_ref(v_toApplicative_3252_);
v___x_3257_ = lean_box(v_pu_3246_);
v___x_3258_ = lean_box(v_t_3247_);
lean_inc(v_inst_3250_);
v___f_3259_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_3259_, 0, v___x_3257_);
lean_closure_set(v___f_3259_, 1, v_decl_3251_);
lean_closure_set(v___f_3259_, 2, v_inst_3248_);
lean_closure_set(v___f_3259_, 3, v_value_3255_);
lean_closure_set(v___f_3259_, 4, v___x_3258_);
lean_closure_set(v___f_3259_, 5, v_toPure_3256_);
lean_closure_set(v___f_3259_, 6, v_toBind_3253_);
lean_closure_set(v___f_3259_, 7, v_inst_3250_);
v___x_3260_ = lean_box(v_pu_3246_);
v___x_3261_ = lean_box(v_t_3247_);
v___f_3262_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3262_, 0, v___x_3260_);
lean_closure_set(v___f_3262_, 1, v___x_3261_);
lean_closure_set(v___f_3262_, 2, v_type_3254_);
lean_closure_set(v___f_3262_, 3, v_toPure_3256_);
v___x_3263_ = lean_apply_4(v_toBind_3253_, lean_box(0), lean_box(0), v_inst_3250_, v___f_3262_);
v___x_3264_ = lean_apply_4(v_toBind_3253_, lean_box(0), lean_box(0), v___x_3263_, v___f_3259_);
return v___x_3264_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normLetDecl___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3246_ = stack[0].m_num;
uint8_t v_t_3247_ = stack[1].m_num;
lean_object* v_inst_3248_ = stack[2].m_obj;
lean_object* v_inst_3249_ = stack[3].m_obj;
lean_object* v_inst_3250_ = stack[4].m_obj;
lean_object* v_decl_3251_ = stack[5].m_obj;
lean_object* v_res_3265_;
v_res_3265_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_3246_, v_t_3247_, v_inst_3248_, v_inst_3249_, v_inst_3250_, v_decl_3251_);
stack->m_obj
 = v_res_3265_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(lean_object* v_pu_3266_, lean_object* v_t_3267_, lean_object* v_inst_3268_, lean_object* v_inst_3269_, lean_object* v_inst_3270_, lean_object* v_decl_3271_){
_start:
{
uint8_t v_pu_boxed_3272_; uint8_t v_t_boxed_3273_; lean_object* v_res_3274_; 
v_pu_boxed_3272_ = lean_unbox(v_pu_3266_);
v_t_boxed_3273_ = lean_unbox(v_t_3267_);
v_res_3274_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_boxed_3272_, v_t_boxed_3273_, v_inst_3268_, v_inst_3269_, v_inst_3270_, v_decl_3271_);
return v_res_3274_;
}
}
lean_object* l_Lean_Compiler_LCNF_normLetDecl(lean_object* v_m_3275_, uint8_t v_pu_3276_, uint8_t v_t_3277_, lean_object* v_inst_3278_, lean_object* v_inst_3279_, lean_object* v_inst_3280_, lean_object* v_decl_3281_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(v_pu_3276_, v_t_3277_, v_inst_3278_, v_inst_3279_, v_inst_3280_, v_decl_3281_);
return v___x_3282_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normLetDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3276_ = stack[1].m_num;
uint8_t v_t_3277_ = stack[2].m_num;
lean_object* v_inst_3278_ = stack[3].m_obj;
lean_object* v_inst_3279_ = stack[4].m_obj;
lean_object* v_inst_3280_ = stack[5].m_obj;
lean_object* v_decl_3281_ = stack[6].m_obj;
lean_object* v_res_3283_;
v_res_3283_ = l_Lean_Compiler_LCNF_normLetDecl(lean_box(0), v_pu_3276_, v_t_3277_, v_inst_3278_, v_inst_3279_, v_inst_3280_, v_decl_3281_);
stack->m_obj
 = v_res_3283_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___boxed(lean_object* v_m_3284_, lean_object* v_pu_3285_, lean_object* v_t_3286_, lean_object* v_inst_3287_, lean_object* v_inst_3288_, lean_object* v_inst_3289_, lean_object* v_decl_3290_){
_start:
{
uint8_t v_pu_boxed_3291_; uint8_t v_t_boxed_3292_; lean_object* v_res_3293_; 
v_pu_boxed_3291_ = lean_unbox(v_pu_3285_);
v_t_boxed_3292_ = lean_unbox(v_t_3286_);
v_res_3293_ = l_Lean_Compiler_LCNF_normLetDecl(v_m_3284_, v_pu_boxed_3291_, v_t_boxed_3292_, v_inst_3287_, v_inst_3288_, v_inst_3289_, v_decl_3290_);
return v_res_3293_;
}
}
lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg(){
_start:
{
lean_object* v___x_3295_; lean_object* v_toApplicative_3296_; lean_object* v_toFunctor_3297_; lean_object* v_toSeq_3298_; lean_object* v_toSeqLeft_3299_; lean_object* v_toSeqRight_3300_; lean_object* v___f_3301_; lean_object* v___f_3302_; lean_object* v___f_3303_; lean_object* v___f_3304_; lean_object* v___x_3305_; lean_object* v___f_3306_; lean_object* v___f_3307_; lean_object* v___f_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v_toApplicative_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3340_; 
v___x_3295_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1, &l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once, _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1);
v_toApplicative_3296_ = lean_ctor_get(v___x_3295_, 0);
v_toFunctor_3297_ = lean_ctor_get(v_toApplicative_3296_, 0);
v_toSeq_3298_ = lean_ctor_get(v_toApplicative_3296_, 2);
v_toSeqLeft_3299_ = lean_ctor_get(v_toApplicative_3296_, 3);
v_toSeqRight_3300_ = lean_ctor_get(v_toApplicative_3296_, 4);
v___f_3301_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2));
v___f_3302_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3));
lean_inc_ref_n(v_toFunctor_3297_, 2);
v___f_3303_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3303_, 0, v_toFunctor_3297_);
v___f_3304_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3304_, 0, v_toFunctor_3297_);
v___x_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___f_3303_);
lean_ctor_set(v___x_3305_, 1, v___f_3304_);
lean_inc(v_toSeqRight_3300_);
v___f_3306_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3306_, 0, v_toSeqRight_3300_);
lean_inc(v_toSeqLeft_3299_);
v___f_3307_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3307_, 0, v_toSeqLeft_3299_);
lean_inc(v_toSeq_3298_);
v___f_3308_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3308_, 0, v_toSeq_3298_);
v___x_3309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3305_);
lean_ctor_set(v___x_3309_, 1, v___f_3301_);
lean_ctor_set(v___x_3309_, 2, v___f_3308_);
lean_ctor_set(v___x_3309_, 3, v___f_3307_);
lean_ctor_set(v___x_3309_, 4, v___f_3306_);
v___x_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
lean_ctor_set(v___x_3310_, 1, v___f_3302_);
v___x_3311_ = l_StateRefT_x27_instMonad___redArg(v___x_3310_);
v_toApplicative_3312_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3340_ == 0)
{
lean_object* v_unused_3341_; 
v_unused_3341_ = lean_ctor_get(v___x_3311_, 1);
lean_dec(v_unused_3341_);
v___x_3314_ = v___x_3311_;
v_isShared_3315_ = v_isSharedCheck_3340_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_toApplicative_3312_);
lean_dec(v___x_3311_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3340_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v_toFunctor_3316_; lean_object* v_toSeq_3317_; lean_object* v_toSeqLeft_3318_; lean_object* v_toSeqRight_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3338_; 
v_toFunctor_3316_ = lean_ctor_get(v_toApplicative_3312_, 0);
v_toSeq_3317_ = lean_ctor_get(v_toApplicative_3312_, 2);
v_toSeqLeft_3318_ = lean_ctor_get(v_toApplicative_3312_, 3);
v_toSeqRight_3319_ = lean_ctor_get(v_toApplicative_3312_, 4);
v_isSharedCheck_3338_ = !lean_is_exclusive(v_toApplicative_3312_);
if (v_isSharedCheck_3338_ == 0)
{
lean_object* v_unused_3339_; 
v_unused_3339_ = lean_ctor_get(v_toApplicative_3312_, 1);
lean_dec(v_unused_3339_);
v___x_3321_ = v_toApplicative_3312_;
v_isShared_3322_ = v_isSharedCheck_3338_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_toSeqRight_3319_);
lean_inc(v_toSeqLeft_3318_);
lean_inc(v_toSeq_3317_);
lean_inc(v_toFunctor_3316_);
lean_dec(v_toApplicative_3312_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3338_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___f_3323_; lean_object* v___f_3324_; lean_object* v___f_3325_; lean_object* v___f_3326_; lean_object* v___x_3327_; lean_object* v___f_3328_; lean_object* v___f_3329_; lean_object* v___f_3330_; lean_object* v___x_3332_; 
v___f_3323_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4));
v___f_3324_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5));
lean_inc_ref(v_toFunctor_3316_);
v___f_3325_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3325_, 0, v_toFunctor_3316_);
v___f_3326_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3326_, 0, v_toFunctor_3316_);
v___x_3327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___f_3325_);
lean_ctor_set(v___x_3327_, 1, v___f_3326_);
v___f_3328_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3328_, 0, v_toSeqRight_3319_);
v___f_3329_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3329_, 0, v_toSeqLeft_3318_);
v___f_3330_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3330_, 0, v_toSeq_3317_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 4, v___f_3328_);
lean_ctor_set(v___x_3321_, 3, v___f_3329_);
lean_ctor_set(v___x_3321_, 2, v___f_3330_);
lean_ctor_set(v___x_3321_, 1, v___f_3323_);
lean_ctor_set(v___x_3321_, 0, v___x_3327_);
v___x_3332_ = v___x_3321_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3327_);
lean_ctor_set(v_reuseFailAlloc_3337_, 1, v___f_3323_);
lean_ctor_set(v_reuseFailAlloc_3337_, 2, v___f_3330_);
lean_ctor_set(v_reuseFailAlloc_3337_, 3, v___f_3329_);
lean_ctor_set(v_reuseFailAlloc_3337_, 4, v___f_3328_);
v___x_3332_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
lean_object* v___x_3334_; 
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 1, v___f_3324_);
lean_ctor_set(v___x_3314_, 0, v___x_3332_);
v___x_3334_ = v___x_3314_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3332_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v___f_3324_);
v___x_3334_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
lean_object* v___x_3335_; 
v___x_3335_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_3335_, 0, lean_box(0));
lean_closure_set(v___x_3335_, 1, lean_box(0));
lean_closure_set(v___x_3335_, 2, v___x_3334_);
return v___x_3335_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3342_;
v_res_3342_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg();
stack->m_obj
 = v_res_3342_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg___boxed(lean_object* v___dummy_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg();
return v_res_3344_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0(void){
_start:
{
lean_object* v___x_3345_; 
v___x_3345_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___redArg();
return v___x_3345_;
}
}
lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(uint8_t v_pu_3346_, uint8_t v_t_3347_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = lean_obj_once(&l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0, &l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0_once, _init_l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___closed__0);
return v___x_3348_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3346_ = stack[0].m_num;
uint8_t v_t_3347_ = stack[1].m_num;
lean_object* v_res_3349_;
v_res_3349_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_3346_, v_t_3347_);
stack->m_obj
 = v_res_3349_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(lean_object* v_pu_3350_, lean_object* v_t_3351_){
_start:
{
uint8_t v_pu_boxed_3352_; uint8_t v_t_boxed_3353_; lean_object* v_res_3354_; 
v_pu_boxed_3352_ = lean_unbox(v_pu_3350_);
v_t_boxed_3353_ = lean_unbox(v_t_3351_);
v_res_3354_ = l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_boxed_3352_, v_t_boxed_3353_);
return v_res_3354_;
}
}
lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg(uint8_t v_pu_3355_, lean_object* v_inst_3356_, lean_object* v_result_3357_, lean_object* v_x_3358_){
_start:
{
if (lean_obj_tag(v_result_3357_) == 0)
{
lean_object* v_fvarId_3359_; lean_object* v___x_3360_; 
lean_dec(v_inst_3356_);
v_fvarId_3359_ = lean_ctor_get(v_result_3357_, 0);
lean_inc(v_fvarId_3359_);
lean_dec_ref_known(v_result_3357_, 1);
v___x_3360_ = lean_apply_1(v_x_3358_, v_fvarId_3359_);
return v___x_3360_;
}
else
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
lean_dec(v_x_3358_);
v___x_3361_ = lean_box(v_pu_3355_);
v___x_3362_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3362_, 0, v___x_3361_);
v___x_3363_ = lean_apply_2(v_inst_3356_, lean_box(0), v___x_3362_);
return v___x_3363_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_withNormFVarResult___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3355_ = stack[0].m_num;
lean_object* v_inst_3356_ = stack[1].m_obj;
lean_object* v_result_3357_ = stack[2].m_obj;
lean_object* v_x_3358_ = stack[3].m_obj;
lean_object* v_res_3364_;
v_res_3364_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(v_pu_3355_, v_inst_3356_, v_result_3357_, v_x_3358_);
stack->m_obj
 = v_res_3364_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(lean_object* v_pu_3365_, lean_object* v_inst_3366_, lean_object* v_result_3367_, lean_object* v_x_3368_){
_start:
{
uint8_t v_pu_boxed_3369_; lean_object* v_res_3370_; 
v_pu_boxed_3369_ = lean_unbox(v_pu_3365_);
v_res_3370_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(v_pu_boxed_3369_, v_inst_3366_, v_result_3367_, v_x_3368_);
return v_res_3370_;
}
}
lean_object* l_Lean_Compiler_LCNF_withNormFVarResult(lean_object* v_m_3371_, uint8_t v_pu_3372_, lean_object* v_inst_3373_, lean_object* v_inst_3374_, lean_object* v_result_3375_, lean_object* v_x_3376_){
_start:
{
if (lean_obj_tag(v_result_3375_) == 0)
{
lean_object* v_fvarId_3377_; lean_object* v___x_3378_; 
lean_dec(v_inst_3373_);
v_fvarId_3377_ = lean_ctor_get(v_result_3375_, 0);
lean_inc(v_fvarId_3377_);
lean_dec_ref_known(v_result_3375_, 1);
v___x_3378_ = lean_apply_1(v_x_3376_, v_fvarId_3377_);
return v___x_3378_;
}
else
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_dec(v_x_3376_);
v___x_3379_ = lean_box(v_pu_3372_);
v___x_3380_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkReturnErased___boxed), 6, 1);
lean_closure_set(v___x_3380_, 0, v___x_3379_);
v___x_3381_ = lean_apply_2(v_inst_3373_, lean_box(0), v___x_3380_);
return v___x_3381_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_withNormFVarResult_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3372_ = stack[1].m_num;
lean_object* v_inst_3373_ = stack[2].m_obj;
lean_object* v_inst_3374_ = stack[3].m_obj;
lean_object* v_result_3375_ = stack[4].m_obj;
lean_object* v_x_3376_ = stack[5].m_obj;
lean_object* v_res_3382_;
v_res_3382_ = l_Lean_Compiler_LCNF_withNormFVarResult(lean_box(0), v_pu_3372_, v_inst_3373_, v_inst_3374_, v_result_3375_, v_x_3376_);
stack->m_obj
 = v_res_3382_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNormFVarResult___boxed(lean_object* v_m_3383_, lean_object* v_pu_3384_, lean_object* v_inst_3385_, lean_object* v_inst_3386_, lean_object* v_result_3387_, lean_object* v_x_3388_){
_start:
{
uint8_t v_pu_boxed_3389_; lean_object* v_res_3390_; 
v_pu_boxed_3389_ = lean_unbox(v_pu_3384_);
v_res_3390_ = l_Lean_Compiler_LCNF_withNormFVarResult(v_m_3383_, v_pu_boxed_3389_, v_inst_3385_, v_inst_3386_, v_result_3387_, v_x_3388_);
lean_dec_ref(v_inst_3386_);
return v_res_3390_;
}
}
lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(uint8_t v_pu_3391_, uint8_t v_t_3392_, lean_object* v_args_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_3391_, v___y_3394_, v_args_3393_, v_t_3392_);
v___x_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3396_);
return v___x_3397_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3391_ = stack[0].m_num;
uint8_t v_t_3392_ = stack[1].m_num;
lean_object* v_args_3393_ = stack[2].m_obj;
lean_object* v___y_3394_ = stack[3].m_obj;
lean_object* v_res_3398_;
v_res_3398_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_3391_, v_t_3392_, v_args_3393_, v___y_3394_);
stack->m_obj
 = v_res_3398_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(lean_object* v_pu_3399_, lean_object* v_t_3400_, lean_object* v_args_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
uint8_t v_pu_boxed_3404_; uint8_t v_t_boxed_3405_; lean_object* v_res_3406_; 
v_pu_boxed_3404_ = lean_unbox(v_pu_3399_);
v_t_boxed_3405_ = lean_unbox(v_t_3400_);
v_res_3406_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_boxed_3404_, v_t_boxed_3405_, v_args_3401_, v___y_3402_);
lean_dec_ref(v___y_3402_);
return v_res_3406_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(uint8_t v_pu_3407_, uint8_t v_t_3408_, lean_object* v_i_3409_, lean_object* v_as_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v___x_3414_; uint8_t v___x_3415_; 
v___x_3414_ = lean_array_get_size(v_as_3410_);
v___x_3415_ = lean_nat_dec_lt(v_i_3409_, v___x_3414_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3416_; 
lean_dec(v_i_3409_);
v___x_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3416_, 0, v_as_3410_);
return v___x_3416_;
}
else
{
lean_object* v_a_3417_; lean_object* v_type_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v_a_3417_ = lean_array_fget_borrowed(v_as_3410_, v_i_3409_);
v_type_3418_ = lean_ctor_get(v_a_3417_, 2);
lean_inc_ref(v_type_3418_);
v___x_3419_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3407_, v___y_3411_, v_t_3408_, v_type_3418_);
lean_inc(v_a_3417_);
v___x_3420_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_3407_, v_a_3417_, v___x_3419_, v___y_3412_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; size_t v___x_3422_; size_t v___x_3423_; uint8_t v___x_3424_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref_known(v___x_3420_, 1);
v___x_3422_ = lean_ptr_addr(v_a_3417_);
v___x_3423_ = lean_ptr_addr(v_a_3421_);
v___x_3424_ = lean_usize_dec_eq(v___x_3422_, v___x_3423_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3425_ = lean_unsigned_to_nat(1u);
v___x_3426_ = lean_nat_add(v_i_3409_, v___x_3425_);
v___x_3427_ = lean_array_fset(v_as_3410_, v_i_3409_, v_a_3421_);
lean_dec(v_i_3409_);
v_i_3409_ = v___x_3426_;
v_as_3410_ = v___x_3427_;
goto _start;
}
else
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
lean_dec(v_a_3421_);
v___x_3429_ = lean_unsigned_to_nat(1u);
v___x_3430_ = lean_nat_add(v_i_3409_, v___x_3429_);
lean_dec(v_i_3409_);
v_i_3409_ = v___x_3430_;
goto _start;
}
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
lean_dec_ref(v_as_3410_);
lean_dec(v_i_3409_);
v_a_3432_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___x_3420_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3420_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3407_ = stack[0].m_num;
uint8_t v_t_3408_ = stack[1].m_num;
lean_object* v_i_3409_ = stack[2].m_obj;
lean_object* v_as_3410_ = stack[3].m_obj;
lean_object* v___y_3411_ = stack[4].m_obj;
lean_object* v___y_3412_ = stack[5].m_obj;
lean_object* v_res_3440_;
v_res_3440_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_3407_, v_t_3408_, v_i_3409_, v_as_3410_, v___y_3411_, v___y_3412_);
stack->m_obj
 = v_res_3440_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(lean_object* v_pu_3441_, lean_object* v_t_3442_, lean_object* v_i_3443_, lean_object* v_as_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
uint8_t v_pu_boxed_3448_; uint8_t v_t_boxed_3449_; lean_object* v_res_3450_; 
v_pu_boxed_3448_ = lean_unbox(v_pu_3441_);
v_t_boxed_3449_ = lean_unbox(v_t_3442_);
v_res_3450_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_boxed_3448_, v_t_boxed_3449_, v_i_3443_, v_as_3444_, v___y_3445_, v___y_3446_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
return v_res_3450_;
}
}
lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(uint8_t v_pu_3451_, uint8_t v_t_3452_, lean_object* v_ps_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3460_ = lean_unsigned_to_nat(0u);
v___x_3461_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_3451_, v_t_3452_, v___x_3460_, v_ps_3453_, v___y_3454_, v___y_3456_);
return v___x_3461_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3451_ = stack[0].m_num;
uint8_t v_t_3452_ = stack[1].m_num;
lean_object* v_ps_3453_ = stack[2].m_obj;
lean_object* v___y_3454_ = stack[3].m_obj;
lean_object* v___y_3455_ = stack[4].m_obj;
lean_object* v___y_3456_ = stack[5].m_obj;
lean_object* v___y_3457_ = stack[6].m_obj;
lean_object* v___y_3458_ = stack[7].m_obj;
lean_object* v_res_3462_;
v_res_3462_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_3451_, v_t_3452_, v_ps_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
stack->m_obj
 = v_res_3462_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(lean_object* v_pu_3463_, lean_object* v_t_3464_, lean_object* v_ps_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
uint8_t v_pu_boxed_3472_; uint8_t v_t_boxed_3473_; lean_object* v_res_3474_; 
v_pu_boxed_3472_ = lean_unbox(v_pu_3463_);
v_t_boxed_3473_ = lean_unbox(v_t_3464_);
v_res_3474_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_boxed_3472_, v_t_boxed_3473_, v_ps_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec_ref(v___y_3466_);
return v_res_3474_;
}
}
lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(uint8_t v_pu_3475_, uint8_t v_t_3476_, lean_object* v_decl_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v_type_3481_; lean_object* v_value_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v_type_3481_ = lean_ctor_get(v_decl_3477_, 2);
v_value_3482_ = lean_ctor_get(v_decl_3477_, 3);
lean_inc_ref(v_type_3481_);
v___x_3483_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3475_, v___y_3478_, v_t_3476_, v_type_3481_);
lean_inc(v_value_3482_);
v___x_3484_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_3475_, v___y_3478_, v_value_3482_, v_t_3476_);
v___x_3485_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_3475_, v_decl_3477_, v___x_3483_, v___x_3484_, v___y_3479_);
return v___x_3485_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3475_ = stack[0].m_num;
uint8_t v_t_3476_ = stack[1].m_num;
lean_object* v_decl_3477_ = stack[2].m_obj;
lean_object* v___y_3478_ = stack[3].m_obj;
lean_object* v___y_3479_ = stack[4].m_obj;
lean_object* v_res_3486_;
v_res_3486_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_3475_, v_t_3476_, v_decl_3477_, v___y_3478_, v___y_3479_);
stack->m_obj
 = v_res_3486_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(lean_object* v_pu_3487_, lean_object* v_t_3488_, lean_object* v_decl_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
uint8_t v_pu_boxed_3493_; uint8_t v_t_boxed_3494_; lean_object* v_res_3495_; 
v_pu_boxed_3493_ = lean_unbox(v_pu_3487_);
v_t_boxed_3494_ = lean_unbox(v_t_3488_);
v_res_3495_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_boxed_3493_, v_t_boxed_3494_, v_decl_3489_, v___y_3490_, v___y_3491_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
return v_res_3495_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(uint8_t v_pu_3496_, uint8_t v_t_3497_, lean_object* v_i_3498_, lean_object* v_as_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v___x_3506_; uint8_t v___x_3507_; 
v___x_3506_ = lean_array_get_size(v_as_3499_);
v___x_3507_ = lean_nat_dec_lt(v_i_3498_, v___x_3506_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; 
lean_dec(v_i_3498_);
v___x_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3508_, 0, v_as_3499_);
return v___x_3508_;
}
else
{
lean_object* v_a_3509_; lean_object* v_a_3511_; 
v_a_3509_ = lean_array_fget_borrowed(v_as_3499_, v_i_3498_);
switch(lean_obj_tag(v_a_3509_))
{
case 0:
{
lean_object* v_params_3522_; lean_object* v_code_3523_; lean_object* v___x_3524_; 
v_params_3522_ = lean_ctor_get(v_a_3509_, 1);
v_code_3523_ = lean_ctor_get(v_a_3509_, 2);
lean_inc_ref(v_params_3522_);
v___x_3524_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_3496_, v_t_3497_, v_params_3522_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3526_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3525_);
lean_dec_ref_known(v___x_3524_, 1);
lean_inc_ref(v_code_3523_);
v___x_3526_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3496_, v_t_3497_, v_code_3523_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3528_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v___x_3526_, 1);
lean_inc_ref(v_a_3509_);
v___x_3528_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_3496_, v_a_3509_, v_a_3525_, v_a_3527_);
v_a_3511_ = v___x_3528_;
goto v___jp_3510_;
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
lean_dec(v_a_3525_);
lean_dec_ref(v_as_3499_);
lean_dec(v_i_3498_);
v_a_3529_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3526_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3526_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec_ref(v_as_3499_);
lean_dec(v_i_3498_);
v_a_3537_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3524_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3524_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
case 1:
{
lean_object* v_code_3545_; lean_object* v___x_3546_; 
v_code_3545_ = lean_ctor_get(v_a_3509_, 1);
lean_inc_ref(v_code_3545_);
v___x_3546_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3496_, v_t_3497_, v_code_3545_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3548_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3547_);
lean_dec_ref_known(v___x_3546_, 1);
lean_inc_ref(v_a_3509_);
v___x_3548_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3509_, v_a_3547_);
v_a_3511_ = v___x_3548_;
goto v___jp_3510_;
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_dec_ref(v_as_3499_);
lean_dec(v_i_3498_);
v_a_3549_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3546_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3546_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
default: 
{
lean_object* v_code_3557_; lean_object* v___x_3558_; 
v_code_3557_ = lean_ctor_get(v_a_3509_, 0);
lean_inc_ref(v_code_3557_);
v___x_3558_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3496_, v_t_3497_, v_code_3557_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; lean_object* v___x_3560_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3559_);
lean_dec_ref_known(v___x_3558_, 1);
lean_inc_ref(v_a_3509_);
v___x_3560_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3509_, v_a_3559_);
v_a_3511_ = v___x_3560_;
goto v___jp_3510_;
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec_ref(v_as_3499_);
lean_dec(v_i_3498_);
v_a_3561_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3558_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3558_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
v___jp_3510_:
{
size_t v___x_3512_; size_t v___x_3513_; uint8_t v___x_3514_; 
v___x_3512_ = lean_ptr_addr(v_a_3509_);
v___x_3513_ = lean_ptr_addr(v_a_3511_);
v___x_3514_ = lean_usize_dec_eq(v___x_3512_, v___x_3513_);
if (v___x_3514_ == 0)
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3515_ = lean_unsigned_to_nat(1u);
v___x_3516_ = lean_nat_add(v_i_3498_, v___x_3515_);
v___x_3517_ = lean_array_fset(v_as_3499_, v_i_3498_, v_a_3511_);
lean_dec(v_i_3498_);
v_i_3498_ = v___x_3516_;
v_as_3499_ = v___x_3517_;
goto _start;
}
else
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
lean_dec_ref(v_a_3511_);
v___x_3519_ = lean_unsigned_to_nat(1u);
v___x_3520_ = lean_nat_add(v_i_3498_, v___x_3519_);
lean_dec(v_i_3498_);
v_i_3498_ = v___x_3520_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3496_ = stack[0].m_num;
uint8_t v_t_3497_ = stack[1].m_num;
lean_object* v_i_3498_ = stack[2].m_obj;
lean_object* v_as_3499_ = stack[3].m_obj;
lean_object* v___y_3500_ = stack[4].m_obj;
lean_object* v___y_3501_ = stack[5].m_obj;
lean_object* v___y_3502_ = stack[6].m_obj;
lean_object* v___y_3503_ = stack[7].m_obj;
lean_object* v___y_3504_ = stack[8].m_obj;
lean_object* v_res_3569_;
v_res_3569_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_3496_, v_t_3497_, v_i_3498_, v_as_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
stack->m_obj
 = v_res_3569_;
}
lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t v_pu_3570_, uint8_t v_t_3571_, lean_object* v_code_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_){
_start:
{
switch(lean_obj_tag(v_code_3572_))
{
case 0:
{
lean_object* v_decl_3579_; lean_object* v_k_3580_; lean_object* v___x_3581_; 
v_decl_3579_ = lean_ctor_get(v_code_3572_, 0);
v_k_3580_ = lean_ctor_get(v_code_3572_, 1);
lean_inc_ref(v_decl_3579_);
v___x_3581_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_3570_, v_t_3571_, v_decl_3579_, v_a_3573_, v_a_3575_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v___x_3583_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3582_);
lean_dec_ref_known(v___x_3581_, 1);
lean_inc_ref(v_k_3580_);
v___x_3583_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3570_, v_t_3571_, v_k_3580_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3621_; 
v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3586_ = v___x_3583_;
v_isShared_3587_ = v_isSharedCheck_3621_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3583_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3621_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
size_t v___x_3588_; size_t v___x_3589_; uint8_t v___x_3590_; 
v___x_3588_ = lean_ptr_addr(v_k_3580_);
v___x_3589_ = lean_ptr_addr(v_a_3584_);
v___x_3590_ = lean_usize_dec_eq(v___x_3588_, v___x_3589_);
if (v___x_3590_ == 0)
{
lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3600_; 
v_isSharedCheck_3600_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_3600_ == 0)
{
lean_object* v_unused_3601_; lean_object* v_unused_3602_; 
v_unused_3601_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_3601_);
v_unused_3602_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_3602_);
v___x_3592_ = v_code_3572_;
v_isShared_3593_ = v_isSharedCheck_3600_;
goto v_resetjp_3591_;
}
else
{
lean_dec(v_code_3572_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3600_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 1, v_a_3584_);
lean_ctor_set(v___x_3592_, 0, v_a_3582_);
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3582_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_a_3584_);
v___x_3595_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
lean_object* v___x_3597_; 
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 0, v___x_3595_);
v___x_3597_ = v___x_3586_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3595_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
else
{
size_t v___x_3603_; size_t v___x_3604_; uint8_t v___x_3605_; 
v___x_3603_ = lean_ptr_addr(v_decl_3579_);
v___x_3604_ = lean_ptr_addr(v_a_3582_);
v___x_3605_ = lean_usize_dec_eq(v___x_3603_, v___x_3604_);
if (v___x_3605_ == 0)
{
lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3615_; 
v_isSharedCheck_3615_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_3615_ == 0)
{
lean_object* v_unused_3616_; lean_object* v_unused_3617_; 
v_unused_3616_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_3616_);
v_unused_3617_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_3617_);
v___x_3607_ = v_code_3572_;
v_isShared_3608_ = v_isSharedCheck_3615_;
goto v_resetjp_3606_;
}
else
{
lean_dec(v_code_3572_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3615_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 1, v_a_3584_);
lean_ctor_set(v___x_3607_, 0, v_a_3582_);
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3582_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v_a_3584_);
v___x_3610_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3612_; 
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 0, v___x_3610_);
v___x_3612_ = v___x_3586_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3610_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
else
{
lean_object* v___x_3619_; 
lean_dec(v_a_3584_);
lean_dec(v_a_3582_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 0, v_code_3572_);
v___x_3619_ = v___x_3586_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_code_3572_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
}
else
{
lean_dec(v_a_3582_);
lean_dec_ref_known(v_code_3572_, 2);
return v___x_3583_;
}
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
lean_dec_ref_known(v_code_3572_, 2);
v_a_3622_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3581_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3581_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
case 1:
{
lean_object* v_decl_3630_; lean_object* v_k_3631_; lean_object* v___x_3632_; 
v_decl_3630_ = lean_ctor_get(v_code_3572_, 0);
v_k_3631_ = lean_ctor_get(v_code_3572_, 1);
lean_inc_ref(v_decl_3630_);
v___x_3632_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3570_, v_t_3571_, v_decl_3630_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v___x_3634_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_a_3633_);
lean_dec_ref_known(v___x_3632_, 1);
lean_inc_ref(v_k_3631_);
v___x_3634_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3570_, v_t_3571_, v_k_3631_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3672_; 
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3637_ = v___x_3634_;
v_isShared_3638_ = v_isSharedCheck_3672_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3634_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3672_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
size_t v___x_3639_; size_t v___x_3640_; uint8_t v___x_3641_; 
v___x_3639_ = lean_ptr_addr(v_k_3631_);
v___x_3640_ = lean_ptr_addr(v_a_3635_);
v___x_3641_ = lean_usize_dec_eq(v___x_3639_, v___x_3640_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3651_; 
v_isSharedCheck_3651_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_3651_ == 0)
{
lean_object* v_unused_3652_; lean_object* v_unused_3653_; 
v_unused_3652_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_3652_);
v_unused_3653_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_3653_);
v___x_3643_ = v_code_3572_;
v_isShared_3644_ = v_isSharedCheck_3651_;
goto v_resetjp_3642_;
}
else
{
lean_dec(v_code_3572_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3651_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 1, v_a_3635_);
lean_ctor_set(v___x_3643_, 0, v_a_3633_);
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3633_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_a_3635_);
v___x_3646_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
lean_object* v___x_3648_; 
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 0, v___x_3646_);
v___x_3648_ = v___x_3637_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3646_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
else
{
size_t v___x_3654_; size_t v___x_3655_; uint8_t v___x_3656_; 
v___x_3654_ = lean_ptr_addr(v_decl_3630_);
v___x_3655_ = lean_ptr_addr(v_a_3633_);
v___x_3656_ = lean_usize_dec_eq(v___x_3654_, v___x_3655_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3666_; 
v_isSharedCheck_3666_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_3666_ == 0)
{
lean_object* v_unused_3667_; lean_object* v_unused_3668_; 
v_unused_3667_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_3667_);
v_unused_3668_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_3668_);
v___x_3658_ = v_code_3572_;
v_isShared_3659_ = v_isSharedCheck_3666_;
goto v_resetjp_3657_;
}
else
{
lean_dec(v_code_3572_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3666_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 1, v_a_3635_);
lean_ctor_set(v___x_3658_, 0, v_a_3633_);
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3633_);
lean_ctor_set(v_reuseFailAlloc_3665_, 1, v_a_3635_);
v___x_3661_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3663_; 
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 0, v___x_3661_);
v___x_3663_ = v___x_3637_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3661_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
else
{
lean_object* v___x_3670_; 
lean_dec(v_a_3635_);
lean_dec(v_a_3633_);
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 0, v_code_3572_);
v___x_3670_ = v___x_3637_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_code_3572_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
}
else
{
lean_dec(v_a_3633_);
lean_dec_ref_known(v_code_3572_, 2);
return v___x_3634_;
}
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
lean_dec_ref_known(v_code_3572_, 2);
v_a_3673_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3632_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3632_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
case 2:
{
lean_object* v_decl_3681_; lean_object* v_k_3682_; lean_object* v___x_3683_; 
v_decl_3681_ = lean_ctor_get(v_code_3572_, 0);
v_k_3682_ = lean_ctor_get(v_code_3572_, 1);
lean_inc_ref(v_decl_3681_);
v___x_3683_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_3570_, v_t_3571_, v_decl_3681_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; lean_object* v___x_3685_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
lean_dec_ref_known(v___x_3683_, 1);
lean_inc_ref(v_k_3682_);
v___x_3685_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3570_, v_t_3571_, v_k_3682_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3723_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3688_ = v___x_3685_;
v_isShared_3689_ = v_isSharedCheck_3723_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3685_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3723_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
size_t v___x_3690_; size_t v___x_3691_; uint8_t v___x_3692_; 
v___x_3690_ = lean_ptr_addr(v_k_3682_);
v___x_3691_ = lean_ptr_addr(v_a_3686_);
v___x_3692_ = lean_usize_dec_eq(v___x_3690_, v___x_3691_);
if (v___x_3692_ == 0)
{
lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3702_; 
v_isSharedCheck_3702_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_3702_ == 0)
{
lean_object* v_unused_3703_; lean_object* v_unused_3704_; 
v_unused_3703_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_3703_);
v_unused_3704_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_3704_);
v___x_3694_ = v_code_3572_;
v_isShared_3695_ = v_isSharedCheck_3702_;
goto v_resetjp_3693_;
}
else
{
lean_dec(v_code_3572_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3702_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 1, v_a_3686_);
lean_ctor_set(v___x_3694_, 0, v_a_3684_);
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3684_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v_a_3686_);
v___x_3697_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
lean_object* v___x_3699_; 
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 0, v___x_3697_);
v___x_3699_ = v___x_3688_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3697_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
else
{
size_t v___x_3705_; size_t v___x_3706_; uint8_t v___x_3707_; 
v___x_3705_ = lean_ptr_addr(v_decl_3681_);
v___x_3706_ = lean_ptr_addr(v_a_3684_);
v___x_3707_ = lean_usize_dec_eq(v___x_3705_, v___x_3706_);
if (v___x_3707_ == 0)
{
lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3717_; 
v_isSharedCheck_3717_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_3717_ == 0)
{
lean_object* v_unused_3718_; lean_object* v_unused_3719_; 
v_unused_3718_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_3718_);
v_unused_3719_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_3719_);
v___x_3709_ = v_code_3572_;
v_isShared_3710_ = v_isSharedCheck_3717_;
goto v_resetjp_3708_;
}
else
{
lean_dec(v_code_3572_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3717_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3712_; 
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 1, v_a_3686_);
lean_ctor_set(v___x_3709_, 0, v_a_3684_);
v___x_3712_ = v___x_3709_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3684_);
lean_ctor_set(v_reuseFailAlloc_3716_, 1, v_a_3686_);
v___x_3712_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___x_3714_; 
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 0, v___x_3712_);
v___x_3714_ = v___x_3688_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v___x_3712_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
else
{
lean_object* v___x_3721_; 
lean_dec(v_a_3686_);
lean_dec(v_a_3684_);
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 0, v_code_3572_);
v___x_3721_ = v___x_3688_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_code_3572_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
}
else
{
lean_dec(v_a_3684_);
lean_dec_ref_known(v_code_3572_, 2);
return v___x_3685_;
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_dec_ref_known(v_code_3572_, 2);
v_a_3724_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3683_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3683_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3732_; lean_object* v_args_3733_; lean_object* v___x_3734_; 
v_fvarId_3732_ = lean_ctor_get(v_code_3572_, 0);
v_args_3733_ = lean_ctor_get(v_code_3572_, 1);
lean_inc(v_fvarId_3732_);
v___x_3734_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3573_, v_fvarId_3732_, v_t_3571_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_fvarId_3735_; lean_object* v___x_3736_; 
v_fvarId_3735_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_fvarId_3735_);
lean_dec_ref_known(v___x_3734_, 1);
lean_inc_ref(v_args_3733_);
v___x_3736_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_3570_, v_t_3571_, v_args_3733_, v_a_3573_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3762_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3739_ = v___x_3736_;
v_isShared_3740_ = v_isSharedCheck_3762_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3736_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3762_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
uint8_t v___y_3742_; uint8_t v___x_3758_; 
v___x_3758_ = l_Lean_instBEqFVarId_beq(v_fvarId_3732_, v_fvarId_3735_);
if (v___x_3758_ == 0)
{
v___y_3742_ = v___x_3758_;
goto v___jp_3741_;
}
else
{
size_t v___x_3759_; size_t v___x_3760_; uint8_t v___x_3761_; 
v___x_3759_ = lean_ptr_addr(v_args_3733_);
v___x_3760_ = lean_ptr_addr(v_a_3737_);
v___x_3761_ = lean_usize_dec_eq(v___x_3759_, v___x_3760_);
v___y_3742_ = v___x_3761_;
goto v___jp_3741_;
}
v___jp_3741_:
{
if (v___y_3742_ == 0)
{
lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3752_; 
v_isSharedCheck_3752_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_3752_ == 0)
{
lean_object* v_unused_3753_; lean_object* v_unused_3754_; 
v_unused_3753_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_3753_);
v_unused_3754_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_3754_);
v___x_3744_ = v_code_3572_;
v_isShared_3745_ = v_isSharedCheck_3752_;
goto v_resetjp_3743_;
}
else
{
lean_dec(v_code_3572_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3752_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 1, v_a_3737_);
lean_ctor_set(v___x_3744_, 0, v_fvarId_3735_);
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_fvarId_3735_);
lean_ctor_set(v_reuseFailAlloc_3751_, 1, v_a_3737_);
v___x_3747_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
lean_object* v___x_3749_; 
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v___x_3747_);
v___x_3749_ = v___x_3739_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
else
{
lean_object* v___x_3756_; 
lean_dec(v_a_3737_);
lean_dec(v_fvarId_3735_);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v_code_3572_);
v___x_3756_ = v___x_3739_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_code_3572_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
}
else
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
lean_dec(v_fvarId_3735_);
lean_dec_ref_known(v_code_3572_, 2);
v_a_3763_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3765_ = v___x_3736_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3736_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3768_; 
if (v_isShared_3766_ == 0)
{
v___x_3768_ = v___x_3765_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
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
else
{
lean_object* v___x_3771_; 
lean_dec_ref_known(v_code_3572_, 2);
v___x_3771_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3570_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
return v___x_3771_;
}
}
case 4:
{
lean_object* v_cases_3772_; lean_object* v_typeName_3773_; lean_object* v_resultType_3774_; lean_object* v_discr_3775_; lean_object* v_alts_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3821_; 
v_cases_3772_ = lean_ctor_get(v_code_3572_, 0);
lean_inc_ref(v_cases_3772_);
v_typeName_3773_ = lean_ctor_get(v_cases_3772_, 0);
v_resultType_3774_ = lean_ctor_get(v_cases_3772_, 1);
v_discr_3775_ = lean_ctor_get(v_cases_3772_, 2);
v_alts_3776_ = lean_ctor_get(v_cases_3772_, 3);
v_isSharedCheck_3821_ = !lean_is_exclusive(v_cases_3772_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3778_ = v_cases_3772_;
v_isShared_3779_ = v_isSharedCheck_3821_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_alts_3776_);
lean_inc(v_discr_3775_);
lean_inc(v_resultType_3774_);
lean_inc(v_typeName_3773_);
lean_dec(v_cases_3772_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3821_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; 
lean_inc_ref(v_resultType_3774_);
v___x_3780_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3570_, v_a_3573_, v_t_3571_, v_resultType_3774_);
lean_inc(v_discr_3775_);
v___x_3781_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3573_, v_discr_3775_, v_t_3571_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_fvarId_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3819_; 
v_fvarId_3782_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3784_ = v___x_3781_;
v_isShared_3785_ = v_isSharedCheck_3819_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_fvarId_3782_);
lean_dec(v___x_3781_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3819_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3786_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3776_);
v___x_3787_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_3570_, v_t_3571_, v___x_3786_, v_alts_3776_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3810_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3790_ = v___x_3787_;
v_isShared_3791_ = v_isSharedCheck_3810_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3787_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3810_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
size_t v___x_3802_; size_t v___x_3803_; uint8_t v___x_3804_; 
v___x_3802_ = lean_ptr_addr(v_alts_3776_);
lean_dec_ref(v_alts_3776_);
v___x_3803_ = lean_ptr_addr(v_a_3788_);
v___x_3804_ = lean_usize_dec_eq(v___x_3802_, v___x_3803_);
if (v___x_3804_ == 0)
{
lean_dec(v_discr_3775_);
lean_dec_ref(v_resultType_3774_);
lean_dec_ref_known(v_code_3572_, 1);
goto v___jp_3792_;
}
else
{
size_t v___x_3805_; size_t v___x_3806_; uint8_t v___x_3807_; 
v___x_3805_ = lean_ptr_addr(v_resultType_3774_);
lean_dec_ref(v_resultType_3774_);
v___x_3806_ = lean_ptr_addr(v___x_3780_);
v___x_3807_ = lean_usize_dec_eq(v___x_3805_, v___x_3806_);
if (v___x_3807_ == 0)
{
lean_dec(v_discr_3775_);
lean_dec_ref_known(v_code_3572_, 1);
goto v___jp_3792_;
}
else
{
uint8_t v___x_3808_; 
v___x_3808_ = l_Lean_instBEqFVarId_beq(v_discr_3775_, v_fvarId_3782_);
lean_dec(v_discr_3775_);
if (v___x_3808_ == 0)
{
lean_dec_ref_known(v_code_3572_, 1);
goto v___jp_3792_;
}
else
{
lean_object* v___x_3809_; 
lean_del_object(v___x_3790_);
lean_dec(v_a_3788_);
lean_del_object(v___x_3784_);
lean_dec(v_fvarId_3782_);
lean_dec_ref(v___x_3780_);
lean_del_object(v___x_3778_);
lean_dec(v_typeName_3773_);
v___x_3809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3809_, 0, v_code_3572_);
return v___x_3809_;
}
}
}
v___jp_3792_:
{
lean_object* v___x_3794_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 3, v_a_3788_);
lean_ctor_set(v___x_3778_, 2, v_fvarId_3782_);
lean_ctor_set(v___x_3778_, 1, v___x_3780_);
v___x_3794_ = v___x_3778_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_typeName_3773_);
lean_ctor_set(v_reuseFailAlloc_3801_, 1, v___x_3780_);
lean_ctor_set(v_reuseFailAlloc_3801_, 2, v_fvarId_3782_);
lean_ctor_set(v_reuseFailAlloc_3801_, 3, v_a_3788_);
v___x_3794_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
lean_object* v___x_3796_; 
if (v_isShared_3785_ == 0)
{
lean_ctor_set_tag(v___x_3784_, 4);
lean_ctor_set(v___x_3784_, 0, v___x_3794_);
v___x_3796_ = v___x_3784_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3794_);
v___x_3796_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
lean_object* v___x_3798_; 
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 0, v___x_3796_);
v___x_3798_ = v___x_3790_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3796_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
}
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_del_object(v___x_3784_);
lean_dec(v_fvarId_3782_);
lean_dec_ref(v___x_3780_);
lean_del_object(v___x_3778_);
lean_dec_ref(v_alts_3776_);
lean_dec(v_discr_3775_);
lean_dec_ref(v_resultType_3774_);
lean_dec(v_typeName_3773_);
lean_dec_ref_known(v_code_3572_, 1);
v_a_3811_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3787_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3787_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
}
else
{
lean_object* v___x_3820_; 
lean_dec_ref(v___x_3780_);
lean_del_object(v___x_3778_);
lean_dec_ref(v_alts_3776_);
lean_dec(v_discr_3775_);
lean_dec_ref(v_resultType_3774_);
lean_dec(v_typeName_3773_);
lean_dec_ref_known(v_code_3572_, 1);
v___x_3820_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3570_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
return v___x_3820_;
}
}
}
case 5:
{
lean_object* v_fvarId_3822_; lean_object* v___x_3823_; 
v_fvarId_3822_ = lean_ctor_get(v_code_3572_, 0);
lean_inc(v_fvarId_3822_);
v___x_3823_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3573_, v_fvarId_3822_, v_t_3571_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_fvarId_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3843_; 
v_fvarId_3824_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3826_ = v___x_3823_;
v_isShared_3827_ = v_isSharedCheck_3843_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_fvarId_3824_);
lean_dec(v___x_3823_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3843_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
uint8_t v___x_3828_; 
v___x_3828_ = l_Lean_instBEqFVarId_beq(v_fvarId_3822_, v_fvarId_3824_);
if (v___x_3828_ == 0)
{
lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3838_; 
v_isSharedCheck_3838_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_3838_ == 0)
{
lean_object* v_unused_3839_; 
v_unused_3839_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_3839_);
v___x_3830_ = v_code_3572_;
v_isShared_3831_ = v_isSharedCheck_3838_;
goto v_resetjp_3829_;
}
else
{
lean_dec(v_code_3572_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3838_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 0, v_fvarId_3824_);
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_fvarId_3824_);
v___x_3833_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
lean_object* v___x_3835_; 
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 0, v___x_3833_);
v___x_3835_ = v___x_3826_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3833_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
}
else
{
lean_object* v___x_3841_; 
lean_dec(v_fvarId_3824_);
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 0, v_code_3572_);
v___x_3841_ = v___x_3826_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_code_3572_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
else
{
lean_object* v___x_3844_; 
lean_dec_ref_known(v_code_3572_, 1);
v___x_3844_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3570_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
return v___x_3844_;
}
}
case 6:
{
lean_object* v_type_3845_; lean_object* v___x_3846_; size_t v___x_3847_; size_t v___x_3848_; uint8_t v___x_3849_; 
v_type_3845_ = lean_ctor_get(v_code_3572_, 0);
lean_inc_ref(v_type_3845_);
v___x_3846_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3570_, v_a_3573_, v_t_3571_, v_type_3845_);
v___x_3847_ = lean_ptr_addr(v_type_3845_);
v___x_3848_ = lean_ptr_addr(v___x_3846_);
v___x_3849_ = lean_usize_dec_eq(v___x_3847_, v___x_3848_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3857_; 
v_isSharedCheck_3857_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_3857_ == 0)
{
lean_object* v_unused_3858_; 
v_unused_3858_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_3858_);
v___x_3851_ = v_code_3572_;
v_isShared_3852_ = v_isSharedCheck_3857_;
goto v_resetjp_3850_;
}
else
{
lean_dec(v_code_3572_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3857_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 0, v___x_3846_);
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3846_);
v___x_3854_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3855_; 
v___x_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
return v___x_3855_;
}
}
}
else
{
lean_object* v___x_3859_; 
lean_dec_ref(v___x_3846_);
v___x_3859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3859_, 0, v_code_3572_);
return v___x_3859_;
}
}
case 7:
{
lean_object* v_fvarId_3860_; lean_object* v_i_3861_; lean_object* v_y_3862_; lean_object* v_k_3863_; lean_object* v___x_3864_; 
v_fvarId_3860_ = lean_ctor_get(v_code_3572_, 0);
v_i_3861_ = lean_ctor_get(v_code_3572_, 1);
v_y_3862_ = lean_ctor_get(v_code_3572_, 2);
v_k_3863_ = lean_ctor_get(v_code_3572_, 3);
lean_inc(v_fvarId_3860_);
v___x_3864_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3573_, v_fvarId_3860_, v_t_3571_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_fvarId_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v_fvarId_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_fvarId_3865_);
lean_dec_ref_known(v___x_3864_, 1);
lean_inc(v_y_3862_);
v___x_3866_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_3570_, v_a_3573_, v_y_3862_, v_t_3571_);
lean_inc_ref(v_k_3863_);
v___x_3867_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3570_, v_t_3571_, v_k_3863_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3941_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3870_ = v___x_3867_;
v_isShared_3871_ = v_isSharedCheck_3941_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3867_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3941_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
size_t v___x_3872_; size_t v___x_3873_; uint8_t v___x_3874_; 
v___x_3872_ = lean_ptr_addr(v_fvarId_3860_);
v___x_3873_ = lean_ptr_addr(v_fvarId_3865_);
v___x_3874_ = lean_usize_dec_eq(v___x_3872_, v___x_3873_);
if (v___x_3874_ == 0)
{
lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3884_; 
lean_inc(v_i_3861_);
v_isSharedCheck_3884_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_3884_ == 0)
{
lean_object* v_unused_3885_; lean_object* v_unused_3886_; lean_object* v_unused_3887_; lean_object* v_unused_3888_; 
v_unused_3885_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_3885_);
v_unused_3886_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_3886_);
v_unused_3887_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_3887_);
v_unused_3888_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_3888_);
v___x_3876_ = v_code_3572_;
v_isShared_3877_ = v_isSharedCheck_3884_;
goto v_resetjp_3875_;
}
else
{
lean_dec(v_code_3572_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3884_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 3, v_a_3868_);
lean_ctor_set(v___x_3876_, 2, v___x_3866_);
lean_ctor_set(v___x_3876_, 0, v_fvarId_3865_);
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_fvarId_3865_);
lean_ctor_set(v_reuseFailAlloc_3883_, 1, v_i_3861_);
lean_ctor_set(v_reuseFailAlloc_3883_, 2, v___x_3866_);
lean_ctor_set(v_reuseFailAlloc_3883_, 3, v_a_3868_);
v___x_3879_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
lean_object* v___x_3881_; 
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v___x_3879_);
v___x_3881_ = v___x_3870_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3879_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
}
else
{
uint8_t v___x_3889_; 
v___x_3889_ = lean_nat_dec_eq(v_i_3861_, v_i_3861_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3899_; 
lean_inc(v_i_3861_);
v_isSharedCheck_3899_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_3899_ == 0)
{
lean_object* v_unused_3900_; lean_object* v_unused_3901_; lean_object* v_unused_3902_; lean_object* v_unused_3903_; 
v_unused_3900_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_3900_);
v_unused_3901_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_3901_);
v_unused_3902_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_3902_);
v_unused_3903_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_3903_);
v___x_3891_ = v_code_3572_;
v_isShared_3892_ = v_isSharedCheck_3899_;
goto v_resetjp_3890_;
}
else
{
lean_dec(v_code_3572_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3899_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 3, v_a_3868_);
lean_ctor_set(v___x_3891_, 2, v___x_3866_);
lean_ctor_set(v___x_3891_, 0, v_fvarId_3865_);
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_fvarId_3865_);
lean_ctor_set(v_reuseFailAlloc_3898_, 1, v_i_3861_);
lean_ctor_set(v_reuseFailAlloc_3898_, 2, v___x_3866_);
lean_ctor_set(v_reuseFailAlloc_3898_, 3, v_a_3868_);
v___x_3894_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
lean_object* v___x_3896_; 
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v___x_3894_);
v___x_3896_ = v___x_3870_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3894_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
else
{
size_t v___x_3904_; size_t v___x_3905_; uint8_t v___x_3906_; 
v___x_3904_ = lean_ptr_addr(v_y_3862_);
v___x_3905_ = lean_ptr_addr(v___x_3866_);
v___x_3906_ = lean_usize_dec_eq(v___x_3904_, v___x_3905_);
if (v___x_3906_ == 0)
{
lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3916_; 
lean_inc(v_i_3861_);
v_isSharedCheck_3916_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_3916_ == 0)
{
lean_object* v_unused_3917_; lean_object* v_unused_3918_; lean_object* v_unused_3919_; lean_object* v_unused_3920_; 
v_unused_3917_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_3917_);
v_unused_3918_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_3918_);
v_unused_3919_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_3919_);
v_unused_3920_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_3920_);
v___x_3908_ = v_code_3572_;
v_isShared_3909_ = v_isSharedCheck_3916_;
goto v_resetjp_3907_;
}
else
{
lean_dec(v_code_3572_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3916_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 3, v_a_3868_);
lean_ctor_set(v___x_3908_, 2, v___x_3866_);
lean_ctor_set(v___x_3908_, 0, v_fvarId_3865_);
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_fvarId_3865_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v_i_3861_);
lean_ctor_set(v_reuseFailAlloc_3915_, 2, v___x_3866_);
lean_ctor_set(v_reuseFailAlloc_3915_, 3, v_a_3868_);
v___x_3911_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
lean_object* v___x_3913_; 
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v___x_3911_);
v___x_3913_ = v___x_3870_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
else
{
size_t v___x_3921_; size_t v___x_3922_; uint8_t v___x_3923_; 
v___x_3921_ = lean_ptr_addr(v_k_3863_);
v___x_3922_ = lean_ptr_addr(v_a_3868_);
v___x_3923_ = lean_usize_dec_eq(v___x_3921_, v___x_3922_);
if (v___x_3923_ == 0)
{
lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3933_; 
lean_inc(v_i_3861_);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_3933_ == 0)
{
lean_object* v_unused_3934_; lean_object* v_unused_3935_; lean_object* v_unused_3936_; lean_object* v_unused_3937_; 
v_unused_3934_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_3934_);
v_unused_3935_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_3935_);
v_unused_3936_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_3936_);
v_unused_3937_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_3937_);
v___x_3925_ = v_code_3572_;
v_isShared_3926_ = v_isSharedCheck_3933_;
goto v_resetjp_3924_;
}
else
{
lean_dec(v_code_3572_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3933_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 3, v_a_3868_);
lean_ctor_set(v___x_3925_, 2, v___x_3866_);
lean_ctor_set(v___x_3925_, 0, v_fvarId_3865_);
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_fvarId_3865_);
lean_ctor_set(v_reuseFailAlloc_3932_, 1, v_i_3861_);
lean_ctor_set(v_reuseFailAlloc_3932_, 2, v___x_3866_);
lean_ctor_set(v_reuseFailAlloc_3932_, 3, v_a_3868_);
v___x_3928_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3930_; 
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v___x_3928_);
v___x_3930_ = v___x_3870_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3928_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
else
{
lean_object* v___x_3939_; 
lean_dec(v_a_3868_);
lean_dec(v___x_3866_);
lean_dec(v_fvarId_3865_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v_code_3572_);
v___x_3939_ = v___x_3870_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_code_3572_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3866_);
lean_dec(v_fvarId_3865_);
lean_dec_ref_known(v_code_3572_, 4);
return v___x_3867_;
}
}
else
{
lean_object* v___x_3942_; 
lean_dec_ref_known(v_code_3572_, 4);
v___x_3942_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3570_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
return v___x_3942_;
}
}
case 8:
{
lean_object* v_fvarId_3943_; lean_object* v_i_3944_; lean_object* v_y_3945_; lean_object* v_k_3946_; lean_object* v___x_3947_; 
v_fvarId_3943_ = lean_ctor_get(v_code_3572_, 0);
v_i_3944_ = lean_ctor_get(v_code_3572_, 1);
v_y_3945_ = lean_ctor_get(v_code_3572_, 2);
v_k_3946_ = lean_ctor_get(v_code_3572_, 3);
lean_inc(v_fvarId_3943_);
v___x_3947_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3573_, v_fvarId_3943_, v_t_3571_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_fvarId_3948_; lean_object* v___x_3949_; 
v_fvarId_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc(v_fvarId_3948_);
lean_dec_ref_known(v___x_3947_, 1);
lean_inc(v_y_3945_);
v___x_3949_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3573_, v_y_3945_, v_t_3571_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v_fvarId_3950_; lean_object* v___x_3951_; 
v_fvarId_3950_ = lean_ctor_get(v___x_3949_, 0);
lean_inc(v_fvarId_3950_);
lean_dec_ref_known(v___x_3949_, 1);
lean_inc_ref(v_k_3946_);
v___x_3951_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3570_, v_t_3571_, v_k_3946_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_4025_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_3954_ = v___x_3951_;
v_isShared_3955_ = v_isSharedCheck_4025_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_a_3952_);
lean_dec(v___x_3951_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_4025_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
size_t v___x_3956_; size_t v___x_3957_; uint8_t v___x_3958_; 
v___x_3956_ = lean_ptr_addr(v_fvarId_3943_);
v___x_3957_ = lean_ptr_addr(v_fvarId_3948_);
v___x_3958_ = lean_usize_dec_eq(v___x_3956_, v___x_3957_);
if (v___x_3958_ == 0)
{
lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3968_; 
lean_inc(v_i_3944_);
v_isSharedCheck_3968_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_3968_ == 0)
{
lean_object* v_unused_3969_; lean_object* v_unused_3970_; lean_object* v_unused_3971_; lean_object* v_unused_3972_; 
v_unused_3969_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_3969_);
v_unused_3970_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_3970_);
v_unused_3971_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_3971_);
v_unused_3972_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_3972_);
v___x_3960_ = v_code_3572_;
v_isShared_3961_ = v_isSharedCheck_3968_;
goto v_resetjp_3959_;
}
else
{
lean_dec(v_code_3572_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3968_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3963_; 
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 3, v_a_3952_);
lean_ctor_set(v___x_3960_, 2, v_fvarId_3950_);
lean_ctor_set(v___x_3960_, 0, v_fvarId_3948_);
v___x_3963_ = v___x_3960_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_fvarId_3948_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_i_3944_);
lean_ctor_set(v_reuseFailAlloc_3967_, 2, v_fvarId_3950_);
lean_ctor_set(v_reuseFailAlloc_3967_, 3, v_a_3952_);
v___x_3963_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
lean_object* v___x_3965_; 
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 0, v___x_3963_);
v___x_3965_ = v___x_3954_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3963_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
else
{
uint8_t v___x_3973_; 
v___x_3973_ = lean_nat_dec_eq(v_i_3944_, v_i_3944_);
if (v___x_3973_ == 0)
{
lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3983_; 
lean_inc(v_i_3944_);
v_isSharedCheck_3983_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_3983_ == 0)
{
lean_object* v_unused_3984_; lean_object* v_unused_3985_; lean_object* v_unused_3986_; lean_object* v_unused_3987_; 
v_unused_3984_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_3984_);
v_unused_3985_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_3985_);
v_unused_3986_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_3986_);
v_unused_3987_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_3987_);
v___x_3975_ = v_code_3572_;
v_isShared_3976_ = v_isSharedCheck_3983_;
goto v_resetjp_3974_;
}
else
{
lean_dec(v_code_3572_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3983_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 3, v_a_3952_);
lean_ctor_set(v___x_3975_, 2, v_fvarId_3950_);
lean_ctor_set(v___x_3975_, 0, v_fvarId_3948_);
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_fvarId_3948_);
lean_ctor_set(v_reuseFailAlloc_3982_, 1, v_i_3944_);
lean_ctor_set(v_reuseFailAlloc_3982_, 2, v_fvarId_3950_);
lean_ctor_set(v_reuseFailAlloc_3982_, 3, v_a_3952_);
v___x_3978_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
lean_object* v___x_3980_; 
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 0, v___x_3978_);
v___x_3980_ = v___x_3954_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3978_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
else
{
size_t v___x_3988_; size_t v___x_3989_; uint8_t v___x_3990_; 
v___x_3988_ = lean_ptr_addr(v_y_3945_);
v___x_3989_ = lean_ptr_addr(v_fvarId_3950_);
v___x_3990_ = lean_usize_dec_eq(v___x_3988_, v___x_3989_);
if (v___x_3990_ == 0)
{
lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4000_; 
lean_inc(v_i_3944_);
v_isSharedCheck_4000_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4000_ == 0)
{
lean_object* v_unused_4001_; lean_object* v_unused_4002_; lean_object* v_unused_4003_; lean_object* v_unused_4004_; 
v_unused_4001_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_4001_);
v_unused_4002_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4002_);
v_unused_4003_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4003_);
v_unused_4004_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4004_);
v___x_3992_ = v_code_3572_;
v_isShared_3993_ = v_isSharedCheck_4000_;
goto v_resetjp_3991_;
}
else
{
lean_dec(v_code_3572_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4000_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 3, v_a_3952_);
lean_ctor_set(v___x_3992_, 2, v_fvarId_3950_);
lean_ctor_set(v___x_3992_, 0, v_fvarId_3948_);
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_fvarId_3948_);
lean_ctor_set(v_reuseFailAlloc_3999_, 1, v_i_3944_);
lean_ctor_set(v_reuseFailAlloc_3999_, 2, v_fvarId_3950_);
lean_ctor_set(v_reuseFailAlloc_3999_, 3, v_a_3952_);
v___x_3995_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
lean_object* v___x_3997_; 
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 0, v___x_3995_);
v___x_3997_ = v___x_3954_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3995_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
}
else
{
size_t v___x_4005_; size_t v___x_4006_; uint8_t v___x_4007_; 
v___x_4005_ = lean_ptr_addr(v_k_3946_);
v___x_4006_ = lean_ptr_addr(v_a_3952_);
v___x_4007_ = lean_usize_dec_eq(v___x_4005_, v___x_4006_);
if (v___x_4007_ == 0)
{
lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4017_; 
lean_inc(v_i_3944_);
v_isSharedCheck_4017_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4017_ == 0)
{
lean_object* v_unused_4018_; lean_object* v_unused_4019_; lean_object* v_unused_4020_; lean_object* v_unused_4021_; 
v_unused_4018_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_4018_);
v_unused_4019_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4019_);
v_unused_4020_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4020_);
v_unused_4021_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4021_);
v___x_4009_ = v_code_3572_;
v_isShared_4010_ = v_isSharedCheck_4017_;
goto v_resetjp_4008_;
}
else
{
lean_dec(v_code_3572_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4017_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 3, v_a_3952_);
lean_ctor_set(v___x_4009_, 2, v_fvarId_3950_);
lean_ctor_set(v___x_4009_, 0, v_fvarId_3948_);
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_fvarId_3948_);
lean_ctor_set(v_reuseFailAlloc_4016_, 1, v_i_3944_);
lean_ctor_set(v_reuseFailAlloc_4016_, 2, v_fvarId_3950_);
lean_ctor_set(v_reuseFailAlloc_4016_, 3, v_a_3952_);
v___x_4012_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
lean_object* v___x_4014_; 
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 0, v___x_4012_);
v___x_4014_ = v___x_3954_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4012_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
else
{
lean_object* v___x_4023_; 
lean_dec(v_a_3952_);
lean_dec(v_fvarId_3950_);
lean_dec(v_fvarId_3948_);
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 0, v_code_3572_);
v___x_4023_ = v___x_3954_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_code_3572_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_3950_);
lean_dec(v_fvarId_3948_);
lean_dec_ref_known(v_code_3572_, 4);
return v___x_3951_;
}
}
else
{
lean_object* v___x_4026_; 
lean_dec(v_fvarId_3948_);
lean_dec_ref_known(v_code_3572_, 4);
v___x_4026_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3570_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
return v___x_4026_;
}
}
else
{
lean_object* v___x_4027_; 
lean_dec_ref_known(v_code_3572_, 4);
v___x_4027_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3570_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
return v___x_4027_;
}
}
case 9:
{
lean_object* v_fvarId_4028_; lean_object* v_i_4029_; lean_object* v_offset_4030_; lean_object* v_y_4031_; lean_object* v_ty_4032_; lean_object* v_k_4033_; lean_object* v___x_4034_; 
v_fvarId_4028_ = lean_ctor_get(v_code_3572_, 0);
v_i_4029_ = lean_ctor_get(v_code_3572_, 1);
v_offset_4030_ = lean_ctor_get(v_code_3572_, 2);
v_y_4031_ = lean_ctor_get(v_code_3572_, 3);
v_ty_4032_ = lean_ctor_get(v_code_3572_, 4);
v_k_4033_ = lean_ctor_get(v_code_3572_, 5);
lean_inc(v_fvarId_4028_);
v___x_4034_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3573_, v_fvarId_4028_, v_t_3571_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_fvarId_4035_; lean_object* v___x_4036_; 
v_fvarId_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_fvarId_4035_);
lean_dec_ref_known(v___x_4034_, 1);
lean_inc(v_y_4031_);
v___x_4036_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3573_, v_y_4031_, v_t_3571_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_fvarId_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v_fvarId_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_fvarId_4037_);
lean_dec_ref_known(v___x_4036_, 1);
lean_inc_ref(v_ty_4032_);
v___x_4038_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_3570_, v_a_3573_, v_t_3571_, v_ty_4032_);
lean_inc_ref(v_k_4033_);
v___x_4039_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3570_, v_t_3571_, v_k_4033_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4157_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4042_ = v___x_4039_;
v_isShared_4043_ = v_isSharedCheck_4157_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_4039_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4157_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
size_t v___x_4044_; size_t v___x_4045_; uint8_t v___x_4046_; 
v___x_4044_ = lean_ptr_addr(v_fvarId_4028_);
v___x_4045_ = lean_ptr_addr(v_fvarId_4035_);
v___x_4046_ = lean_usize_dec_eq(v___x_4044_, v___x_4045_);
if (v___x_4046_ == 0)
{
lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4056_; 
lean_inc(v_offset_4030_);
lean_inc(v_i_4029_);
v_isSharedCheck_4056_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4056_ == 0)
{
lean_object* v_unused_4057_; lean_object* v_unused_4058_; lean_object* v_unused_4059_; lean_object* v_unused_4060_; lean_object* v_unused_4061_; lean_object* v_unused_4062_; 
v_unused_4057_ = lean_ctor_get(v_code_3572_, 5);
lean_dec(v_unused_4057_);
v_unused_4058_ = lean_ctor_get(v_code_3572_, 4);
lean_dec(v_unused_4058_);
v_unused_4059_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_4059_);
v_unused_4060_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4060_);
v_unused_4061_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4061_);
v_unused_4062_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4062_);
v___x_4048_ = v_code_3572_;
v_isShared_4049_ = v_isSharedCheck_4056_;
goto v_resetjp_4047_;
}
else
{
lean_dec(v_code_3572_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4056_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 5, v_a_4040_);
lean_ctor_set(v___x_4048_, 4, v___x_4038_);
lean_ctor_set(v___x_4048_, 3, v_fvarId_4037_);
lean_ctor_set(v___x_4048_, 0, v_fvarId_4035_);
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_fvarId_4035_);
lean_ctor_set(v_reuseFailAlloc_4055_, 1, v_i_4029_);
lean_ctor_set(v_reuseFailAlloc_4055_, 2, v_offset_4030_);
lean_ctor_set(v_reuseFailAlloc_4055_, 3, v_fvarId_4037_);
lean_ctor_set(v_reuseFailAlloc_4055_, 4, v___x_4038_);
lean_ctor_set(v_reuseFailAlloc_4055_, 5, v_a_4040_);
v___x_4051_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
lean_object* v___x_4053_; 
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 0, v___x_4051_);
v___x_4053_ = v___x_4042_;
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
uint8_t v___x_4063_; 
v___x_4063_ = lean_nat_dec_eq(v_i_4029_, v_i_4029_);
if (v___x_4063_ == 0)
{
lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4073_; 
lean_inc(v_offset_4030_);
lean_inc(v_i_4029_);
v_isSharedCheck_4073_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4073_ == 0)
{
lean_object* v_unused_4074_; lean_object* v_unused_4075_; lean_object* v_unused_4076_; lean_object* v_unused_4077_; lean_object* v_unused_4078_; lean_object* v_unused_4079_; 
v_unused_4074_ = lean_ctor_get(v_code_3572_, 5);
lean_dec(v_unused_4074_);
v_unused_4075_ = lean_ctor_get(v_code_3572_, 4);
lean_dec(v_unused_4075_);
v_unused_4076_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_4076_);
v_unused_4077_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4077_);
v_unused_4078_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4078_);
v_unused_4079_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4079_);
v___x_4065_ = v_code_3572_;
v_isShared_4066_ = v_isSharedCheck_4073_;
goto v_resetjp_4064_;
}
else
{
lean_dec(v_code_3572_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4073_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
lean_ctor_set(v___x_4065_, 5, v_a_4040_);
lean_ctor_set(v___x_4065_, 4, v___x_4038_);
lean_ctor_set(v___x_4065_, 3, v_fvarId_4037_);
lean_ctor_set(v___x_4065_, 0, v_fvarId_4035_);
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_fvarId_4035_);
lean_ctor_set(v_reuseFailAlloc_4072_, 1, v_i_4029_);
lean_ctor_set(v_reuseFailAlloc_4072_, 2, v_offset_4030_);
lean_ctor_set(v_reuseFailAlloc_4072_, 3, v_fvarId_4037_);
lean_ctor_set(v_reuseFailAlloc_4072_, 4, v___x_4038_);
lean_ctor_set(v_reuseFailAlloc_4072_, 5, v_a_4040_);
v___x_4068_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
lean_object* v___x_4070_; 
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 0, v___x_4068_);
v___x_4070_ = v___x_4042_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4068_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
else
{
uint8_t v___x_4080_; 
v___x_4080_ = lean_nat_dec_eq(v_offset_4030_, v_offset_4030_);
if (v___x_4080_ == 0)
{
lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4090_; 
lean_inc(v_offset_4030_);
lean_inc(v_i_4029_);
v_isSharedCheck_4090_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4090_ == 0)
{
lean_object* v_unused_4091_; lean_object* v_unused_4092_; lean_object* v_unused_4093_; lean_object* v_unused_4094_; lean_object* v_unused_4095_; lean_object* v_unused_4096_; 
v_unused_4091_ = lean_ctor_get(v_code_3572_, 5);
lean_dec(v_unused_4091_);
v_unused_4092_ = lean_ctor_get(v_code_3572_, 4);
lean_dec(v_unused_4092_);
v_unused_4093_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_4093_);
v_unused_4094_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4094_);
v_unused_4095_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4095_);
v_unused_4096_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4096_);
v___x_4082_ = v_code_3572_;
v_isShared_4083_ = v_isSharedCheck_4090_;
goto v_resetjp_4081_;
}
else
{
lean_dec(v_code_3572_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4090_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4085_; 
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 5, v_a_4040_);
lean_ctor_set(v___x_4082_, 4, v___x_4038_);
lean_ctor_set(v___x_4082_, 3, v_fvarId_4037_);
lean_ctor_set(v___x_4082_, 0, v_fvarId_4035_);
v___x_4085_ = v___x_4082_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_fvarId_4035_);
lean_ctor_set(v_reuseFailAlloc_4089_, 1, v_i_4029_);
lean_ctor_set(v_reuseFailAlloc_4089_, 2, v_offset_4030_);
lean_ctor_set(v_reuseFailAlloc_4089_, 3, v_fvarId_4037_);
lean_ctor_set(v_reuseFailAlloc_4089_, 4, v___x_4038_);
lean_ctor_set(v_reuseFailAlloc_4089_, 5, v_a_4040_);
v___x_4085_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
lean_object* v___x_4087_; 
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 0, v___x_4085_);
v___x_4087_ = v___x_4042_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4085_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
else
{
size_t v___x_4097_; size_t v___x_4098_; uint8_t v___x_4099_; 
v___x_4097_ = lean_ptr_addr(v_y_4031_);
v___x_4098_ = lean_ptr_addr(v_fvarId_4037_);
v___x_4099_ = lean_usize_dec_eq(v___x_4097_, v___x_4098_);
if (v___x_4099_ == 0)
{
lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4109_; 
lean_inc(v_offset_4030_);
lean_inc(v_i_4029_);
v_isSharedCheck_4109_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4109_ == 0)
{
lean_object* v_unused_4110_; lean_object* v_unused_4111_; lean_object* v_unused_4112_; lean_object* v_unused_4113_; lean_object* v_unused_4114_; lean_object* v_unused_4115_; 
v_unused_4110_ = lean_ctor_get(v_code_3572_, 5);
lean_dec(v_unused_4110_);
v_unused_4111_ = lean_ctor_get(v_code_3572_, 4);
lean_dec(v_unused_4111_);
v_unused_4112_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_4112_);
v_unused_4113_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4113_);
v_unused_4114_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4114_);
v_unused_4115_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4115_);
v___x_4101_ = v_code_3572_;
v_isShared_4102_ = v_isSharedCheck_4109_;
goto v_resetjp_4100_;
}
else
{
lean_dec(v_code_3572_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4109_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 5, v_a_4040_);
lean_ctor_set(v___x_4101_, 4, v___x_4038_);
lean_ctor_set(v___x_4101_, 3, v_fvarId_4037_);
lean_ctor_set(v___x_4101_, 0, v_fvarId_4035_);
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_fvarId_4035_);
lean_ctor_set(v_reuseFailAlloc_4108_, 1, v_i_4029_);
lean_ctor_set(v_reuseFailAlloc_4108_, 2, v_offset_4030_);
lean_ctor_set(v_reuseFailAlloc_4108_, 3, v_fvarId_4037_);
lean_ctor_set(v_reuseFailAlloc_4108_, 4, v___x_4038_);
lean_ctor_set(v_reuseFailAlloc_4108_, 5, v_a_4040_);
v___x_4104_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
lean_object* v___x_4106_; 
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 0, v___x_4104_);
v___x_4106_ = v___x_4042_;
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
size_t v___x_4116_; size_t v___x_4117_; uint8_t v___x_4118_; 
v___x_4116_ = lean_ptr_addr(v_ty_4032_);
v___x_4117_ = lean_ptr_addr(v___x_4038_);
v___x_4118_ = lean_usize_dec_eq(v___x_4116_, v___x_4117_);
if (v___x_4118_ == 0)
{
lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4128_; 
lean_inc(v_offset_4030_);
lean_inc(v_i_4029_);
v_isSharedCheck_4128_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4128_ == 0)
{
lean_object* v_unused_4129_; lean_object* v_unused_4130_; lean_object* v_unused_4131_; lean_object* v_unused_4132_; lean_object* v_unused_4133_; lean_object* v_unused_4134_; 
v_unused_4129_ = lean_ctor_get(v_code_3572_, 5);
lean_dec(v_unused_4129_);
v_unused_4130_ = lean_ctor_get(v_code_3572_, 4);
lean_dec(v_unused_4130_);
v_unused_4131_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_4131_);
v_unused_4132_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4132_);
v_unused_4133_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4133_);
v_unused_4134_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4134_);
v___x_4120_ = v_code_3572_;
v_isShared_4121_ = v_isSharedCheck_4128_;
goto v_resetjp_4119_;
}
else
{
lean_dec(v_code_3572_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4128_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 5, v_a_4040_);
lean_ctor_set(v___x_4120_, 4, v___x_4038_);
lean_ctor_set(v___x_4120_, 3, v_fvarId_4037_);
lean_ctor_set(v___x_4120_, 0, v_fvarId_4035_);
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_fvarId_4035_);
lean_ctor_set(v_reuseFailAlloc_4127_, 1, v_i_4029_);
lean_ctor_set(v_reuseFailAlloc_4127_, 2, v_offset_4030_);
lean_ctor_set(v_reuseFailAlloc_4127_, 3, v_fvarId_4037_);
lean_ctor_set(v_reuseFailAlloc_4127_, 4, v___x_4038_);
lean_ctor_set(v_reuseFailAlloc_4127_, 5, v_a_4040_);
v___x_4123_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
lean_object* v___x_4125_; 
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 0, v___x_4123_);
v___x_4125_ = v___x_4042_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4123_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
else
{
size_t v___x_4135_; size_t v___x_4136_; uint8_t v___x_4137_; 
v___x_4135_ = lean_ptr_addr(v_k_4033_);
v___x_4136_ = lean_ptr_addr(v_a_4040_);
v___x_4137_ = lean_usize_dec_eq(v___x_4135_, v___x_4136_);
if (v___x_4137_ == 0)
{
lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4147_; 
lean_inc(v_offset_4030_);
lean_inc(v_i_4029_);
v_isSharedCheck_4147_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4147_ == 0)
{
lean_object* v_unused_4148_; lean_object* v_unused_4149_; lean_object* v_unused_4150_; lean_object* v_unused_4151_; lean_object* v_unused_4152_; lean_object* v_unused_4153_; 
v_unused_4148_ = lean_ctor_get(v_code_3572_, 5);
lean_dec(v_unused_4148_);
v_unused_4149_ = lean_ctor_get(v_code_3572_, 4);
lean_dec(v_unused_4149_);
v_unused_4150_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_4150_);
v_unused_4151_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4151_);
v_unused_4152_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4152_);
v_unused_4153_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4153_);
v___x_4139_ = v_code_3572_;
v_isShared_4140_ = v_isSharedCheck_4147_;
goto v_resetjp_4138_;
}
else
{
lean_dec(v_code_3572_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4147_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 5, v_a_4040_);
lean_ctor_set(v___x_4139_, 4, v___x_4038_);
lean_ctor_set(v___x_4139_, 3, v_fvarId_4037_);
lean_ctor_set(v___x_4139_, 0, v_fvarId_4035_);
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_fvarId_4035_);
lean_ctor_set(v_reuseFailAlloc_4146_, 1, v_i_4029_);
lean_ctor_set(v_reuseFailAlloc_4146_, 2, v_offset_4030_);
lean_ctor_set(v_reuseFailAlloc_4146_, 3, v_fvarId_4037_);
lean_ctor_set(v_reuseFailAlloc_4146_, 4, v___x_4038_);
lean_ctor_set(v_reuseFailAlloc_4146_, 5, v_a_4040_);
v___x_4142_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
lean_object* v___x_4144_; 
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 0, v___x_4142_);
v___x_4144_ = v___x_4042_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v___x_4142_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
else
{
lean_object* v___x_4155_; 
lean_dec(v_a_4040_);
lean_dec_ref(v___x_4038_);
lean_dec(v_fvarId_4037_);
lean_dec(v_fvarId_4035_);
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 0, v_code_3572_);
v___x_4155_ = v___x_4042_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_code_3572_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
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
lean_dec_ref(v___x_4038_);
lean_dec(v_fvarId_4037_);
lean_dec(v_fvarId_4035_);
lean_dec_ref_known(v_code_3572_, 6);
return v___x_4039_;
}
}
else
{
lean_object* v___x_4158_; 
lean_dec(v_fvarId_4035_);
lean_dec_ref_known(v_code_3572_, 6);
v___x_4158_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3570_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
return v___x_4158_;
}
}
else
{
lean_object* v___x_4159_; 
lean_dec_ref_known(v_code_3572_, 6);
v___x_4159_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3570_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
return v___x_4159_;
}
}
case 10:
{
lean_object* v_fvarId_4160_; lean_object* v_cidx_4161_; lean_object* v_k_4162_; lean_object* v___x_4163_; 
v_fvarId_4160_ = lean_ctor_get(v_code_3572_, 0);
v_cidx_4161_ = lean_ctor_get(v_code_3572_, 1);
v_k_4162_ = lean_ctor_get(v_code_3572_, 2);
lean_inc(v_fvarId_4160_);
v___x_4163_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3573_, v_fvarId_4160_, v_t_3571_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_object* v_fvarId_4164_; lean_object* v___x_4165_; 
v_fvarId_4164_ = lean_ctor_get(v___x_4163_, 0);
lean_inc(v_fvarId_4164_);
lean_dec_ref_known(v___x_4163_, 1);
lean_inc_ref(v_k_4162_);
v___x_4165_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3570_, v_t_3571_, v_k_4162_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4219_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4168_ = v___x_4165_;
v_isShared_4169_ = v_isSharedCheck_4219_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4165_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4219_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
size_t v___x_4170_; size_t v___x_4171_; uint8_t v___x_4172_; 
v___x_4170_ = lean_ptr_addr(v_fvarId_4160_);
v___x_4171_ = lean_ptr_addr(v_fvarId_4164_);
v___x_4172_ = lean_usize_dec_eq(v___x_4170_, v___x_4171_);
if (v___x_4172_ == 0)
{
lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4182_; 
lean_inc(v_cidx_4161_);
v_isSharedCheck_4182_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4182_ == 0)
{
lean_object* v_unused_4183_; lean_object* v_unused_4184_; lean_object* v_unused_4185_; 
v_unused_4183_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4183_);
v_unused_4184_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4184_);
v_unused_4185_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4185_);
v___x_4174_ = v_code_3572_;
v_isShared_4175_ = v_isSharedCheck_4182_;
goto v_resetjp_4173_;
}
else
{
lean_dec(v_code_3572_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4182_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4177_; 
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 2, v_a_4166_);
lean_ctor_set(v___x_4174_, 0, v_fvarId_4164_);
v___x_4177_ = v___x_4174_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_fvarId_4164_);
lean_ctor_set(v_reuseFailAlloc_4181_, 1, v_cidx_4161_);
lean_ctor_set(v_reuseFailAlloc_4181_, 2, v_a_4166_);
v___x_4177_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
lean_object* v___x_4179_; 
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 0, v___x_4177_);
v___x_4179_ = v___x_4168_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4177_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
}
else
{
uint8_t v___x_4186_; 
v___x_4186_ = lean_nat_dec_eq(v_cidx_4161_, v_cidx_4161_);
if (v___x_4186_ == 0)
{
lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4196_; 
lean_inc(v_cidx_4161_);
v_isSharedCheck_4196_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4196_ == 0)
{
lean_object* v_unused_4197_; lean_object* v_unused_4198_; lean_object* v_unused_4199_; 
v_unused_4197_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4197_);
v_unused_4198_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4198_);
v_unused_4199_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4199_);
v___x_4188_ = v_code_3572_;
v_isShared_4189_ = v_isSharedCheck_4196_;
goto v_resetjp_4187_;
}
else
{
lean_dec(v_code_3572_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4196_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 2, v_a_4166_);
lean_ctor_set(v___x_4188_, 0, v_fvarId_4164_);
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_fvarId_4164_);
lean_ctor_set(v_reuseFailAlloc_4195_, 1, v_cidx_4161_);
lean_ctor_set(v_reuseFailAlloc_4195_, 2, v_a_4166_);
v___x_4191_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
lean_object* v___x_4193_; 
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 0, v___x_4191_);
v___x_4193_ = v___x_4168_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___x_4191_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
}
}
else
{
size_t v___x_4200_; size_t v___x_4201_; uint8_t v___x_4202_; 
v___x_4200_ = lean_ptr_addr(v_k_4162_);
v___x_4201_ = lean_ptr_addr(v_a_4166_);
v___x_4202_ = lean_usize_dec_eq(v___x_4200_, v___x_4201_);
if (v___x_4202_ == 0)
{
lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4212_; 
lean_inc(v_cidx_4161_);
v_isSharedCheck_4212_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4212_ == 0)
{
lean_object* v_unused_4213_; lean_object* v_unused_4214_; lean_object* v_unused_4215_; 
v_unused_4213_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4213_);
v_unused_4214_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4214_);
v_unused_4215_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4215_);
v___x_4204_ = v_code_3572_;
v_isShared_4205_ = v_isSharedCheck_4212_;
goto v_resetjp_4203_;
}
else
{
lean_dec(v_code_3572_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4212_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
lean_ctor_set(v___x_4204_, 2, v_a_4166_);
lean_ctor_set(v___x_4204_, 0, v_fvarId_4164_);
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_fvarId_4164_);
lean_ctor_set(v_reuseFailAlloc_4211_, 1, v_cidx_4161_);
lean_ctor_set(v_reuseFailAlloc_4211_, 2, v_a_4166_);
v___x_4207_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
lean_object* v___x_4209_; 
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 0, v___x_4207_);
v___x_4209_ = v___x_4168_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v___x_4207_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
}
else
{
lean_object* v___x_4217_; 
lean_dec(v_a_4166_);
lean_dec(v_fvarId_4164_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 0, v_code_3572_);
v___x_4217_ = v___x_4168_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_code_3572_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4164_);
lean_dec_ref_known(v_code_3572_, 3);
return v___x_4165_;
}
}
else
{
lean_object* v___x_4220_; 
lean_dec_ref_known(v_code_3572_, 3);
v___x_4220_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3570_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
return v___x_4220_;
}
}
case 11:
{
lean_object* v_fvarId_4221_; lean_object* v_n_4222_; uint8_t v_check_4223_; uint8_t v_persistent_4224_; lean_object* v_k_4225_; lean_object* v___x_4226_; 
v_fvarId_4221_ = lean_ctor_get(v_code_3572_, 0);
v_n_4222_ = lean_ctor_get(v_code_3572_, 1);
v_check_4223_ = lean_ctor_get_uint8(v_code_3572_, sizeof(void*)*3);
v_persistent_4224_ = lean_ctor_get_uint8(v_code_3572_, sizeof(void*)*3 + 1);
v_k_4225_ = lean_ctor_get(v_code_3572_, 2);
lean_inc(v_fvarId_4221_);
v___x_4226_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3573_, v_fvarId_4221_, v_t_3571_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v_fvarId_4227_; lean_object* v___x_4228_; 
v_fvarId_4227_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_fvarId_4227_);
lean_dec_ref_known(v___x_4226_, 1);
lean_inc_ref(v_k_4225_);
v___x_4228_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3570_, v_t_3571_, v_k_4225_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_4228_) == 0)
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4282_; 
v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4231_ = v___x_4228_;
v_isShared_4232_ = v_isSharedCheck_4282_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4228_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4282_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
size_t v___x_4233_; size_t v___x_4234_; uint8_t v___x_4235_; 
v___x_4233_ = lean_ptr_addr(v_fvarId_4221_);
v___x_4234_ = lean_ptr_addr(v_fvarId_4227_);
v___x_4235_ = lean_usize_dec_eq(v___x_4233_, v___x_4234_);
if (v___x_4235_ == 0)
{
lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4245_; 
lean_inc(v_n_4222_);
v_isSharedCheck_4245_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4245_ == 0)
{
lean_object* v_unused_4246_; lean_object* v_unused_4247_; lean_object* v_unused_4248_; 
v_unused_4246_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4246_);
v_unused_4247_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4247_);
v_unused_4248_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4248_);
v___x_4237_ = v_code_3572_;
v_isShared_4238_ = v_isSharedCheck_4245_;
goto v_resetjp_4236_;
}
else
{
lean_dec(v_code_3572_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4245_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
lean_ctor_set(v___x_4237_, 2, v_a_4229_);
lean_ctor_set(v___x_4237_, 0, v_fvarId_4227_);
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_fvarId_4227_);
lean_ctor_set(v_reuseFailAlloc_4244_, 1, v_n_4222_);
lean_ctor_set(v_reuseFailAlloc_4244_, 2, v_a_4229_);
lean_ctor_set_uint8(v_reuseFailAlloc_4244_, sizeof(void*)*3, v_check_4223_);
lean_ctor_set_uint8(v_reuseFailAlloc_4244_, sizeof(void*)*3 + 1, v_persistent_4224_);
v___x_4240_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
lean_object* v___x_4242_; 
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 0, v___x_4240_);
v___x_4242_ = v___x_4231_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4240_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
else
{
uint8_t v___x_4249_; 
v___x_4249_ = lean_nat_dec_eq(v_n_4222_, v_n_4222_);
if (v___x_4249_ == 0)
{
lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4259_; 
lean_inc(v_n_4222_);
v_isSharedCheck_4259_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4259_ == 0)
{
lean_object* v_unused_4260_; lean_object* v_unused_4261_; lean_object* v_unused_4262_; 
v_unused_4260_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4260_);
v_unused_4261_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4261_);
v_unused_4262_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4262_);
v___x_4251_ = v_code_3572_;
v_isShared_4252_ = v_isSharedCheck_4259_;
goto v_resetjp_4250_;
}
else
{
lean_dec(v_code_3572_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4259_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 2, v_a_4229_);
lean_ctor_set(v___x_4251_, 0, v_fvarId_4227_);
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_fvarId_4227_);
lean_ctor_set(v_reuseFailAlloc_4258_, 1, v_n_4222_);
lean_ctor_set(v_reuseFailAlloc_4258_, 2, v_a_4229_);
lean_ctor_set_uint8(v_reuseFailAlloc_4258_, sizeof(void*)*3, v_check_4223_);
lean_ctor_set_uint8(v_reuseFailAlloc_4258_, sizeof(void*)*3 + 1, v_persistent_4224_);
v___x_4254_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
lean_object* v___x_4256_; 
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 0, v___x_4254_);
v___x_4256_ = v___x_4231_;
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
size_t v___x_4263_; size_t v___x_4264_; uint8_t v___x_4265_; 
v___x_4263_ = lean_ptr_addr(v_k_4225_);
v___x_4264_ = lean_ptr_addr(v_a_4229_);
v___x_4265_ = lean_usize_dec_eq(v___x_4263_, v___x_4264_);
if (v___x_4265_ == 0)
{
lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4275_; 
lean_inc(v_n_4222_);
v_isSharedCheck_4275_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4275_ == 0)
{
lean_object* v_unused_4276_; lean_object* v_unused_4277_; lean_object* v_unused_4278_; 
v_unused_4276_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4276_);
v_unused_4277_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4277_);
v_unused_4278_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4278_);
v___x_4267_ = v_code_3572_;
v_isShared_4268_ = v_isSharedCheck_4275_;
goto v_resetjp_4266_;
}
else
{
lean_dec(v_code_3572_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4275_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4270_; 
if (v_isShared_4268_ == 0)
{
lean_ctor_set(v___x_4267_, 2, v_a_4229_);
lean_ctor_set(v___x_4267_, 0, v_fvarId_4227_);
v___x_4270_ = v___x_4267_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_fvarId_4227_);
lean_ctor_set(v_reuseFailAlloc_4274_, 1, v_n_4222_);
lean_ctor_set(v_reuseFailAlloc_4274_, 2, v_a_4229_);
lean_ctor_set_uint8(v_reuseFailAlloc_4274_, sizeof(void*)*3, v_check_4223_);
lean_ctor_set_uint8(v_reuseFailAlloc_4274_, sizeof(void*)*3 + 1, v_persistent_4224_);
v___x_4270_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
lean_object* v___x_4272_; 
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 0, v___x_4270_);
v___x_4272_ = v___x_4231_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v___x_4270_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
else
{
lean_object* v___x_4280_; 
lean_dec(v_a_4229_);
lean_dec(v_fvarId_4227_);
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 0, v_code_3572_);
v___x_4280_ = v___x_4231_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_code_3572_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4227_);
lean_dec_ref_known(v_code_3572_, 3);
return v___x_4228_;
}
}
else
{
lean_object* v___x_4283_; 
lean_dec_ref_known(v_code_3572_, 3);
v___x_4283_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3570_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
return v___x_4283_;
}
}
case 12:
{
lean_object* v_fvarId_4284_; lean_object* v_n_4285_; uint8_t v_check_4286_; uint8_t v_persistent_4287_; lean_object* v_objs_x3f_4288_; lean_object* v_k_4289_; lean_object* v___x_4290_; 
v_fvarId_4284_ = lean_ctor_get(v_code_3572_, 0);
v_n_4285_ = lean_ctor_get(v_code_3572_, 1);
v_check_4286_ = lean_ctor_get_uint8(v_code_3572_, sizeof(void*)*4);
v_persistent_4287_ = lean_ctor_get_uint8(v_code_3572_, sizeof(void*)*4 + 1);
v_objs_x3f_4288_ = lean_ctor_get(v_code_3572_, 2);
v_k_4289_ = lean_ctor_get(v_code_3572_, 3);
lean_inc(v_fvarId_4284_);
v___x_4290_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3573_, v_fvarId_4284_, v_t_3571_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_fvarId_4291_; lean_object* v___x_4292_; 
v_fvarId_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_fvarId_4291_);
lean_dec_ref_known(v___x_4290_, 1);
lean_inc_ref(v_k_4289_);
v___x_4292_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3570_, v_t_3571_, v_k_4289_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_4292_) == 0)
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4365_; 
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4295_ = v___x_4292_;
v_isShared_4296_ = v_isSharedCheck_4365_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4292_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4365_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
size_t v___x_4297_; size_t v___x_4298_; uint8_t v___x_4299_; 
v___x_4297_ = lean_ptr_addr(v_fvarId_4284_);
v___x_4298_ = lean_ptr_addr(v_fvarId_4291_);
v___x_4299_ = lean_usize_dec_eq(v___x_4297_, v___x_4298_);
if (v___x_4299_ == 0)
{
lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4309_; 
lean_inc(v_objs_x3f_4288_);
lean_inc(v_n_4285_);
v_isSharedCheck_4309_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4309_ == 0)
{
lean_object* v_unused_4310_; lean_object* v_unused_4311_; lean_object* v_unused_4312_; lean_object* v_unused_4313_; 
v_unused_4310_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_4310_);
v_unused_4311_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4311_);
v_unused_4312_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4312_);
v_unused_4313_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4313_);
v___x_4301_ = v_code_3572_;
v_isShared_4302_ = v_isSharedCheck_4309_;
goto v_resetjp_4300_;
}
else
{
lean_dec(v_code_3572_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4309_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4302_ == 0)
{
lean_ctor_set(v___x_4301_, 3, v_a_4293_);
lean_ctor_set(v___x_4301_, 0, v_fvarId_4291_);
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_fvarId_4291_);
lean_ctor_set(v_reuseFailAlloc_4308_, 1, v_n_4285_);
lean_ctor_set(v_reuseFailAlloc_4308_, 2, v_objs_x3f_4288_);
lean_ctor_set(v_reuseFailAlloc_4308_, 3, v_a_4293_);
lean_ctor_set_uint8(v_reuseFailAlloc_4308_, sizeof(void*)*4, v_check_4286_);
lean_ctor_set_uint8(v_reuseFailAlloc_4308_, sizeof(void*)*4 + 1, v_persistent_4287_);
v___x_4304_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
lean_object* v___x_4306_; 
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 0, v___x_4304_);
v___x_4306_ = v___x_4295_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4304_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
}
else
{
uint8_t v___x_4314_; 
v___x_4314_ = lean_nat_dec_eq(v_n_4285_, v_n_4285_);
if (v___x_4314_ == 0)
{
lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4324_; 
lean_inc(v_objs_x3f_4288_);
lean_inc(v_n_4285_);
v_isSharedCheck_4324_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4324_ == 0)
{
lean_object* v_unused_4325_; lean_object* v_unused_4326_; lean_object* v_unused_4327_; lean_object* v_unused_4328_; 
v_unused_4325_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_4325_);
v_unused_4326_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4326_);
v_unused_4327_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4327_);
v_unused_4328_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4328_);
v___x_4316_ = v_code_3572_;
v_isShared_4317_ = v_isSharedCheck_4324_;
goto v_resetjp_4315_;
}
else
{
lean_dec(v_code_3572_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4324_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
lean_ctor_set(v___x_4316_, 3, v_a_4293_);
lean_ctor_set(v___x_4316_, 0, v_fvarId_4291_);
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v_fvarId_4291_);
lean_ctor_set(v_reuseFailAlloc_4323_, 1, v_n_4285_);
lean_ctor_set(v_reuseFailAlloc_4323_, 2, v_objs_x3f_4288_);
lean_ctor_set(v_reuseFailAlloc_4323_, 3, v_a_4293_);
lean_ctor_set_uint8(v_reuseFailAlloc_4323_, sizeof(void*)*4, v_check_4286_);
lean_ctor_set_uint8(v_reuseFailAlloc_4323_, sizeof(void*)*4 + 1, v_persistent_4287_);
v___x_4319_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
lean_object* v___x_4321_; 
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 0, v___x_4319_);
v___x_4321_ = v___x_4295_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4319_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
}
else
{
size_t v___x_4329_; uint8_t v___x_4330_; 
v___x_4329_ = lean_ptr_addr(v_objs_x3f_4288_);
v___x_4330_ = lean_usize_dec_eq(v___x_4329_, v___x_4329_);
if (v___x_4330_ == 0)
{
lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4340_; 
lean_inc(v_objs_x3f_4288_);
lean_inc(v_n_4285_);
v_isSharedCheck_4340_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4340_ == 0)
{
lean_object* v_unused_4341_; lean_object* v_unused_4342_; lean_object* v_unused_4343_; lean_object* v_unused_4344_; 
v_unused_4341_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_4341_);
v_unused_4342_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4342_);
v_unused_4343_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4343_);
v_unused_4344_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4344_);
v___x_4332_ = v_code_3572_;
v_isShared_4333_ = v_isSharedCheck_4340_;
goto v_resetjp_4331_;
}
else
{
lean_dec(v_code_3572_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4340_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v___x_4335_; 
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 3, v_a_4293_);
lean_ctor_set(v___x_4332_, 0, v_fvarId_4291_);
v___x_4335_ = v___x_4332_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_fvarId_4291_);
lean_ctor_set(v_reuseFailAlloc_4339_, 1, v_n_4285_);
lean_ctor_set(v_reuseFailAlloc_4339_, 2, v_objs_x3f_4288_);
lean_ctor_set(v_reuseFailAlloc_4339_, 3, v_a_4293_);
lean_ctor_set_uint8(v_reuseFailAlloc_4339_, sizeof(void*)*4, v_check_4286_);
lean_ctor_set_uint8(v_reuseFailAlloc_4339_, sizeof(void*)*4 + 1, v_persistent_4287_);
v___x_4335_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
lean_object* v___x_4337_; 
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 0, v___x_4335_);
v___x_4337_ = v___x_4295_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v___x_4335_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
}
}
else
{
size_t v___x_4345_; size_t v___x_4346_; uint8_t v___x_4347_; 
v___x_4345_ = lean_ptr_addr(v_k_4289_);
v___x_4346_ = lean_ptr_addr(v_a_4293_);
v___x_4347_ = lean_usize_dec_eq(v___x_4345_, v___x_4346_);
if (v___x_4347_ == 0)
{
lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4357_; 
lean_inc(v_objs_x3f_4288_);
lean_inc(v_n_4285_);
v_isSharedCheck_4357_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4357_ == 0)
{
lean_object* v_unused_4358_; lean_object* v_unused_4359_; lean_object* v_unused_4360_; lean_object* v_unused_4361_; 
v_unused_4358_ = lean_ctor_get(v_code_3572_, 3);
lean_dec(v_unused_4358_);
v_unused_4359_ = lean_ctor_get(v_code_3572_, 2);
lean_dec(v_unused_4359_);
v_unused_4360_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4360_);
v_unused_4361_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4361_);
v___x_4349_ = v_code_3572_;
v_isShared_4350_ = v_isSharedCheck_4357_;
goto v_resetjp_4348_;
}
else
{
lean_dec(v_code_3572_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4357_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
lean_ctor_set(v___x_4349_, 3, v_a_4293_);
lean_ctor_set(v___x_4349_, 0, v_fvarId_4291_);
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_fvarId_4291_);
lean_ctor_set(v_reuseFailAlloc_4356_, 1, v_n_4285_);
lean_ctor_set(v_reuseFailAlloc_4356_, 2, v_objs_x3f_4288_);
lean_ctor_set(v_reuseFailAlloc_4356_, 3, v_a_4293_);
lean_ctor_set_uint8(v_reuseFailAlloc_4356_, sizeof(void*)*4, v_check_4286_);
lean_ctor_set_uint8(v_reuseFailAlloc_4356_, sizeof(void*)*4 + 1, v_persistent_4287_);
v___x_4352_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
lean_object* v___x_4354_; 
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 0, v___x_4352_);
v___x_4354_ = v___x_4295_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v___x_4352_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
}
}
else
{
lean_object* v___x_4363_; 
lean_dec(v_a_4293_);
lean_dec(v_fvarId_4291_);
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 0, v_code_3572_);
v___x_4363_ = v___x_4295_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_code_3572_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_4291_);
lean_dec_ref_known(v_code_3572_, 4);
return v___x_4292_;
}
}
else
{
lean_object* v___x_4366_; 
lean_dec_ref_known(v_code_3572_, 4);
v___x_4366_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3570_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
return v___x_4366_;
}
}
default: 
{
lean_object* v_fvarId_4367_; lean_object* v_k_4368_; lean_object* v___x_4369_; 
v_fvarId_4367_ = lean_ctor_get(v_code_3572_, 0);
v_k_4368_ = lean_ctor_get(v_code_3572_, 1);
lean_inc(v_fvarId_4367_);
v___x_4369_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_3573_, v_fvarId_4367_, v_t_3571_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v_fvarId_4370_; lean_object* v___x_4371_; 
v_fvarId_4370_ = lean_ctor_get(v___x_4369_, 0);
lean_inc(v_fvarId_4370_);
lean_dec_ref_known(v___x_4369_, 1);
lean_inc_ref(v_k_4368_);
v___x_4371_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3570_, v_t_3571_, v_k_4368_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_4371_) == 0)
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4409_; 
v_a_4372_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4374_ = v___x_4371_;
v_isShared_4375_ = v_isSharedCheck_4409_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4371_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4409_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
size_t v___x_4376_; size_t v___x_4377_; uint8_t v___x_4378_; 
v___x_4376_ = lean_ptr_addr(v_fvarId_4367_);
v___x_4377_ = lean_ptr_addr(v_fvarId_4370_);
v___x_4378_ = lean_usize_dec_eq(v___x_4376_, v___x_4377_);
if (v___x_4378_ == 0)
{
lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4388_; 
v_isSharedCheck_4388_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4388_ == 0)
{
lean_object* v_unused_4389_; lean_object* v_unused_4390_; 
v_unused_4389_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4389_);
v_unused_4390_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4390_);
v___x_4380_ = v_code_3572_;
v_isShared_4381_ = v_isSharedCheck_4388_;
goto v_resetjp_4379_;
}
else
{
lean_dec(v_code_3572_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4388_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4383_; 
if (v_isShared_4381_ == 0)
{
lean_ctor_set(v___x_4380_, 1, v_a_4372_);
lean_ctor_set(v___x_4380_, 0, v_fvarId_4370_);
v___x_4383_ = v___x_4380_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_fvarId_4370_);
lean_ctor_set(v_reuseFailAlloc_4387_, 1, v_a_4372_);
v___x_4383_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
lean_object* v___x_4385_; 
if (v_isShared_4375_ == 0)
{
lean_ctor_set(v___x_4374_, 0, v___x_4383_);
v___x_4385_ = v___x_4374_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4383_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
else
{
size_t v___x_4391_; size_t v___x_4392_; uint8_t v___x_4393_; 
v___x_4391_ = lean_ptr_addr(v_k_4368_);
v___x_4392_ = lean_ptr_addr(v_a_4372_);
v___x_4393_ = lean_usize_dec_eq(v___x_4391_, v___x_4392_);
if (v___x_4393_ == 0)
{
lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4403_; 
v_isSharedCheck_4403_ = !lean_is_exclusive(v_code_3572_);
if (v_isSharedCheck_4403_ == 0)
{
lean_object* v_unused_4404_; lean_object* v_unused_4405_; 
v_unused_4404_ = lean_ctor_get(v_code_3572_, 1);
lean_dec(v_unused_4404_);
v_unused_4405_ = lean_ctor_get(v_code_3572_, 0);
lean_dec(v_unused_4405_);
v___x_4395_ = v_code_3572_;
v_isShared_4396_ = v_isSharedCheck_4403_;
goto v_resetjp_4394_;
}
else
{
lean_dec(v_code_3572_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4403_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4398_; 
if (v_isShared_4396_ == 0)
{
lean_ctor_set(v___x_4395_, 1, v_a_4372_);
lean_ctor_set(v___x_4395_, 0, v_fvarId_4370_);
v___x_4398_ = v___x_4395_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_fvarId_4370_);
lean_ctor_set(v_reuseFailAlloc_4402_, 1, v_a_4372_);
v___x_4398_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
lean_object* v___x_4400_; 
if (v_isShared_4375_ == 0)
{
lean_ctor_set(v___x_4374_, 0, v___x_4398_);
v___x_4400_ = v___x_4374_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4398_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
}
else
{
lean_object* v___x_4407_; 
lean_dec(v_a_4372_);
lean_dec(v_fvarId_4370_);
if (v_isShared_4375_ == 0)
{
lean_ctor_set(v___x_4374_, 0, v_code_3572_);
v___x_4407_ = v___x_4374_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_code_3572_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_4370_);
lean_dec_ref_known(v_code_3572_, 2);
return v___x_4371_;
}
}
else
{
lean_object* v___x_4410_; 
lean_dec_ref_known(v_code_3572_, 2);
v___x_4410_ = l_Lean_Compiler_LCNF_mkReturnErased(v_pu_3570_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
return v___x_4410_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normCodeImp_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3570_ = stack[0].m_num;
uint8_t v_t_3571_ = stack[1].m_num;
lean_object* v_code_3572_ = stack[2].m_obj;
lean_object* v_a_3573_ = stack[3].m_obj;
lean_object* v_a_3574_ = stack[4].m_obj;
lean_object* v_a_3575_ = stack[5].m_obj;
lean_object* v_a_3576_ = stack[6].m_obj;
lean_object* v_a_3577_ = stack[7].m_obj;
lean_object* v_res_4411_;
v_res_4411_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_3570_, v_t_3571_, v_code_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
stack->m_obj
 = v_res_4411_;
}
lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t v_pu_4412_, uint8_t v_t_4413_, lean_object* v_decl_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_){
_start:
{
lean_object* v_params_4421_; lean_object* v_type_4422_; lean_object* v_value_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v_params_4421_ = lean_ctor_get(v_decl_4414_, 2);
v_type_4422_ = lean_ctor_get(v_decl_4414_, 3);
v_value_4423_ = lean_ctor_get(v_decl_4414_, 4);
lean_inc_ref(v_type_4422_);
v___x_4424_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4412_, v_a_4415_, v_t_4413_, v_type_4422_);
lean_inc_ref(v_params_4421_);
v___x_4425_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4412_, v_t_4413_, v_params_4421_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; lean_object* v___x_4427_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_a_4426_);
lean_dec_ref_known(v___x_4425_, 1);
lean_inc_ref(v_value_4423_);
v___x_4427_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4412_, v_t_4413_, v_value_4423_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_object* v_a_4428_; lean_object* v___x_4429_; 
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4428_);
lean_dec_ref_known(v___x_4427_, 1);
v___x_4429_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_4412_, v_decl_4414_, v___x_4424_, v_a_4426_, v_a_4428_, v_a_4417_);
return v___x_4429_;
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
lean_dec(v_a_4426_);
lean_dec_ref(v___x_4424_);
lean_dec_ref(v_decl_4414_);
v_a_4430_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4427_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4427_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
else
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4445_; 
lean_dec_ref(v___x_4424_);
lean_dec_ref(v_decl_4414_);
v_a_4438_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4440_ = v___x_4425_;
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4425_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4443_; 
if (v_isShared_4441_ == 0)
{
v___x_4443_ = v___x_4440_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normFunDeclImp_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_4412_ = stack[0].m_num;
uint8_t v_t_4413_ = stack[1].m_num;
lean_object* v_decl_4414_ = stack[2].m_obj;
lean_object* v_a_4415_ = stack[3].m_obj;
lean_object* v_a_4416_ = stack[4].m_obj;
lean_object* v_a_4417_ = stack[5].m_obj;
lean_object* v_a_4418_ = stack[6].m_obj;
lean_object* v_a_4419_ = stack[7].m_obj;
lean_object* v_res_4446_;
v_res_4446_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_4412_, v_t_4413_, v_decl_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
stack->m_obj
 = v_res_4446_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDeclImp___boxed(lean_object* v_pu_4447_, lean_object* v_t_4448_, lean_object* v_decl_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_){
_start:
{
uint8_t v_pu_boxed_4456_; uint8_t v_t_boxed_4457_; lean_object* v_res_4458_; 
v_pu_boxed_4456_ = lean_unbox(v_pu_4447_);
v_t_boxed_4457_ = lean_unbox(v_t_4448_);
v_res_4458_ = l_Lean_Compiler_LCNF_normFunDeclImp(v_pu_boxed_4456_, v_t_boxed_4457_, v_decl_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
lean_dec(v_a_4454_);
lean_dec_ref(v_a_4453_);
lean_dec(v_a_4452_);
lean_dec_ref(v_a_4451_);
lean_dec_ref(v_a_4450_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(lean_object* v_pu_4459_, lean_object* v_t_4460_, lean_object* v_i_4461_, lean_object* v_as_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
uint8_t v_pu_boxed_4469_; uint8_t v_t_boxed_4470_; lean_object* v_res_4471_; 
v_pu_boxed_4469_ = lean_unbox(v_pu_4459_);
v_t_boxed_4470_ = lean_unbox(v_t_4460_);
v_res_4471_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_boxed_4469_, v_t_boxed_4470_, v_i_4461_, v_as_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
lean_dec(v___y_4465_);
lean_dec_ref(v___y_4464_);
lean_dec_ref(v___y_4463_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCodeImp___boxed(lean_object* v_pu_4472_, lean_object* v_t_4473_, lean_object* v_code_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_){
_start:
{
uint8_t v_pu_boxed_4481_; uint8_t v_t_boxed_4482_; lean_object* v_res_4483_; 
v_pu_boxed_4481_ = lean_unbox(v_pu_4472_);
v_t_boxed_4482_ = lean_unbox(v_t_4473_);
v_res_4483_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_boxed_4481_, v_t_boxed_4482_, v_code_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_);
lean_dec(v_a_4479_);
lean_dec_ref(v_a_4478_);
lean_dec(v_a_4477_);
lean_dec_ref(v_a_4476_);
lean_dec_ref(v_a_4475_);
return v_res_4483_;
}
}
lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(uint8_t v_pu_4484_, uint8_t v_t_4485_, uint8_t v_pu_4486_, uint8_t v_t_4487_, lean_object* v_decl_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
lean_object* v___x_4495_; 
v___x_4495_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_4486_, v_t_4487_, v_decl_4488_, v___y_4489_, v___y_4491_);
return v___x_4495_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_4484_ = stack[0].m_num;
uint8_t v_t_4485_ = stack[1].m_num;
uint8_t v_pu_4486_ = stack[2].m_num;
uint8_t v_t_4487_ = stack[3].m_num;
lean_object* v_decl_4488_ = stack[4].m_obj;
lean_object* v___y_4489_ = stack[5].m_obj;
lean_object* v___y_4490_ = stack[6].m_obj;
lean_object* v___y_4491_ = stack[7].m_obj;
lean_object* v___y_4492_ = stack[8].m_obj;
lean_object* v___y_4493_ = stack[9].m_obj;
lean_object* v_res_4496_;
v_res_4496_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(v_pu_4484_, v_t_4485_, v_pu_4486_, v_t_4487_, v_decl_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
stack->m_obj
 = v_res_4496_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(lean_object* v_pu_4497_, lean_object* v_t_4498_, lean_object* v_pu_4499_, lean_object* v_t_4500_, lean_object* v_decl_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_){
_start:
{
uint8_t v_pu_boxed_4508_; uint8_t v_t_boxed_4509_; uint8_t v_pu_boxed_4510_; uint8_t v_t_boxed_4511_; lean_object* v_res_4512_; 
v_pu_boxed_4508_ = lean_unbox(v_pu_4497_);
v_t_boxed_4509_ = lean_unbox(v_t_4498_);
v_pu_boxed_4510_ = lean_unbox(v_pu_4499_);
v_t_boxed_4511_ = lean_unbox(v_t_4500_);
v_res_4512_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(v_pu_boxed_4508_, v_t_boxed_4509_, v_pu_boxed_4510_, v_t_boxed_4511_, v_decl_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_);
lean_dec(v___y_4506_);
lean_dec_ref(v___y_4505_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
lean_dec_ref(v___y_4502_);
return v_res_4512_;
}
}
lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(uint8_t v_pu_4513_, uint8_t v_t_4514_, uint8_t v_pu_4515_, uint8_t v_t_4516_, lean_object* v_args_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
lean_object* v___x_4524_; 
v___x_4524_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_4515_, v_t_4516_, v_args_4517_, v___y_4518_);
return v___x_4524_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_4513_ = stack[0].m_num;
uint8_t v_t_4514_ = stack[1].m_num;
uint8_t v_pu_4515_ = stack[2].m_num;
uint8_t v_t_4516_ = stack[3].m_num;
lean_object* v_args_4517_ = stack[4].m_obj;
lean_object* v___y_4518_ = stack[5].m_obj;
lean_object* v___y_4519_ = stack[6].m_obj;
lean_object* v___y_4520_ = stack[7].m_obj;
lean_object* v___y_4521_ = stack[8].m_obj;
lean_object* v___y_4522_ = stack[9].m_obj;
lean_object* v_res_4525_;
v_res_4525_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(v_pu_4513_, v_t_4514_, v_pu_4515_, v_t_4516_, v_args_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
stack->m_obj
 = v_res_4525_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(lean_object* v_pu_4526_, lean_object* v_t_4527_, lean_object* v_pu_4528_, lean_object* v_t_4529_, lean_object* v_args_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_){
_start:
{
uint8_t v_pu_boxed_4537_; uint8_t v_t_boxed_4538_; uint8_t v_pu_boxed_4539_; uint8_t v_t_boxed_4540_; lean_object* v_res_4541_; 
v_pu_boxed_4537_ = lean_unbox(v_pu_4526_);
v_t_boxed_4538_ = lean_unbox(v_t_4527_);
v_pu_boxed_4539_ = lean_unbox(v_pu_4528_);
v_t_boxed_4540_ = lean_unbox(v_t_4529_);
v_res_4541_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(v_pu_boxed_4537_, v_t_boxed_4538_, v_pu_boxed_4539_, v_t_boxed_4540_, v_args_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4534_);
lean_dec(v___y_4533_);
lean_dec_ref(v___y_4532_);
lean_dec_ref(v___y_4531_);
return v_res_4541_;
}
}
lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(uint8_t v_pu_4542_, uint8_t v_t_4543_, uint8_t v_pu_4544_, uint8_t v_t_4545_, lean_object* v_ps_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
lean_object* v___x_4553_; 
v___x_4553_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_4544_, v_t_4545_, v_ps_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
return v___x_4553_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_4542_ = stack[0].m_num;
uint8_t v_t_4543_ = stack[1].m_num;
uint8_t v_pu_4544_ = stack[2].m_num;
uint8_t v_t_4545_ = stack[3].m_num;
lean_object* v_ps_4546_ = stack[4].m_obj;
lean_object* v___y_4547_ = stack[5].m_obj;
lean_object* v___y_4548_ = stack[6].m_obj;
lean_object* v___y_4549_ = stack[7].m_obj;
lean_object* v___y_4550_ = stack[8].m_obj;
lean_object* v___y_4551_ = stack[9].m_obj;
lean_object* v_res_4554_;
v_res_4554_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(v_pu_4542_, v_t_4543_, v_pu_4544_, v_t_4545_, v_ps_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
stack->m_obj
 = v_res_4554_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(lean_object* v_pu_4555_, lean_object* v_t_4556_, lean_object* v_pu_4557_, lean_object* v_t_4558_, lean_object* v_ps_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
uint8_t v_pu_boxed_4566_; uint8_t v_t_boxed_4567_; uint8_t v_pu_boxed_4568_; uint8_t v_t_boxed_4569_; lean_object* v_res_4570_; 
v_pu_boxed_4566_ = lean_unbox(v_pu_4555_);
v_t_boxed_4567_ = lean_unbox(v_t_4556_);
v_pu_boxed_4568_ = lean_unbox(v_pu_4557_);
v_t_boxed_4569_ = lean_unbox(v_t_4558_);
v_res_4570_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(v_pu_boxed_4566_, v_t_boxed_4567_, v_pu_boxed_4568_, v_t_boxed_4569_, v_ps_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec_ref(v___y_4560_);
return v_res_4570_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(uint8_t v_pu_4571_, uint8_t v_t_4572_, lean_object* v_i_4573_, lean_object* v_as_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_){
_start:
{
lean_object* v___x_4581_; 
v___x_4581_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_4571_, v_t_4572_, v_i_4573_, v_as_4574_, v___y_4575_, v___y_4577_);
return v___x_4581_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_4571_ = stack[0].m_num;
uint8_t v_t_4572_ = stack[1].m_num;
lean_object* v_i_4573_ = stack[2].m_obj;
lean_object* v_as_4574_ = stack[3].m_obj;
lean_object* v___y_4575_ = stack[4].m_obj;
lean_object* v___y_4576_ = stack[5].m_obj;
lean_object* v___y_4577_ = stack[6].m_obj;
lean_object* v___y_4578_ = stack[7].m_obj;
lean_object* v___y_4579_ = stack[8].m_obj;
lean_object* v_res_4582_;
v_res_4582_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_4571_, v_t_4572_, v_i_4573_, v_as_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
stack->m_obj
 = v_res_4582_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(lean_object* v_pu_4583_, lean_object* v_t_4584_, lean_object* v_i_4585_, lean_object* v_as_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_){
_start:
{
uint8_t v_pu_boxed_4593_; uint8_t v_t_boxed_4594_; lean_object* v_res_4595_; 
v_pu_boxed_4593_ = lean_unbox(v_pu_4583_);
v_t_boxed_4594_ = lean_unbox(v_t_4584_);
v_res_4595_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_boxed_4593_, v_t_boxed_4594_, v_i_4585_, v_as_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
lean_dec_ref(v___y_4587_);
return v_res_4595_;
}
}
lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(uint8_t v_pu_4596_, uint8_t v_t_4597_, lean_object* v_decl_4598_, lean_object* v_inst_4599_, lean_object* v_____do__lift_4600_){
_start:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; 
v___x_4601_ = lean_box(v_pu_4596_);
v___x_4602_ = lean_box(v_t_4597_);
v___x_4603_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDeclImp___boxed), 9, 4);
lean_closure_set(v___x_4603_, 0, v___x_4601_);
lean_closure_set(v___x_4603_, 1, v___x_4602_);
lean_closure_set(v___x_4603_, 2, v_decl_4598_);
lean_closure_set(v___x_4603_, 3, v_____do__lift_4600_);
v___x_4604_ = lean_apply_2(v_inst_4599_, lean_box(0), v___x_4603_);
return v___x_4604_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_4596_ = stack[0].m_num;
uint8_t v_t_4597_ = stack[1].m_num;
lean_object* v_decl_4598_ = stack[2].m_obj;
lean_object* v_inst_4599_ = stack[3].m_obj;
lean_object* v_____do__lift_4600_ = stack[4].m_obj;
lean_object* v_res_4605_;
v_res_4605_ = l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(v_pu_4596_, v_t_4597_, v_decl_4598_, v_inst_4599_, v_____do__lift_4600_);
stack->m_obj
 = v_res_4605_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(lean_object* v_pu_4606_, lean_object* v_t_4607_, lean_object* v_decl_4608_, lean_object* v_inst_4609_, lean_object* v_____do__lift_4610_){
_start:
{
uint8_t v_pu_boxed_4611_; uint8_t v_t_boxed_4612_; lean_object* v_res_4613_; 
v_pu_boxed_4611_ = lean_unbox(v_pu_4606_);
v_t_boxed_4612_ = lean_unbox(v_t_4607_);
v_res_4613_ = l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(v_pu_boxed_4611_, v_t_boxed_4612_, v_decl_4608_, v_inst_4609_, v_____do__lift_4610_);
return v_res_4613_;
}
}
lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg(uint8_t v_pu_4614_, uint8_t v_t_4615_, lean_object* v_inst_4616_, lean_object* v_inst_4617_, lean_object* v_inst_4618_, lean_object* v_decl_4619_){
_start:
{
lean_object* v_toBind_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___f_4623_; lean_object* v___x_4624_; 
v_toBind_4620_ = lean_ctor_get(v_inst_4617_, 1);
lean_inc(v_toBind_4620_);
lean_dec_ref(v_inst_4617_);
v___x_4621_ = lean_box(v_pu_4614_);
v___x_4622_ = lean_box(v_t_4615_);
v___f_4623_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4623_, 0, v___x_4621_);
lean_closure_set(v___f_4623_, 1, v___x_4622_);
lean_closure_set(v___f_4623_, 2, v_decl_4619_);
lean_closure_set(v___f_4623_, 3, v_inst_4616_);
v___x_4624_ = lean_apply_4(v_toBind_4620_, lean_box(0), lean_box(0), v_inst_4618_, v___f_4623_);
return v___x_4624_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normFunDecl___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_4614_ = stack[0].m_num;
uint8_t v_t_4615_ = stack[1].m_num;
lean_object* v_inst_4616_ = stack[2].m_obj;
lean_object* v_inst_4617_ = stack[3].m_obj;
lean_object* v_inst_4618_ = stack[4].m_obj;
lean_object* v_decl_4619_ = stack[5].m_obj;
lean_object* v_res_4625_;
v_res_4625_ = l_Lean_Compiler_LCNF_normFunDecl___redArg(v_pu_4614_, v_t_4615_, v_inst_4616_, v_inst_4617_, v_inst_4618_, v_decl_4619_);
stack->m_obj
 = v_res_4625_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(lean_object* v_pu_4626_, lean_object* v_t_4627_, lean_object* v_inst_4628_, lean_object* v_inst_4629_, lean_object* v_inst_4630_, lean_object* v_decl_4631_){
_start:
{
uint8_t v_pu_boxed_4632_; uint8_t v_t_boxed_4633_; lean_object* v_res_4634_; 
v_pu_boxed_4632_ = lean_unbox(v_pu_4626_);
v_t_boxed_4633_ = lean_unbox(v_t_4627_);
v_res_4634_ = l_Lean_Compiler_LCNF_normFunDecl___redArg(v_pu_boxed_4632_, v_t_boxed_4633_, v_inst_4628_, v_inst_4629_, v_inst_4630_, v_decl_4631_);
return v_res_4634_;
}
}
lean_object* l_Lean_Compiler_LCNF_normFunDecl(lean_object* v_m_4635_, uint8_t v_pu_4636_, uint8_t v_t_4637_, lean_object* v_inst_4638_, lean_object* v_inst_4639_, lean_object* v_inst_4640_, lean_object* v_decl_4641_){
_start:
{
lean_object* v_toBind_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___f_4645_; lean_object* v___x_4646_; 
v_toBind_4642_ = lean_ctor_get(v_inst_4639_, 1);
lean_inc(v_toBind_4642_);
lean_dec_ref(v_inst_4639_);
v___x_4643_ = lean_box(v_pu_4636_);
v___x_4644_ = lean_box(v_t_4637_);
v___f_4645_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4645_, 0, v___x_4643_);
lean_closure_set(v___f_4645_, 1, v___x_4644_);
lean_closure_set(v___f_4645_, 2, v_decl_4641_);
lean_closure_set(v___f_4645_, 3, v_inst_4638_);
v___x_4646_ = lean_apply_4(v_toBind_4642_, lean_box(0), lean_box(0), v_inst_4640_, v___f_4645_);
return v___x_4646_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normFunDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_4636_ = stack[1].m_num;
uint8_t v_t_4637_ = stack[2].m_num;
lean_object* v_inst_4638_ = stack[3].m_obj;
lean_object* v_inst_4639_ = stack[4].m_obj;
lean_object* v_inst_4640_ = stack[5].m_obj;
lean_object* v_decl_4641_ = stack[6].m_obj;
lean_object* v_res_4647_;
v_res_4647_ = l_Lean_Compiler_LCNF_normFunDecl(lean_box(0), v_pu_4636_, v_t_4637_, v_inst_4638_, v_inst_4639_, v_inst_4640_, v_decl_4641_);
stack->m_obj
 = v_res_4647_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normFunDecl___boxed(lean_object* v_m_4648_, lean_object* v_pu_4649_, lean_object* v_t_4650_, lean_object* v_inst_4651_, lean_object* v_inst_4652_, lean_object* v_inst_4653_, lean_object* v_decl_4654_){
_start:
{
uint8_t v_pu_boxed_4655_; uint8_t v_t_boxed_4656_; lean_object* v_res_4657_; 
v_pu_boxed_4655_ = lean_unbox(v_pu_4649_);
v_t_boxed_4656_ = lean_unbox(v_t_4650_);
v_res_4657_ = l_Lean_Compiler_LCNF_normFunDecl(v_m_4648_, v_pu_boxed_4655_, v_t_boxed_4656_, v_inst_4651_, v_inst_4652_, v_inst_4653_, v_decl_4654_);
return v_res_4657_;
}
}
lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0(uint8_t v_pu_4658_, uint8_t v_t_4659_, lean_object* v_code_4660_, lean_object* v_inst_4661_, lean_object* v_____do__lift_4662_){
_start:
{
lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; 
v___x_4663_ = lean_box(v_pu_4658_);
v___x_4664_ = lean_box(v_t_4659_);
v___x_4665_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCodeImp___boxed), 9, 4);
lean_closure_set(v___x_4665_, 0, v___x_4663_);
lean_closure_set(v___x_4665_, 1, v___x_4664_);
lean_closure_set(v___x_4665_, 2, v_code_4660_);
lean_closure_set(v___x_4665_, 3, v_____do__lift_4662_);
v___x_4666_ = lean_apply_2(v_inst_4661_, lean_box(0), v___x_4665_);
return v___x_4666_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normCode___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_4658_ = stack[0].m_num;
uint8_t v_t_4659_ = stack[1].m_num;
lean_object* v_code_4660_ = stack[2].m_obj;
lean_object* v_inst_4661_ = stack[3].m_obj;
lean_object* v_____do__lift_4662_ = stack[4].m_obj;
lean_object* v_res_4667_;
v_res_4667_ = l_Lean_Compiler_LCNF_normCode___redArg___lam__0(v_pu_4658_, v_t_4659_, v_code_4660_, v_inst_4661_, v_____do__lift_4662_);
stack->m_obj
 = v_res_4667_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(lean_object* v_pu_4668_, lean_object* v_t_4669_, lean_object* v_code_4670_, lean_object* v_inst_4671_, lean_object* v_____do__lift_4672_){
_start:
{
uint8_t v_pu_boxed_4673_; uint8_t v_t_boxed_4674_; lean_object* v_res_4675_; 
v_pu_boxed_4673_ = lean_unbox(v_pu_4668_);
v_t_boxed_4674_ = lean_unbox(v_t_4669_);
v_res_4675_ = l_Lean_Compiler_LCNF_normCode___redArg___lam__0(v_pu_boxed_4673_, v_t_boxed_4674_, v_code_4670_, v_inst_4671_, v_____do__lift_4672_);
return v_res_4675_;
}
}
lean_object* l_Lean_Compiler_LCNF_normCode___redArg(uint8_t v_pu_4676_, uint8_t v_t_4677_, lean_object* v_inst_4678_, lean_object* v_inst_4679_, lean_object* v_inst_4680_, lean_object* v_code_4681_){
_start:
{
lean_object* v_toBind_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___f_4685_; lean_object* v___x_4686_; 
v_toBind_4682_ = lean_ctor_get(v_inst_4679_, 1);
lean_inc(v_toBind_4682_);
lean_dec_ref(v_inst_4679_);
v___x_4683_ = lean_box(v_pu_4676_);
v___x_4684_ = lean_box(v_t_4677_);
v___f_4685_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4685_, 0, v___x_4683_);
lean_closure_set(v___f_4685_, 1, v___x_4684_);
lean_closure_set(v___f_4685_, 2, v_code_4681_);
lean_closure_set(v___f_4685_, 3, v_inst_4678_);
v___x_4686_ = lean_apply_4(v_toBind_4682_, lean_box(0), lean_box(0), v_inst_4680_, v___f_4685_);
return v___x_4686_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normCode___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_4676_ = stack[0].m_num;
uint8_t v_t_4677_ = stack[1].m_num;
lean_object* v_inst_4678_ = stack[2].m_obj;
lean_object* v_inst_4679_ = stack[3].m_obj;
lean_object* v_inst_4680_ = stack[4].m_obj;
lean_object* v_code_4681_ = stack[5].m_obj;
lean_object* v_res_4687_;
v_res_4687_ = l_Lean_Compiler_LCNF_normCode___redArg(v_pu_4676_, v_t_4677_, v_inst_4678_, v_inst_4679_, v_inst_4680_, v_code_4681_);
stack->m_obj
 = v_res_4687_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___redArg___boxed(lean_object* v_pu_4688_, lean_object* v_t_4689_, lean_object* v_inst_4690_, lean_object* v_inst_4691_, lean_object* v_inst_4692_, lean_object* v_code_4693_){
_start:
{
uint8_t v_pu_boxed_4694_; uint8_t v_t_boxed_4695_; lean_object* v_res_4696_; 
v_pu_boxed_4694_ = lean_unbox(v_pu_4688_);
v_t_boxed_4695_ = lean_unbox(v_t_4689_);
v_res_4696_ = l_Lean_Compiler_LCNF_normCode___redArg(v_pu_boxed_4694_, v_t_boxed_4695_, v_inst_4690_, v_inst_4691_, v_inst_4692_, v_code_4693_);
return v_res_4696_;
}
}
lean_object* l_Lean_Compiler_LCNF_normCode(lean_object* v_m_4697_, uint8_t v_pu_4698_, uint8_t v_t_4699_, lean_object* v_inst_4700_, lean_object* v_inst_4701_, lean_object* v_inst_4702_, lean_object* v_code_4703_){
_start:
{
lean_object* v_toBind_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___f_4707_; lean_object* v___x_4708_; 
v_toBind_4704_ = lean_ctor_get(v_inst_4701_, 1);
lean_inc(v_toBind_4704_);
lean_dec_ref(v_inst_4701_);
v___x_4705_ = lean_box(v_pu_4698_);
v___x_4706_ = lean_box(v_t_4699_);
v___f_4707_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_4707_, 0, v___x_4705_);
lean_closure_set(v___f_4707_, 1, v___x_4706_);
lean_closure_set(v___f_4707_, 2, v_code_4703_);
lean_closure_set(v___f_4707_, 3, v_inst_4700_);
v___x_4708_ = lean_apply_4(v_toBind_4704_, lean_box(0), lean_box(0), v_inst_4702_, v___f_4707_);
return v___x_4708_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normCode_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_4698_ = stack[1].m_num;
uint8_t v_t_4699_ = stack[2].m_num;
lean_object* v_inst_4700_ = stack[3].m_obj;
lean_object* v_inst_4701_ = stack[4].m_obj;
lean_object* v_inst_4702_ = stack[5].m_obj;
lean_object* v_code_4703_ = stack[6].m_obj;
lean_object* v_res_4709_;
v_res_4709_ = l_Lean_Compiler_LCNF_normCode(lean_box(0), v_pu_4698_, v_t_4699_, v_inst_4700_, v_inst_4701_, v_inst_4702_, v_code_4703_);
stack->m_obj
 = v_res_4709_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normCode___boxed(lean_object* v_m_4710_, lean_object* v_pu_4711_, lean_object* v_t_4712_, lean_object* v_inst_4713_, lean_object* v_inst_4714_, lean_object* v_inst_4715_, lean_object* v_code_4716_){
_start:
{
uint8_t v_pu_boxed_4717_; uint8_t v_t_boxed_4718_; lean_object* v_res_4719_; 
v_pu_boxed_4717_ = lean_unbox(v_pu_4711_);
v_t_boxed_4718_ = lean_unbox(v_t_4712_);
v_res_4719_ = l_Lean_Compiler_LCNF_normCode(v_m_4710_, v_pu_boxed_4717_, v_t_boxed_4718_, v_inst_4713_, v_inst_4714_, v_inst_4715_, v_code_4716_);
return v_res_4719_;
}
}
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t v_pu_4720_, lean_object* v_e_4721_, lean_object* v_s_4722_, uint8_t v_translator_4723_){
_start:
{
lean_object* v___x_4725_; lean_object* v___x_4726_; 
v___x_4725_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4720_, v_s_4722_, v_translator_4723_, v_e_4721_);
v___x_4726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4726_, 0, v___x_4725_);
return v___x_4726_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_replaceExprFVars___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_4720_ = stack[0].m_num;
lean_object* v_e_4721_ = stack[1].m_obj;
lean_object* v_s_4722_ = stack[2].m_obj;
uint8_t v_translator_4723_ = stack[3].m_num;
lean_object* v_res_4727_;
v_res_4727_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_4720_, v_e_4721_, v_s_4722_, v_translator_4723_);
stack->m_obj
 = v_res_4727_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(lean_object* v_pu_4728_, lean_object* v_e_4729_, lean_object* v_s_4730_, lean_object* v_translator_4731_, lean_object* v_a_4732_){
_start:
{
uint8_t v_pu_boxed_4733_; uint8_t v_translator_boxed_4734_; lean_object* v_res_4735_; 
v_pu_boxed_4733_ = lean_unbox(v_pu_4728_);
v_translator_boxed_4734_ = lean_unbox(v_translator_4731_);
v_res_4735_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_boxed_4733_, v_e_4729_, v_s_4730_, v_translator_boxed_4734_);
lean_dec_ref(v_s_4730_);
return v_res_4735_;
}
}
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(uint8_t v_pu_4736_, lean_object* v_e_4737_, lean_object* v_s_4738_, uint8_t v_translator_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_){
_start:
{
lean_object* v___x_4745_; 
v___x_4745_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v_pu_4736_, v_e_4737_, v_s_4738_, v_translator_4739_);
return v___x_4745_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_replaceExprFVars_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_4736_ = stack[0].m_num;
lean_object* v_e_4737_ = stack[1].m_obj;
lean_object* v_s_4738_ = stack[2].m_obj;
uint8_t v_translator_4739_ = stack[3].m_num;
lean_object* v_a_4740_ = stack[4].m_obj;
lean_object* v_a_4741_ = stack[5].m_obj;
lean_object* v_a_4742_ = stack[6].m_obj;
lean_object* v_a_4743_ = stack[7].m_obj;
lean_object* v_res_4746_;
v_res_4746_ = l_Lean_Compiler_LCNF_replaceExprFVars(v_pu_4736_, v_e_4737_, v_s_4738_, v_translator_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_);
stack->m_obj
 = v_res_4746_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___boxed(lean_object* v_pu_4747_, lean_object* v_e_4748_, lean_object* v_s_4749_, lean_object* v_translator_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_){
_start:
{
uint8_t v_pu_boxed_4756_; uint8_t v_translator_boxed_4757_; lean_object* v_res_4758_; 
v_pu_boxed_4756_ = lean_unbox(v_pu_4747_);
v_translator_boxed_4757_ = lean_unbox(v_translator_4750_);
v_res_4758_ = l_Lean_Compiler_LCNF_replaceExprFVars(v_pu_boxed_4756_, v_e_4748_, v_s_4749_, v_translator_boxed_4757_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_);
lean_dec(v_a_4754_);
lean_dec_ref(v_a_4753_);
lean_dec(v_a_4752_);
lean_dec_ref(v_a_4751_);
lean_dec_ref(v_s_4749_);
return v_res_4758_;
}
}
lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t v_pu_4759_, lean_object* v_code_4760_, lean_object* v_s_4761_, uint8_t v_translator_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_){
_start:
{
lean_object* v___x_4768_; 
v___x_4768_ = l_Lean_Compiler_LCNF_normCodeImp(v_pu_4759_, v_translator_4762_, v_code_4760_, v_s_4761_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_);
return v___x_4768_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_replaceFVars_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_4759_ = stack[0].m_num;
lean_object* v_code_4760_ = stack[1].m_obj;
lean_object* v_s_4761_ = stack[2].m_obj;
uint8_t v_translator_4762_ = stack[3].m_num;
lean_object* v_a_4763_ = stack[4].m_obj;
lean_object* v_a_4764_ = stack[5].m_obj;
lean_object* v_a_4765_ = stack[6].m_obj;
lean_object* v_a_4766_ = stack[7].m_obj;
lean_object* v_res_4769_;
v_res_4769_ = l_Lean_Compiler_LCNF_replaceFVars(v_pu_4759_, v_code_4760_, v_s_4761_, v_translator_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_);
stack->m_obj
 = v_res_4769_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_replaceFVars___boxed(lean_object* v_pu_4770_, lean_object* v_code_4771_, lean_object* v_s_4772_, lean_object* v_translator_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_){
_start:
{
uint8_t v_pu_boxed_4779_; uint8_t v_translator_boxed_4780_; lean_object* v_res_4781_; 
v_pu_boxed_4779_ = lean_unbox(v_pu_4770_);
v_translator_boxed_4780_ = lean_unbox(v_translator_4773_);
v_res_4781_ = l_Lean_Compiler_LCNF_replaceFVars(v_pu_boxed_4779_, v_code_4771_, v_s_4772_, v_translator_boxed_4780_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_);
lean_dec(v_a_4777_);
lean_dec_ref(v_a_4776_);
lean_dec(v_a_4775_);
lean_dec_ref(v_a_4774_);
lean_dec_ref(v_s_4772_);
return v_res_4781_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object* v_a_4785_){
_start:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; 
v___x_4787_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1));
v___x_4788_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4787_, v_a_4785_);
return v___x_4788_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkFreshJpName___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4785_ = stack[0].m_obj;
lean_object* v_res_4789_;
v_res_4789_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4785_);
stack->m_obj
 = v_res_4789_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(lean_object* v_a_4790_, lean_object* v_a_4791_){
_start:
{
lean_object* v_res_4792_; 
v_res_4792_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4790_);
lean_dec(v_a_4790_);
return v_res_4792_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_){
_start:
{
lean_object* v___x_4798_; 
v___x_4798_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_4794_);
return v___x_4798_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkFreshJpName_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4793_ = stack[0].m_obj;
lean_object* v_a_4794_ = stack[1].m_obj;
lean_object* v_a_4795_ = stack[2].m_obj;
lean_object* v_a_4796_ = stack[3].m_obj;
lean_object* v_res_4799_;
v_res_4799_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_);
stack->m_obj
 = v_res_4799_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___boxed(lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_){
_start:
{
lean_object* v_res_4805_; 
v_res_4805_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_);
lean_dec(v_a_4803_);
lean_dec_ref(v_a_4802_);
lean_dec(v_a_4801_);
lean_dec_ref(v_a_4800_);
return v_res_4805_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t v_pu_4806_, lean_object* v_type_4807_, uint8_t v_borrow_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_){
_start:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v_a_4816_; lean_object* v___x_4817_; 
v___x_4814_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkParam___closed__1));
v___x_4815_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4814_, v_a_4810_);
v_a_4816_ = lean_ctor_get(v___x_4815_, 0);
lean_inc(v_a_4816_);
lean_dec_ref(v___x_4815_);
v___x_4817_ = l_Lean_Compiler_LCNF_mkParam(v_pu_4806_, v_a_4816_, v_type_4807_, v_borrow_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_);
return v___x_4817_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkAuxParam_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_4806_ = stack[0].m_num;
lean_object* v_type_4807_ = stack[1].m_obj;
uint8_t v_borrow_4808_ = stack[2].m_num;
lean_object* v_a_4809_ = stack[3].m_obj;
lean_object* v_a_4810_ = stack[4].m_obj;
lean_object* v_a_4811_ = stack[5].m_obj;
lean_object* v_a_4812_ = stack[6].m_obj;
lean_object* v_res_4818_;
v_res_4818_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_4806_, v_type_4807_, v_borrow_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_);
stack->m_obj
 = v_res_4818_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxParam___boxed(lean_object* v_pu_4819_, lean_object* v_type_4820_, lean_object* v_borrow_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_){
_start:
{
uint8_t v_pu_boxed_4827_; uint8_t v_borrow_boxed_4828_; lean_object* v_res_4829_; 
v_pu_boxed_4827_ = lean_unbox(v_pu_4819_);
v_borrow_boxed_4828_ = lean_unbox(v_borrow_4821_);
v_res_4829_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_boxed_4827_, v_type_4820_, v_borrow_boxed_4828_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_);
lean_dec(v_a_4825_);
lean_dec_ref(v_a_4824_);
lean_dec(v_a_4823_);
lean_dec_ref(v_a_4822_);
return v_res_4829_;
}
}
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object* v_a_4830_){
_start:
{
lean_object* v_config_4832_; lean_object* v___x_4833_; 
v_config_4832_ = lean_ctor_get(v_a_4830_, 0);
lean_inc_ref(v_config_4832_);
v___x_4833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4833_, 0, v_config_4832_);
return v___x_4833_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_getConfig___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4830_ = stack[0].m_obj;
lean_object* v_res_4834_;
v_res_4834_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4830_);
stack->m_obj
 = v_res_4834_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___redArg___boxed(lean_object* v_a_4835_, lean_object* v_a_4836_){
_start:
{
lean_object* v_res_4837_; 
v_res_4837_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4835_);
lean_dec_ref(v_a_4835_);
return v_res_4837_;
}
}
lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_){
_start:
{
lean_object* v___x_4843_; 
v___x_4843_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_4838_);
return v___x_4843_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_getConfig_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4838_ = stack[0].m_obj;
lean_object* v_a_4839_ = stack[1].m_obj;
lean_object* v_a_4840_ = stack[2].m_obj;
lean_object* v_a_4841_ = stack[3].m_obj;
lean_object* v_res_4844_;
v_res_4844_ = l_Lean_Compiler_LCNF_getConfig(v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_);
stack->m_obj
 = v_res_4844_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getConfig___boxed(lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l_Lean_Compiler_LCNF_getConfig(v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
lean_dec(v_a_4848_);
lean_dec_ref(v_a_4847_);
lean_dec(v_a_4846_);
lean_dec_ref(v_a_4845_);
return v_res_4850_;
}
}
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object* v_x_4851_, lean_object* v_s_4852_, uint8_t v_phase_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_){
_start:
{
lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; 
v___x_4857_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4854_);
v___x_4858_ = l_Lean_Compiler_LCNF_toConfigOptions(v___x_4857_);
lean_dec_ref(v___x_4857_);
v___x_4859_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4859_, 0, v___x_4858_);
lean_ctor_set_uint8(v___x_4859_, sizeof(void*)*1, v_phase_4853_);
v___x_4860_ = lean_st_mk_ref(v_s_4852_);
lean_inc(v_a_4855_);
lean_inc_ref(v_a_4854_);
lean_inc(v___x_4860_);
v___x_4861_ = lean_apply_5(v_x_4851_, v___x_4859_, v___x_4860_, v_a_4854_, v_a_4855_, lean_box(0));
if (lean_obj_tag(v___x_4861_) == 0)
{
lean_object* v_a_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4870_; 
v_a_4862_ = lean_ctor_get(v___x_4861_, 0);
v_isSharedCheck_4870_ = !lean_is_exclusive(v___x_4861_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4864_ = v___x_4861_;
v_isShared_4865_ = v_isSharedCheck_4870_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_a_4862_);
lean_dec(v___x_4861_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4870_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
lean_object* v___x_4866_; lean_object* v___x_4868_; 
v___x_4866_ = lean_st_ref_get(v___x_4860_);
lean_dec(v___x_4860_);
lean_dec(v___x_4866_);
if (v_isShared_4865_ == 0)
{
v___x_4868_ = v___x_4864_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_a_4862_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
}
else
{
lean_dec(v___x_4860_);
return v___x_4861_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CompilerM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4851_ = stack[0].m_obj;
lean_object* v_s_4852_ = stack[1].m_obj;
uint8_t v_phase_4853_ = stack[2].m_num;
lean_object* v_a_4854_ = stack[3].m_obj;
lean_object* v_a_4855_ = stack[4].m_obj;
lean_object* v_res_4871_;
v_res_4871_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4851_, v_s_4852_, v_phase_4853_, v_a_4854_, v_a_4855_);
stack->m_obj
 = v_res_4871_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(lean_object* v_x_4872_, lean_object* v_s_4873_, lean_object* v_phase_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_){
_start:
{
uint8_t v_phase_boxed_4878_; lean_object* v_res_4879_; 
v_phase_boxed_4878_ = lean_unbox(v_phase_4874_);
v_res_4879_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4872_, v_s_4873_, v_phase_boxed_4878_, v_a_4875_, v_a_4876_);
lean_dec(v_a_4876_);
lean_dec_ref(v_a_4875_);
return v_res_4879_;
}
}
lean_object* l_Lean_Compiler_LCNF_CompilerM_run(lean_object* v_00_u03b1_4880_, lean_object* v_x_4881_, lean_object* v_s_4882_, uint8_t v_phase_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_){
_start:
{
lean_object* v___x_4887_; 
v___x_4887_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v_x_4881_, v_s_4882_, v_phase_4883_, v_a_4884_, v_a_4885_);
return v___x_4887_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CompilerM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4881_ = stack[1].m_obj;
lean_object* v_s_4882_ = stack[2].m_obj;
uint8_t v_phase_4883_ = stack[3].m_num;
lean_object* v_a_4884_ = stack[4].m_obj;
lean_object* v_a_4885_ = stack[5].m_obj;
lean_object* v_res_4888_;
v_res_4888_ = l_Lean_Compiler_LCNF_CompilerM_run(lean_box(0), v_x_4881_, v_s_4882_, v_phase_4883_, v_a_4884_, v_a_4885_);
stack->m_obj
 = v_res_4888_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object* v_00_u03b1_4889_, lean_object* v_x_4890_, lean_object* v_s_4891_, lean_object* v_phase_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_){
_start:
{
uint8_t v_phase_boxed_4896_; lean_object* v_res_4897_; 
v_phase_boxed_4896_ = lean_unbox(v_phase_4892_);
v_res_4897_ = l_Lean_Compiler_LCNF_CompilerM_run(v_00_u03b1_4889_, v_x_4890_, v_s_4891_, v_phase_boxed_4896_, v_a_4893_, v_a_4894_);
lean_dec(v_a_4894_);
lean_dec_ref(v_a_4893_);
return v_res_4897_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_4898_; 
v___x_4898_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_4898_;
}
}
lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg(){
_start:
{
lean_object* v___x_4900_; 
v___x_4900_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4900_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4901_;
v_res_4901_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg();
stack->m_obj
 = v_res_4901_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___boxed(lean_object* v___dummy_4902_){
_start:
{
lean_object* v_res_4903_; 
v_res_4903_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg();
return v_res_4903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(lean_object* v_00_u03b1_4904_, lean_object* v_00_u03b2_4905_, lean_object* v_inst_4906_, lean_object* v_inst_4907_){
_start:
{
lean_object* v___x_4908_; 
v___x_4908_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(lean_object* v_00_u03b1_4909_, lean_object* v_00_u03b2_4910_, lean_object* v_inst_4911_, lean_object* v_inst_4912_){
_start:
{
lean_object* v_res_4913_; 
v_res_4913_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(v_00_u03b1_4909_, v_00_u03b2_4910_, v_inst_4911_, v_inst_4912_);
lean_dec_ref(v_inst_4912_);
lean_dec_ref(v_inst_4911_);
return v_res_4913_;
}
}
lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg(){
_start:
{
lean_object* v___x_4915_; 
v___x_4915_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4915_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4916_;
v_res_4916_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg();
stack->m_obj
 = v_res_4916_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg___boxed(lean_object* v___dummy_4917_){
_start:
{
lean_object* v_res_4918_; 
v_res_4918_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension___redArg();
return v_res_4918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension(lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_){
_start:
{
lean_object* v___x_4923_; 
v___x_4923_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0, &l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___redArg___closed__0);
return v___x_4923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_){
_start:
{
lean_object* v_res_4928_; 
v_res_4928_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension(v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
lean_dec_ref(v_a_4927_);
lean_dec_ref(v_a_4926_);
return v_res_4928_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; 
v___x_4932_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2));
v___x_4933_ = lean_unsigned_to_nat(14u);
v___x_4934_ = lean_unsigned_to_nat(178u);
v___x_4935_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1));
v___x_4936_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0));
v___x_4937_ = l_mkPanicMessageWithDecl(v___x_4936_, v___x_4935_, v___x_4934_, v___x_4933_, v___x_4932_);
return v___x_4937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(lean_object* v_inst_4938_, lean_object* v_inst_4939_, lean_object* v_snd_4940_, lean_object* v_inst_4941_, lean_object* v_s_4942_, lean_object* v_e_4943_){
_start:
{
lean_object* v_fst_4944_; lean_object* v_snd_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4960_; 
v_fst_4944_ = lean_ctor_get(v_s_4942_, 0);
v_snd_4945_ = lean_ctor_get(v_s_4942_, 1);
v_isSharedCheck_4960_ = !lean_is_exclusive(v_s_4942_);
if (v_isSharedCheck_4960_ == 0)
{
v___x_4947_ = v_s_4942_;
v_isShared_4948_ = v_isSharedCheck_4960_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_snd_4945_);
lean_inc(v_fst_4944_);
lean_dec(v_s_4942_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4960_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
lean_object* v___x_4949_; lean_object* v___y_4951_; lean_object* v___x_4956_; 
lean_inc_n(v_e_4943_, 2);
v___x_4949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4949_, 0, v_e_4943_);
lean_ctor_set(v___x_4949_, 1, v_fst_4944_);
lean_inc_ref(v_inst_4939_);
lean_inc_ref(v_inst_4938_);
v___x_4956_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_4938_, v_inst_4939_, v_snd_4940_, v_e_4943_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4957_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3);
v___x_4958_ = l_panic___redArg(v_inst_4941_, v___x_4957_);
v___y_4951_ = v___x_4958_;
goto v___jp_4950_;
}
else
{
lean_object* v_val_4959_; 
v_val_4959_ = lean_ctor_get(v___x_4956_, 0);
lean_inc(v_val_4959_);
lean_dec_ref_known(v___x_4956_, 1);
v___y_4951_ = v_val_4959_;
goto v___jp_4950_;
}
v___jp_4950_:
{
lean_object* v___x_4952_; lean_object* v___x_4954_; 
v___x_4952_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_4938_, v_inst_4939_, v_snd_4945_, v_e_4943_, v___y_4951_);
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 1, v___x_4952_);
lean_ctor_set(v___x_4947_, 0, v___x_4949_);
v___x_4954_ = v___x_4947_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v___x_4949_);
lean_ctor_set(v_reuseFailAlloc_4955_, 1, v___x_4952_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed(lean_object* v_inst_4961_, lean_object* v_inst_4962_, lean_object* v_snd_4963_, lean_object* v_inst_4964_, lean_object* v_s_4965_, lean_object* v_e_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(v_inst_4961_, v_inst_4962_, v_snd_4963_, v_inst_4964_, v_s_4965_, v_e_4966_);
lean_dec(v_inst_4964_);
lean_dec(v_snd_4963_);
return v_res_4967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(lean_object* v_inst_4968_, lean_object* v_inst_4969_, lean_object* v_inst_4970_, lean_object* v_oldState_4971_, lean_object* v_newState_4972_, lean_object* v_x_4973_, lean_object* v_s_4974_){
_start:
{
lean_object* v_fst_4975_; lean_object* v_snd_4976_; lean_object* v_fst_4977_; lean_object* v___f_4978_; lean_object* v_newEntries_4979_; lean_object* v___x_4980_; 
v_fst_4975_ = lean_ctor_get(v_newState_4972_, 0);
lean_inc(v_fst_4975_);
v_snd_4976_ = lean_ctor_get(v_newState_4972_, 1);
lean_inc(v_snd_4976_);
lean_dec_ref(v_newState_4972_);
v_fst_4977_ = lean_ctor_get(v_oldState_4971_, 0);
v___f_4978_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_4978_, 0, v_inst_4968_);
lean_closure_set(v___f_4978_, 1, v_inst_4969_);
lean_closure_set(v___f_4978_, 2, v_snd_4976_);
lean_closure_set(v___f_4978_, 3, v_inst_4970_);
v_newEntries_4979_ = l_Lean_takeNewEntries___redArg(v_fst_4975_, v_fst_4977_);
v___x_4980_ = l_List_foldl___redArg(v___f_4978_, v_s_4974_, v_newEntries_4979_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(lean_object* v_inst_4981_, lean_object* v_inst_4982_, lean_object* v_inst_4983_, lean_object* v_oldState_4984_, lean_object* v_newState_4985_, lean_object* v_x_4986_, lean_object* v_s_4987_){
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(v_inst_4981_, v_inst_4982_, v_inst_4983_, v_oldState_4984_, v_newState_4985_, v_x_4986_, v_s_4987_);
lean_dec(v_x_4986_);
lean_dec_ref(v_oldState_4984_);
return v_res_4988_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0(void){
_start:
{
lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4989_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_4990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4989_);
return v___x_4990_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1(void){
_start:
{
lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; 
v___x_4991_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0);
v___x_4992_ = lean_box(0);
v___x_4993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4993_, 0, v___x_4992_);
lean_ctor_set(v___x_4993_, 1, v___x_4991_);
return v___x_4993_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2(void){
_start:
{
lean_object* v___x_4994_; lean_object* v___x_4995_; 
v___x_4994_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1);
v___x_4995_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_4995_, 0, lean_box(0));
lean_closure_set(v___x_4995_, 1, lean_box(0));
lean_closure_set(v___x_4995_, 2, v___x_4994_);
return v___x_4995_;
}
}
lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg(lean_object* v_inst_5007_, lean_object* v_inst_5008_, lean_object* v_inst_5009_){
_start:
{
lean_object* v___f_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; uint8_t v___x_5016_; lean_object* v___x_5017_; 
v___f_5011_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5011_, 0, v_inst_5007_);
lean_closure_set(v___f_5011_, 1, v_inst_5008_);
lean_closure_set(v___f_5011_, 2, v_inst_5009_);
v___x_5012_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2, &l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2);
v___x_5013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5013_, 0, v___f_5011_);
v___x_5014_ = lean_box(0);
v___x_5015_ = ((lean_object*)(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__8));
v___x_5016_ = 0;
v___x_5017_ = l_Lean_registerEnvExtension___redArg(v___x_5012_, v___x_5013_, v___x_5014_, v___x_5015_, v___x_5016_, v___x_5016_);
if (lean_obj_tag(v___x_5017_) == 0)
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5025_; 
v_a_5018_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5025_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5020_ = v___x_5017_;
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_5017_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5023_; 
if (v_isShared_5021_ == 0)
{
v___x_5023_ = v___x_5020_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_5018_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
return v___x_5023_;
}
}
}
else
{
lean_object* v_a_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5033_; 
v_a_5026_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_5028_ = v___x_5017_;
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
else
{
lean_inc(v_a_5026_);
lean_dec(v___x_5017_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v___x_5031_; 
if (v_isShared_5029_ == 0)
{
v___x_5031_ = v___x_5028_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v_a_5026_);
v___x_5031_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
return v___x_5031_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CacheExtension_register___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5007_ = stack[0].m_obj;
lean_object* v_inst_5008_ = stack[1].m_obj;
lean_object* v_inst_5009_ = stack[2].m_obj;
lean_object* v_res_5034_;
v_res_5034_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_5007_, v_inst_5008_, v_inst_5009_);
stack->m_obj
 = v_res_5034_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(lean_object* v_inst_5035_, lean_object* v_inst_5036_, lean_object* v_inst_5037_, lean_object* v_a_5038_){
_start:
{
lean_object* v_res_5039_; 
v_res_5039_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_5035_, v_inst_5036_, v_inst_5037_);
return v_res_5039_;
}
}
lean_object* l_Lean_Compiler_LCNF_CacheExtension_register(lean_object* v_00_u03b1_5040_, lean_object* v_00_u03b2_5041_, lean_object* v_inst_5042_, lean_object* v_inst_5043_, lean_object* v_inst_5044_){
_start:
{
lean_object* v___x_5046_; 
v___x_5046_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(v_inst_5042_, v_inst_5043_, v_inst_5044_);
return v___x_5046_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CacheExtension_register_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5042_ = stack[2].m_obj;
lean_object* v_inst_5043_ = stack[3].m_obj;
lean_object* v_inst_5044_ = stack[4].m_obj;
lean_object* v_res_5047_;
v_res_5047_ = l_Lean_Compiler_LCNF_CacheExtension_register(lean_box(0), lean_box(0), v_inst_5042_, v_inst_5043_, v_inst_5044_);
stack->m_obj
 = v_res_5047_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___boxed(lean_object* v_00_u03b1_5048_, lean_object* v_00_u03b2_5049_, lean_object* v_inst_5050_, lean_object* v_inst_5051_, lean_object* v_inst_5052_, lean_object* v_a_5053_){
_start:
{
lean_object* v_res_5054_; 
v_res_5054_ = l_Lean_Compiler_LCNF_CacheExtension_register(v_00_u03b1_5048_, v_00_u03b2_5049_, v_inst_5050_, v_inst_5051_, v_inst_5052_);
return v_res_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(lean_object* v_a_5055_, lean_object* v_inst_5056_, lean_object* v_inst_5057_, lean_object* v_b_5058_, lean_object* v_x_5059_){
_start:
{
lean_object* v_fst_5060_; lean_object* v_snd_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5070_; 
v_fst_5060_ = lean_ctor_get(v_x_5059_, 0);
v_snd_5061_ = lean_ctor_get(v_x_5059_, 1);
v_isSharedCheck_5070_ = !lean_is_exclusive(v_x_5059_);
if (v_isSharedCheck_5070_ == 0)
{
v___x_5063_ = v_x_5059_;
v_isShared_5064_ = v_isSharedCheck_5070_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_snd_5061_);
lean_inc(v_fst_5060_);
lean_dec(v_x_5059_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5070_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5068_; 
lean_inc(v_a_5055_);
v___x_5065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5065_, 0, v_a_5055_);
lean_ctor_set(v___x_5065_, 1, v_fst_5060_);
v___x_5066_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_5056_, v_inst_5057_, v_snd_5061_, v_a_5055_, v_b_5058_);
if (v_isShared_5064_ == 0)
{
lean_ctor_set(v___x_5063_, 1, v___x_5066_);
lean_ctor_set(v___x_5063_, 0, v___x_5065_);
v___x_5068_ = v___x_5063_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v___x_5065_);
lean_ctor_set(v_reuseFailAlloc_5069_, 1, v___x_5066_);
v___x_5068_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
return v___x_5068_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_5071_; lean_object* v___x_5072_; 
v___x_5071_ = lean_obj_once(&l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0, &l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0);
v___x_5072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5072_, 0, v___x_5071_);
return v___x_5072_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_5073_; lean_object* v___x_5074_; 
v___x_5073_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0);
v___x_5074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5074_, 0, v___x_5073_);
lean_ctor_set(v___x_5074_, 1, v___x_5073_);
return v___x_5074_;
}
}
lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(lean_object* v_inst_5075_, lean_object* v_inst_5076_, lean_object* v_ext_5077_, lean_object* v_a_5078_, lean_object* v_b_5079_, lean_object* v_a_5080_){
_start:
{
lean_object* v___f_5082_; lean_object* v___x_5083_; lean_object* v_env_5084_; lean_object* v_nextMacroScope_5085_; lean_object* v_ngen_5086_; lean_object* v_auxDeclNGen_5087_; lean_object* v_traceState_5088_; lean_object* v_recordedDeps_5089_; lean_object* v_messages_5090_; lean_object* v_infoState_5091_; lean_object* v_snapshotTasks_5092_; lean_object* v___x_5094_; uint8_t v_isShared_5095_; uint8_t v_isSharedCheck_5112_; 
v___f_5082_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0), 5, 4);
lean_closure_set(v___f_5082_, 0, v_a_5078_);
lean_closure_set(v___f_5082_, 1, v_inst_5075_);
lean_closure_set(v___f_5082_, 2, v_inst_5076_);
lean_closure_set(v___f_5082_, 3, v_b_5079_);
v___x_5083_ = lean_st_ref_take(v_a_5080_);
v_env_5084_ = lean_ctor_get(v___x_5083_, 0);
v_nextMacroScope_5085_ = lean_ctor_get(v___x_5083_, 1);
v_ngen_5086_ = lean_ctor_get(v___x_5083_, 2);
v_auxDeclNGen_5087_ = lean_ctor_get(v___x_5083_, 3);
v_traceState_5088_ = lean_ctor_get(v___x_5083_, 4);
v_recordedDeps_5089_ = lean_ctor_get(v___x_5083_, 6);
v_messages_5090_ = lean_ctor_get(v___x_5083_, 7);
v_infoState_5091_ = lean_ctor_get(v___x_5083_, 8);
v_snapshotTasks_5092_ = lean_ctor_get(v___x_5083_, 9);
v_isSharedCheck_5112_ = !lean_is_exclusive(v___x_5083_);
if (v_isSharedCheck_5112_ == 0)
{
lean_object* v_unused_5113_; 
v_unused_5113_ = lean_ctor_get(v___x_5083_, 5);
lean_dec(v_unused_5113_);
v___x_5094_ = v___x_5083_;
v_isShared_5095_ = v_isSharedCheck_5112_;
goto v_resetjp_5093_;
}
else
{
lean_inc(v_snapshotTasks_5092_);
lean_inc(v_infoState_5091_);
lean_inc(v_messages_5090_);
lean_inc(v_recordedDeps_5089_);
lean_inc(v_traceState_5088_);
lean_inc(v_auxDeclNGen_5087_);
lean_inc(v_ngen_5086_);
lean_inc(v_nextMacroScope_5085_);
lean_inc(v_env_5084_);
lean_dec(v___x_5083_);
v___x_5094_ = lean_box(0);
v_isShared_5095_ = v_isSharedCheck_5112_;
goto v_resetjp_5093_;
}
v_resetjp_5093_:
{
lean_object* v_asyncMode_5096_; uint8_t v_logWrites_5097_; lean_object* v___x_5098_; lean_object* v___y_5100_; lean_object* v___x_5107_; uint8_t v___x_5108_; 
v_asyncMode_5096_ = lean_ctor_get(v_ext_5077_, 2);
lean_inc(v_asyncMode_5096_);
v_logWrites_5097_ = lean_ctor_get_uint8(v_ext_5077_, sizeof(void*)*6);
v___x_5098_ = lean_box(0);
v___x_5107_ = lean_box(0);
v___x_5108_ = 1;
if (v_logWrites_5097_ == 0)
{
lean_object* v___x_5109_; 
v___x_5109_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_ext_5077_, v_env_5084_, v___f_5082_, v_asyncMode_5096_, v___x_5107_, v___x_5108_);
lean_dec(v_asyncMode_5096_);
v___y_5100_ = v___x_5109_;
goto v___jp_5099_;
}
else
{
lean_object* v___x_5110_; lean_object* v___x_5111_; 
lean_inc_ref(v_ext_5077_);
v___x_5110_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_ext_5077_, v_env_5084_);
lean_dec_ref(v_env_5084_);
v___x_5111_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_ext_5077_, v___x_5110_, v___f_5082_, v_asyncMode_5096_, v___x_5107_, v___x_5108_);
lean_dec(v_asyncMode_5096_);
v___y_5100_ = v___x_5111_;
goto v___jp_5099_;
}
v___jp_5099_:
{
lean_object* v___x_5101_; lean_object* v___x_5103_; 
v___x_5101_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1);
if (v_isShared_5095_ == 0)
{
lean_ctor_set(v___x_5094_, 5, v___x_5101_);
lean_ctor_set(v___x_5094_, 0, v___y_5100_);
v___x_5103_ = v___x_5094_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v___y_5100_);
lean_ctor_set(v_reuseFailAlloc_5106_, 1, v_nextMacroScope_5085_);
lean_ctor_set(v_reuseFailAlloc_5106_, 2, v_ngen_5086_);
lean_ctor_set(v_reuseFailAlloc_5106_, 3, v_auxDeclNGen_5087_);
lean_ctor_set(v_reuseFailAlloc_5106_, 4, v_traceState_5088_);
lean_ctor_set(v_reuseFailAlloc_5106_, 5, v___x_5101_);
lean_ctor_set(v_reuseFailAlloc_5106_, 6, v_recordedDeps_5089_);
lean_ctor_set(v_reuseFailAlloc_5106_, 7, v_messages_5090_);
lean_ctor_set(v_reuseFailAlloc_5106_, 8, v_infoState_5091_);
lean_ctor_set(v_reuseFailAlloc_5106_, 9, v_snapshotTasks_5092_);
v___x_5103_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
lean_object* v___x_5104_; lean_object* v___x_5105_; 
v___x_5104_ = lean_st_ref_put(v_a_5080_, v___x_5103_);
v___x_5105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5105_, 0, v___x_5098_);
return v___x_5105_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CacheExtension_insert___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5075_ = stack[0].m_obj;
lean_object* v_inst_5076_ = stack[1].m_obj;
lean_object* v_ext_5077_ = stack[2].m_obj;
lean_object* v_a_5078_ = stack[3].m_obj;
lean_object* v_b_5079_ = stack[4].m_obj;
lean_object* v_a_5080_ = stack[5].m_obj;
lean_object* v_res_5114_;
v_res_5114_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_5075_, v_inst_5076_, v_ext_5077_, v_a_5078_, v_b_5079_, v_a_5080_);
stack->m_obj
 = v_res_5114_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(lean_object* v_inst_5115_, lean_object* v_inst_5116_, lean_object* v_ext_5117_, lean_object* v_a_5118_, lean_object* v_b_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_){
_start:
{
lean_object* v_res_5122_; 
v_res_5122_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_5115_, v_inst_5116_, v_ext_5117_, v_a_5118_, v_b_5119_, v_a_5120_);
lean_dec(v_a_5120_);
return v_res_5122_;
}
}
lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert(lean_object* v_00_u03b1_5123_, lean_object* v_00_u03b2_5124_, lean_object* v_inst_5125_, lean_object* v_inst_5126_, lean_object* v_inst_5127_, lean_object* v_ext_5128_, lean_object* v_a_5129_, lean_object* v_b_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_){
_start:
{
lean_object* v___x_5134_; 
v___x_5134_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(v_inst_5125_, v_inst_5126_, v_ext_5128_, v_a_5129_, v_b_5130_, v_a_5132_);
return v___x_5134_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CacheExtension_insert_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5125_ = stack[2].m_obj;
lean_object* v_inst_5126_ = stack[3].m_obj;
lean_object* v_inst_5127_ = stack[4].m_obj;
lean_object* v_ext_5128_ = stack[5].m_obj;
lean_object* v_a_5129_ = stack[6].m_obj;
lean_object* v_b_5130_ = stack[7].m_obj;
lean_object* v_a_5131_ = stack[8].m_obj;
lean_object* v_a_5132_ = stack[9].m_obj;
lean_object* v_res_5135_;
v_res_5135_ = l_Lean_Compiler_LCNF_CacheExtension_insert(lean_box(0), lean_box(0), v_inst_5125_, v_inst_5126_, v_inst_5127_, v_ext_5128_, v_a_5129_, v_b_5130_, v_a_5131_, v_a_5132_);
stack->m_obj
 = v_res_5135_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(lean_object* v_00_u03b1_5136_, lean_object* v_00_u03b2_5137_, lean_object* v_inst_5138_, lean_object* v_inst_5139_, lean_object* v_inst_5140_, lean_object* v_ext_5141_, lean_object* v_a_5142_, lean_object* v_b_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_){
_start:
{
lean_object* v_res_5147_; 
v_res_5147_ = l_Lean_Compiler_LCNF_CacheExtension_insert(v_00_u03b1_5136_, v_00_u03b2_5137_, v_inst_5138_, v_inst_5139_, v_inst_5140_, v_ext_5141_, v_a_5142_, v_b_5143_, v_a_5144_, v_a_5145_);
lean_dec(v_a_5145_);
lean_dec_ref(v_a_5144_);
lean_dec(v_inst_5140_);
return v_res_5147_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_5148_; 
v___x_5148_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_5148_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; 
v___x_5149_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0, &l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__0);
v___x_5150_ = lean_box(0);
v___x_5151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5151_, 0, v___x_5150_);
lean_ctor_set(v___x_5151_, 1, v___x_5149_);
return v___x_5151_;
}
}
lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(lean_object* v_inst_5152_, lean_object* v_inst_5153_, lean_object* v_ext_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_){
_start:
{
lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v_env_5160_; lean_object* v_asyncMode_5161_; lean_object* v___x_5162_; uint8_t v___x_5163_; lean_object* v___x_5164_; lean_object* v_snd_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; 
v___x_5158_ = lean_obj_once(&l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1, &l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___closed__1);
v___x_5159_ = lean_st_ref_get(v_a_5156_);
v_env_5160_ = lean_ctor_get(v___x_5159_, 0);
lean_inc_ref(v_env_5160_);
lean_dec(v___x_5159_);
v_asyncMode_5161_ = lean_ctor_get(v_ext_5154_, 2);
v___x_5162_ = lean_box(0);
v___x_5163_ = 0;
v___x_5164_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5158_, v_ext_5154_, v_env_5160_, v_asyncMode_5161_, v___x_5162_, v___x_5163_);
v_snd_5165_ = lean_ctor_get(v___x_5164_, 1);
lean_inc(v_snd_5165_);
lean_dec(v___x_5164_);
v___x_5166_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_5152_, v_inst_5153_, v_snd_5165_, v_a_5155_);
lean_dec(v_snd_5165_);
v___x_5167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5167_, 0, v___x_5166_);
return v___x_5167_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5152_ = stack[0].m_obj;
lean_object* v_inst_5153_ = stack[1].m_obj;
lean_object* v_ext_5154_ = stack[2].m_obj;
lean_object* v_a_5155_ = stack[3].m_obj;
lean_object* v_a_5156_ = stack[4].m_obj;
lean_object* v_res_5168_;
v_res_5168_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_5152_, v_inst_5153_, v_ext_5154_, v_a_5155_, v_a_5156_);
stack->m_obj
 = v_res_5168_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(lean_object* v_inst_5169_, lean_object* v_inst_5170_, lean_object* v_ext_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_){
_start:
{
lean_object* v_res_5175_; 
v_res_5175_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_5169_, v_inst_5170_, v_ext_5171_, v_a_5172_, v_a_5173_);
lean_dec(v_a_5173_);
lean_dec_ref(v_ext_5171_);
return v_res_5175_;
}
}
lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_object* v_00_u03b1_5176_, lean_object* v_00_u03b2_5177_, lean_object* v_inst_5178_, lean_object* v_inst_5179_, lean_object* v_inst_5180_, lean_object* v_ext_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_){
_start:
{
lean_object* v___x_5186_; 
v___x_5186_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(v_inst_5178_, v_inst_5179_, v_ext_5181_, v_a_5182_, v_a_5184_);
return v___x_5186_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CacheExtension_find_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5178_ = stack[2].m_obj;
lean_object* v_inst_5179_ = stack[3].m_obj;
lean_object* v_inst_5180_ = stack[4].m_obj;
lean_object* v_ext_5181_ = stack[5].m_obj;
lean_object* v_a_5182_ = stack[6].m_obj;
lean_object* v_a_5183_ = stack[7].m_obj;
lean_object* v_a_5184_ = stack[8].m_obj;
lean_object* v_res_5187_;
v_res_5187_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(lean_box(0), lean_box(0), v_inst_5178_, v_inst_5179_, v_inst_5180_, v_ext_5181_, v_a_5182_, v_a_5183_, v_a_5184_);
stack->m_obj
 = v_res_5187_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(lean_object* v_00_u03b1_5188_, lean_object* v_00_u03b2_5189_, lean_object* v_inst_5190_, lean_object* v_inst_5191_, lean_object* v_inst_5192_, lean_object* v_ext_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_, lean_object* v_a_5197_){
_start:
{
lean_object* v_res_5198_; 
v_res_5198_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(v_00_u03b1_5188_, v_00_u03b2_5189_, v_inst_5190_, v_inst_5191_, v_inst_5192_, v_ext_5193_, v_a_5194_, v_a_5195_, v_a_5196_);
lean_dec(v_a_5196_);
lean_dec_ref(v_a_5195_);
lean_dec_ref(v_ext_5193_);
lean_dec(v_inst_5192_);
return v_res_5198_;
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
