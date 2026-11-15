// Lean compiler output
// Module: Lean.Meta.Match.SimpH
// Imports: public import Lean.Meta.Basic import Lean.Meta.Tactic.Contradiction
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_heqToEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_contradictionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_closeIfDistinctFloatLits(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Lean_MVarId_tryClearMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Meta.Match.SimpH"};
static const lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "_private.Lean.Meta.Match.SimpH.0.Lean.Meta.Match.SimpH.substRHS"};
static const lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Match.SimpH.2345676235._hygCtx._hyg.10.0 ).xs.contains rhs\n  "};
static const lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(16) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst_spec__0(lean_object* v_s_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
if (lean_obj_tag(v_a_2_) == 0)
{
lean_object* v___x_4_; 
lean_dec(v_s_1_);
v___x_4_ = lean_array_to_list(v_a_3_);
return v___x_4_;
}
else
{
lean_object* v_head_5_; lean_object* v_tail_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_head_5_ = lean_ctor_get(v_a_2_, 0);
lean_inc(v_head_5_);
v_tail_6_ = lean_ctor_get(v_a_2_, 1);
lean_inc(v_tail_6_);
lean_dec_ref_known(v_a_2_, 2);
v___x_7_ = l_Lean_mkFVar(v_head_5_);
lean_inc(v_s_1_);
v___x_8_ = l_Lean_Meta_FVarSubst_apply(v_s_1_, v___x_7_);
lean_dec_ref(v___x_7_);
if (lean_obj_tag(v___x_8_) == 1)
{
lean_object* v_fvarId_9_; lean_object* v___x_10_; 
v_fvarId_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fvarId_9_);
lean_dec_ref_known(v___x_8_, 1);
v___x_10_ = lean_array_push(v_a_3_, v_fvarId_9_);
v_a_2_ = v_tail_6_;
v_a_3_ = v___x_10_;
goto _start;
}
else
{
lean_dec_ref(v___x_8_);
v_a_2_ = v_tail_6_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(lean_object* v_s_15_, lean_object* v_fvarIds_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = ((lean_object*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0));
v___x_18_ = l_List_filterMapTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst_spec__0(v_s_15_, v_fvarIds_16_, v___x_17_);
return v___x_18_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_instMonadEIO___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1(lean_object* v_msg_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v_toApplicative_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_95_; 
v___x_31_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0);
v___x_32_ = l_StateRefT_x27_instMonad___redArg(v___x_31_);
v_toApplicative_33_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_95_ == 0)
{
lean_object* v_unused_96_; 
v_unused_96_ = lean_ctor_get(v___x_32_, 1);
lean_dec(v_unused_96_);
v___x_35_ = v___x_32_;
v_isShared_36_ = v_isSharedCheck_95_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_toApplicative_33_);
lean_dec(v___x_32_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_95_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v_toFunctor_37_; lean_object* v_toSeq_38_; lean_object* v_toSeqLeft_39_; lean_object* v_toSeqRight_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_93_; 
v_toFunctor_37_ = lean_ctor_get(v_toApplicative_33_, 0);
v_toSeq_38_ = lean_ctor_get(v_toApplicative_33_, 2);
v_toSeqLeft_39_ = lean_ctor_get(v_toApplicative_33_, 3);
v_toSeqRight_40_ = lean_ctor_get(v_toApplicative_33_, 4);
v_isSharedCheck_93_ = !lean_is_exclusive(v_toApplicative_33_);
if (v_isSharedCheck_93_ == 0)
{
lean_object* v_unused_94_; 
v_unused_94_ = lean_ctor_get(v_toApplicative_33_, 1);
lean_dec(v_unused_94_);
v___x_42_ = v_toApplicative_33_;
v_isShared_43_ = v_isSharedCheck_93_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_toSeqRight_40_);
lean_inc(v_toSeqLeft_39_);
lean_inc(v_toSeq_38_);
lean_inc(v_toFunctor_37_);
lean_dec(v_toApplicative_33_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_93_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___f_44_; lean_object* v___f_45_; lean_object* v___f_46_; lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___f_49_; lean_object* v___f_50_; lean_object* v___f_51_; lean_object* v___x_53_; 
v___f_44_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__1));
v___f_45_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__2));
lean_inc_ref(v_toFunctor_37_);
v___f_46_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_46_, 0, v_toFunctor_37_);
v___f_47_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_47_, 0, v_toFunctor_37_);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v___f_46_);
lean_ctor_set(v___x_48_, 1, v___f_47_);
v___f_49_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_49_, 0, v_toSeqRight_40_);
v___f_50_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_50_, 0, v_toSeqLeft_39_);
v___f_51_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_51_, 0, v_toSeq_38_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 4, v___f_49_);
lean_ctor_set(v___x_42_, 3, v___f_50_);
lean_ctor_set(v___x_42_, 2, v___f_51_);
lean_ctor_set(v___x_42_, 1, v___f_44_);
lean_ctor_set(v___x_42_, 0, v___x_48_);
v___x_53_ = v___x_42_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_48_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v___f_44_);
lean_ctor_set(v_reuseFailAlloc_92_, 2, v___f_51_);
lean_ctor_set(v_reuseFailAlloc_92_, 3, v___f_50_);
lean_ctor_set(v_reuseFailAlloc_92_, 4, v___f_49_);
v___x_53_ = v_reuseFailAlloc_92_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
lean_object* v___x_55_; 
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 1, v___f_45_);
lean_ctor_set(v___x_35_, 0, v___x_53_);
v___x_55_ = v___x_35_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_53_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v___f_45_);
v___x_55_ = v_reuseFailAlloc_91_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
lean_object* v___x_56_; lean_object* v_toApplicative_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_89_; 
v___x_56_ = l_StateRefT_x27_instMonad___redArg(v___x_55_);
v_toApplicative_57_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v___x_56_, 1);
lean_dec(v_unused_90_);
v___x_59_ = v___x_56_;
v_isShared_60_ = v_isSharedCheck_89_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_toApplicative_57_);
lean_dec(v___x_56_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_89_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v_toFunctor_61_; lean_object* v_toSeq_62_; lean_object* v_toSeqLeft_63_; lean_object* v_toSeqRight_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_87_; 
v_toFunctor_61_ = lean_ctor_get(v_toApplicative_57_, 0);
v_toSeq_62_ = lean_ctor_get(v_toApplicative_57_, 2);
v_toSeqLeft_63_ = lean_ctor_get(v_toApplicative_57_, 3);
v_toSeqRight_64_ = lean_ctor_get(v_toApplicative_57_, 4);
v_isSharedCheck_87_ = !lean_is_exclusive(v_toApplicative_57_);
if (v_isSharedCheck_87_ == 0)
{
lean_object* v_unused_88_; 
v_unused_88_ = lean_ctor_get(v_toApplicative_57_, 1);
lean_dec(v_unused_88_);
v___x_66_ = v_toApplicative_57_;
v_isShared_67_ = v_isSharedCheck_87_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_toSeqRight_64_);
lean_inc(v_toSeqLeft_63_);
lean_inc(v_toSeq_62_);
lean_inc(v_toFunctor_61_);
lean_dec(v_toApplicative_57_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_87_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___f_68_; lean_object* v___f_69_; lean_object* v___f_70_; lean_object* v___f_71_; lean_object* v___x_72_; lean_object* v___f_73_; lean_object* v___f_74_; lean_object* v___f_75_; lean_object* v___x_77_; 
v___f_68_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3));
v___f_69_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4));
lean_inc_ref(v_toFunctor_61_);
v___f_70_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_70_, 0, v_toFunctor_61_);
v___f_71_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_71_, 0, v_toFunctor_61_);
v___x_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_72_, 0, v___f_70_);
lean_ctor_set(v___x_72_, 1, v___f_71_);
v___f_73_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_73_, 0, v_toSeqRight_64_);
v___f_74_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_74_, 0, v_toSeqLeft_63_);
v___f_75_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_75_, 0, v_toSeq_62_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 4, v___f_73_);
lean_ctor_set(v___x_66_, 3, v___f_74_);
lean_ctor_set(v___x_66_, 2, v___f_75_);
lean_ctor_set(v___x_66_, 1, v___f_68_);
lean_ctor_set(v___x_66_, 0, v___x_72_);
v___x_77_ = v___x_66_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_72_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v___f_68_);
lean_ctor_set(v_reuseFailAlloc_86_, 2, v___f_75_);
lean_ctor_set(v_reuseFailAlloc_86_, 3, v___f_74_);
lean_ctor_set(v_reuseFailAlloc_86_, 4, v___f_73_);
v___x_77_ = v_reuseFailAlloc_86_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_79_; 
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 1, v___f_69_);
lean_ctor_set(v___x_59_, 0, v___x_77_);
v___x_79_ = v___x_59_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v___f_69_);
v___x_79_ = v_reuseFailAlloc_85_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_1500__overap_83_; lean_object* v___x_84_; 
v___x_80_ = l_StateRefT_x27_instMonad___redArg(v___x_79_);
v___x_81_ = lean_box(0);
v___x_82_ = l_instInhabitedOfMonad___redArg(v___x_80_, v___x_81_);
v___x_1500__overap_83_ = lean_panic_fn_borrowed(v___x_82_, v_msg_24_);
lean_dec(v___x_82_);
lean_inc(v___y_29_);
lean_inc_ref(v___y_28_);
lean_inc(v___y_27_);
lean_inc_ref(v___y_26_);
lean_inc(v___y_25_);
v___x_84_ = lean_apply_6(v___x_1500__overap_83_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, lean_box(0));
return v___x_84_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___boxed(lean_object* v_msg_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1(v_msg_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
return v_res_104_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(lean_object* v_a_105_, lean_object* v_x_106_){
_start:
{
if (lean_obj_tag(v_x_106_) == 0)
{
uint8_t v___x_107_; 
v___x_107_ = 0;
return v___x_107_;
}
else
{
lean_object* v_head_108_; lean_object* v_tail_109_; uint8_t v___x_110_; 
v_head_108_ = lean_ctor_get(v_x_106_, 0);
v_tail_109_ = lean_ctor_get(v_x_106_, 1);
v___x_110_ = l_Lean_instBEqFVarId_beq(v_a_105_, v_head_108_);
if (v___x_110_ == 0)
{
v_x_106_ = v_tail_109_;
goto _start;
}
else
{
return v___x_110_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0___boxed(lean_object* v_a_112_, lean_object* v_x_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(v_a_112_, v_x_113_);
lean_dec(v_x_113_);
lean_dec(v_a_112_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2(lean_object* v_as_116_, size_t v_i_117_, size_t v_stop_118_, lean_object* v_b_119_){
_start:
{
uint8_t v___x_120_; 
v___x_120_ = lean_usize_dec_eq(v_i_117_, v_stop_118_);
if (v___x_120_ == 0)
{
size_t v___x_121_; size_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_121_ = ((size_t)1ULL);
v___x_122_ = lean_usize_sub(v_i_117_, v___x_121_);
v___x_123_ = lean_array_uget_borrowed(v_as_116_, v___x_122_);
lean_inc(v___x_123_);
v___x_124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v_b_119_);
v_i_117_ = v___x_122_;
v_b_119_ = v___x_124_;
goto _start;
}
else
{
return v_b_119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2___boxed(lean_object* v_as_126_, lean_object* v_i_127_, lean_object* v_stop_128_, lean_object* v_b_129_){
_start:
{
size_t v_i_boxed_130_; size_t v_stop_boxed_131_; lean_object* v_res_132_; 
v_i_boxed_130_ = lean_unbox_usize(v_i_127_);
lean_dec(v_i_127_);
v_stop_boxed_131_ = lean_unbox_usize(v_stop_128_);
lean_dec(v_stop_128_);
v_res_132_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2(v_as_126_, v_i_boxed_130_, v_stop_boxed_131_, v_b_129_);
lean_dec_ref(v_as_126_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(lean_object* v_l_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
if (lean_obj_tag(v_a_135_) == 0)
{
lean_dec_ref(v_a_136_);
lean_inc(v_l_133_);
return v_l_133_;
}
else
{
lean_object* v_head_137_; lean_object* v_tail_138_; uint8_t v___x_139_; 
v_head_137_ = lean_ctor_get(v_a_135_, 0);
lean_inc(v_head_137_);
v_tail_138_ = lean_ctor_get(v_a_135_, 1);
lean_inc(v_tail_138_);
lean_dec_ref_known(v_a_135_, 2);
v___x_139_ = l_Lean_instBEqFVarId_beq(v_head_137_, v_a_134_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
v___x_140_ = lean_array_push(v_a_136_, v_head_137_);
v_a_135_ = v_tail_138_;
v_a_136_ = v___x_140_;
goto _start;
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
lean_dec(v_head_137_);
v___x_142_ = lean_array_get_size(v_a_136_);
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = lean_nat_dec_lt(v___x_143_, v___x_142_);
if (v___x_144_ == 0)
{
lean_dec_ref(v_a_136_);
return v_tail_138_;
}
else
{
size_t v___x_145_; size_t v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_usize_of_nat(v___x_142_);
v___x_146_ = ((size_t)0ULL);
v___x_147_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2(v_a_136_, v___x_145_, v___x_146_, v_tail_138_);
lean_dec_ref(v_a_136_);
return v___x_147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2___boxed(lean_object* v_l_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(v_l_148_, v_a_149_, v_a_150_, v_a_151_);
lean_dec(v_a_149_);
lean_dec(v_l_148_);
return v_res_152_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_156_ = ((lean_object*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__2));
v___x_157_ = lean_unsigned_to_nat(2u);
v___x_158_ = lean_unsigned_to_nat(46u);
v___x_159_ = ((lean_object*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__1));
v___x_160_ = ((lean_object*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__0));
v___x_161_ = l_mkPanicMessageWithDecl(v___x_160_, v___x_159_, v___x_158_, v___x_157_, v___x_156_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(lean_object* v_eq_162_, lean_object* v_rhs_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_170_; lean_object* v_xs_171_; uint8_t v___x_172_; 
v___x_170_ = lean_st_ref_get(v_a_164_);
v_xs_171_ = lean_ctor_get(v___x_170_, 1);
lean_inc(v_xs_171_);
lean_dec(v___x_170_);
v___x_172_ = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(v_rhs_163_, v_xs_171_);
lean_dec(v_xs_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec(v_eq_162_);
v___x_173_ = lean_obj_once(&l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3, &l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3_once, _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3);
v___x_174_ = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1(v___x_173_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; lean_object* v_mvarId_176_; lean_object* v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; 
v___x_175_ = lean_st_ref_get(v_a_164_);
v_mvarId_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_mvarId_176_);
lean_dec(v___x_175_);
v___x_177_ = lean_box(0);
v___x_178_ = 0;
v___x_179_ = l_Lean_Meta_substCore(v_mvarId_176_, v_eq_162_, v___x_172_, v___x_177_, v___x_172_, v___x_178_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_208_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_208_ == 0)
{
v___x_182_ = v___x_179_;
v_isShared_183_ = v_isSharedCheck_208_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_208_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v_fst_184_; lean_object* v_snd_185_; lean_object* v___x_186_; lean_object* v_xs_187_; lean_object* v_eqs_188_; lean_object* v_eqsNew_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_206_; 
v_fst_184_ = lean_ctor_get(v_a_180_, 0);
lean_inc(v_fst_184_);
v_snd_185_ = lean_ctor_get(v_a_180_, 1);
lean_inc(v_snd_185_);
lean_dec(v_a_180_);
v___x_186_ = lean_st_ref_take(v_a_164_);
v_xs_187_ = lean_ctor_get(v___x_186_, 1);
v_eqs_188_ = lean_ctor_get(v___x_186_, 2);
v_eqsNew_189_ = lean_ctor_get(v___x_186_, 3);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; 
v_unused_207_ = lean_ctor_get(v___x_186_, 0);
lean_dec(v_unused_207_);
v___x_191_ = v___x_186_;
v_isShared_192_ = v_isSharedCheck_206_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_eqsNew_189_);
lean_inc(v_eqs_188_);
lean_inc(v_xs_187_);
lean_dec(v___x_186_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_206_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_193_ = lean_box(0);
v___x_194_ = ((lean_object*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0));
lean_inc(v_xs_187_);
v___x_195_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(v_xs_187_, v_rhs_163_, v_xs_187_, v___x_194_);
lean_dec(v_xs_187_);
lean_inc_n(v_fst_184_, 2);
v___x_196_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(v_fst_184_, v___x_195_);
v___x_197_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(v_fst_184_, v_eqs_188_);
v___x_198_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(v_fst_184_, v_eqsNew_189_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 3, v___x_198_);
lean_ctor_set(v___x_191_, 2, v___x_197_);
lean_ctor_set(v___x_191_, 1, v___x_196_);
lean_ctor_set(v___x_191_, 0, v_snd_185_);
v___x_200_ = v___x_191_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_snd_185_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v___x_198_);
v___x_200_ = v_reuseFailAlloc_205_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_201_ = lean_st_ref_put(v_a_164_, v___x_200_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_193_);
v___x_203_ = v___x_182_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_193_);
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
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
v_a_209_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_179_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_179_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___boxed(lean_object* v_eq_217_, lean_object* v_rhs_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(v_eq_217_, v_rhs_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec(v_rhs_218_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(lean_object* v_a_226_){
_start:
{
lean_object* v___x_228_; lean_object* v_eqs_229_; uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_228_ = lean_st_ref_get(v_a_226_);
v_eqs_229_ = lean_ctor_get(v___x_228_, 2);
lean_inc(v_eqs_229_);
lean_dec(v___x_228_);
v___x_230_ = l_List_isEmpty___redArg(v_eqs_229_);
lean_dec(v_eqs_229_);
v___x_231_ = lean_box(v___x_230_);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg___boxed(lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(v_a_233_);
lean_dec(v_a_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone(lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(v_a_236_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___boxed(lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone(v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(lean_object* v_mvarId_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___closed__0));
v___x_261_ = l_Lean_MVarId_contradictionCore(v_mvarId_254_, v___x_260_, v_a_255_, v_a_256_, v_a_257_, v_a_258_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___boxed(lean_object* v_mvarId_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(v_mvarId_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(lean_object* v_x_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Meta_saveState___redArg(v___y_271_, v___y_273_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___y_278_; lean_object* v_a_279_; lean_object* v___x_299_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
lean_inc(v___y_273_);
lean_inc_ref(v___y_272_);
lean_inc(v___y_271_);
lean_inc_ref(v___y_270_);
v___x_299_ = lean_apply_5(v_x_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, lean_box(0));
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; uint8_t v___x_301_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_300_);
v___x_301_ = lean_unbox(v_a_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; 
lean_dec_ref_known(v___x_299_, 1);
lean_inc(v_a_276_);
v___x_302_ = l_Lean_Meta_SavedState_restore___redArg(v_a_276_, v___y_271_, v___y_273_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec(v_a_276_);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_309_ == 0)
{
lean_object* v_unused_310_; 
v_unused_310_ = lean_ctor_get(v___x_302_, 0);
lean_dec(v_unused_310_);
v___x_304_ = v___x_302_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_dec(v___x_302_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v_a_300_);
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_300_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_dec(v_a_300_);
v_a_311_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_302_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_302_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
lean_inc(v_a_311_);
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
v___y_278_ = v___x_316_;
v_a_279_ = v_a_311_;
goto v___jp_277_;
}
}
}
}
else
{
lean_dec(v_a_300_);
lean_dec(v_a_276_);
return v___x_299_;
}
}
else
{
lean_object* v_a_319_; 
v_a_319_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_319_);
v___y_278_ = v___x_299_;
v_a_279_ = v_a_319_;
goto v___jp_277_;
}
v___jp_277_:
{
uint8_t v___x_280_; 
v___x_280_ = l_Lean_Exception_isInterrupt(v_a_279_);
if (v___x_280_ == 0)
{
uint8_t v___x_281_; 
lean_inc_ref(v_a_279_);
v___x_281_ = l_Lean_Exception_isRuntime(v_a_279_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; 
lean_dec_ref(v___y_278_);
v___x_282_ = l_Lean_Meta_SavedState_restore___redArg(v_a_276_, v___y_271_, v___y_273_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; 
v_unused_290_ = lean_ctor_get(v___x_282_, 0);
lean_dec(v_unused_290_);
v___x_284_ = v___x_282_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_dec(v___x_282_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
lean_ctor_set_tag(v___x_284_, 1);
lean_ctor_set(v___x_284_, 0, v_a_279_);
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_279_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec_ref(v_a_279_);
v_a_291_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_282_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_282_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
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
else
{
lean_dec_ref(v_a_279_);
lean_dec(v_a_276_);
return v___y_278_;
}
}
else
{
lean_dec_ref(v_a_279_);
lean_dec(v_a_276_);
return v___y_278_;
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec_ref(v_x_269_);
v_a_320_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_275_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_275_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0___boxed(lean_object* v_x_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(v_x_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0(lean_object* v_mvarId_335_, lean_object* v_forbidden_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Meta_substVars(v_mvarId_335_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc_n(v_a_343_, 2);
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = lean_box(0);
v___x_345_ = lean_unsigned_to_nat(5u);
v___x_346_ = l_Lean_Meta_injections(v_a_343_, v___x_344_, v___x_345_, v_forbidden_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_361_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_361_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_361_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_361_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
if (lean_obj_tag(v_a_347_) == 0)
{
uint8_t v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
lean_dec(v_a_343_);
v___x_351_ = 1;
v___x_352_ = lean_box(v___x_351_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_352_);
v___x_354_ = v___x_349_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
else
{
lean_object* v_mvarId_356_; lean_object* v_forbidden_357_; uint8_t v___x_358_; 
lean_del_object(v___x_349_);
v_mvarId_356_ = lean_ctor_get(v_a_347_, 0);
lean_inc(v_mvarId_356_);
v_forbidden_357_ = lean_ctor_get(v_a_347_, 2);
lean_inc(v_forbidden_357_);
lean_dec_ref_known(v_a_347_, 3);
v___x_358_ = l_Lean_instBEqMVarId_beq(v_mvarId_356_, v_a_343_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
lean_dec(v_a_343_);
v___x_359_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(v_mvarId_356_, v_forbidden_357_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
return v___x_359_;
}
else
{
lean_object* v___x_360_; 
lean_dec(v_forbidden_357_);
lean_dec(v_mvarId_356_);
v___x_360_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(v_a_343_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
return v___x_360_;
}
}
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec(v_a_343_);
v_a_362_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_346_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_346_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
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
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec(v_forbidden_336_);
v_a_370_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_342_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_342_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0___boxed(lean_object* v_mvarId_378_, lean_object* v_forbidden_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0(v_mvarId_378_, v_forbidden_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(lean_object* v_mvarId_386_, lean_object* v_forbidden_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___f_393_; lean_object* v___x_394_; 
v___f_393_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0___boxed), 7, 2);
lean_closure_set(v___f_393_, 0, v_mvarId_386_);
lean_closure_set(v___f_393_, 1, v_forbidden_387_);
v___x_394_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(v___f_393_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___boxed(lean_object* v_mvarId_395_, lean_object* v_forbidden_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(v_mvarId_395_, v_forbidden_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0(lean_object* v_x_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v___x_410_; 
lean_inc(v___y_404_);
v___x_410_ = lean_apply_6(v_x_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, lean_box(0));
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0___boxed(lean_object* v_x_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0(v_x_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_412_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(lean_object* v_mvarId_419_, lean_object* v_x_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___f_427_; lean_object* v___x_428_; 
lean_inc(v___y_421_);
v___f_427_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_427_, 0, v_x_420_);
lean_closure_set(v___f_427_, 1, v___y_421_);
v___x_428_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_419_, v___f_427_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_428_) == 0)
{
return v___x_428_;
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___boxed(lean_object* v_mvarId_437_, lean_object* v_x_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(v_mvarId_437_, v_x_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0(lean_object* v_00_u03b1_446_, lean_object* v_mvarId_447_, lean_object* v_x_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(v_mvarId_447_, v_x_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___boxed(lean_object* v_00_u03b1_456_, lean_object* v_mvarId_457_, lean_object* v_x_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0(v_00_u03b1_456_, v_mvarId_457_, v_x_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0(lean_object* v_____r_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
uint8_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = 1;
v___x_474_ = lean_box(v___x_473_);
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0___boxed(lean_object* v_____r_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0(v_____r_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1(lean_object* v_eqs_484_, lean_object* v_mvarId_485_, lean_object* v___f_486_, lean_object* v___x_487_, lean_object* v_xs_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
if (lean_obj_tag(v_eqs_484_) == 1)
{
lean_object* v_head_495_; lean_object* v_tail_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_742_; 
v_head_495_ = lean_ctor_get(v_eqs_484_, 0);
v_tail_496_ = lean_ctor_get(v_eqs_484_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_eqs_484_);
if (v_isSharedCheck_742_ == 0)
{
v___x_498_ = v_eqs_484_;
v_isShared_499_ = v_isSharedCheck_742_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_tail_496_);
lean_inc(v_head_495_);
lean_dec(v_eqs_484_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_742_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___x_568_; lean_object* v_mvarId_569_; lean_object* v_xs_570_; lean_object* v_eqsNew_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_740_; 
v___x_568_ = lean_st_ref_take(v___y_489_);
v_mvarId_569_ = lean_ctor_get(v___x_568_, 0);
v_xs_570_ = lean_ctor_get(v___x_568_, 1);
v_eqsNew_571_ = lean_ctor_get(v___x_568_, 3);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v___x_568_, 2);
lean_dec(v_unused_741_);
v___x_573_ = v___x_568_;
v_isShared_574_ = v_isSharedCheck_740_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_eqsNew_571_);
lean_inc(v_xs_570_);
lean_inc(v_mvarId_569_);
lean_dec(v___x_568_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_740_;
goto v_resetjp_572_;
}
v___jp_500_:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_box(0);
lean_inc(v_head_495_);
v___x_507_ = l_Lean_Meta_injection(v_mvarId_485_, v_head_495_, v___x_506_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_536_; 
lean_del_object(v___x_498_);
lean_dec(v_head_495_);
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_536_ == 0)
{
v___x_510_ = v___x_507_;
v_isShared_511_ = v_isSharedCheck_536_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_536_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
if (lean_obj_tag(v_a_508_) == 0)
{
uint8_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
lean_dec_ref(v___f_486_);
v___x_512_ = 0;
v___x_513_ = lean_box(v___x_512_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_513_);
v___x_515_ = v___x_510_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
else
{
lean_object* v_mvarId_517_; lean_object* v_newEqs_518_; lean_object* v___x_519_; lean_object* v_xs_520_; lean_object* v_eqs_521_; lean_object* v_eqsNew_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_534_; 
lean_del_object(v___x_510_);
v_mvarId_517_ = lean_ctor_get(v_a_508_, 0);
lean_inc(v_mvarId_517_);
v_newEqs_518_ = lean_ctor_get(v_a_508_, 1);
lean_inc_ref(v_newEqs_518_);
lean_dec_ref_known(v_a_508_, 3);
v___x_519_ = lean_st_ref_take(v___y_501_);
v_xs_520_ = lean_ctor_get(v___x_519_, 1);
v_eqs_521_ = lean_ctor_get(v___x_519_, 2);
v_eqsNew_522_ = lean_ctor_get(v___x_519_, 3);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; 
v_unused_535_ = lean_ctor_get(v___x_519_, 0);
lean_dec(v_unused_535_);
v___x_524_ = v___x_519_;
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_eqsNew_522_);
lean_inc(v_eqs_521_);
lean_inc(v_xs_520_);
lean_dec(v___x_519_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_526_ = lean_box(0);
v___x_527_ = lean_array_to_list(v_newEqs_518_);
v___x_528_ = l_List_appendTR___redArg(v___x_527_, v_eqs_521_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 2, v___x_528_);
lean_ctor_set(v___x_524_, 0, v_mvarId_517_);
v___x_530_ = v___x_524_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_mvarId_517_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_xs_520_);
lean_ctor_set(v_reuseFailAlloc_533_, 2, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_533_, 3, v_eqsNew_522_);
v___x_530_ = v_reuseFailAlloc_533_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_st_ref_put(v___y_501_, v___x_530_);
lean_inc(v___y_505_);
lean_inc_ref(v___y_504_);
lean_inc(v___y_503_);
lean_inc_ref(v___y_502_);
lean_inc(v___y_501_);
v___x_532_ = lean_apply_7(v___f_486_, v___x_526_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, lean_box(0));
return v___x_532_;
}
}
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_567_; 
v_a_537_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_567_ == 0)
{
v___x_539_ = v___x_507_;
v_isShared_540_ = v_isSharedCheck_567_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_507_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_567_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
uint8_t v___x_541_; 
v___x_541_ = l_Lean_Exception_isInterrupt(v_a_537_);
if (v___x_541_ == 0)
{
uint8_t v___x_542_; 
lean_inc(v_a_537_);
v___x_542_ = l_Lean_Exception_isRuntime(v_a_537_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v_mvarId_544_; lean_object* v_xs_545_; lean_object* v_eqs_546_; lean_object* v_eqsNew_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_560_; 
lean_del_object(v___x_539_);
lean_dec(v_a_537_);
v___x_543_ = lean_st_ref_take(v___y_501_);
v_mvarId_544_ = lean_ctor_get(v___x_543_, 0);
v_xs_545_ = lean_ctor_get(v___x_543_, 1);
v_eqs_546_ = lean_ctor_get(v___x_543_, 2);
v_eqsNew_547_ = lean_ctor_get(v___x_543_, 3);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_560_ == 0)
{
v___x_549_ = v___x_543_;
v_isShared_550_ = v_isSharedCheck_560_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_eqsNew_547_);
lean_inc(v_eqs_546_);
lean_inc(v_xs_545_);
lean_inc(v_mvarId_544_);
lean_dec(v___x_543_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_560_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_box(0);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v_eqsNew_547_);
v___x_553_ = v___x_498_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_head_495_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_eqsNew_547_);
v___x_553_ = v_reuseFailAlloc_559_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_555_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 3, v___x_553_);
v___x_555_ = v___x_549_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_mvarId_544_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_xs_545_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_eqs_546_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v___x_553_);
v___x_555_ = v_reuseFailAlloc_558_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_st_ref_put(v___y_501_, v___x_555_);
lean_inc(v___y_505_);
lean_inc_ref(v___y_504_);
lean_inc(v___y_503_);
lean_inc_ref(v___y_502_);
lean_inc(v___y_501_);
v___x_557_ = lean_apply_7(v___f_486_, v___x_551_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, lean_box(0));
return v___x_557_;
}
}
}
}
else
{
lean_object* v___x_562_; 
lean_del_object(v___x_498_);
lean_dec(v_head_495_);
lean_dec_ref(v___f_486_);
if (v_isShared_540_ == 0)
{
v___x_562_ = v___x_539_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_537_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
else
{
lean_object* v___x_565_; 
lean_del_object(v___x_498_);
lean_dec(v_head_495_);
lean_dec_ref(v___f_486_);
if (v_isShared_540_ == 0)
{
v___x_565_ = v___x_539_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_537_);
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
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 2, v_tail_496_);
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_mvarId_569_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_xs_570_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v_tail_496_);
lean_ctor_set(v_reuseFailAlloc_739_, 3, v_eqsNew_571_);
v___x_576_ = v_reuseFailAlloc_739_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = lean_st_ref_put(v___y_489_, v___x_576_);
lean_inc(v_head_495_);
v___x_578_ = l_Lean_mkFVar(v_head_495_);
lean_inc(v___y_493_);
lean_inc_ref(v___y_492_);
lean_inc(v___y_491_);
lean_inc_ref(v___y_490_);
lean_inc_ref(v___x_578_);
v___x_579_ = lean_infer_type(v___x_578_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___x_651_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc_n(v_a_580_, 2);
lean_dec_ref_known(v___x_579_, 1);
v___x_651_ = l_Lean_Meta_matchEq_x3f(v_a_580_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
if (lean_obj_tag(v_a_652_) == 1)
{
lean_object* v_val_653_; lean_object* v_snd_654_; lean_object* v_fst_655_; lean_object* v_snd_656_; lean_object* v___x_657_; 
v_val_653_ = lean_ctor_get(v_a_652_, 0);
lean_inc(v_val_653_);
lean_dec_ref_known(v_a_652_, 1);
v_snd_654_ = lean_ctor_get(v_val_653_, 1);
lean_inc(v_snd_654_);
lean_dec(v_val_653_);
v_fst_655_ = lean_ctor_get(v_snd_654_, 0);
lean_inc_n(v_fst_655_, 2);
v_snd_656_ = lean_ctor_get(v_snd_654_, 1);
lean_inc_n(v_snd_656_, 2);
lean_dec(v_snd_654_);
v___x_657_ = l_Lean_Meta_isExprDefEq(v_fst_655_, v_snd_656_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; uint8_t v___x_659_; uint8_t v___x_660_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_657_, 1);
v___x_659_ = 1;
v___x_660_ = lean_unbox(v_a_658_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
lean_inc(v_snd_656_);
lean_inc(v_mvarId_485_);
v___x_661_ = l_Lean_MVarId_closeIfDistinctFloatLits(v_mvarId_485_, v___x_578_, v_fst_655_, v_snd_656_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_691_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_691_ == 0)
{
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_691_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_691_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
uint8_t v___x_666_; 
v___x_666_ = lean_unbox(v_a_662_);
lean_dec(v_a_662_);
if (v___x_666_ == 0)
{
uint8_t v___x_667_; 
lean_del_object(v___x_664_);
lean_dec(v_a_658_);
v___x_667_ = l_Lean_Expr_isFVar(v_snd_656_);
if (v___x_667_ == 0)
{
lean_dec(v_snd_656_);
v___y_582_ = v___y_489_;
v___y_583_ = v___y_490_;
v___y_584_ = v___y_491_;
v___y_585_ = v___y_492_;
v___y_586_ = v___y_493_;
goto v___jp_581_;
}
else
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = l_Lean_Expr_fvarId_x21(v_snd_656_);
lean_dec(v_snd_656_);
v___x_669_ = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(v___x_668_, v_xs_488_);
if (v___x_669_ == 0)
{
lean_dec(v___x_668_);
v___y_582_ = v___y_489_;
v___y_583_ = v___y_490_;
v___y_584_ = v___y_491_;
v___y_585_ = v___y_492_;
v___y_586_ = v___y_493_;
goto v___jp_581_;
}
else
{
lean_object* v___x_670_; 
lean_dec(v_a_580_);
lean_del_object(v___x_498_);
lean_dec(v___x_487_);
lean_dec_ref(v___f_486_);
lean_dec(v_mvarId_485_);
v___x_670_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(v_head_495_, v___x_668_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___x_668_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_678_; 
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; 
v_unused_679_ = lean_ctor_get(v___x_670_, 0);
lean_dec(v_unused_679_);
v___x_672_ = v___x_670_;
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
else
{
lean_dec(v___x_670_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = lean_box(v___x_659_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_674_);
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
v_a_680_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_670_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_670_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
}
else
{
lean_object* v___x_689_; 
lean_dec(v_snd_656_);
lean_dec(v_a_580_);
lean_del_object(v___x_498_);
lean_dec(v_head_495_);
lean_dec(v___x_487_);
lean_dec_ref(v___f_486_);
lean_dec(v_mvarId_485_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v_a_658_);
v___x_689_ = v___x_664_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_658_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
else
{
lean_dec(v_a_658_);
lean_dec(v_snd_656_);
lean_dec(v_a_580_);
lean_del_object(v___x_498_);
lean_dec(v_head_495_);
lean_dec(v___x_487_);
lean_dec_ref(v___f_486_);
lean_dec(v_mvarId_485_);
return v___x_661_;
}
}
else
{
lean_object* v___x_692_; 
lean_dec(v_a_658_);
lean_dec(v_snd_656_);
lean_dec(v_fst_655_);
lean_dec(v_a_580_);
lean_dec_ref(v___x_578_);
lean_del_object(v___x_498_);
lean_dec(v___x_487_);
lean_dec_ref(v___f_486_);
v___x_692_ = l_Lean_MVarId_clear(v_mvarId_485_, v_head_495_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_714_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_714_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_714_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_714_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v_xs_698_; lean_object* v_eqs_699_; lean_object* v_eqsNew_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_712_; 
v___x_697_ = lean_st_ref_take(v___y_489_);
v_xs_698_ = lean_ctor_get(v___x_697_, 1);
v_eqs_699_ = lean_ctor_get(v___x_697_, 2);
v_eqsNew_700_ = lean_ctor_get(v___x_697_, 3);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v___x_697_, 0);
lean_dec(v_unused_713_);
v___x_702_ = v___x_697_;
v_isShared_703_ = v_isSharedCheck_712_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_eqsNew_700_);
lean_inc(v_eqs_699_);
lean_inc(v_xs_698_);
lean_dec(v___x_697_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_712_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v_a_693_);
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_693_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_xs_698_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v_eqs_699_);
lean_ctor_set(v_reuseFailAlloc_711_, 3, v_eqsNew_700_);
v___x_705_ = v_reuseFailAlloc_711_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_706_ = lean_st_ref_put(v___y_489_, v___x_705_);
v___x_707_ = lean_box(v___x_659_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_707_);
v___x_709_ = v___x_695_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
v_a_715_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_692_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_692_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
else
{
lean_dec(v_snd_656_);
lean_dec(v_fst_655_);
lean_dec(v_a_580_);
lean_dec_ref(v___x_578_);
lean_del_object(v___x_498_);
lean_dec(v_head_495_);
lean_dec(v___x_487_);
lean_dec_ref(v___f_486_);
lean_dec(v_mvarId_485_);
return v___x_657_;
}
}
else
{
lean_dec(v_a_652_);
lean_dec_ref(v___x_578_);
v___y_582_ = v___y_489_;
v___y_583_ = v___y_490_;
v___y_584_ = v___y_491_;
v___y_585_ = v___y_492_;
v___y_586_ = v___y_493_;
goto v___jp_581_;
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v_a_580_);
lean_dec_ref(v___x_578_);
lean_del_object(v___x_498_);
lean_dec(v_head_495_);
lean_dec(v___x_487_);
lean_dec_ref(v___f_486_);
lean_dec(v_mvarId_485_);
v_a_723_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_651_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_651_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
v___jp_581_:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Meta_matchHEq_x3f(v_a_580_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
if (lean_obj_tag(v_a_588_) == 1)
{
uint8_t v___x_589_; lean_object* v___x_590_; 
lean_dec_ref_known(v_a_588_, 1);
v___x_589_ = 1;
lean_inc(v_head_495_);
lean_inc(v_mvarId_485_);
v___x_590_ = l_Lean_Meta_heqToEq(v_mvarId_485_, v_head_495_, v___x_589_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_634_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_634_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_634_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_634_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_fst_595_; lean_object* v_snd_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_633_; 
v_fst_595_ = lean_ctor_get(v_a_591_, 0);
v_snd_596_ = lean_ctor_get(v_a_591_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_a_591_);
if (v_isSharedCheck_633_ == 0)
{
v___x_598_ = v_a_591_;
v_isShared_599_ = v_isSharedCheck_633_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_snd_596_);
lean_inc(v_fst_595_);
lean_dec(v_a_591_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_633_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
uint8_t v___x_600_; 
v___x_600_ = l_Lean_instBEqMVarId_beq(v_snd_596_, v_mvarId_485_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v_xs_602_; lean_object* v_eqs_603_; lean_object* v_eqsNew_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_619_; 
lean_del_object(v___x_498_);
lean_dec(v_head_495_);
lean_dec(v___x_487_);
lean_dec_ref(v___f_486_);
lean_dec(v_mvarId_485_);
v___x_601_ = lean_st_ref_take(v___y_582_);
v_xs_602_ = lean_ctor_get(v___x_601_, 1);
v_eqs_603_ = lean_ctor_get(v___x_601_, 2);
v_eqsNew_604_ = lean_ctor_get(v___x_601_, 3);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v___x_601_, 0);
lean_dec(v_unused_620_);
v___x_606_ = v___x_601_;
v_isShared_607_ = v_isSharedCheck_619_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_eqsNew_604_);
lean_inc(v_eqs_603_);
lean_inc(v_xs_602_);
lean_dec(v___x_601_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_619_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set_tag(v___x_598_, 1);
lean_ctor_set(v___x_598_, 1, v_eqs_603_);
v___x_609_ = v___x_598_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_fst_595_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_eqs_603_);
v___x_609_ = v_reuseFailAlloc_618_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_611_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 2, v___x_609_);
lean_ctor_set(v___x_606_, 0, v_snd_596_);
v___x_611_ = v___x_606_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_snd_596_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_xs_602_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_eqsNew_604_);
v___x_611_ = v_reuseFailAlloc_617_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_612_ = lean_st_ref_put(v___y_582_, v___x_611_);
v___x_613_ = lean_box(v___x_589_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_613_);
v___x_615_ = v___x_593_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
else
{
uint8_t v___x_621_; lean_object* v___x_622_; 
lean_del_object(v___x_598_);
lean_dec(v_snd_596_);
lean_dec(v_fst_595_);
lean_del_object(v___x_593_);
v___x_621_ = 0;
lean_inc(v_mvarId_485_);
v___x_622_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(v_mvarId_485_, v___x_487_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_632_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_632_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_632_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_632_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
uint8_t v___x_627_; 
v___x_627_ = lean_unbox(v_a_623_);
lean_dec(v_a_623_);
if (v___x_627_ == 0)
{
lean_del_object(v___x_625_);
v___y_501_ = v___y_582_;
v___y_502_ = v___y_583_;
v___y_503_ = v___y_584_;
v___y_504_ = v___y_585_;
v___y_505_ = v___y_586_;
goto v___jp_500_;
}
else
{
lean_object* v___x_628_; lean_object* v___x_630_; 
lean_del_object(v___x_498_);
lean_dec(v_head_495_);
lean_dec_ref(v___f_486_);
lean_dec(v_mvarId_485_);
v___x_628_ = lean_box(v___x_621_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v___x_628_);
v___x_630_ = v___x_625_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
else
{
lean_del_object(v___x_498_);
lean_dec(v_head_495_);
lean_dec_ref(v___f_486_);
lean_dec(v_mvarId_485_);
return v___x_622_;
}
}
}
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_del_object(v___x_498_);
lean_dec(v_head_495_);
lean_dec(v___x_487_);
lean_dec_ref(v___f_486_);
lean_dec(v_mvarId_485_);
v_a_635_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_590_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_590_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
else
{
lean_dec(v_a_588_);
lean_dec(v___x_487_);
v___y_501_ = v___y_582_;
v___y_502_ = v___y_583_;
v___y_503_ = v___y_584_;
v___y_504_ = v___y_585_;
v___y_505_ = v___y_586_;
goto v___jp_500_;
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_del_object(v___x_498_);
lean_dec(v_head_495_);
lean_dec(v___x_487_);
lean_dec_ref(v___f_486_);
lean_dec(v_mvarId_485_);
v_a_643_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_587_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_587_);
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
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v___x_578_);
lean_del_object(v___x_498_);
lean_dec(v_head_495_);
lean_dec(v___x_487_);
lean_dec_ref(v___f_486_);
lean_dec(v_mvarId_485_);
v_a_731_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_579_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_579_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; 
lean_dec(v___x_487_);
lean_dec(v_mvarId_485_);
lean_dec(v_eqs_484_);
v___x_743_ = lean_box(0);
lean_inc(v___y_493_);
lean_inc_ref(v___y_492_);
lean_inc(v___y_491_);
lean_inc_ref(v___y_490_);
lean_inc(v___y_489_);
v___x_744_ = lean_apply_7(v___f_486_, v___x_743_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, lean_box(0));
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1___boxed(lean_object* v_eqs_745_, lean_object* v_mvarId_746_, lean_object* v___f_747_, lean_object* v___x_748_, lean_object* v_xs_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1(v_eqs_745_, v_mvarId_746_, v___f_747_, v___x_748_, v_xs_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec(v_xs_749_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v___f_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v_mvarId_767_; lean_object* v_xs_768_; lean_object* v_eqs_769_; lean_object* v___y_770_; lean_object* v___x_771_; 
v___f_764_ = ((lean_object*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___closed__0));
v___x_765_ = lean_box(1);
v___x_766_ = lean_st_ref_get(v_a_758_);
v_mvarId_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc_n(v_mvarId_767_, 2);
v_xs_768_ = lean_ctor_get(v___x_766_, 1);
lean_inc(v_xs_768_);
v_eqs_769_ = lean_ctor_get(v___x_766_, 2);
lean_inc(v_eqs_769_);
lean_dec(v___x_766_);
v___y_770_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1___boxed), 11, 5);
lean_closure_set(v___y_770_, 0, v_eqs_769_);
lean_closure_set(v___y_770_, 1, v_mvarId_767_);
lean_closure_set(v___y_770_, 2, v___f_764_);
lean_closure_set(v___y_770_, 3, v___x_765_);
lean_closure_set(v___y_770_, 4, v_xs_768_);
v___x_771_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(v_mvarId_767_, v___y_770_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___boxed(lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(v_a_779_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; uint8_t v___x_787_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v___x_787_ = lean_unbox(v_a_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
lean_dec_ref_known(v___x_785_, 1);
v___x_788_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; uint8_t v___x_790_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v___x_790_ = lean_unbox(v_a_789_);
if (v___x_790_ == 0)
{
return v___x_788_;
}
else
{
lean_dec_ref_known(v___x_788_, 1);
goto _start;
}
}
else
{
return v___x_788_;
}
}
else
{
return v___x_785_;
}
}
else
{
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go___boxed(lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
lean_dec(v_a_792_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0(lean_object* v_k_799_, lean_object* v_b_800_, lean_object* v_c_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v___x_807_; 
lean_inc(v___y_805_);
lean_inc_ref(v___y_804_);
lean_inc(v___y_803_);
lean_inc_ref(v___y_802_);
v___x_807_ = lean_apply_7(v_k_799_, v_b_800_, v_c_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, lean_box(0));
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0___boxed(lean_object* v_k_808_, lean_object* v_b_809_, lean_object* v_c_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0(v_k_808_, v_b_809_, v_c_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(lean_object* v_type_817_, lean_object* v_k_818_, uint8_t v_cleanupAnnotations_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v___f_825_; uint8_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___f_825_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_825_, 0, v_k_818_);
v___x_826_ = 0;
v___x_827_ = lean_box(0);
v___x_828_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_826_, v___x_827_, v_type_817_, v___f_825_, v_cleanupAnnotations_819_, v___x_826_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
v_a_837_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_828_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_828_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___boxed(lean_object* v_type_845_, lean_object* v_k_846_, lean_object* v_cleanupAnnotations_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_853_; lean_object* v_res_854_; 
v_cleanupAnnotations_boxed_853_ = lean_unbox(v_cleanupAnnotations_847_);
v_res_854_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(v_type_845_, v_k_846_, v_cleanupAnnotations_boxed_853_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0(lean_object* v_00_u03b1_855_, lean_object* v_type_856_, lean_object* v_k_857_, uint8_t v_cleanupAnnotations_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(v_type_856_, v_k_857_, v_cleanupAnnotations_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___boxed(lean_object* v_00_u03b1_865_, lean_object* v_type_866_, lean_object* v_k_867_, lean_object* v_cleanupAnnotations_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_874_; lean_object* v_res_875_; 
v_cleanupAnnotations_boxed_874_ = lean_unbox(v_cleanupAnnotations_868_);
v_res_875_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0(v_00_u03b1_865_, v_type_866_, v_k_867_, v_cleanupAnnotations_boxed_874_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
return v_res_875_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0(lean_object* v_x_876_){
_start:
{
uint8_t v___x_877_; 
v___x_877_ = 0;
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0___boxed(lean_object* v_x_878_){
_start:
{
uint8_t v_res_879_; lean_object* v_r_880_; 
v_res_879_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0(v_x_878_);
lean_dec(v_x_878_);
v_r_880_ = lean_box(v_res_879_);
return v_r_880_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1(lean_object* v_fvarId_881_, lean_object* v_x_882_){
_start:
{
uint8_t v___x_883_; 
v___x_883_ = l_Lean_instBEqFVarId_beq(v_fvarId_881_, v_x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1___boxed(lean_object* v_fvarId_884_, lean_object* v_x_885_){
_start:
{
uint8_t v_res_886_; lean_object* v_r_887_; 
v_res_886_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1(v_fvarId_884_, v_x_885_);
lean_dec(v_x_885_);
lean_dec(v_fvarId_884_);
v_r_887_ = lean_box(v_res_886_);
return v_r_887_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_box(0);
v___x_890_ = lean_unsigned_to_nat(16u);
v___x_891_ = lean_mk_array(v___x_890_, v___x_889_);
return v___x_891_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1);
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v___x_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(lean_object* v_e_895_, lean_object* v_fvarId_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___f_899_; lean_object* v___f_900_; lean_object* v___x_901_; uint8_t v_fst_903_; lean_object* v_mctx_904_; lean_object* v___y_922_; lean_object* v_mctx_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v___f_899_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__0));
v___f_900_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_900_, 0, v_fvarId_896_);
v___x_901_ = lean_st_ref_get(v___y_897_);
v_mctx_927_ = lean_ctor_get(v___x_901_, 0);
lean_inc_ref_n(v_mctx_927_, 2);
lean_dec(v___x_901_);
v___x_928_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v_mctx_927_);
v___x_930_ = l_Lean_Expr_hasFVar(v_e_895_);
if (v___x_930_ == 0)
{
uint8_t v___x_931_; 
v___x_931_ = l_Lean_Expr_hasMVar(v_e_895_);
if (v___x_931_ == 0)
{
lean_dec_ref_known(v___x_929_, 2);
lean_dec_ref(v___f_900_);
lean_dec_ref(v_e_895_);
v_fst_903_ = v___x_931_;
v_mctx_904_ = v_mctx_927_;
goto v___jp_902_;
}
else
{
lean_object* v___x_932_; 
lean_dec_ref(v_mctx_927_);
v___x_932_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_900_, v___f_899_, v_e_895_, v___x_929_);
v___y_922_ = v___x_932_;
goto v___jp_921_;
}
}
else
{
lean_object* v___x_933_; 
lean_dec_ref(v_mctx_927_);
v___x_933_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_900_, v___f_899_, v_e_895_, v___x_929_);
v___y_922_ = v___x_933_;
goto v___jp_921_;
}
v___jp_902_:
{
lean_object* v___x_905_; lean_object* v_cache_906_; lean_object* v_zetaDeltaFVarIds_907_; lean_object* v_postponed_908_; lean_object* v_diag_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_919_; 
v___x_905_ = lean_st_ref_take(v___y_897_);
v_cache_906_ = lean_ctor_get(v___x_905_, 1);
v_zetaDeltaFVarIds_907_ = lean_ctor_get(v___x_905_, 2);
v_postponed_908_ = lean_ctor_get(v___x_905_, 3);
v_diag_909_ = lean_ctor_get(v___x_905_, 4);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_919_ == 0)
{
lean_object* v_unused_920_; 
v_unused_920_ = lean_ctor_get(v___x_905_, 0);
lean_dec(v_unused_920_);
v___x_911_ = v___x_905_;
v_isShared_912_ = v_isSharedCheck_919_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_diag_909_);
lean_inc(v_postponed_908_);
lean_inc(v_zetaDeltaFVarIds_907_);
lean_inc(v_cache_906_);
lean_dec(v___x_905_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_919_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_mctx_904_);
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_mctx_904_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_cache_906_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v_zetaDeltaFVarIds_907_);
lean_ctor_set(v_reuseFailAlloc_918_, 3, v_postponed_908_);
lean_ctor_set(v_reuseFailAlloc_918_, 4, v_diag_909_);
v___x_914_ = v_reuseFailAlloc_918_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_915_ = lean_st_ref_put(v___y_897_, v___x_914_);
v___x_916_ = lean_box(v_fst_903_);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
return v___x_917_;
}
}
}
v___jp_921_:
{
lean_object* v_snd_923_; lean_object* v_fst_924_; lean_object* v_mctx_925_; uint8_t v___x_926_; 
v_snd_923_ = lean_ctor_get(v___y_922_, 1);
lean_inc(v_snd_923_);
v_fst_924_ = lean_ctor_get(v___y_922_, 0);
lean_inc(v_fst_924_);
lean_dec_ref(v___y_922_);
v_mctx_925_ = lean_ctor_get(v_snd_923_, 1);
lean_inc_ref(v_mctx_925_);
lean_dec(v_snd_923_);
v___x_926_ = lean_unbox(v_fst_924_);
lean_dec(v_fst_924_);
v_fst_903_ = v___x_926_;
v_mctx_904_ = v_mctx_925_;
goto v___jp_902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___boxed(lean_object* v_e_934_, lean_object* v_fvarId_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(v_e_934_, v_fvarId_935_, v___y_936_);
lean_dec(v___y_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1(lean_object* v_e_939_, lean_object* v_fvarId_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(v_e_939_, v_fvarId_940_, v___y_942_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___boxed(lean_object* v_e_947_, lean_object* v_fvarId_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1(v_e_947_, v_fvarId_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(lean_object* v_mvarId_955_, lean_object* v_x_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_955_, v_x_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
v_a_971_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_962_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_962_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg___boxed(lean_object* v_mvarId_979_, lean_object* v_x_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(v_mvarId_979_, v_x_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3(lean_object* v_00_u03b1_987_, lean_object* v_mvarId_988_, lean_object* v_x_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(v_mvarId_988_, v_x_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___boxed(lean_object* v_00_u03b1_996_, lean_object* v_mvarId_997_, lean_object* v_x_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3(v_00_u03b1_996_, v_mvarId_997_, v_x_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__0(lean_object* v_numEqs_1005_, lean_object* v_ys_1006_, lean_object* v_x_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1013_ = lean_array_get_size(v_ys_1006_);
v___x_1014_ = lean_nat_sub(v___x_1013_, v_numEqs_1005_);
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__0___boxed(lean_object* v_numEqs_1016_, lean_object* v_ys_1017_, lean_object* v_x_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_Meta_Match_simpH___lam__0(v_numEqs_1016_, v_ys_1017_, v_x_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec_ref(v_x_1018_);
lean_dec_ref(v_ys_1017_);
lean_dec(v_numEqs_1016_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(lean_object* v_a_1025_, lean_object* v_as_1026_, size_t v_i_1027_, size_t v_stop_1028_, lean_object* v_b_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_a_1036_; uint8_t v___x_1040_; 
v___x_1040_ = lean_usize_dec_eq(v_i_1027_, v_stop_1028_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_array_uget_borrowed(v_as_1026_, v_i_1027_);
lean_inc(v___x_1041_);
lean_inc_ref(v_a_1025_);
v___x_1042_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(v_a_1025_, v___x_1041_, v___y_1031_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; uint8_t v___x_1044_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1042_, 1);
v___x_1044_ = lean_unbox(v_a_1043_);
lean_dec(v_a_1043_);
if (v___x_1044_ == 0)
{
v_a_1036_ = v_b_1029_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1045_; 
lean_inc(v___x_1041_);
v___x_1045_ = lean_array_push(v_b_1029_, v___x_1041_);
v_a_1036_ = v___x_1045_;
goto v___jp_1035_;
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec_ref(v_b_1029_);
lean_dec_ref(v_a_1025_);
v_a_1046_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1042_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1042_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
else
{
lean_object* v___x_1054_; 
lean_dec_ref(v_a_1025_);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v_b_1029_);
return v___x_1054_;
}
v___jp_1035_:
{
size_t v___x_1037_; size_t v___x_1038_; 
v___x_1037_ = ((size_t)1ULL);
v___x_1038_ = lean_usize_add(v_i_1027_, v___x_1037_);
v_i_1027_ = v___x_1038_;
v_b_1029_ = v_a_1036_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2___boxed(lean_object* v_a_1055_, lean_object* v_as_1056_, lean_object* v_i_1057_, lean_object* v_stop_1058_, lean_object* v_b_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
size_t v_i_boxed_1065_; size_t v_stop_boxed_1066_; lean_object* v_res_1067_; 
v_i_boxed_1065_ = lean_unbox_usize(v_i_1057_);
lean_dec(v_i_1057_);
v_stop_boxed_1066_ = lean_unbox_usize(v_stop_1058_);
lean_dec(v_stop_1058_);
v_res_1067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(v_a_1055_, v_as_1056_, v_i_boxed_1065_, v_stop_boxed_1066_, v_b_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec_ref(v_as_1056_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__1(lean_object* v_snd_1068_, uint8_t v___x_1069_, lean_object* v___x_1070_, lean_object* v___x_1071_, lean_object* v_a_1072_, lean_object* v___x_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_a_1080_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = lean_mk_empty_array_with_capacity(v___x_1070_);
v___x_1101_ = lean_nat_dec_lt(v___x_1070_, v___x_1071_);
if (v___x_1101_ == 0)
{
lean_dec_ref(v_a_1072_);
v_a_1080_ = v___x_1100_;
goto v___jp_1079_;
}
else
{
size_t v___x_1102_; size_t v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = ((size_t)0ULL);
v___x_1103_ = lean_usize_of_nat(v___x_1071_);
v___x_1104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(v_a_1072_, v___x_1073_, v___x_1102_, v___x_1103_, v___x_1100_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1104_, 1);
v_a_1080_ = v_a_1105_;
goto v___jp_1079_;
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec(v_snd_1068_);
v_a_1106_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1104_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1104_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
v___jp_1079_:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_MVarId_revert(v_snd_1068_, v_a_1080_, v___x_1069_, v___x_1069_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1091_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1091_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1091_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v_snd_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v_snd_1086_ = lean_ctor_get(v_a_1082_, 1);
lean_inc(v_snd_1086_);
lean_dec(v_a_1082_);
v___x_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1087_, 0, v_snd_1086_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1087_);
v___x_1089_ = v___x_1084_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
v_a_1092_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1081_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1081_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__1___boxed(lean_object* v_snd_1114_, lean_object* v___x_1115_, lean_object* v___x_1116_, lean_object* v___x_1117_, lean_object* v_a_1118_, lean_object* v___x_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
uint8_t v___x_6307__boxed_1125_; lean_object* v_res_1126_; 
v___x_6307__boxed_1125_ = lean_unbox(v___x_1115_);
v_res_1126_ = l_Lean_Meta_Match_simpH___lam__1(v_snd_1114_, v___x_6307__boxed_1125_, v___x_1116_, v___x_1117_, v_a_1118_, v___x_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec_ref(v___x_1119_);
lean_dec(v___x_1117_);
lean_dec(v___x_1116_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__2(lean_object* v_mvarId_1127_, lean_object* v___x_1128_, uint8_t v___x_1129_, lean_object* v_xs_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_MVarId_revert(v_mvarId_1127_, v___x_1128_, v___x_1129_, v___x_1129_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v_snd_1138_; lean_object* v___x_1139_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___x_1136_, 1);
v_snd_1138_ = lean_ctor_get(v_a_1137_, 1);
lean_inc_n(v_snd_1138_, 2);
lean_dec(v_a_1137_);
v___x_1139_ = l_Lean_MVarId_getType(v_snd_1138_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___f_1146_; lean_object* v___x_1147_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v___x_1141_ = lean_array_mk(v_xs_1130_);
v___x_1142_ = l_Array_reverse___redArg(v___x_1141_);
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = lean_array_get_size(v___x_1142_);
v___x_1145_ = lean_box(v___x_1129_);
lean_inc(v_snd_1138_);
v___f_1146_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH___lam__1___boxed), 11, 6);
lean_closure_set(v___f_1146_, 0, v_snd_1138_);
lean_closure_set(v___f_1146_, 1, v___x_1145_);
lean_closure_set(v___f_1146_, 2, v___x_1143_);
lean_closure_set(v___f_1146_, 3, v___x_1144_);
lean_closure_set(v___f_1146_, 4, v_a_1140_);
lean_closure_set(v___f_1146_, 5, v___x_1142_);
v___x_1147_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(v_snd_1138_, v___f_1146_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
return v___x_1147_;
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec(v_snd_1138_);
lean_dec(v_xs_1130_);
v_a_1148_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1139_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1139_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec(v_xs_1130_);
v_a_1156_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1136_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1136_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__2___boxed(lean_object* v_mvarId_1164_, lean_object* v___x_1165_, lean_object* v___x_1166_, lean_object* v_xs_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
uint8_t v___x_6406__boxed_1173_; lean_object* v_res_1174_; 
v___x_6406__boxed_1173_ = lean_unbox(v___x_1166_);
v_res_1174_ = l_Lean_Meta_Match_simpH___lam__2(v_mvarId_1164_, v___x_1165_, v___x_6406__boxed_1173_, v_xs_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__3(lean_object* v_mvarId_1175_, lean_object* v___f_1176_, lean_object* v_numEqs_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; 
lean_inc(v_mvarId_1175_);
v___x_1183_ = l_Lean_MVarId_getType(v_mvarId_1175_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; uint8_t v___x_1185_; lean_object* v___x_1186_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1185_ = 0;
v___x_1186_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(v_a_1184_, v___f_1176_, v___x_1185_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v_lctx_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1186_, 1);
v_lctx_1188_ = lean_ctor_get(v___y_1178_, 2);
v___x_1189_ = l_Lean_LocalContext_getFVarIds(v_lctx_1188_);
v___x_1190_ = l_Lean_MVarId_tryClearMany(v_mvarId_1175_, v___x_1189_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec_ref(v___x_1189_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v___x_1190_, 1);
v___x_1192_ = lean_box(0);
v___x_1193_ = l_Lean_Meta_introNCore(v_a_1191_, v_a_1187_, v___x_1192_, v___x_1185_, v___x_1185_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v_fst_1195_; lean_object* v_snd_1196_; lean_object* v___x_1197_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1193_, 1);
v_fst_1195_ = lean_ctor_get(v_a_1194_, 0);
lean_inc(v_fst_1195_);
v_snd_1196_ = lean_ctor_get(v_a_1194_, 1);
lean_inc(v_snd_1196_);
lean_dec(v_a_1194_);
v___x_1197_ = l_Lean_Meta_introNCore(v_snd_1196_, v_numEqs_1177_, v___x_1192_, v___x_1185_, v___x_1185_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v_fst_1199_; lean_object* v_snd_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v___x_1197_, 1);
v_fst_1199_ = lean_ctor_get(v_a_1198_, 0);
lean_inc(v_fst_1199_);
v_snd_1200_ = lean_ctor_get(v_a_1198_, 1);
lean_inc(v_snd_1200_);
lean_dec(v_a_1198_);
v___x_1201_ = lean_array_to_list(v_fst_1195_);
v___x_1202_ = lean_array_to_list(v_fst_1199_);
v___x_1203_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1203_, 0, v_snd_1200_);
lean_ctor_set(v___x_1203_, 1, v___x_1201_);
lean_ctor_set(v___x_1203_, 2, v___x_1202_);
lean_ctor_set(v___x_1203_, 3, v___x_1192_);
v___x_1204_ = lean_st_mk_ref(v___x_1203_);
v___x_1205_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(v___x_1204_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1224_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1224_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1224_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = lean_st_ref_get(v___x_1204_);
lean_dec(v___x_1204_);
v___x_1211_ = lean_unbox(v_a_1206_);
lean_dec(v_a_1206_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
lean_dec(v___x_1210_);
v___x_1212_ = lean_box(0);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1212_);
v___x_1214_ = v___x_1208_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
else
{
lean_object* v_mvarId_1216_; lean_object* v_xs_1217_; lean_object* v_eqsNew_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___f_1222_; lean_object* v___x_1223_; 
lean_del_object(v___x_1208_);
v_mvarId_1216_ = lean_ctor_get(v___x_1210_, 0);
lean_inc_n(v_mvarId_1216_, 2);
v_xs_1217_ = lean_ctor_get(v___x_1210_, 1);
lean_inc(v_xs_1217_);
v_eqsNew_1218_ = lean_ctor_get(v___x_1210_, 3);
lean_inc(v_eqsNew_1218_);
lean_dec(v___x_1210_);
v___x_1219_ = l_List_reverse___redArg(v_eqsNew_1218_);
v___x_1220_ = lean_array_mk(v___x_1219_);
v___x_1221_ = lean_box(v___x_1185_);
v___f_1222_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1222_, 0, v_mvarId_1216_);
lean_closure_set(v___f_1222_, 1, v___x_1220_);
lean_closure_set(v___f_1222_, 2, v___x_1221_);
lean_closure_set(v___f_1222_, 3, v_xs_1217_);
v___x_1223_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(v_mvarId_1216_, v___f_1222_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
return v___x_1223_;
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec(v___x_1204_);
v_a_1225_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1205_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1205_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
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
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v_fst_1195_);
v_a_1233_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1197_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1197_);
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
lean_dec(v_numEqs_1177_);
v_a_1241_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1193_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1193_);
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
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v_a_1187_);
lean_dec(v_numEqs_1177_);
v_a_1249_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1190_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1190_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
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
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v_numEqs_1177_);
lean_dec(v_mvarId_1175_);
v_a_1257_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1186_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1186_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v_numEqs_1177_);
lean_dec_ref(v___f_1176_);
lean_dec(v_mvarId_1175_);
v_a_1265_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1183_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1183_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__3___boxed(lean_object* v_mvarId_1273_, lean_object* v___f_1274_, lean_object* v_numEqs_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Meta_Match_simpH___lam__3(v_mvarId_1273_, v___f_1274_, v_numEqs_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH(lean_object* v_mvarId_1282_, lean_object* v_numEqs_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v___y_1290_; lean_object* v___x_1307_; uint8_t v_transparency_1308_; lean_object* v___f_1309_; uint8_t v___x_1310_; uint8_t v___x_1311_; 
v___x_1307_ = l_Lean_Meta_Context_config(v_a_1284_);
v_transparency_1308_ = lean_ctor_get_uint8(v___x_1307_, 9);
lean_dec_ref(v___x_1307_);
lean_inc(v_numEqs_1283_);
v___f_1309_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1309_, 0, v_numEqs_1283_);
v___x_1310_ = 1;
v___x_1311_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1308_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_object* v_keyedConfig_1312_; uint8_t v_trackZetaDelta_1313_; lean_object* v_zetaDeltaSet_1314_; lean_object* v_lctx_1315_; lean_object* v_localInstances_1316_; lean_object* v_defEqCtx_x3f_1317_; lean_object* v_synthPendingDepth_1318_; lean_object* v_customCanUnfoldPredicate_x3f_1319_; uint8_t v_univApprox_1320_; uint8_t v_inTypeClassResolution_1321_; uint8_t v_cacheInferType_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_keyedConfig_1312_ = lean_ctor_get(v_a_1284_, 0);
v_trackZetaDelta_1313_ = lean_ctor_get_uint8(v_a_1284_, sizeof(void*)*7);
v_zetaDeltaSet_1314_ = lean_ctor_get(v_a_1284_, 1);
v_lctx_1315_ = lean_ctor_get(v_a_1284_, 2);
v_localInstances_1316_ = lean_ctor_get(v_a_1284_, 3);
v_defEqCtx_x3f_1317_ = lean_ctor_get(v_a_1284_, 4);
v_synthPendingDepth_1318_ = lean_ctor_get(v_a_1284_, 5);
v_customCanUnfoldPredicate_x3f_1319_ = lean_ctor_get(v_a_1284_, 6);
v_univApprox_1320_ = lean_ctor_get_uint8(v_a_1284_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1321_ = lean_ctor_get_uint8(v_a_1284_, sizeof(void*)*7 + 2);
v_cacheInferType_1322_ = lean_ctor_get_uint8(v_a_1284_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1312_);
v___x_1323_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1310_, v_keyedConfig_1312_);
lean_inc(v_customCanUnfoldPredicate_x3f_1319_);
lean_inc(v_synthPendingDepth_1318_);
lean_inc(v_defEqCtx_x3f_1317_);
lean_inc_ref(v_localInstances_1316_);
lean_inc_ref(v_lctx_1315_);
lean_inc(v_zetaDeltaSet_1314_);
v___x_1324_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
lean_ctor_set(v___x_1324_, 1, v_zetaDeltaSet_1314_);
lean_ctor_set(v___x_1324_, 2, v_lctx_1315_);
lean_ctor_set(v___x_1324_, 3, v_localInstances_1316_);
lean_ctor_set(v___x_1324_, 4, v_defEqCtx_x3f_1317_);
lean_ctor_set(v___x_1324_, 5, v_synthPendingDepth_1318_);
lean_ctor_set(v___x_1324_, 6, v_customCanUnfoldPredicate_x3f_1319_);
lean_ctor_set_uint8(v___x_1324_, sizeof(void*)*7, v_trackZetaDelta_1313_);
lean_ctor_set_uint8(v___x_1324_, sizeof(void*)*7 + 1, v_univApprox_1320_);
lean_ctor_set_uint8(v___x_1324_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1321_);
lean_ctor_set_uint8(v___x_1324_, sizeof(void*)*7 + 3, v_cacheInferType_1322_);
v___x_1325_ = l_Lean_Meta_Match_simpH___lam__3(v_mvarId_1282_, v___f_1309_, v_numEqs_1283_, v___x_1324_, v_a_1285_, v_a_1286_, v_a_1287_);
lean_dec_ref_known(v___x_1324_, 7);
v___y_1290_ = v___x_1325_;
goto v___jp_1289_;
}
else
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_Meta_Match_simpH___lam__3(v_mvarId_1282_, v___f_1309_, v_numEqs_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
v___y_1290_ = v___x_1326_;
goto v___jp_1289_;
}
v___jp_1289_:
{
if (lean_obj_tag(v___y_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_a_1291_ = lean_ctor_get(v___y_1290_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___y_1290_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___y_1290_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___y_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
v_a_1299_ = lean_ctor_get(v___y_1290_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___y_1290_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___y_1290_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___y_1290_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___boxed(lean_object* v_mvarId_1327_, lean_object* v_numEqs_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_Meta_Match_simpH(v_mvarId_1327_, v_numEqs_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
lean_dec(v_a_1332_);
lean_dec_ref(v_a_1331_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f(lean_object* v_h_1335_, lean_object* v_numEqs_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = lean_box(0);
v___x_1343_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_h_1335_, v___x_1342_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v___x_1345_ = l_Lean_Expr_mvarId_x21(v_a_1344_);
lean_dec(v_a_1344_);
v___x_1346_ = l_Lean_Meta_Match_simpH(v___x_1345_, v_numEqs_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1380_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1380_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1380_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
if (lean_obj_tag(v_a_1347_) == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1351_ = lean_box(0);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1351_);
v___x_1353_ = v___x_1349_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
else
{
lean_object* v_val_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1379_; 
lean_del_object(v___x_1349_);
v_val_1355_ = lean_ctor_get(v_a_1347_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_a_1347_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1357_ = v_a_1347_;
v_isShared_1358_ = v_isSharedCheck_1379_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_val_1355_);
lean_dec(v_a_1347_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1379_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_MVarId_getType(v_val_1355_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1370_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1370_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1370_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v_a_1360_);
v___x_1365_ = v___x_1357_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1367_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1365_);
v___x_1367_ = v___x_1362_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
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
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_del_object(v___x_1357_);
v_a_1371_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1359_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1359_);
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
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
v_a_1381_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1346_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1346_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec(v_numEqs_1336_);
v_a_1389_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1343_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1343_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f___boxed(lean_object* v_h_1397_, lean_object* v_numEqs_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_Meta_Match_simpH_x3f(v_h_1397_, v_numEqs_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
return v_res_1404_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_SimpH(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Contradiction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_SimpH(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_SimpH(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Contradiction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_SimpH(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_SimpH(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_SimpH(builtin);
}
#ifdef __cplusplus
}
#endif
