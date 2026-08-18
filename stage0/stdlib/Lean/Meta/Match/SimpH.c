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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
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
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Lean_MVarId_tryClearMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__3;
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
v___x_19_ = l_instMonadEIO(lean_box(0));
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
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_1653__overap_83_; lean_object* v___x_84_; 
v___x_80_ = l_StateRefT_x27_instMonad___redArg(v___x_79_);
v___x_81_ = lean_box(0);
v___x_82_ = l_instInhabitedOfMonad___redArg(v___x_80_, v___x_81_);
v___x_1653__overap_83_ = lean_panic_fn_borrowed(v___x_82_, v_msg_24_);
lean_dec(v___x_82_);
lean_inc(v___y_29_);
lean_inc_ref(v___y_28_);
lean_inc(v___y_27_);
lean_inc_ref(v___y_26_);
lean_inc(v___y_25_);
v___x_84_ = lean_apply_6(v___x_1653__overap_83_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, lean_box(0));
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
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0));
lean_inc(v_xs_187_);
v___x_194_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(v_xs_187_, v_rhs_163_, v_xs_187_, v___x_193_);
lean_dec(v_xs_187_);
lean_inc_n(v_fst_184_, 2);
v___x_195_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(v_fst_184_, v___x_194_);
v___x_196_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(v_fst_184_, v_eqs_188_);
v___x_197_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(v_fst_184_, v_eqsNew_189_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 3, v___x_197_);
lean_ctor_set(v___x_191_, 2, v___x_196_);
lean_ctor_set(v___x_191_, 1, v___x_195_);
lean_ctor_set(v___x_191_, 0, v_snd_185_);
v___x_199_ = v___x_191_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_snd_185_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v___x_197_);
v___x_199_ = v_reuseFailAlloc_205_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_200_ = lean_st_ref_put(v_a_164_, v___x_199_);
v___x_201_ = lean_box(0);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_201_);
v___x_203_ = v___x_182_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
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
lean_object* v_a_276_; lean_object* v___y_278_; lean_object* v___y_279_; uint8_t v___y_280_; lean_object* v___y_299_; lean_object* v_a_300_; lean_object* v___x_303_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
lean_inc(v___y_273_);
lean_inc_ref(v___y_272_);
lean_inc(v___y_271_);
lean_inc_ref(v___y_270_);
v___x_303_ = lean_apply_5(v_x_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, lean_box(0));
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; uint8_t v___x_305_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
v___x_305_ = lean_unbox(v_a_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; 
lean_dec_ref_known(v___x_303_, 1);
v___x_306_ = l_Lean_Meta_SavedState_restore___redArg(v_a_276_, v___y_271_, v___y_273_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec(v_a_276_);
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
lean_ctor_set(v___x_308_, 0, v_a_304_);
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_304_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_dec(v_a_304_);
v_a_315_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_306_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_306_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
lean_inc(v_a_315_);
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
v___y_299_ = v___x_320_;
v_a_300_ = v_a_315_;
goto v___jp_298_;
}
}
}
}
else
{
lean_dec(v_a_304_);
lean_dec(v_a_276_);
return v___x_303_;
}
}
else
{
lean_object* v_a_323_; 
v_a_323_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_323_);
v___y_299_ = v___x_303_;
v_a_300_ = v_a_323_;
goto v___jp_298_;
}
v___jp_277_:
{
if (v___y_280_ == 0)
{
lean_object* v___x_281_; 
lean_dec_ref(v___y_278_);
v___x_281_ = l_Lean_Meta_SavedState_restore___redArg(v_a_276_, v___y_271_, v___y_273_);
lean_dec(v_a_276_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; 
v_unused_289_ = lean_ctor_get(v___x_281_, 0);
lean_dec(v_unused_289_);
v___x_283_ = v___x_281_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_dec(v___x_281_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
lean_ctor_set_tag(v___x_283_, 1);
lean_ctor_set(v___x_283_, 0, v___y_279_);
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___y_279_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec_ref(v___y_279_);
v_a_290_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_281_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_281_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
else
{
lean_dec_ref(v___y_279_);
lean_dec(v_a_276_);
return v___y_278_;
}
}
v___jp_298_:
{
uint8_t v___x_301_; 
v___x_301_ = l_Lean_Exception_isInterrupt(v_a_300_);
if (v___x_301_ == 0)
{
uint8_t v___x_302_; 
lean_inc_ref(v_a_300_);
v___x_302_ = l_Lean_Exception_isRuntime(v_a_300_);
v___y_278_ = v___y_299_;
v___y_279_ = v_a_300_;
v___y_280_ = v___x_302_;
goto v___jp_277_;
}
else
{
v___y_278_ = v___y_299_;
v___y_279_ = v_a_300_;
v___y_280_ = v___x_301_;
goto v___jp_277_;
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec_ref(v_x_269_);
v_a_324_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_275_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_275_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0___boxed(lean_object* v_x_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(v_x_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0(lean_object* v_mvarId_339_, lean_object* v_forbidden_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_Meta_substVars(v_mvarId_339_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc_n(v_a_347_, 2);
lean_dec_ref_known(v___x_346_, 1);
v___x_348_ = lean_box(0);
v___x_349_ = lean_unsigned_to_nat(5u);
v___x_350_ = l_Lean_Meta_injections(v_a_347_, v___x_348_, v___x_349_, v_forbidden_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_365_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_365_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_365_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_365_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
if (lean_obj_tag(v_a_351_) == 0)
{
uint8_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_358_; 
lean_dec(v_a_347_);
v___x_355_ = 1;
v___x_356_ = lean_box(v___x_355_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_356_);
v___x_358_ = v___x_353_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
else
{
lean_object* v_mvarId_360_; lean_object* v_forbidden_361_; uint8_t v___x_362_; 
lean_del_object(v___x_353_);
v_mvarId_360_ = lean_ctor_get(v_a_351_, 0);
lean_inc(v_mvarId_360_);
v_forbidden_361_ = lean_ctor_get(v_a_351_, 2);
lean_inc(v_forbidden_361_);
lean_dec_ref_known(v_a_351_, 3);
v___x_362_ = l_Lean_instBEqMVarId_beq(v_mvarId_360_, v_a_347_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
lean_dec(v_a_347_);
v___x_363_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(v_mvarId_360_, v_forbidden_361_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
return v___x_363_;
}
else
{
lean_object* v___x_364_; 
lean_dec(v_forbidden_361_);
lean_dec(v_mvarId_360_);
v___x_364_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(v_a_347_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
return v___x_364_;
}
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec(v_a_347_);
v_a_366_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_350_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_350_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec(v_forbidden_340_);
v_a_374_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_346_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_346_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0___boxed(lean_object* v_mvarId_382_, lean_object* v_forbidden_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0(v_mvarId_382_, v_forbidden_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(lean_object* v_mvarId_390_, lean_object* v_forbidden_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___f_397_; lean_object* v___x_398_; 
v___f_397_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0___boxed), 7, 2);
lean_closure_set(v___f_397_, 0, v_mvarId_390_);
lean_closure_set(v___f_397_, 1, v_forbidden_391_);
v___x_398_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(v___f_397_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___boxed(lean_object* v_mvarId_399_, lean_object* v_forbidden_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(v_mvarId_399_, v_forbidden_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0(lean_object* v_x_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_414_; 
lean_inc(v___y_408_);
v___x_414_ = lean_apply_6(v_x_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, lean_box(0));
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0___boxed(lean_object* v_x_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0(v_x_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_416_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(lean_object* v_mvarId_423_, lean_object* v_x_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___f_431_; lean_object* v___x_432_; 
lean_inc(v___y_425_);
v___f_431_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_431_, 0, v_x_424_);
lean_closure_set(v___f_431_, 1, v___y_425_);
v___x_432_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_423_, v___f_431_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
if (lean_obj_tag(v___x_432_) == 0)
{
return v___x_432_;
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___boxed(lean_object* v_mvarId_441_, lean_object* v_x_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(v_mvarId_441_, v_x_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0(lean_object* v_00_u03b1_450_, lean_object* v_mvarId_451_, lean_object* v_x_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(v_mvarId_451_, v_x_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___boxed(lean_object* v_00_u03b1_460_, lean_object* v_mvarId_461_, lean_object* v_x_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0(v_00_u03b1_460_, v_mvarId_461_, v_x_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0(lean_object* v_____r_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = 1;
v___x_478_ = lean_box(v___x_477_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0___boxed(lean_object* v_____r_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0(v_____r_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1(lean_object* v_eqs_488_, lean_object* v___f_489_, lean_object* v_mvarId_490_, lean_object* v_xs_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
if (lean_obj_tag(v_eqs_488_) == 1)
{
lean_object* v_head_498_; lean_object* v_tail_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_738_; 
v_head_498_ = lean_ctor_get(v_eqs_488_, 0);
v_tail_499_ = lean_ctor_get(v_eqs_488_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_eqs_488_);
if (v_isSharedCheck_738_ == 0)
{
v___x_501_ = v_eqs_488_;
v_isShared_502_ = v_isSharedCheck_738_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_tail_499_);
lean_inc(v_head_498_);
lean_dec(v_eqs_488_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_738_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; uint8_t v___y_510_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___x_570_; lean_object* v_mvarId_571_; lean_object* v_xs_572_; lean_object* v_eqsNew_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_736_; 
v___x_570_ = lean_st_ref_take(v___y_492_);
v_mvarId_571_ = lean_ctor_get(v___x_570_, 0);
v_xs_572_ = lean_ctor_get(v___x_570_, 1);
v_eqsNew_573_ = lean_ctor_get(v___x_570_, 3);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; 
v_unused_737_ = lean_ctor_get(v___x_570_, 2);
lean_dec(v_unused_737_);
v___x_575_ = v___x_570_;
v_isShared_576_ = v_isSharedCheck_736_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_eqsNew_573_);
lean_inc(v_xs_572_);
lean_inc(v_mvarId_571_);
lean_dec(v___x_570_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_736_;
goto v_resetjp_574_;
}
v___jp_503_:
{
if (v___y_510_ == 0)
{
lean_object* v___x_511_; lean_object* v_mvarId_512_; lean_object* v_xs_513_; lean_object* v_eqs_514_; lean_object* v_eqsNew_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_528_; 
lean_dec_ref(v___y_508_);
v___x_511_ = lean_st_ref_take(v___y_505_);
v_mvarId_512_ = lean_ctor_get(v___x_511_, 0);
v_xs_513_ = lean_ctor_get(v___x_511_, 1);
v_eqs_514_ = lean_ctor_get(v___x_511_, 2);
v_eqsNew_515_ = lean_ctor_get(v___x_511_, 3);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_528_ == 0)
{
v___x_517_ = v___x_511_;
v_isShared_518_ = v_isSharedCheck_528_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_eqsNew_515_);
lean_inc(v_eqs_514_);
lean_inc(v_xs_513_);
lean_inc(v_mvarId_512_);
lean_dec(v___x_511_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_528_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 1, v_eqsNew_515_);
v___x_520_ = v___x_501_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_head_498_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_eqsNew_515_);
v___x_520_ = v_reuseFailAlloc_527_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_522_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 3, v___x_520_);
v___x_522_ = v___x_517_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_mvarId_512_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_xs_513_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v_eqs_514_);
lean_ctor_set(v_reuseFailAlloc_526_, 3, v___x_520_);
v___x_522_ = v_reuseFailAlloc_526_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = lean_st_ref_put(v___y_505_, v___x_522_);
v___x_524_ = lean_box(0);
lean_inc(v___y_509_);
lean_inc_ref(v___y_506_);
lean_inc(v___y_507_);
lean_inc_ref(v___y_504_);
lean_inc(v___y_505_);
v___x_525_ = lean_apply_7(v___f_489_, v___x_524_, v___y_505_, v___y_504_, v___y_507_, v___y_506_, v___y_509_, lean_box(0));
return v___x_525_;
}
}
}
}
else
{
lean_object* v___x_529_; 
lean_del_object(v___x_501_);
lean_dec(v_head_498_);
lean_dec_ref(v___f_489_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v___y_508_);
return v___x_529_;
}
}
v___jp_530_:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_box(0);
lean_inc(v_head_498_);
v___x_537_ = l_Lean_Meta_injection(v_mvarId_490_, v_head_498_, v___x_536_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_566_; 
lean_del_object(v___x_501_);
lean_dec(v_head_498_);
v_a_538_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_566_ == 0)
{
v___x_540_ = v___x_537_;
v_isShared_541_ = v_isSharedCheck_566_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_566_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
if (lean_obj_tag(v_a_538_) == 0)
{
uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
lean_dec_ref(v___f_489_);
v___x_542_ = 0;
v___x_543_ = lean_box(v___x_542_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v___x_543_);
v___x_545_ = v___x_540_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
else
{
lean_object* v_mvarId_547_; lean_object* v_newEqs_548_; lean_object* v___x_549_; lean_object* v_xs_550_; lean_object* v_eqs_551_; lean_object* v_eqsNew_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_564_; 
lean_del_object(v___x_540_);
v_mvarId_547_ = lean_ctor_get(v_a_538_, 0);
lean_inc(v_mvarId_547_);
v_newEqs_548_ = lean_ctor_get(v_a_538_, 1);
lean_inc_ref(v_newEqs_548_);
lean_dec_ref_known(v_a_538_, 3);
v___x_549_ = lean_st_ref_take(v___y_531_);
v_xs_550_ = lean_ctor_get(v___x_549_, 1);
v_eqs_551_ = lean_ctor_get(v___x_549_, 2);
v_eqsNew_552_ = lean_ctor_get(v___x_549_, 3);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; 
v_unused_565_ = lean_ctor_get(v___x_549_, 0);
lean_dec(v_unused_565_);
v___x_554_ = v___x_549_;
v_isShared_555_ = v_isSharedCheck_564_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_eqsNew_552_);
lean_inc(v_eqs_551_);
lean_inc(v_xs_550_);
lean_dec(v___x_549_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_564_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_556_ = lean_array_to_list(v_newEqs_548_);
v___x_557_ = l_List_appendTR___redArg(v___x_556_, v_eqs_551_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 2, v___x_557_);
lean_ctor_set(v___x_554_, 0, v_mvarId_547_);
v___x_559_ = v___x_554_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_mvarId_547_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_xs_550_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_eqsNew_552_);
v___x_559_ = v_reuseFailAlloc_563_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_560_ = lean_st_ref_put(v___y_531_, v___x_559_);
v___x_561_ = lean_box(0);
lean_inc(v___y_535_);
lean_inc_ref(v___y_534_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc(v___y_531_);
v___x_562_ = lean_apply_7(v___f_489_, v___x_561_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, lean_box(0));
return v___x_562_;
}
}
}
}
}
else
{
lean_object* v_a_567_; uint8_t v___x_568_; 
v_a_567_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_537_, 1);
v___x_568_ = l_Lean_Exception_isInterrupt(v_a_567_);
if (v___x_568_ == 0)
{
uint8_t v___x_569_; 
lean_inc(v_a_567_);
v___x_569_ = l_Lean_Exception_isRuntime(v_a_567_);
v___y_504_ = v___y_532_;
v___y_505_ = v___y_531_;
v___y_506_ = v___y_534_;
v___y_507_ = v___y_533_;
v___y_508_ = v_a_567_;
v___y_509_ = v___y_535_;
v___y_510_ = v___x_569_;
goto v___jp_503_;
}
else
{
v___y_504_ = v___y_532_;
v___y_505_ = v___y_531_;
v___y_506_ = v___y_534_;
v___y_507_ = v___y_533_;
v___y_508_ = v_a_567_;
v___y_509_ = v___y_535_;
v___y_510_ = v___x_568_;
goto v___jp_503_;
}
}
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 2, v_tail_499_);
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_mvarId_571_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_xs_572_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v_tail_499_);
lean_ctor_set(v_reuseFailAlloc_735_, 3, v_eqsNew_573_);
v___x_578_ = v_reuseFailAlloc_735_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_579_ = lean_st_ref_put(v___y_492_, v___x_578_);
lean_inc(v_head_498_);
v___x_580_ = l_Lean_mkFVar(v_head_498_);
lean_inc(v___y_496_);
lean_inc_ref(v___y_495_);
lean_inc(v___y_494_);
lean_inc_ref(v___y_493_);
v___x_581_ = lean_infer_type(v___x_580_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___x_654_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc_n(v_a_582_, 2);
lean_dec_ref_known(v___x_581_, 1);
v___x_654_ = l_Lean_Meta_matchEq_x3f(v_a_582_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref_known(v___x_654_, 1);
if (lean_obj_tag(v_a_655_) == 1)
{
lean_object* v_val_656_; lean_object* v_snd_657_; lean_object* v_fst_658_; lean_object* v_snd_659_; lean_object* v___x_660_; 
v_val_656_ = lean_ctor_get(v_a_655_, 0);
lean_inc(v_val_656_);
lean_dec_ref_known(v_a_655_, 1);
v_snd_657_ = lean_ctor_get(v_val_656_, 1);
lean_inc(v_snd_657_);
lean_dec(v_val_656_);
v_fst_658_ = lean_ctor_get(v_snd_657_, 0);
lean_inc(v_fst_658_);
v_snd_659_ = lean_ctor_get(v_snd_657_, 1);
lean_inc_n(v_snd_659_, 2);
lean_dec(v_snd_657_);
v___x_660_ = l_Lean_Meta_isExprDefEq(v_fst_658_, v_snd_659_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; uint8_t v___x_662_; uint8_t v___y_664_; uint8_t v___x_684_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v___x_660_, 1);
v___x_662_ = 1;
v___x_684_ = lean_unbox(v_a_661_);
lean_dec(v_a_661_);
if (v___x_684_ == 0)
{
uint8_t v___x_685_; 
v___x_685_ = l_Lean_Expr_isFVar(v_snd_659_);
if (v___x_685_ == 0)
{
v___y_664_ = v___x_685_;
goto v___jp_663_;
}
else
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = l_Lean_Expr_fvarId_x21(v_snd_659_);
v___x_687_ = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(v___x_686_, v_xs_491_);
lean_dec(v___x_686_);
v___y_664_ = v___x_687_;
goto v___jp_663_;
}
}
else
{
lean_object* v___x_688_; 
lean_dec(v_snd_659_);
lean_dec(v_a_582_);
lean_del_object(v___x_501_);
lean_dec_ref(v___f_489_);
v___x_688_ = l_Lean_MVarId_clear(v_mvarId_490_, v_head_498_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_710_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_710_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_710_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_710_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v_xs_694_; lean_object* v_eqs_695_; lean_object* v_eqsNew_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_708_; 
v___x_693_ = lean_st_ref_take(v___y_492_);
v_xs_694_ = lean_ctor_get(v___x_693_, 1);
v_eqs_695_ = lean_ctor_get(v___x_693_, 2);
v_eqsNew_696_ = lean_ctor_get(v___x_693_, 3);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; 
v_unused_709_ = lean_ctor_get(v___x_693_, 0);
lean_dec(v_unused_709_);
v___x_698_ = v___x_693_;
v_isShared_699_ = v_isSharedCheck_708_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_eqsNew_696_);
lean_inc(v_eqs_695_);
lean_inc(v_xs_694_);
lean_dec(v___x_693_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_708_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v_a_689_);
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_689_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_xs_694_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_eqs_695_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_eqsNew_696_);
v___x_701_ = v_reuseFailAlloc_707_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_702_ = lean_st_ref_put(v___y_492_, v___x_701_);
v___x_703_ = lean_box(v___x_662_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_703_);
v___x_705_ = v___x_691_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
v_a_711_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_688_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_688_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
v___jp_663_:
{
if (v___y_664_ == 0)
{
lean_dec(v_snd_659_);
v___y_584_ = v___y_492_;
v___y_585_ = v___y_493_;
v___y_586_ = v___y_494_;
v___y_587_ = v___y_495_;
v___y_588_ = v___y_496_;
goto v___jp_583_;
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec(v_a_582_);
lean_del_object(v___x_501_);
lean_dec(v_mvarId_490_);
lean_dec_ref(v___f_489_);
v___x_665_ = l_Lean_Expr_fvarId_x21(v_snd_659_);
lean_dec(v_snd_659_);
v___x_666_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(v_head_498_, v___x_665_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
lean_dec(v___x_665_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_674_; 
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; 
v_unused_675_ = lean_ctor_get(v___x_666_, 0);
lean_dec(v_unused_675_);
v___x_668_ = v___x_666_;
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
else
{
lean_dec(v___x_666_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = lean_box(v___x_662_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_670_);
v___x_672_ = v___x_668_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
v_a_676_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_666_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_666_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
}
else
{
lean_dec(v_snd_659_);
lean_dec(v_a_582_);
lean_del_object(v___x_501_);
lean_dec(v_head_498_);
lean_dec(v_mvarId_490_);
lean_dec_ref(v___f_489_);
return v___x_660_;
}
}
else
{
lean_dec(v_a_655_);
v___y_584_ = v___y_492_;
v___y_585_ = v___y_493_;
v___y_586_ = v___y_494_;
v___y_587_ = v___y_495_;
v___y_588_ = v___y_496_;
goto v___jp_583_;
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_a_582_);
lean_del_object(v___x_501_);
lean_dec(v_head_498_);
lean_dec(v_mvarId_490_);
lean_dec_ref(v___f_489_);
v_a_719_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_654_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_654_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
v___jp_583_:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_Meta_matchHEq_x3f(v_a_582_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_589_, 1);
if (lean_obj_tag(v_a_590_) == 1)
{
uint8_t v___x_591_; lean_object* v___x_592_; 
lean_dec_ref_known(v_a_590_, 1);
v___x_591_ = 1;
lean_inc(v_head_498_);
lean_inc(v_mvarId_490_);
v___x_592_ = l_Lean_Meta_heqToEq(v_mvarId_490_, v_head_498_, v___x_591_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_637_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_637_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_637_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_637_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v_fst_597_; lean_object* v_snd_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_636_; 
v_fst_597_ = lean_ctor_get(v_a_593_, 0);
v_snd_598_ = lean_ctor_get(v_a_593_, 1);
v_isSharedCheck_636_ = !lean_is_exclusive(v_a_593_);
if (v_isSharedCheck_636_ == 0)
{
v___x_600_ = v_a_593_;
v_isShared_601_ = v_isSharedCheck_636_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_snd_598_);
lean_inc(v_fst_597_);
lean_dec(v_a_593_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_636_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
uint8_t v___x_602_; 
v___x_602_ = l_Lean_instBEqMVarId_beq(v_snd_598_, v_mvarId_490_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v_xs_604_; lean_object* v_eqs_605_; lean_object* v_eqsNew_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_621_; 
lean_del_object(v___x_501_);
lean_dec(v_head_498_);
lean_dec(v_mvarId_490_);
lean_dec_ref(v___f_489_);
v___x_603_ = lean_st_ref_take(v___y_584_);
v_xs_604_ = lean_ctor_get(v___x_603_, 1);
v_eqs_605_ = lean_ctor_get(v___x_603_, 2);
v_eqsNew_606_ = lean_ctor_get(v___x_603_, 3);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v___x_603_, 0);
lean_dec(v_unused_622_);
v___x_608_ = v___x_603_;
v_isShared_609_ = v_isSharedCheck_621_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_eqsNew_606_);
lean_inc(v_eqs_605_);
lean_inc(v_xs_604_);
lean_dec(v___x_603_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_621_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_601_ == 0)
{
lean_ctor_set_tag(v___x_600_, 1);
lean_ctor_set(v___x_600_, 1, v_eqs_605_);
v___x_611_ = v___x_600_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_fst_597_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_eqs_605_);
v___x_611_ = v_reuseFailAlloc_620_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 2, v___x_611_);
lean_ctor_set(v___x_608_, 0, v_snd_598_);
v___x_613_ = v___x_608_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_snd_598_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_xs_604_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v_eqsNew_606_);
v___x_613_ = v_reuseFailAlloc_619_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_614_ = lean_st_ref_put(v___y_584_, v___x_613_);
v___x_615_ = lean_box(v___x_591_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_615_);
v___x_617_ = v___x_595_;
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
}
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; 
lean_del_object(v___x_600_);
lean_dec(v_snd_598_);
lean_dec(v_fst_597_);
lean_del_object(v___x_595_);
v___x_623_ = lean_box(1);
lean_inc(v_mvarId_490_);
v___x_624_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(v_mvarId_490_, v___x_623_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_635_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_635_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_635_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_635_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
uint8_t v___x_629_; 
v___x_629_ = lean_unbox(v_a_625_);
lean_dec(v_a_625_);
if (v___x_629_ == 0)
{
lean_del_object(v___x_627_);
v___y_531_ = v___y_584_;
v___y_532_ = v___y_585_;
v___y_533_ = v___y_586_;
v___y_534_ = v___y_587_;
v___y_535_ = v___y_588_;
goto v___jp_530_;
}
else
{
uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
lean_del_object(v___x_501_);
lean_dec(v_head_498_);
lean_dec(v_mvarId_490_);
lean_dec_ref(v___f_489_);
v___x_630_ = 0;
v___x_631_ = lean_box(v___x_630_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_631_);
v___x_633_ = v___x_627_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
else
{
lean_del_object(v___x_501_);
lean_dec(v_head_498_);
lean_dec(v_mvarId_490_);
lean_dec_ref(v___f_489_);
return v___x_624_;
}
}
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_del_object(v___x_501_);
lean_dec(v_head_498_);
lean_dec(v_mvarId_490_);
lean_dec_ref(v___f_489_);
v_a_638_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_592_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_592_);
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
else
{
lean_dec(v_a_590_);
v___y_531_ = v___y_584_;
v___y_532_ = v___y_585_;
v___y_533_ = v___y_586_;
v___y_534_ = v___y_587_;
v___y_535_ = v___y_588_;
goto v___jp_530_;
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_del_object(v___x_501_);
lean_dec(v_head_498_);
lean_dec(v_mvarId_490_);
lean_dec_ref(v___f_489_);
v_a_646_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_589_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_589_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_del_object(v___x_501_);
lean_dec(v_head_498_);
lean_dec(v_mvarId_490_);
lean_dec_ref(v___f_489_);
v_a_727_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_581_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_581_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; 
lean_dec(v_mvarId_490_);
lean_dec(v_eqs_488_);
v___x_739_ = lean_box(0);
lean_inc(v___y_496_);
lean_inc_ref(v___y_495_);
lean_inc(v___y_494_);
lean_inc_ref(v___y_493_);
lean_inc(v___y_492_);
v___x_740_ = lean_apply_7(v___f_489_, v___x_739_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, lean_box(0));
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1___boxed(lean_object* v_eqs_741_, lean_object* v___f_742_, lean_object* v_mvarId_743_, lean_object* v_xs_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1(v_eqs_741_, v___f_742_, v_mvarId_743_, v_xs_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec(v_xs_744_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v___x_759_; lean_object* v_mvarId_760_; lean_object* v_xs_761_; lean_object* v_eqs_762_; lean_object* v___f_763_; lean_object* v___y_764_; lean_object* v___x_765_; 
v___x_759_ = lean_st_ref_get(v_a_753_);
v_mvarId_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc_n(v_mvarId_760_, 2);
v_xs_761_ = lean_ctor_get(v___x_759_, 1);
lean_inc(v_xs_761_);
v_eqs_762_ = lean_ctor_get(v___x_759_, 2);
lean_inc(v_eqs_762_);
lean_dec(v___x_759_);
v___f_763_ = ((lean_object*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___closed__0));
v___y_764_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1___boxed), 10, 4);
lean_closure_set(v___y_764_, 0, v_eqs_762_);
lean_closure_set(v___y_764_, 1, v___f_763_);
lean_closure_set(v___y_764_, 2, v_mvarId_760_);
lean_closure_set(v___y_764_, 3, v_xs_761_);
v___x_765_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(v_mvarId_760_, v___y_764_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___boxed(lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(v_a_773_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; uint8_t v___x_781_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
v___x_781_ = lean_unbox(v_a_780_);
lean_dec(v_a_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; 
lean_dec_ref_known(v___x_779_, 1);
v___x_782_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; uint8_t v___x_784_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
v___x_784_ = lean_unbox(v_a_783_);
lean_dec(v_a_783_);
if (v___x_784_ == 0)
{
return v___x_782_;
}
else
{
lean_dec_ref_known(v___x_782_, 1);
goto _start;
}
}
else
{
return v___x_782_;
}
}
else
{
return v___x_779_;
}
}
else
{
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go___boxed(lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0(lean_object* v_k_793_, lean_object* v_b_794_, lean_object* v_c_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; 
lean_inc(v___y_799_);
lean_inc_ref(v___y_798_);
lean_inc(v___y_797_);
lean_inc_ref(v___y_796_);
v___x_801_ = lean_apply_7(v_k_793_, v_b_794_, v_c_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, lean_box(0));
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0___boxed(lean_object* v_k_802_, lean_object* v_b_803_, lean_object* v_c_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0(v_k_802_, v_b_803_, v_c_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(lean_object* v_type_811_, lean_object* v_k_812_, uint8_t v_cleanupAnnotations_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___f_819_; uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___f_819_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_819_, 0, v_k_812_);
v___x_820_ = 0;
v___x_821_ = lean_box(0);
v___x_822_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_820_, v___x_821_, v_type_811_, v___f_819_, v_cleanupAnnotations_813_, v___x_820_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
v_a_831_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_822_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_822_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___boxed(lean_object* v_type_839_, lean_object* v_k_840_, lean_object* v_cleanupAnnotations_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_847_; lean_object* v_res_848_; 
v_cleanupAnnotations_boxed_847_ = lean_unbox(v_cleanupAnnotations_841_);
v_res_848_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(v_type_839_, v_k_840_, v_cleanupAnnotations_boxed_847_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0(lean_object* v_00_u03b1_849_, lean_object* v_type_850_, lean_object* v_k_851_, uint8_t v_cleanupAnnotations_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(v_type_850_, v_k_851_, v_cleanupAnnotations_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___boxed(lean_object* v_00_u03b1_859_, lean_object* v_type_860_, lean_object* v_k_861_, lean_object* v_cleanupAnnotations_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_868_; lean_object* v_res_869_; 
v_cleanupAnnotations_boxed_868_ = lean_unbox(v_cleanupAnnotations_862_);
v_res_869_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0(v_00_u03b1_859_, v_type_860_, v_k_861_, v_cleanupAnnotations_boxed_868_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
return v_res_869_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0(lean_object* v_x_870_){
_start:
{
uint8_t v___x_871_; 
v___x_871_ = 0;
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0___boxed(lean_object* v_x_872_){
_start:
{
uint8_t v_res_873_; lean_object* v_r_874_; 
v_res_873_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0(v_x_872_);
lean_dec(v_x_872_);
v_r_874_ = lean_box(v_res_873_);
return v_r_874_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1(lean_object* v_fvarId_875_, lean_object* v_x_876_){
_start:
{
uint8_t v___x_877_; 
v___x_877_ = l_Lean_instBEqFVarId_beq(v_fvarId_875_, v_x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1___boxed(lean_object* v_fvarId_878_, lean_object* v_x_879_){
_start:
{
uint8_t v_res_880_; lean_object* v_r_881_; 
v_res_880_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1(v_fvarId_878_, v_x_879_);
lean_dec(v_x_879_);
lean_dec(v_fvarId_878_);
v_r_881_ = lean_box(v_res_880_);
return v_r_881_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_883_; lean_object* v___x_884_; 
v_cellCount_883_ = lean_unsigned_to_nat(16u);
v___x_884_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_883_);
return v___x_884_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v_cellCount_885_; lean_object* v___x_886_; 
v_cellCount_885_ = lean_unsigned_to_nat(16u);
v___x_886_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_885_);
return v___x_886_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_887_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2);
v___x_888_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1);
v___x_889_ = lean_unsigned_to_nat(0u);
v___x_890_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v___x_888_);
lean_ctor_set(v___x_890_, 2, v___x_887_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(lean_object* v_e_891_, lean_object* v_fvarId_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; uint8_t v_fst_897_; lean_object* v_mctx_898_; lean_object* v___y_916_; lean_object* v_mctx_921_; lean_object* v___f_922_; lean_object* v___f_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_895_ = lean_st_ref_get(v___y_893_);
v_mctx_921_ = lean_ctor_get(v___x_895_, 0);
lean_inc_ref_n(v_mctx_921_, 2);
lean_dec(v___x_895_);
v___f_922_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__0));
v___f_923_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_923_, 0, v_fvarId_892_);
v___x_924_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__3, &l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__3_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__3);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v_mctx_921_);
v___x_926_ = l_Lean_Expr_hasFVar(v_e_891_);
if (v___x_926_ == 0)
{
uint8_t v___x_927_; 
v___x_927_ = l_Lean_Expr_hasMVar(v_e_891_);
if (v___x_927_ == 0)
{
lean_dec_ref_known(v___x_925_, 2);
lean_dec_ref(v___f_923_);
lean_dec_ref(v_e_891_);
v_fst_897_ = v___x_927_;
v_mctx_898_ = v_mctx_921_;
goto v___jp_896_;
}
else
{
lean_object* v___x_928_; 
lean_dec_ref(v_mctx_921_);
v___x_928_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_923_, v___f_922_, v_e_891_, v___x_925_);
v___y_916_ = v___x_928_;
goto v___jp_915_;
}
}
else
{
lean_object* v___x_929_; 
lean_dec_ref(v_mctx_921_);
v___x_929_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_923_, v___f_922_, v_e_891_, v___x_925_);
v___y_916_ = v___x_929_;
goto v___jp_915_;
}
v___jp_896_:
{
lean_object* v___x_899_; lean_object* v_cache_900_; lean_object* v_zetaDeltaFVarIds_901_; lean_object* v_postponed_902_; lean_object* v_diag_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_913_; 
v___x_899_ = lean_st_ref_take(v___y_893_);
v_cache_900_ = lean_ctor_get(v___x_899_, 1);
v_zetaDeltaFVarIds_901_ = lean_ctor_get(v___x_899_, 2);
v_postponed_902_ = lean_ctor_get(v___x_899_, 3);
v_diag_903_ = lean_ctor_get(v___x_899_, 4);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; 
v_unused_914_ = lean_ctor_get(v___x_899_, 0);
lean_dec(v_unused_914_);
v___x_905_ = v___x_899_;
v_isShared_906_ = v_isSharedCheck_913_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_diag_903_);
lean_inc(v_postponed_902_);
lean_inc(v_zetaDeltaFVarIds_901_);
lean_inc(v_cache_900_);
lean_dec(v___x_899_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_913_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v_mctx_898_);
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_mctx_898_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_cache_900_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_zetaDeltaFVarIds_901_);
lean_ctor_set(v_reuseFailAlloc_912_, 3, v_postponed_902_);
lean_ctor_set(v_reuseFailAlloc_912_, 4, v_diag_903_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_st_ref_put(v___y_893_, v___x_908_);
v___x_910_ = lean_box(v_fst_897_);
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
return v___x_911_;
}
}
}
v___jp_915_:
{
lean_object* v_snd_917_; lean_object* v_fst_918_; lean_object* v_mctx_919_; uint8_t v___x_920_; 
v_snd_917_ = lean_ctor_get(v___y_916_, 1);
lean_inc(v_snd_917_);
v_fst_918_ = lean_ctor_get(v___y_916_, 0);
lean_inc(v_fst_918_);
lean_dec_ref(v___y_916_);
v_mctx_919_ = lean_ctor_get(v_snd_917_, 1);
lean_inc_ref(v_mctx_919_);
lean_dec(v_snd_917_);
v___x_920_ = lean_unbox(v_fst_918_);
lean_dec(v_fst_918_);
v_fst_897_ = v___x_920_;
v_mctx_898_ = v_mctx_919_;
goto v___jp_896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___boxed(lean_object* v_e_930_, lean_object* v_fvarId_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(v_e_930_, v_fvarId_931_, v___y_932_);
lean_dec(v___y_932_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1(lean_object* v_e_935_, lean_object* v_fvarId_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(v_e_935_, v_fvarId_936_, v___y_938_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___boxed(lean_object* v_e_943_, lean_object* v_fvarId_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1(v_e_943_, v_fvarId_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(lean_object* v_mvarId_951_, lean_object* v_x_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_951_, v_x_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
v_a_967_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_958_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_958_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg___boxed(lean_object* v_mvarId_975_, lean_object* v_x_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(v_mvarId_975_, v_x_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3(lean_object* v_00_u03b1_983_, lean_object* v_mvarId_984_, lean_object* v_x_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(v_mvarId_984_, v_x_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___boxed(lean_object* v_00_u03b1_992_, lean_object* v_mvarId_993_, lean_object* v_x_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3(v_00_u03b1_992_, v_mvarId_993_, v_x_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__0(lean_object* v_numEqs_1001_, lean_object* v_ys_1002_, lean_object* v_x_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_array_get_size(v_ys_1002_);
v___x_1010_ = lean_nat_sub(v___x_1009_, v_numEqs_1001_);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__0___boxed(lean_object* v_numEqs_1012_, lean_object* v_ys_1013_, lean_object* v_x_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_Meta_Match_simpH___lam__0(v_numEqs_1012_, v_ys_1013_, v_x_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec_ref(v_x_1014_);
lean_dec_ref(v_ys_1013_);
lean_dec(v_numEqs_1012_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(lean_object* v_a_1021_, lean_object* v_as_1022_, size_t v_i_1023_, size_t v_stop_1024_, lean_object* v_b_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
uint8_t v___x_1031_; 
v___x_1031_ = lean_usize_dec_eq(v_i_1023_, v_stop_1024_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_array_uget_borrowed(v_as_1022_, v_i_1023_);
lean_inc(v___x_1032_);
lean_inc_ref(v_a_1021_);
v___x_1033_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(v_a_1021_, v___x_1032_, v___y_1027_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v_a_1036_; uint8_t v___x_1040_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref_known(v___x_1033_, 1);
v___x_1040_ = lean_unbox(v_a_1034_);
lean_dec(v_a_1034_);
if (v___x_1040_ == 0)
{
v_a_1036_ = v_b_1025_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1041_; 
lean_inc(v___x_1032_);
v___x_1041_ = lean_array_push(v_b_1025_, v___x_1032_);
v_a_1036_ = v___x_1041_;
goto v___jp_1035_;
}
v___jp_1035_:
{
size_t v___x_1037_; size_t v___x_1038_; 
v___x_1037_ = ((size_t)1ULL);
v___x_1038_ = lean_usize_add(v_i_1023_, v___x_1037_);
v_i_1023_ = v___x_1038_;
v_b_1025_ = v_a_1036_;
goto _start;
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v_b_1025_);
lean_dec_ref(v_a_1021_);
v_a_1042_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1033_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1033_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
else
{
lean_object* v___x_1050_; 
lean_dec_ref(v_a_1021_);
v___x_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1050_, 0, v_b_1025_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2___boxed(lean_object* v_a_1051_, lean_object* v_as_1052_, lean_object* v_i_1053_, lean_object* v_stop_1054_, lean_object* v_b_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
size_t v_i_boxed_1061_; size_t v_stop_boxed_1062_; lean_object* v_res_1063_; 
v_i_boxed_1061_ = lean_unbox_usize(v_i_1053_);
lean_dec(v_i_1053_);
v_stop_boxed_1062_ = lean_unbox_usize(v_stop_1054_);
lean_dec(v_stop_1054_);
v_res_1063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(v_a_1051_, v_as_1052_, v_i_boxed_1061_, v_stop_boxed_1062_, v_b_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec_ref(v_as_1052_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__1(lean_object* v_snd_1064_, uint8_t v___x_1065_, lean_object* v___x_1066_, lean_object* v___x_1067_, lean_object* v_a_1068_, lean_object* v___x_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_a_1076_; lean_object* v___y_1097_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = lean_mk_empty_array_with_capacity(v___x_1066_);
v___x_1108_ = lean_nat_dec_lt(v___x_1066_, v___x_1067_);
if (v___x_1108_ == 0)
{
lean_dec_ref(v_a_1068_);
v_a_1076_ = v___x_1107_;
goto v___jp_1075_;
}
else
{
uint8_t v___x_1109_; 
v___x_1109_ = lean_nat_dec_le(v___x_1067_, v___x_1067_);
if (v___x_1109_ == 0)
{
if (v___x_1108_ == 0)
{
lean_dec_ref(v_a_1068_);
v_a_1076_ = v___x_1107_;
goto v___jp_1075_;
}
else
{
size_t v___x_1110_; size_t v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = ((size_t)0ULL);
v___x_1111_ = lean_usize_of_nat(v___x_1067_);
v___x_1112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(v_a_1068_, v___x_1069_, v___x_1110_, v___x_1111_, v___x_1107_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
v___y_1097_ = v___x_1112_;
goto v___jp_1096_;
}
}
else
{
size_t v___x_1113_; size_t v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = ((size_t)0ULL);
v___x_1114_ = lean_usize_of_nat(v___x_1067_);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(v_a_1068_, v___x_1069_, v___x_1113_, v___x_1114_, v___x_1107_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
v___y_1097_ = v___x_1115_;
goto v___jp_1096_;
}
}
v___jp_1075_:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_MVarId_revert(v_snd_1064_, v_a_1076_, v___x_1065_, v___x_1065_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1087_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1087_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1087_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v_snd_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v_snd_1082_ = lean_ctor_get(v_a_1078_, 1);
lean_inc(v_snd_1082_);
lean_dec(v_a_1078_);
v___x_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1083_, 0, v_snd_1082_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1083_);
v___x_1085_ = v___x_1080_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
v_a_1088_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1077_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1077_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
v___jp_1096_:
{
if (lean_obj_tag(v___y_1097_) == 0)
{
lean_object* v_a_1098_; 
v_a_1098_ = lean_ctor_get(v___y_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___y_1097_, 1);
v_a_1076_ = v_a_1098_;
goto v___jp_1075_;
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v_snd_1064_);
v_a_1099_ = lean_ctor_get(v___y_1097_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___y_1097_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___y_1097_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___y_1097_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__1___boxed(lean_object* v_snd_1116_, lean_object* v___x_1117_, lean_object* v___x_1118_, lean_object* v___x_1119_, lean_object* v_a_1120_, lean_object* v___x_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
uint8_t v___x_6770__boxed_1127_; lean_object* v_res_1128_; 
v___x_6770__boxed_1127_ = lean_unbox(v___x_1117_);
v_res_1128_ = l_Lean_Meta_Match_simpH___lam__1(v_snd_1116_, v___x_6770__boxed_1127_, v___x_1118_, v___x_1119_, v_a_1120_, v___x_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec_ref(v___x_1121_);
lean_dec(v___x_1119_);
lean_dec(v___x_1118_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__2(lean_object* v_mvarId_1129_, lean_object* v___x_1130_, uint8_t v___x_1131_, lean_object* v_xs_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_MVarId_revert(v_mvarId_1129_, v___x_1130_, v___x_1131_, v___x_1131_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v_snd_1140_; lean_object* v___x_1141_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref_known(v___x_1138_, 1);
v_snd_1140_ = lean_ctor_get(v_a_1139_, 1);
lean_inc_n(v_snd_1140_, 2);
lean_dec(v_a_1139_);
v___x_1141_ = l_Lean_MVarId_getType(v_snd_1140_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___f_1148_; lean_object* v___x_1149_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = lean_array_mk(v_xs_1132_);
v___x_1144_ = l_Array_reverse___redArg(v___x_1143_);
v___x_1145_ = lean_unsigned_to_nat(0u);
v___x_1146_ = lean_array_get_size(v___x_1144_);
v___x_1147_ = lean_box(v___x_1131_);
lean_inc(v_snd_1140_);
v___f_1148_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH___lam__1___boxed), 11, 6);
lean_closure_set(v___f_1148_, 0, v_snd_1140_);
lean_closure_set(v___f_1148_, 1, v___x_1147_);
lean_closure_set(v___f_1148_, 2, v___x_1145_);
lean_closure_set(v___f_1148_, 3, v___x_1146_);
lean_closure_set(v___f_1148_, 4, v_a_1142_);
lean_closure_set(v___f_1148_, 5, v___x_1144_);
v___x_1149_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(v_snd_1140_, v___f_1148_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
return v___x_1149_;
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec(v_snd_1140_);
lean_dec(v_xs_1132_);
v_a_1150_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1141_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1141_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v_xs_1132_);
v_a_1158_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1138_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1138_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__2___boxed(lean_object* v_mvarId_1166_, lean_object* v___x_1167_, lean_object* v___x_1168_, lean_object* v_xs_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
uint8_t v___x_6881__boxed_1175_; lean_object* v_res_1176_; 
v___x_6881__boxed_1175_ = lean_unbox(v___x_1168_);
v_res_1176_ = l_Lean_Meta_Match_simpH___lam__2(v_mvarId_1166_, v___x_1167_, v___x_6881__boxed_1175_, v_xs_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH(lean_object* v_mvarId_1177_, lean_object* v_numEqs_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v_keyedConfig_1184_; uint8_t v_trackZetaDelta_1185_; lean_object* v_zetaDeltaSet_1186_; lean_object* v_lctx_1187_; lean_object* v_localInstances_1188_; lean_object* v_defEqCtx_x3f_1189_; lean_object* v_synthPendingDepth_1190_; lean_object* v_customCanUnfoldPredicate_x3f_1191_; uint8_t v_univApprox_1192_; uint8_t v_inTypeClassResolution_1193_; uint8_t v_cacheInferType_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_keyedConfig_1184_ = lean_ctor_get(v_a_1179_, 0);
v_trackZetaDelta_1185_ = lean_ctor_get_uint8(v_a_1179_, sizeof(void*)*7);
v_zetaDeltaSet_1186_ = lean_ctor_get(v_a_1179_, 1);
v_lctx_1187_ = lean_ctor_get(v_a_1179_, 2);
v_localInstances_1188_ = lean_ctor_get(v_a_1179_, 3);
v_defEqCtx_x3f_1189_ = lean_ctor_get(v_a_1179_, 4);
v_synthPendingDepth_1190_ = lean_ctor_get(v_a_1179_, 5);
v_customCanUnfoldPredicate_x3f_1191_ = lean_ctor_get(v_a_1179_, 6);
v_univApprox_1192_ = lean_ctor_get_uint8(v_a_1179_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1193_ = lean_ctor_get_uint8(v_a_1179_, sizeof(void*)*7 + 2);
v_cacheInferType_1194_ = lean_ctor_get_uint8(v_a_1179_, sizeof(void*)*7 + 3);
v___x_1195_ = 1;
lean_inc_ref(v_keyedConfig_1184_);
v___x_1196_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1195_, v_keyedConfig_1184_);
lean_inc(v_customCanUnfoldPredicate_x3f_1191_);
lean_inc(v_synthPendingDepth_1190_);
lean_inc(v_defEqCtx_x3f_1189_);
lean_inc_ref(v_localInstances_1188_);
lean_inc_ref(v_lctx_1187_);
lean_inc(v_zetaDeltaSet_1186_);
v___x_1197_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v_zetaDeltaSet_1186_);
lean_ctor_set(v___x_1197_, 2, v_lctx_1187_);
lean_ctor_set(v___x_1197_, 3, v_localInstances_1188_);
lean_ctor_set(v___x_1197_, 4, v_defEqCtx_x3f_1189_);
lean_ctor_set(v___x_1197_, 5, v_synthPendingDepth_1190_);
lean_ctor_set(v___x_1197_, 6, v_customCanUnfoldPredicate_x3f_1191_);
lean_ctor_set_uint8(v___x_1197_, sizeof(void*)*7, v_trackZetaDelta_1185_);
lean_ctor_set_uint8(v___x_1197_, sizeof(void*)*7 + 1, v_univApprox_1192_);
lean_ctor_set_uint8(v___x_1197_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1193_);
lean_ctor_set_uint8(v___x_1197_, sizeof(void*)*7 + 3, v_cacheInferType_1194_);
lean_inc(v_mvarId_1177_);
v___x_1198_ = l_Lean_MVarId_getType(v_mvarId_1177_, v___x_1197_, v_a_1180_, v_a_1181_, v_a_1182_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___f_1200_; uint8_t v___x_1201_; lean_object* v___x_1202_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
lean_inc(v_numEqs_1178_);
v___f_1200_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1200_, 0, v_numEqs_1178_);
v___x_1201_ = 0;
v___x_1202_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(v_a_1199_, v___f_1200_, v___x_1201_, v___x_1197_, v_a_1180_, v_a_1181_, v_a_1182_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1202_, 1);
v___x_1204_ = l_Lean_LocalContext_getFVarIds(v_lctx_1187_);
v___x_1205_ = l_Lean_MVarId_tryClearMany(v_mvarId_1177_, v___x_1204_, v___x_1197_, v_a_1180_, v_a_1181_, v_a_1182_);
lean_dec_ref(v___x_1204_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
lean_dec_ref_known(v___x_1205_, 1);
v___x_1207_ = lean_box(0);
v___x_1208_ = l_Lean_Meta_introNCore(v_a_1206_, v_a_1203_, v___x_1207_, v___x_1201_, v___x_1201_, v___x_1197_, v_a_1180_, v_a_1181_, v_a_1182_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v_fst_1210_; lean_object* v_snd_1211_; lean_object* v___x_1212_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1209_);
lean_dec_ref_known(v___x_1208_, 1);
v_fst_1210_ = lean_ctor_get(v_a_1209_, 0);
lean_inc(v_fst_1210_);
v_snd_1211_ = lean_ctor_get(v_a_1209_, 1);
lean_inc(v_snd_1211_);
lean_dec(v_a_1209_);
v___x_1212_ = l_Lean_Meta_introNCore(v_snd_1211_, v_numEqs_1178_, v___x_1207_, v___x_1201_, v___x_1201_, v___x_1197_, v_a_1180_, v_a_1181_, v_a_1182_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v_fst_1214_; lean_object* v_snd_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 1);
v_fst_1214_ = lean_ctor_get(v_a_1213_, 0);
lean_inc(v_fst_1214_);
v_snd_1215_ = lean_ctor_get(v_a_1213_, 1);
lean_inc(v_snd_1215_);
lean_dec(v_a_1213_);
v___x_1216_ = lean_array_to_list(v_fst_1210_);
v___x_1217_ = lean_array_to_list(v_fst_1214_);
v___x_1218_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1218_, 0, v_snd_1215_);
lean_ctor_set(v___x_1218_, 1, v___x_1216_);
lean_ctor_set(v___x_1218_, 2, v___x_1217_);
lean_ctor_set(v___x_1218_, 3, v___x_1207_);
v___x_1219_ = lean_st_mk_ref(v___x_1218_);
v___x_1220_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(v___x_1219_, v___x_1197_, v_a_1180_, v_a_1181_, v_a_1182_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1239_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1239_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1239_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = lean_st_ref_get(v___x_1219_);
lean_dec(v___x_1219_);
v___x_1226_ = lean_unbox(v_a_1221_);
lean_dec(v_a_1221_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
lean_dec(v___x_1225_);
lean_dec_ref_known(v___x_1197_, 7);
v___x_1227_ = lean_box(0);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1227_);
v___x_1229_ = v___x_1223_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
else
{
lean_object* v_mvarId_1231_; lean_object* v_xs_1232_; lean_object* v_eqsNew_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___f_1237_; lean_object* v___x_1238_; 
lean_del_object(v___x_1223_);
v_mvarId_1231_ = lean_ctor_get(v___x_1225_, 0);
lean_inc_n(v_mvarId_1231_, 2);
v_xs_1232_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_xs_1232_);
v_eqsNew_1233_ = lean_ctor_get(v___x_1225_, 3);
lean_inc(v_eqsNew_1233_);
lean_dec(v___x_1225_);
v___x_1234_ = l_List_reverse___redArg(v_eqsNew_1233_);
v___x_1235_ = lean_array_mk(v___x_1234_);
v___x_1236_ = lean_box(v___x_1201_);
v___f_1237_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1237_, 0, v_mvarId_1231_);
lean_closure_set(v___f_1237_, 1, v___x_1235_);
lean_closure_set(v___f_1237_, 2, v___x_1236_);
lean_closure_set(v___f_1237_, 3, v_xs_1232_);
v___x_1238_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(v_mvarId_1231_, v___f_1237_, v___x_1197_, v_a_1180_, v_a_1181_, v_a_1182_);
lean_dec_ref_known(v___x_1197_, 7);
return v___x_1238_;
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v___x_1219_);
lean_dec_ref_known(v___x_1197_, 7);
v_a_1240_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1220_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1220_);
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
lean_dec(v_fst_1210_);
lean_dec_ref_known(v___x_1197_, 7);
v_a_1248_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1212_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1212_);
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
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec_ref_known(v___x_1197_, 7);
lean_dec(v_numEqs_1178_);
v_a_1256_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1208_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1208_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v_a_1203_);
lean_dec_ref_known(v___x_1197_, 7);
lean_dec(v_numEqs_1178_);
v_a_1264_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1205_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1205_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec_ref_known(v___x_1197_, 7);
lean_dec(v_numEqs_1178_);
lean_dec(v_mvarId_1177_);
v_a_1272_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1202_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1202_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec_ref_known(v___x_1197_, 7);
lean_dec(v_numEqs_1178_);
lean_dec(v_mvarId_1177_);
v_a_1280_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1198_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1198_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___boxed(lean_object* v_mvarId_1288_, lean_object* v_numEqs_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Meta_Match_simpH(v_mvarId_1288_, v_numEqs_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f(lean_object* v_h_1296_, lean_object* v_numEqs_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_box(0);
v___x_1304_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_h_1296_, v___x_1303_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1306_ = l_Lean_Expr_mvarId_x21(v_a_1305_);
lean_dec(v_a_1305_);
v___x_1307_ = l_Lean_Meta_Match_simpH(v___x_1306_, v_numEqs_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1341_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1341_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1341_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
if (lean_obj_tag(v_a_1308_) == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = lean_box(0);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1312_);
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
else
{
lean_object* v_val_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1340_; 
lean_del_object(v___x_1310_);
v_val_1316_ = lean_ctor_get(v_a_1308_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_a_1308_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1318_ = v_a_1308_;
v_isShared_1319_ = v_isSharedCheck_1340_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_val_1316_);
lean_dec(v_a_1308_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1340_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_MVarId_getType(v_val_1316_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1331_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1331_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1331_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v_a_1321_);
v___x_1326_ = v___x_1318_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1328_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1326_);
v___x_1328_ = v___x_1323_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
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
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_del_object(v___x_1318_);
v_a_1332_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1320_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1320_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
v_a_1342_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1307_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1307_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec(v_numEqs_1297_);
v_a_1350_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1304_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1304_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f___boxed(lean_object* v_h_1358_, lean_object* v_numEqs_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_Meta_Match_simpH_x3f(v_h_1358_, v_numEqs_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
return v_res_1365_;
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
