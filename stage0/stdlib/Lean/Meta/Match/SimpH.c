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
lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1(lean_object* v_msg_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
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
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_24_ = stack[0].m_obj;
lean_object* v___y_25_ = stack[1].m_obj;
lean_object* v___y_26_ = stack[2].m_obj;
lean_object* v___y_27_ = stack[3].m_obj;
lean_object* v___y_28_ = stack[4].m_obj;
lean_object* v___y_29_ = stack[5].m_obj;
lean_object* v_res_97_;
v_res_97_ = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1(v_msg_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_);
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___boxed(lean_object* v_msg_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1(v_msg_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
return v_res_105_;
}
}
uint8_t l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(lean_object* v_a_106_, lean_object* v_x_107_){
_start:
{
if (lean_obj_tag(v_x_107_) == 0)
{
uint8_t v___x_108_; 
v___x_108_ = 0;
return v___x_108_;
}
else
{
lean_object* v_head_109_; lean_object* v_tail_110_; uint8_t v___x_111_; 
v_head_109_ = lean_ctor_get(v_x_107_, 0);
v_tail_110_ = lean_ctor_get(v_x_107_, 1);
v___x_111_ = l_Lean_instBEqFVarId_beq(v_a_106_, v_head_109_);
if (v___x_111_ == 0)
{
v_x_107_ = v_tail_110_;
goto _start;
}
else
{
return v___x_111_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_106_ = stack[0].m_obj;
lean_object* v_x_107_ = stack[1].m_obj;
uint8_t v_res_113_;
v_res_113_ = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(v_a_106_, v_x_107_);
stack->m_num = v_res_113_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0___boxed(lean_object* v_a_114_, lean_object* v_x_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(v_a_114_, v_x_115_);
lean_dec(v_x_115_);
lean_dec(v_a_114_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2(lean_object* v_as_118_, size_t v_i_119_, size_t v_stop_120_, lean_object* v_b_121_){
_start:
{
uint8_t v___x_122_; 
v___x_122_ = lean_usize_dec_eq(v_i_119_, v_stop_120_);
if (v___x_122_ == 0)
{
size_t v___x_123_; size_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_123_ = ((size_t)1ULL);
v___x_124_ = lean_usize_sub(v_i_119_, v___x_123_);
v___x_125_ = lean_array_uget_borrowed(v_as_118_, v___x_124_);
lean_inc(v___x_125_);
v___x_126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v_b_121_);
v_i_119_ = v___x_124_;
v_b_121_ = v___x_126_;
goto _start;
}
else
{
return v_b_121_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_118_ = stack[0].m_obj;
size_t v_i_119_ = stack[1].m_num;
size_t v_stop_120_ = stack[2].m_num;
lean_object* v_b_121_ = stack[3].m_obj;
lean_object* v_res_128_;
v_res_128_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2(v_as_118_, v_i_119_, v_stop_120_, v_b_121_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2___boxed(lean_object* v_as_129_, lean_object* v_i_130_, lean_object* v_stop_131_, lean_object* v_b_132_){
_start:
{
size_t v_i_boxed_133_; size_t v_stop_boxed_134_; lean_object* v_res_135_; 
v_i_boxed_133_ = lean_unbox_usize(v_i_130_);
lean_dec(v_i_130_);
v_stop_boxed_134_ = lean_unbox_usize(v_stop_131_);
lean_dec(v_stop_131_);
v_res_135_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2(v_as_129_, v_i_boxed_133_, v_stop_boxed_134_, v_b_132_);
lean_dec_ref(v_as_129_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(lean_object* v_l_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
if (lean_obj_tag(v_a_138_) == 0)
{
lean_dec_ref(v_a_139_);
lean_inc(v_l_136_);
return v_l_136_;
}
else
{
lean_object* v_head_140_; lean_object* v_tail_141_; uint8_t v___x_142_; 
v_head_140_ = lean_ctor_get(v_a_138_, 0);
lean_inc(v_head_140_);
v_tail_141_ = lean_ctor_get(v_a_138_, 1);
lean_inc(v_tail_141_);
lean_dec_ref_known(v_a_138_, 2);
v___x_142_ = l_Lean_instBEqFVarId_beq(v_head_140_, v_a_137_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = lean_array_push(v_a_139_, v_head_140_);
v_a_138_ = v_tail_141_;
v_a_139_ = v___x_143_;
goto _start;
}
else
{
lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
lean_dec(v_head_140_);
v___x_145_ = lean_array_get_size(v_a_139_);
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = lean_nat_dec_lt(v___x_146_, v___x_145_);
if (v___x_147_ == 0)
{
lean_dec_ref(v_a_139_);
return v_tail_141_;
}
else
{
size_t v___x_148_; size_t v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_usize_of_nat(v___x_145_);
v___x_149_ = ((size_t)0ULL);
v___x_150_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2(v_a_139_, v___x_148_, v___x_149_, v_tail_141_);
lean_dec_ref(v_a_139_);
return v___x_150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2___boxed(lean_object* v_l_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(v_l_151_, v_a_152_, v_a_153_, v_a_154_);
lean_dec(v_a_152_);
lean_dec(v_l_151_);
return v_res_155_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_159_ = ((lean_object*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__2));
v___x_160_ = lean_unsigned_to_nat(2u);
v___x_161_ = lean_unsigned_to_nat(46u);
v___x_162_ = ((lean_object*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__1));
v___x_163_ = ((lean_object*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__0));
v___x_164_ = l_mkPanicMessageWithDecl(v___x_163_, v___x_162_, v___x_161_, v___x_160_, v___x_159_);
return v___x_164_;
}
}
lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(lean_object* v_eq_165_, lean_object* v_rhs_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_173_; lean_object* v_xs_174_; uint8_t v___x_175_; 
v___x_173_ = lean_st_ref_get(v_a_167_);
v_xs_174_ = lean_ctor_get(v___x_173_, 1);
lean_inc(v_xs_174_);
lean_dec(v___x_173_);
v___x_175_ = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(v_rhs_166_, v_xs_174_);
lean_dec(v_xs_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_dec(v_eq_165_);
v___x_176_ = lean_obj_once(&l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3, &l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3_once, _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3);
v___x_177_ = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1(v___x_176_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
return v___x_177_;
}
else
{
lean_object* v___x_178_; lean_object* v_mvarId_179_; lean_object* v___x_180_; uint8_t v___x_181_; lean_object* v___x_182_; 
v___x_178_ = lean_st_ref_get(v_a_167_);
v_mvarId_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_mvarId_179_);
lean_dec(v___x_178_);
v___x_180_ = lean_box(0);
v___x_181_ = 0;
v___x_182_ = l_Lean_Meta_substCore(v_mvarId_179_, v_eq_165_, v___x_175_, v___x_180_, v___x_175_, v___x_181_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_211_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_211_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_211_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_211_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v_fst_187_; lean_object* v_snd_188_; lean_object* v___x_189_; lean_object* v_xs_190_; lean_object* v_eqs_191_; lean_object* v_eqsNew_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_209_; 
v_fst_187_ = lean_ctor_get(v_a_183_, 0);
lean_inc(v_fst_187_);
v_snd_188_ = lean_ctor_get(v_a_183_, 1);
lean_inc(v_snd_188_);
lean_dec(v_a_183_);
v___x_189_ = lean_st_ref_take(v_a_167_);
v_xs_190_ = lean_ctor_get(v___x_189_, 1);
v_eqs_191_ = lean_ctor_get(v___x_189_, 2);
v_eqsNew_192_ = lean_ctor_get(v___x_189_, 3);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; 
v_unused_210_ = lean_ctor_get(v___x_189_, 0);
lean_dec(v_unused_210_);
v___x_194_ = v___x_189_;
v_isShared_195_ = v_isSharedCheck_209_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_eqsNew_192_);
lean_inc(v_eqs_191_);
lean_inc(v_xs_190_);
lean_dec(v___x_189_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_209_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_196_ = lean_box(0);
v___x_197_ = ((lean_object*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0));
lean_inc(v_xs_190_);
v___x_198_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(v_xs_190_, v_rhs_166_, v_xs_190_, v___x_197_);
lean_dec(v_xs_190_);
lean_inc_n(v_fst_187_, 2);
v___x_199_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(v_fst_187_, v___x_198_);
v___x_200_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(v_fst_187_, v_eqs_191_);
v___x_201_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(v_fst_187_, v_eqsNew_192_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 3, v___x_201_);
lean_ctor_set(v___x_194_, 2, v___x_200_);
lean_ctor_set(v___x_194_, 1, v___x_199_);
lean_ctor_set(v___x_194_, 0, v_snd_188_);
v___x_203_ = v___x_194_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_snd_188_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_208_, 3, v___x_201_);
v___x_203_ = v_reuseFailAlloc_208_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_204_ = lean_st_ref_put(v_a_167_, v___x_203_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_196_);
v___x_206_ = v___x_185_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_196_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
else
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
v_a_212_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_182_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_182_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_0interp(lean_interpreter_value* stack)
{
lean_object* v_eq_165_ = stack[0].m_obj;
lean_object* v_rhs_166_ = stack[1].m_obj;
lean_object* v_a_167_ = stack[2].m_obj;
lean_object* v_a_168_ = stack[3].m_obj;
lean_object* v_a_169_ = stack[4].m_obj;
lean_object* v_a_170_ = stack[5].m_obj;
lean_object* v_a_171_ = stack[6].m_obj;
lean_object* v_res_220_;
v_res_220_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(v_eq_165_, v_rhs_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
stack->m_obj
 = v_res_220_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___boxed(lean_object* v_eq_221_, lean_object* v_rhs_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(v_eq_221_, v_rhs_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec(v_rhs_222_);
return v_res_229_;
}
}
lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(lean_object* v_a_230_){
_start:
{
lean_object* v___x_232_; lean_object* v_eqs_233_; uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_232_ = lean_st_ref_get(v_a_230_);
v_eqs_233_ = lean_ctor_get(v___x_232_, 2);
lean_inc(v_eqs_233_);
lean_dec(v___x_232_);
v___x_234_ = l_List_isEmpty___redArg(v_eqs_233_);
lean_dec(v_eqs_233_);
v___x_235_ = lean_box(v___x_234_);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_230_ = stack[0].m_obj;
lean_object* v_res_237_;
v_res_237_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(v_a_230_);
stack->m_obj
 = v_res_237_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg___boxed(lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(v_a_238_);
lean_dec(v_a_238_);
return v_res_240_;
}
}
lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone(lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(v_a_241_);
return v___x_247_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_241_ = stack[0].m_obj;
lean_object* v_a_242_ = stack[1].m_obj;
lean_object* v_a_243_ = stack[2].m_obj;
lean_object* v_a_244_ = stack[3].m_obj;
lean_object* v_a_245_ = stack[4].m_obj;
lean_object* v_res_248_;
v_res_248_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone(v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
stack->m_obj
 = v_res_248_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___boxed(lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone(v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
return v_res_255_;
}
}
lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(lean_object* v_mvarId_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = ((lean_object*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___closed__0));
v___x_267_ = l_Lean_MVarId_contradictionCore(v_mvarId_260_, v___x_266_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
return v___x_267_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_260_ = stack[0].m_obj;
lean_object* v_a_261_ = stack[1].m_obj;
lean_object* v_a_262_ = stack[2].m_obj;
lean_object* v_a_263_ = stack[3].m_obj;
lean_object* v_a_264_ = stack[4].m_obj;
lean_object* v_res_268_;
v_res_268_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(v_mvarId_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___boxed(lean_object* v_mvarId_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(v_mvarId_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
return v_res_275_;
}
}
lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(lean_object* v_x_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_Meta_saveState___redArg(v___y_278_, v___y_280_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___y_285_; lean_object* v___y_286_; uint8_t v___y_287_; lean_object* v___y_306_; lean_object* v_a_307_; lean_object* v___x_310_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_283_);
lean_dec_ref_known(v___x_282_, 1);
lean_inc(v___y_280_);
lean_inc_ref(v___y_279_);
lean_inc(v___y_278_);
lean_inc_ref(v___y_277_);
v___x_310_ = lean_apply_5(v_x_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, lean_box(0));
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; uint8_t v___x_312_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
v___x_312_ = lean_unbox(v_a_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; 
lean_dec_ref_known(v___x_310_, 1);
lean_inc(v_a_283_);
v___x_313_ = l_Lean_Meta_SavedState_restore___redArg(v_a_283_, v___y_278_, v___y_280_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec(v_a_283_);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v___x_313_, 0);
lean_dec(v_unused_321_);
v___x_315_ = v___x_313_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_dec(v___x_313_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v_a_311_);
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_311_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_dec(v_a_311_);
v_a_322_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_313_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_313_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
lean_inc(v_a_322_);
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
v___y_306_ = v___x_327_;
v_a_307_ = v_a_322_;
goto v___jp_305_;
}
}
}
}
else
{
lean_dec(v_a_311_);
lean_dec(v_a_283_);
return v___x_310_;
}
}
else
{
lean_object* v_a_330_; 
v_a_330_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_330_);
v___y_306_ = v___x_310_;
v_a_307_ = v_a_330_;
goto v___jp_305_;
}
v___jp_284_:
{
if (v___y_287_ == 0)
{
lean_object* v___x_288_; 
lean_dec_ref(v___y_286_);
v___x_288_ = l_Lean_Meta_SavedState_restore___redArg(v_a_283_, v___y_278_, v___y_280_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v___x_288_, 0);
lean_dec(v_unused_296_);
v___x_290_ = v___x_288_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_dec(v___x_288_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set_tag(v___x_290_, 1);
lean_ctor_set(v___x_290_, 0, v___y_285_);
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___y_285_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_dec_ref(v___y_285_);
v_a_297_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_288_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_288_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
else
{
lean_dec_ref(v___y_285_);
lean_dec(v_a_283_);
return v___y_286_;
}
}
v___jp_305_:
{
uint8_t v___x_308_; 
v___x_308_ = l_Lean_Exception_isInterrupt(v_a_307_);
if (v___x_308_ == 0)
{
uint8_t v___x_309_; 
lean_inc_ref(v_a_307_);
v___x_309_ = l_Lean_Exception_isRuntime(v_a_307_);
v___y_285_ = v_a_307_;
v___y_286_ = v___y_306_;
v___y_287_ = v___x_309_;
goto v___jp_284_;
}
else
{
v___y_285_ = v_a_307_;
v___y_286_ = v___y_306_;
v___y_287_ = v___x_308_;
goto v___jp_284_;
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec_ref(v_x_276_);
v_a_331_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_282_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_282_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_276_ = stack[0].m_obj;
lean_object* v___y_277_ = stack[1].m_obj;
lean_object* v___y_278_ = stack[2].m_obj;
lean_object* v___y_279_ = stack[3].m_obj;
lean_object* v___y_280_ = stack[4].m_obj;
lean_object* v_res_339_;
v_res_339_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(v_x_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0___boxed(lean_object* v_x_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(v_x_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_346_;
}
}
lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0(lean_object* v_mvarId_347_, lean_object* v_forbidden_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_Meta_substVars(v_mvarId_347_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc_n(v_a_355_, 2);
lean_dec_ref_known(v___x_354_, 1);
v___x_356_ = lean_box(0);
v___x_357_ = lean_unsigned_to_nat(5u);
v___x_358_ = l_Lean_Meta_injections(v_a_355_, v___x_356_, v___x_357_, v_forbidden_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_373_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_373_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_373_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_373_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
if (lean_obj_tag(v_a_359_) == 0)
{
uint8_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
lean_dec(v_a_355_);
v___x_363_ = 1;
v___x_364_ = lean_box(v___x_363_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_364_);
v___x_366_ = v___x_361_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
else
{
lean_object* v_mvarId_368_; lean_object* v_forbidden_369_; uint8_t v___x_370_; 
lean_del_object(v___x_361_);
v_mvarId_368_ = lean_ctor_get(v_a_359_, 0);
lean_inc(v_mvarId_368_);
v_forbidden_369_ = lean_ctor_get(v_a_359_, 2);
lean_inc(v_forbidden_369_);
lean_dec_ref_known(v_a_359_, 3);
v___x_370_ = l_Lean_instBEqMVarId_beq(v_mvarId_368_, v_a_355_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_dec(v_a_355_);
v___x_371_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(v_mvarId_368_, v_forbidden_369_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
return v___x_371_;
}
else
{
lean_object* v___x_372_; 
lean_dec(v_forbidden_369_);
lean_dec(v_mvarId_368_);
v___x_372_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(v_a_355_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
return v___x_372_;
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec(v_a_355_);
v_a_374_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_358_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_358_);
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
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec(v_forbidden_348_);
v_a_382_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_354_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_354_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_347_ = stack[0].m_obj;
lean_object* v_forbidden_348_ = stack[1].m_obj;
lean_object* v___y_349_ = stack[2].m_obj;
lean_object* v___y_350_ = stack[3].m_obj;
lean_object* v___y_351_ = stack[4].m_obj;
lean_object* v___y_352_ = stack[5].m_obj;
lean_object* v_res_390_;
v_res_390_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0(v_mvarId_347_, v_forbidden_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0___boxed(lean_object* v_mvarId_391_, lean_object* v_forbidden_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0(v_mvarId_391_, v_forbidden_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_398_;
}
}
lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(lean_object* v_mvarId_399_, lean_object* v_forbidden_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___f_406_; lean_object* v___x_407_; 
v___f_406_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0___boxed), 7, 2);
lean_closure_set(v___f_406_, 0, v_mvarId_399_);
lean_closure_set(v___f_406_, 1, v_forbidden_400_);
v___x_407_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(v___f_406_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
return v___x_407_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_399_ = stack[0].m_obj;
lean_object* v_forbidden_400_ = stack[1].m_obj;
lean_object* v_a_401_ = stack[2].m_obj;
lean_object* v_a_402_ = stack[3].m_obj;
lean_object* v_a_403_ = stack[4].m_obj;
lean_object* v_a_404_ = stack[5].m_obj;
lean_object* v_res_408_;
v_res_408_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(v_mvarId_399_, v_forbidden_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
stack->m_obj
 = v_res_408_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___boxed(lean_object* v_mvarId_409_, lean_object* v_forbidden_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(v_mvarId_409_, v_forbidden_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
return v_res_416_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0(lean_object* v_x_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v___x_424_; 
lean_inc(v___y_418_);
v___x_424_ = lean_apply_6(v_x_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, lean_box(0));
return v___x_424_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_417_ = stack[0].m_obj;
lean_object* v___y_418_ = stack[1].m_obj;
lean_object* v___y_419_ = stack[2].m_obj;
lean_object* v___y_420_ = stack[3].m_obj;
lean_object* v___y_421_ = stack[4].m_obj;
lean_object* v___y_422_ = stack[5].m_obj;
lean_object* v_res_425_;
v_res_425_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0(v_x_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
stack->m_obj
 = v_res_425_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0___boxed(lean_object* v_x_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0(v_x_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_427_);
return v_res_433_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(lean_object* v_mvarId_434_, lean_object* v_x_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v___f_442_; lean_object* v___x_443_; 
lean_inc(v___y_436_);
v___f_442_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_442_, 0, v_x_435_);
lean_closure_set(v___f_442_, 1, v___y_436_);
v___x_443_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_434_, v___f_442_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_443_) == 0)
{
return v___x_443_;
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_434_ = stack[0].m_obj;
lean_object* v_x_435_ = stack[1].m_obj;
lean_object* v___y_436_ = stack[2].m_obj;
lean_object* v___y_437_ = stack[3].m_obj;
lean_object* v___y_438_ = stack[4].m_obj;
lean_object* v___y_439_ = stack[5].m_obj;
lean_object* v___y_440_ = stack[6].m_obj;
lean_object* v_res_452_;
v_res_452_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(v_mvarId_434_, v_x_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
stack->m_obj
 = v_res_452_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___boxed(lean_object* v_mvarId_453_, lean_object* v_x_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(v_mvarId_453_, v_x_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
return v_res_461_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0(lean_object* v_00_u03b1_462_, lean_object* v_mvarId_463_, lean_object* v_x_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(v_mvarId_463_, v_x_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
return v___x_471_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_463_ = stack[1].m_obj;
lean_object* v_x_464_ = stack[2].m_obj;
lean_object* v___y_465_ = stack[3].m_obj;
lean_object* v___y_466_ = stack[4].m_obj;
lean_object* v___y_467_ = stack[5].m_obj;
lean_object* v___y_468_ = stack[6].m_obj;
lean_object* v___y_469_ = stack[7].m_obj;
lean_object* v_res_472_;
v_res_472_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0(lean_box(0), v_mvarId_463_, v_x_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
stack->m_obj
 = v_res_472_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___boxed(lean_object* v_00_u03b1_473_, lean_object* v_mvarId_474_, lean_object* v_x_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0(v_00_u03b1_473_, v_mvarId_474_, v_x_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
return v_res_482_;
}
}
lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0(lean_object* v_____r_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = 1;
v___x_491_ = lean_box(v___x_490_);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____r_483_ = stack[0].m_obj;
lean_object* v___y_484_ = stack[1].m_obj;
lean_object* v___y_485_ = stack[2].m_obj;
lean_object* v___y_486_ = stack[3].m_obj;
lean_object* v___y_487_ = stack[4].m_obj;
lean_object* v___y_488_ = stack[5].m_obj;
lean_object* v_res_493_;
v_res_493_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0(v_____r_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
stack->m_obj
 = v_res_493_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0___boxed(lean_object* v_____r_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0(v_____r_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
return v_res_501_;
}
}
lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1(lean_object* v_eqs_502_, lean_object* v___f_503_, lean_object* v_mvarId_504_, lean_object* v___x_505_, lean_object* v_xs_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
if (lean_obj_tag(v_eqs_502_) == 1)
{
lean_object* v_head_513_; lean_object* v_tail_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_749_; 
v_head_513_ = lean_ctor_get(v_eqs_502_, 0);
v_tail_514_ = lean_ctor_get(v_eqs_502_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v_eqs_502_);
if (v_isSharedCheck_749_ == 0)
{
v___x_516_ = v_eqs_502_;
v_isShared_517_ = v_isSharedCheck_749_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_tail_514_);
lean_inc(v_head_513_);
lean_dec(v_eqs_502_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_749_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; uint8_t v___y_525_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___x_585_; lean_object* v_mvarId_586_; lean_object* v_xs_587_; lean_object* v_eqsNew_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_747_; 
v___x_585_ = lean_st_ref_take(v___y_507_);
v_mvarId_586_ = lean_ctor_get(v___x_585_, 0);
v_xs_587_ = lean_ctor_get(v___x_585_, 1);
v_eqsNew_588_ = lean_ctor_get(v___x_585_, 3);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v___x_585_, 2);
lean_dec(v_unused_748_);
v___x_590_ = v___x_585_;
v_isShared_591_ = v_isSharedCheck_747_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_eqsNew_588_);
lean_inc(v_xs_587_);
lean_inc(v_mvarId_586_);
lean_dec(v___x_585_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_747_;
goto v_resetjp_589_;
}
v___jp_518_:
{
if (v___y_525_ == 0)
{
lean_object* v___x_526_; lean_object* v_mvarId_527_; lean_object* v_xs_528_; lean_object* v_eqs_529_; lean_object* v_eqsNew_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_543_; 
lean_dec_ref(v___y_519_);
v___x_526_ = lean_st_ref_take(v___y_520_);
v_mvarId_527_ = lean_ctor_get(v___x_526_, 0);
v_xs_528_ = lean_ctor_get(v___x_526_, 1);
v_eqs_529_ = lean_ctor_get(v___x_526_, 2);
v_eqsNew_530_ = lean_ctor_get(v___x_526_, 3);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_543_ == 0)
{
v___x_532_ = v___x_526_;
v_isShared_533_ = v_isSharedCheck_543_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_eqsNew_530_);
lean_inc(v_eqs_529_);
lean_inc(v_xs_528_);
lean_inc(v_mvarId_527_);
lean_dec(v___x_526_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_543_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = lean_box(0);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v_eqsNew_530_);
v___x_536_ = v___x_516_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_head_513_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_eqsNew_530_);
v___x_536_ = v_reuseFailAlloc_542_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_538_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 3, v___x_536_);
v___x_538_ = v___x_532_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_mvarId_527_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_xs_528_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_eqs_529_);
lean_ctor_set(v_reuseFailAlloc_541_, 3, v___x_536_);
v___x_538_ = v_reuseFailAlloc_541_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_st_ref_put(v___y_520_, v___x_538_);
lean_inc(v___y_523_);
lean_inc_ref(v___y_524_);
lean_inc(v___y_521_);
lean_inc_ref(v___y_522_);
lean_inc(v___y_520_);
v___x_540_ = lean_apply_7(v___f_503_, v___x_534_, v___y_520_, v___y_522_, v___y_521_, v___y_524_, v___y_523_, lean_box(0));
return v___x_540_;
}
}
}
}
else
{
lean_object* v___x_544_; 
lean_del_object(v___x_516_);
lean_dec(v_head_513_);
lean_dec_ref(v___f_503_);
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v___y_519_);
return v___x_544_;
}
}
v___jp_545_:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_box(0);
lean_inc(v_head_513_);
v___x_552_ = l_Lean_Meta_injection(v_mvarId_504_, v_head_513_, v___x_551_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_581_; 
lean_del_object(v___x_516_);
lean_dec(v_head_513_);
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_581_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_581_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_581_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
if (lean_obj_tag(v_a_553_) == 0)
{
uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
lean_dec_ref(v___f_503_);
v___x_557_ = 0;
v___x_558_ = lean_box(v___x_557_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_558_);
v___x_560_ = v___x_555_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
else
{
lean_object* v_mvarId_562_; lean_object* v_newEqs_563_; lean_object* v___x_564_; lean_object* v_xs_565_; lean_object* v_eqs_566_; lean_object* v_eqsNew_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_579_; 
lean_del_object(v___x_555_);
v_mvarId_562_ = lean_ctor_get(v_a_553_, 0);
lean_inc(v_mvarId_562_);
v_newEqs_563_ = lean_ctor_get(v_a_553_, 1);
lean_inc_ref(v_newEqs_563_);
lean_dec_ref_known(v_a_553_, 3);
v___x_564_ = lean_st_ref_take(v___y_546_);
v_xs_565_ = lean_ctor_get(v___x_564_, 1);
v_eqs_566_ = lean_ctor_get(v___x_564_, 2);
v_eqsNew_567_ = lean_ctor_get(v___x_564_, 3);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v___x_564_, 0);
lean_dec(v_unused_580_);
v___x_569_ = v___x_564_;
v_isShared_570_ = v_isSharedCheck_579_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_eqsNew_567_);
lean_inc(v_eqs_566_);
lean_inc(v_xs_565_);
lean_dec(v___x_564_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_579_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_571_ = lean_box(0);
v___x_572_ = lean_array_to_list(v_newEqs_563_);
v___x_573_ = l_List_appendTR___redArg(v___x_572_, v_eqs_566_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 2, v___x_573_);
lean_ctor_set(v___x_569_, 0, v_mvarId_562_);
v___x_575_ = v___x_569_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_mvarId_562_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_xs_565_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_578_, 3, v_eqsNew_567_);
v___x_575_ = v_reuseFailAlloc_578_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_st_ref_put(v___y_546_, v___x_575_);
lean_inc(v___y_550_);
lean_inc_ref(v___y_549_);
lean_inc(v___y_548_);
lean_inc_ref(v___y_547_);
lean_inc(v___y_546_);
v___x_577_ = lean_apply_7(v___f_503_, v___x_571_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, lean_box(0));
return v___x_577_;
}
}
}
}
}
else
{
lean_object* v_a_582_; uint8_t v___x_583_; 
v_a_582_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_552_, 1);
v___x_583_ = l_Lean_Exception_isInterrupt(v_a_582_);
if (v___x_583_ == 0)
{
uint8_t v___x_584_; 
lean_inc(v_a_582_);
v___x_584_ = l_Lean_Exception_isRuntime(v_a_582_);
v___y_519_ = v_a_582_;
v___y_520_ = v___y_546_;
v___y_521_ = v___y_548_;
v___y_522_ = v___y_547_;
v___y_523_ = v___y_550_;
v___y_524_ = v___y_549_;
v___y_525_ = v___x_584_;
goto v___jp_518_;
}
else
{
v___y_519_ = v_a_582_;
v___y_520_ = v___y_546_;
v___y_521_ = v___y_548_;
v___y_522_ = v___y_547_;
v___y_523_ = v___y_550_;
v___y_524_ = v___y_549_;
v___y_525_ = v___x_583_;
goto v___jp_518_;
}
}
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 2, v_tail_514_);
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_mvarId_586_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_xs_587_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_tail_514_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v_eqsNew_588_);
v___x_593_ = v_reuseFailAlloc_746_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = lean_st_ref_put(v___y_507_, v___x_593_);
lean_inc(v_head_513_);
v___x_595_ = l_Lean_mkFVar(v_head_513_);
lean_inc(v___y_511_);
lean_inc_ref(v___y_510_);
lean_inc(v___y_509_);
lean_inc_ref(v___y_508_);
v___x_596_ = lean_infer_type(v___x_595_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___x_668_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc_n(v_a_597_, 2);
lean_dec_ref_known(v___x_596_, 1);
v___x_668_ = l_Lean_Meta_matchEq_x3f(v_a_597_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
if (lean_obj_tag(v_a_669_) == 1)
{
lean_object* v_val_670_; lean_object* v_snd_671_; lean_object* v_fst_672_; lean_object* v_snd_673_; lean_object* v___x_674_; 
v_val_670_ = lean_ctor_get(v_a_669_, 0);
lean_inc(v_val_670_);
lean_dec_ref_known(v_a_669_, 1);
v_snd_671_ = lean_ctor_get(v_val_670_, 1);
lean_inc(v_snd_671_);
lean_dec(v_val_670_);
v_fst_672_ = lean_ctor_get(v_snd_671_, 0);
lean_inc(v_fst_672_);
v_snd_673_ = lean_ctor_get(v_snd_671_, 1);
lean_inc_n(v_snd_673_, 2);
lean_dec(v_snd_671_);
v___x_674_ = l_Lean_Meta_isExprDefEq(v_fst_672_, v_snd_673_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; uint8_t v___x_676_; uint8_t v___x_677_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_674_, 1);
v___x_676_ = 1;
v___x_677_ = lean_unbox(v_a_675_);
lean_dec(v_a_675_);
if (v___x_677_ == 0)
{
uint8_t v___x_678_; 
v___x_678_ = l_Lean_Expr_isFVar(v_snd_673_);
if (v___x_678_ == 0)
{
lean_dec(v_snd_673_);
v___y_599_ = v___y_507_;
v___y_600_ = v___y_508_;
v___y_601_ = v___y_509_;
v___y_602_ = v___y_510_;
v___y_603_ = v___y_511_;
goto v___jp_598_;
}
else
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = l_Lean_Expr_fvarId_x21(v_snd_673_);
lean_dec(v_snd_673_);
v___x_680_ = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(v___x_679_, v_xs_506_);
if (v___x_680_ == 0)
{
lean_dec(v___x_679_);
v___y_599_ = v___y_507_;
v___y_600_ = v___y_508_;
v___y_601_ = v___y_509_;
v___y_602_ = v___y_510_;
v___y_603_ = v___y_511_;
goto v___jp_598_;
}
else
{
lean_object* v___x_681_; 
lean_dec(v_a_597_);
lean_del_object(v___x_516_);
lean_dec(v___x_505_);
lean_dec(v_mvarId_504_);
lean_dec_ref(v___f_503_);
v___x_681_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(v_head_513_, v___x_679_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___x_679_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_689_; 
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v___x_681_, 0);
lean_dec(v_unused_690_);
v___x_683_ = v___x_681_;
v_isShared_684_ = v_isSharedCheck_689_;
goto v_resetjp_682_;
}
else
{
lean_dec(v___x_681_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_689_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_685_ = lean_box(v___x_676_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_685_);
v___x_687_ = v___x_683_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
v_a_691_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_681_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_681_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
}
else
{
lean_object* v___x_699_; 
lean_dec(v_snd_673_);
lean_dec(v_a_597_);
lean_del_object(v___x_516_);
lean_dec(v___x_505_);
lean_dec_ref(v___f_503_);
v___x_699_ = l_Lean_MVarId_clear(v_mvarId_504_, v_head_513_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_721_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_721_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_721_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_721_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v_xs_705_; lean_object* v_eqs_706_; lean_object* v_eqsNew_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_719_; 
v___x_704_ = lean_st_ref_take(v___y_507_);
v_xs_705_ = lean_ctor_get(v___x_704_, 1);
v_eqs_706_ = lean_ctor_get(v___x_704_, 2);
v_eqsNew_707_ = lean_ctor_get(v___x_704_, 3);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; 
v_unused_720_ = lean_ctor_get(v___x_704_, 0);
lean_dec(v_unused_720_);
v___x_709_ = v___x_704_;
v_isShared_710_ = v_isSharedCheck_719_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_eqsNew_707_);
lean_inc(v_eqs_706_);
lean_inc(v_xs_705_);
lean_dec(v___x_704_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_719_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v_a_700_);
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_700_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_xs_705_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_eqs_706_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v_eqsNew_707_);
v___x_712_ = v_reuseFailAlloc_718_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = lean_st_ref_put(v___y_507_, v___x_712_);
v___x_714_ = lean_box(v___x_676_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_714_);
v___x_716_ = v___x_702_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
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
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
v_a_722_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_699_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_699_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
else
{
lean_dec(v_snd_673_);
lean_dec(v_a_597_);
lean_del_object(v___x_516_);
lean_dec(v_head_513_);
lean_dec(v___x_505_);
lean_dec(v_mvarId_504_);
lean_dec_ref(v___f_503_);
return v___x_674_;
}
}
else
{
lean_dec(v_a_669_);
v___y_599_ = v___y_507_;
v___y_600_ = v___y_508_;
v___y_601_ = v___y_509_;
v___y_602_ = v___y_510_;
v___y_603_ = v___y_511_;
goto v___jp_598_;
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec(v_a_597_);
lean_del_object(v___x_516_);
lean_dec(v_head_513_);
lean_dec(v___x_505_);
lean_dec(v_mvarId_504_);
lean_dec_ref(v___f_503_);
v_a_730_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_668_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_668_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
v___jp_598_:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Meta_matchHEq_x3f(v_a_597_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
if (lean_obj_tag(v_a_605_) == 1)
{
uint8_t v___x_606_; lean_object* v___x_607_; 
lean_dec_ref_known(v_a_605_, 1);
v___x_606_ = 1;
lean_inc(v_head_513_);
lean_inc(v_mvarId_504_);
v___x_607_ = l_Lean_Meta_heqToEq(v_mvarId_504_, v_head_513_, v___x_606_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_651_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_651_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_651_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_651_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v_fst_612_; lean_object* v_snd_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_650_; 
v_fst_612_ = lean_ctor_get(v_a_608_, 0);
v_snd_613_ = lean_ctor_get(v_a_608_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v_a_608_);
if (v_isSharedCheck_650_ == 0)
{
v___x_615_ = v_a_608_;
v_isShared_616_ = v_isSharedCheck_650_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_snd_613_);
lean_inc(v_fst_612_);
lean_dec(v_a_608_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_650_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
uint8_t v___x_617_; 
v___x_617_ = l_Lean_instBEqMVarId_beq(v_snd_613_, v_mvarId_504_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v_xs_619_; lean_object* v_eqs_620_; lean_object* v_eqsNew_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_636_; 
lean_del_object(v___x_516_);
lean_dec(v_head_513_);
lean_dec(v___x_505_);
lean_dec(v_mvarId_504_);
lean_dec_ref(v___f_503_);
v___x_618_ = lean_st_ref_take(v___y_599_);
v_xs_619_ = lean_ctor_get(v___x_618_, 1);
v_eqs_620_ = lean_ctor_get(v___x_618_, 2);
v_eqsNew_621_ = lean_ctor_get(v___x_618_, 3);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; 
v_unused_637_ = lean_ctor_get(v___x_618_, 0);
lean_dec(v_unused_637_);
v___x_623_ = v___x_618_;
v_isShared_624_ = v_isSharedCheck_636_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_eqsNew_621_);
lean_inc(v_eqs_620_);
lean_inc(v_xs_619_);
lean_dec(v___x_618_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_636_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set_tag(v___x_615_, 1);
lean_ctor_set(v___x_615_, 1, v_eqs_620_);
v___x_626_ = v___x_615_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_fst_612_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_eqs_620_);
v___x_626_ = v_reuseFailAlloc_635_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_628_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 2, v___x_626_);
lean_ctor_set(v___x_623_, 0, v_snd_613_);
v___x_628_ = v___x_623_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_snd_613_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_xs_619_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v_eqsNew_621_);
v___x_628_ = v_reuseFailAlloc_634_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_629_ = lean_st_ref_put(v___y_599_, v___x_628_);
v___x_630_ = lean_box(v___x_606_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_630_);
v___x_632_ = v___x_610_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
else
{
uint8_t v___x_638_; lean_object* v___x_639_; 
lean_del_object(v___x_615_);
lean_dec(v_snd_613_);
lean_dec(v_fst_612_);
lean_del_object(v___x_610_);
v___x_638_ = 0;
lean_inc(v_mvarId_504_);
v___x_639_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(v_mvarId_504_, v___x_505_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_649_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_649_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_649_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_649_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
uint8_t v___x_644_; 
v___x_644_ = lean_unbox(v_a_640_);
lean_dec(v_a_640_);
if (v___x_644_ == 0)
{
lean_del_object(v___x_642_);
v___y_546_ = v___y_599_;
v___y_547_ = v___y_600_;
v___y_548_ = v___y_601_;
v___y_549_ = v___y_602_;
v___y_550_ = v___y_603_;
goto v___jp_545_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_647_; 
lean_del_object(v___x_516_);
lean_dec(v_head_513_);
lean_dec(v_mvarId_504_);
lean_dec_ref(v___f_503_);
v___x_645_ = lean_box(v___x_638_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_645_);
v___x_647_ = v___x_642_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_del_object(v___x_516_);
lean_dec(v_head_513_);
lean_dec(v_mvarId_504_);
lean_dec_ref(v___f_503_);
return v___x_639_;
}
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_del_object(v___x_516_);
lean_dec(v_head_513_);
lean_dec(v___x_505_);
lean_dec(v_mvarId_504_);
lean_dec_ref(v___f_503_);
v_a_652_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_607_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_607_);
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
else
{
lean_dec(v_a_605_);
lean_dec(v___x_505_);
v___y_546_ = v___y_599_;
v___y_547_ = v___y_600_;
v___y_548_ = v___y_601_;
v___y_549_ = v___y_602_;
v___y_550_ = v___y_603_;
goto v___jp_545_;
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_del_object(v___x_516_);
lean_dec(v_head_513_);
lean_dec(v___x_505_);
lean_dec(v_mvarId_504_);
lean_dec_ref(v___f_503_);
v_a_660_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_604_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_604_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_del_object(v___x_516_);
lean_dec(v_head_513_);
lean_dec(v___x_505_);
lean_dec(v_mvarId_504_);
lean_dec_ref(v___f_503_);
v_a_738_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_596_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_596_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec(v___x_505_);
lean_dec(v_mvarId_504_);
lean_dec(v_eqs_502_);
v___x_750_ = lean_box(0);
lean_inc(v___y_511_);
lean_inc_ref(v___y_510_);
lean_inc(v___y_509_);
lean_inc_ref(v___y_508_);
lean_inc(v___y_507_);
v___x_751_ = lean_apply_7(v___f_503_, v___x_750_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, lean_box(0));
return v___x_751_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_eqs_502_ = stack[0].m_obj;
lean_object* v___f_503_ = stack[1].m_obj;
lean_object* v_mvarId_504_ = stack[2].m_obj;
lean_object* v___x_505_ = stack[3].m_obj;
lean_object* v_xs_506_ = stack[4].m_obj;
lean_object* v___y_507_ = stack[5].m_obj;
lean_object* v___y_508_ = stack[6].m_obj;
lean_object* v___y_509_ = stack[7].m_obj;
lean_object* v___y_510_ = stack[8].m_obj;
lean_object* v___y_511_ = stack[9].m_obj;
lean_object* v_res_752_;
v_res_752_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1(v_eqs_502_, v___f_503_, v_mvarId_504_, v___x_505_, v_xs_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
stack->m_obj
 = v_res_752_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1___boxed(lean_object* v_eqs_753_, lean_object* v___f_754_, lean_object* v_mvarId_755_, lean_object* v___x_756_, lean_object* v_xs_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1(v_eqs_753_, v___f_754_, v_mvarId_755_, v___x_756_, v_xs_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec(v_xs_757_);
return v_res_764_;
}
}
lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v_mvarId_775_; lean_object* v_xs_776_; lean_object* v_eqs_777_; lean_object* v___y_778_; lean_object* v___x_779_; 
v___f_772_ = ((lean_object*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___closed__0));
v___x_773_ = lean_box(1);
v___x_774_ = lean_st_ref_get(v_a_766_);
v_mvarId_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc_n(v_mvarId_775_, 2);
v_xs_776_ = lean_ctor_get(v___x_774_, 1);
lean_inc(v_xs_776_);
v_eqs_777_ = lean_ctor_get(v___x_774_, 2);
lean_inc(v_eqs_777_);
lean_dec(v___x_774_);
v___y_778_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1___boxed), 11, 5);
lean_closure_set(v___y_778_, 0, v_eqs_777_);
lean_closure_set(v___y_778_, 1, v___f_772_);
lean_closure_set(v___y_778_, 2, v_mvarId_775_);
lean_closure_set(v___y_778_, 3, v___x_773_);
lean_closure_set(v___y_778_, 4, v_xs_776_);
v___x_779_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(v_mvarId_775_, v___y_778_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
return v___x_779_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_766_ = stack[0].m_obj;
lean_object* v_a_767_ = stack[1].m_obj;
lean_object* v_a_768_ = stack[2].m_obj;
lean_object* v_a_769_ = stack[3].m_obj;
lean_object* v_a_770_ = stack[4].m_obj;
lean_object* v_res_780_;
v_res_780_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
stack->m_obj
 = v_res_780_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___boxed(lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
return v_res_787_;
}
}
lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(v_a_788_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; uint8_t v___x_796_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v___x_796_ = lean_unbox(v_a_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; 
lean_dec_ref_known(v___x_794_, 1);
v___x_797_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; uint8_t v___x_799_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
v___x_799_ = lean_unbox(v_a_798_);
if (v___x_799_ == 0)
{
return v___x_797_;
}
else
{
lean_dec_ref_known(v___x_797_, 1);
goto _start;
}
}
else
{
return v___x_797_;
}
}
else
{
return v___x_794_;
}
}
else
{
return v___x_794_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_788_ = stack[0].m_obj;
lean_object* v_a_789_ = stack[1].m_obj;
lean_object* v_a_790_ = stack[2].m_obj;
lean_object* v_a_791_ = stack[3].m_obj;
lean_object* v_a_792_ = stack[4].m_obj;
lean_object* v_res_801_;
v_res_801_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
stack->m_obj
 = v_res_801_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go___boxed(lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
return v_res_808_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0(lean_object* v_k_809_, lean_object* v_b_810_, lean_object* v_c_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; 
lean_inc(v___y_815_);
lean_inc_ref(v___y_814_);
lean_inc(v___y_813_);
lean_inc_ref(v___y_812_);
v___x_817_ = lean_apply_7(v_k_809_, v_b_810_, v_c_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, lean_box(0));
return v___x_817_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_809_ = stack[0].m_obj;
lean_object* v_b_810_ = stack[1].m_obj;
lean_object* v_c_811_ = stack[2].m_obj;
lean_object* v___y_812_ = stack[3].m_obj;
lean_object* v___y_813_ = stack[4].m_obj;
lean_object* v___y_814_ = stack[5].m_obj;
lean_object* v___y_815_ = stack[6].m_obj;
lean_object* v_res_818_;
v_res_818_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0(v_k_809_, v_b_810_, v_c_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
stack->m_obj
 = v_res_818_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0___boxed(lean_object* v_k_819_, lean_object* v_b_820_, lean_object* v_c_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0(v_k_819_, v_b_820_, v_c_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
return v_res_827_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(lean_object* v_type_828_, lean_object* v_k_829_, uint8_t v_cleanupAnnotations_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___f_836_; uint8_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___f_836_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_836_, 0, v_k_829_);
v___x_837_ = 0;
v___x_838_ = lean_box(0);
v___x_839_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_837_, v___x_838_, v_type_828_, v___f_836_, v_cleanupAnnotations_830_, v___x_837_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
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
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
v_a_848_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_839_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_839_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_828_ = stack[0].m_obj;
lean_object* v_k_829_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_830_ = stack[2].m_num;
lean_object* v___y_831_ = stack[3].m_obj;
lean_object* v___y_832_ = stack[4].m_obj;
lean_object* v___y_833_ = stack[5].m_obj;
lean_object* v___y_834_ = stack[6].m_obj;
lean_object* v_res_856_;
v_res_856_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(v_type_828_, v_k_829_, v_cleanupAnnotations_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
stack->m_obj
 = v_res_856_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___boxed(lean_object* v_type_857_, lean_object* v_k_858_, lean_object* v_cleanupAnnotations_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_865_; lean_object* v_res_866_; 
v_cleanupAnnotations_boxed_865_ = lean_unbox(v_cleanupAnnotations_859_);
v_res_866_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(v_type_857_, v_k_858_, v_cleanupAnnotations_boxed_865_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
return v_res_866_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0(lean_object* v_00_u03b1_867_, lean_object* v_type_868_, lean_object* v_k_869_, uint8_t v_cleanupAnnotations_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(v_type_868_, v_k_869_, v_cleanupAnnotations_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
return v___x_876_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_868_ = stack[1].m_obj;
lean_object* v_k_869_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_870_ = stack[3].m_num;
lean_object* v___y_871_ = stack[4].m_obj;
lean_object* v___y_872_ = stack[5].m_obj;
lean_object* v___y_873_ = stack[6].m_obj;
lean_object* v___y_874_ = stack[7].m_obj;
lean_object* v_res_877_;
v_res_877_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0(lean_box(0), v_type_868_, v_k_869_, v_cleanupAnnotations_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
stack->m_obj
 = v_res_877_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___boxed(lean_object* v_00_u03b1_878_, lean_object* v_type_879_, lean_object* v_k_880_, lean_object* v_cleanupAnnotations_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_887_; lean_object* v_res_888_; 
v_cleanupAnnotations_boxed_887_ = lean_unbox(v_cleanupAnnotations_881_);
v_res_888_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0(v_00_u03b1_878_, v_type_879_, v_k_880_, v_cleanupAnnotations_boxed_887_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
return v_res_888_;
}
}
uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0(lean_object* v_x_889_){
_start:
{
uint8_t v___x_890_; 
v___x_890_ = 0;
return v___x_890_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_889_ = stack[0].m_obj;
uint8_t v_res_891_;
v_res_891_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0(v_x_889_);
stack->m_num = v_res_891_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0___boxed(lean_object* v_x_892_){
_start:
{
uint8_t v_res_893_; lean_object* v_r_894_; 
v_res_893_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0(v_x_892_);
lean_dec(v_x_892_);
v_r_894_ = lean_box(v_res_893_);
return v_r_894_;
}
}
uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1(lean_object* v_fvarId_895_, lean_object* v_x_896_){
_start:
{
uint8_t v___x_897_; 
v___x_897_ = l_Lean_instBEqFVarId_beq(v_fvarId_895_, v_x_896_);
return v___x_897_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_895_ = stack[0].m_obj;
lean_object* v_x_896_ = stack[1].m_obj;
uint8_t v_res_898_;
v_res_898_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1(v_fvarId_895_, v_x_896_);
stack->m_num = v_res_898_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1___boxed(lean_object* v_fvarId_899_, lean_object* v_x_900_){
_start:
{
uint8_t v_res_901_; lean_object* v_r_902_; 
v_res_901_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1(v_fvarId_899_, v_x_900_);
lean_dec(v_x_900_);
lean_dec(v_fvarId_899_);
v_r_902_ = lean_box(v_res_901_);
return v_r_902_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = lean_box(0);
v___x_905_ = lean_unsigned_to_nat(16u);
v___x_906_ = lean_mk_array(v___x_905_, v___x_904_);
return v___x_906_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1);
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v___x_907_);
return v___x_909_;
}
}
lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(lean_object* v_e_910_, lean_object* v_fvarId_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___f_914_; lean_object* v___f_915_; lean_object* v___x_916_; uint8_t v_fst_918_; lean_object* v_mctx_919_; lean_object* v___y_937_; lean_object* v_mctx_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v___f_914_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__0));
v___f_915_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_915_, 0, v_fvarId_911_);
v___x_916_ = lean_st_ref_get(v___y_912_);
v_mctx_942_ = lean_ctor_get(v___x_916_, 0);
lean_inc_ref_n(v_mctx_942_, 2);
lean_dec(v___x_916_);
v___x_943_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v_mctx_942_);
v___x_945_ = l_Lean_Expr_hasFVar(v_e_910_);
if (v___x_945_ == 0)
{
uint8_t v___x_946_; 
v___x_946_ = l_Lean_Expr_hasMVar(v_e_910_);
if (v___x_946_ == 0)
{
lean_dec_ref_known(v___x_944_, 2);
lean_dec_ref(v___f_915_);
lean_dec_ref(v_e_910_);
v_fst_918_ = v___x_946_;
v_mctx_919_ = v_mctx_942_;
goto v___jp_917_;
}
else
{
lean_object* v___x_947_; 
lean_dec_ref(v_mctx_942_);
v___x_947_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_915_, v___f_914_, v_e_910_, v___x_944_);
v___y_937_ = v___x_947_;
goto v___jp_936_;
}
}
else
{
lean_object* v___x_948_; 
lean_dec_ref(v_mctx_942_);
v___x_948_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_915_, v___f_914_, v_e_910_, v___x_944_);
v___y_937_ = v___x_948_;
goto v___jp_936_;
}
v___jp_917_:
{
lean_object* v___x_920_; lean_object* v_cache_921_; lean_object* v_zetaDeltaFVarIds_922_; lean_object* v_postponed_923_; lean_object* v_diag_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_934_; 
v___x_920_ = lean_st_ref_take(v___y_912_);
v_cache_921_ = lean_ctor_get(v___x_920_, 1);
v_zetaDeltaFVarIds_922_ = lean_ctor_get(v___x_920_, 2);
v_postponed_923_ = lean_ctor_get(v___x_920_, 3);
v_diag_924_ = lean_ctor_get(v___x_920_, 4);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; 
v_unused_935_ = lean_ctor_get(v___x_920_, 0);
lean_dec(v_unused_935_);
v___x_926_ = v___x_920_;
v_isShared_927_ = v_isSharedCheck_934_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_diag_924_);
lean_inc(v_postponed_923_);
lean_inc(v_zetaDeltaFVarIds_922_);
lean_inc(v_cache_921_);
lean_dec(v___x_920_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_934_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v_mctx_919_);
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_mctx_919_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_cache_921_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_zetaDeltaFVarIds_922_);
lean_ctor_set(v_reuseFailAlloc_933_, 3, v_postponed_923_);
lean_ctor_set(v_reuseFailAlloc_933_, 4, v_diag_924_);
v___x_929_ = v_reuseFailAlloc_933_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = lean_st_ref_put(v___y_912_, v___x_929_);
v___x_931_ = lean_box(v_fst_918_);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
}
}
}
v___jp_936_:
{
lean_object* v_snd_938_; lean_object* v_fst_939_; lean_object* v_mctx_940_; uint8_t v___x_941_; 
v_snd_938_ = lean_ctor_get(v___y_937_, 1);
lean_inc(v_snd_938_);
v_fst_939_ = lean_ctor_get(v___y_937_, 0);
lean_inc(v_fst_939_);
lean_dec_ref(v___y_937_);
v_mctx_940_ = lean_ctor_get(v_snd_938_, 1);
lean_inc_ref(v_mctx_940_);
lean_dec(v_snd_938_);
v___x_941_ = lean_unbox(v_fst_939_);
lean_dec(v_fst_939_);
v_fst_918_ = v___x_941_;
v_mctx_919_ = v_mctx_940_;
goto v___jp_917_;
}
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_910_ = stack[0].m_obj;
lean_object* v_fvarId_911_ = stack[1].m_obj;
lean_object* v___y_912_ = stack[2].m_obj;
lean_object* v_res_949_;
v_res_949_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(v_e_910_, v_fvarId_911_, v___y_912_);
stack->m_obj
 = v_res_949_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___boxed(lean_object* v_e_950_, lean_object* v_fvarId_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(v_e_950_, v_fvarId_951_, v___y_952_);
lean_dec(v___y_952_);
return v_res_954_;
}
}
lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1(lean_object* v_e_955_, lean_object* v_fvarId_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(v_e_955_, v_fvarId_956_, v___y_958_);
return v___x_962_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_955_ = stack[0].m_obj;
lean_object* v_fvarId_956_ = stack[1].m_obj;
lean_object* v___y_957_ = stack[2].m_obj;
lean_object* v___y_958_ = stack[3].m_obj;
lean_object* v___y_959_ = stack[4].m_obj;
lean_object* v___y_960_ = stack[5].m_obj;
lean_object* v_res_963_;
v_res_963_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1(v_e_955_, v_fvarId_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
stack->m_obj
 = v_res_963_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___boxed(lean_object* v_e_964_, lean_object* v_fvarId_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1(v_e_964_, v_fvarId_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
return v_res_971_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(lean_object* v_mvarId_972_, lean_object* v_x_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_972_, v_x_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_a_988_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_979_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_979_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_972_ = stack[0].m_obj;
lean_object* v_x_973_ = stack[1].m_obj;
lean_object* v___y_974_ = stack[2].m_obj;
lean_object* v___y_975_ = stack[3].m_obj;
lean_object* v___y_976_ = stack[4].m_obj;
lean_object* v___y_977_ = stack[5].m_obj;
lean_object* v_res_996_;
v_res_996_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(v_mvarId_972_, v_x_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
stack->m_obj
 = v_res_996_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg___boxed(lean_object* v_mvarId_997_, lean_object* v_x_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(v_mvarId_997_, v_x_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
return v_res_1004_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3(lean_object* v_00_u03b1_1005_, lean_object* v_mvarId_1006_, lean_object* v_x_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(v_mvarId_1006_, v_x_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
return v___x_1013_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1006_ = stack[1].m_obj;
lean_object* v_x_1007_ = stack[2].m_obj;
lean_object* v___y_1008_ = stack[3].m_obj;
lean_object* v___y_1009_ = stack[4].m_obj;
lean_object* v___y_1010_ = stack[5].m_obj;
lean_object* v___y_1011_ = stack[6].m_obj;
lean_object* v_res_1014_;
v_res_1014_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3(lean_box(0), v_mvarId_1006_, v_x_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
stack->m_obj
 = v_res_1014_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___boxed(lean_object* v_00_u03b1_1015_, lean_object* v_mvarId_1016_, lean_object* v_x_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3(v_00_u03b1_1015_, v_mvarId_1016_, v_x_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
return v_res_1023_;
}
}
lean_object* l_Lean_Meta_Match_simpH___lam__0(lean_object* v_numEqs_1024_, lean_object* v_ys_1025_, lean_object* v_x_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = lean_array_get_size(v_ys_1025_);
v___x_1033_ = lean_nat_sub(v___x_1032_, v_numEqs_1024_);
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_simpH___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_numEqs_1024_ = stack[0].m_obj;
lean_object* v_ys_1025_ = stack[1].m_obj;
lean_object* v_x_1026_ = stack[2].m_obj;
lean_object* v___y_1027_ = stack[3].m_obj;
lean_object* v___y_1028_ = stack[4].m_obj;
lean_object* v___y_1029_ = stack[5].m_obj;
lean_object* v___y_1030_ = stack[6].m_obj;
lean_object* v_res_1035_;
v_res_1035_ = l_Lean_Meta_Match_simpH___lam__0(v_numEqs_1024_, v_ys_1025_, v_x_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
stack->m_obj
 = v_res_1035_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__0___boxed(lean_object* v_numEqs_1036_, lean_object* v_ys_1037_, lean_object* v_x_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_Meta_Match_simpH___lam__0(v_numEqs_1036_, v_ys_1037_, v_x_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec_ref(v_x_1038_);
lean_dec_ref(v_ys_1037_);
lean_dec(v_numEqs_1036_);
return v_res_1044_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(lean_object* v_a_1045_, lean_object* v_as_1046_, size_t v_i_1047_, size_t v_stop_1048_, lean_object* v_b_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_a_1056_; uint8_t v___x_1060_; 
v___x_1060_ = lean_usize_dec_eq(v_i_1047_, v_stop_1048_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_array_uget_borrowed(v_as_1046_, v_i_1047_);
lean_inc(v___x_1061_);
lean_inc_ref(v_a_1045_);
v___x_1062_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(v_a_1045_, v___x_1061_, v___y_1051_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; uint8_t v___x_1064_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1062_, 1);
v___x_1064_ = lean_unbox(v_a_1063_);
lean_dec(v_a_1063_);
if (v___x_1064_ == 0)
{
v_a_1056_ = v_b_1049_;
goto v___jp_1055_;
}
else
{
lean_object* v___x_1065_; 
lean_inc(v___x_1061_);
v___x_1065_ = lean_array_push(v_b_1049_, v___x_1061_);
v_a_1056_ = v___x_1065_;
goto v___jp_1055_;
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec_ref(v_b_1049_);
lean_dec_ref(v_a_1045_);
v_a_1066_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1062_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1062_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
else
{
lean_object* v___x_1074_; 
lean_dec_ref(v_a_1045_);
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v_b_1049_);
return v___x_1074_;
}
v___jp_1055_:
{
size_t v___x_1057_; size_t v___x_1058_; 
v___x_1057_ = ((size_t)1ULL);
v___x_1058_ = lean_usize_add(v_i_1047_, v___x_1057_);
v_i_1047_ = v___x_1058_;
v_b_1049_ = v_a_1056_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1045_ = stack[0].m_obj;
lean_object* v_as_1046_ = stack[1].m_obj;
size_t v_i_1047_ = stack[2].m_num;
size_t v_stop_1048_ = stack[3].m_num;
lean_object* v_b_1049_ = stack[4].m_obj;
lean_object* v___y_1050_ = stack[5].m_obj;
lean_object* v___y_1051_ = stack[6].m_obj;
lean_object* v___y_1052_ = stack[7].m_obj;
lean_object* v___y_1053_ = stack[8].m_obj;
lean_object* v_res_1075_;
v_res_1075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(v_a_1045_, v_as_1046_, v_i_1047_, v_stop_1048_, v_b_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
stack->m_obj
 = v_res_1075_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2___boxed(lean_object* v_a_1076_, lean_object* v_as_1077_, lean_object* v_i_1078_, lean_object* v_stop_1079_, lean_object* v_b_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
size_t v_i_boxed_1086_; size_t v_stop_boxed_1087_; lean_object* v_res_1088_; 
v_i_boxed_1086_ = lean_unbox_usize(v_i_1078_);
lean_dec(v_i_1078_);
v_stop_boxed_1087_ = lean_unbox_usize(v_stop_1079_);
lean_dec(v_stop_1079_);
v_res_1088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(v_a_1076_, v_as_1077_, v_i_boxed_1086_, v_stop_boxed_1087_, v_b_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec_ref(v_as_1077_);
return v_res_1088_;
}
}
lean_object* l_Lean_Meta_Match_simpH___lam__1(lean_object* v_snd_1089_, uint8_t v___x_1090_, lean_object* v___x_1091_, lean_object* v___x_1092_, lean_object* v_a_1093_, lean_object* v___x_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_a_1101_; lean_object* v___y_1122_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = lean_mk_empty_array_with_capacity(v___x_1091_);
v___x_1133_ = lean_nat_dec_lt(v___x_1091_, v___x_1092_);
if (v___x_1133_ == 0)
{
lean_dec_ref(v_a_1093_);
v_a_1101_ = v___x_1132_;
goto v___jp_1100_;
}
else
{
uint8_t v___x_1134_; 
v___x_1134_ = lean_nat_dec_le(v___x_1092_, v___x_1092_);
if (v___x_1134_ == 0)
{
if (v___x_1133_ == 0)
{
lean_dec_ref(v_a_1093_);
v_a_1101_ = v___x_1132_;
goto v___jp_1100_;
}
else
{
size_t v___x_1135_; size_t v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = ((size_t)0ULL);
v___x_1136_ = lean_usize_of_nat(v___x_1092_);
v___x_1137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(v_a_1093_, v___x_1094_, v___x_1135_, v___x_1136_, v___x_1132_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
v___y_1122_ = v___x_1137_;
goto v___jp_1121_;
}
}
else
{
size_t v___x_1138_; size_t v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = ((size_t)0ULL);
v___x_1139_ = lean_usize_of_nat(v___x_1092_);
v___x_1140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(v_a_1093_, v___x_1094_, v___x_1138_, v___x_1139_, v___x_1132_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
v___y_1122_ = v___x_1140_;
goto v___jp_1121_;
}
}
v___jp_1100_:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lean_MVarId_revert(v_snd_1089_, v_a_1101_, v___x_1090_, v___x_1090_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1112_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1105_ = v___x_1102_;
v_isShared_1106_ = v_isSharedCheck_1112_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1112_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v_snd_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
v_snd_1107_ = lean_ctor_get(v_a_1103_, 1);
lean_inc(v_snd_1107_);
lean_dec(v_a_1103_);
v___x_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1108_, 0, v_snd_1107_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1108_);
v___x_1110_ = v___x_1105_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
v_a_1113_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1102_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1102_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
v___jp_1121_:
{
if (lean_obj_tag(v___y_1122_) == 0)
{
lean_object* v_a_1123_; 
v_a_1123_ = lean_ctor_get(v___y_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___y_1122_, 1);
v_a_1101_ = v_a_1123_;
goto v___jp_1100_;
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec(v_snd_1089_);
v_a_1124_ = lean_ctor_get(v___y_1122_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___y_1122_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___y_1122_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___y_1122_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_simpH___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_1089_ = stack[0].m_obj;
uint8_t v___x_1090_ = stack[1].m_num;
lean_object* v___x_1091_ = stack[2].m_obj;
lean_object* v___x_1092_ = stack[3].m_obj;
lean_object* v_a_1093_ = stack[4].m_obj;
lean_object* v___x_1094_ = stack[5].m_obj;
lean_object* v___y_1095_ = stack[6].m_obj;
lean_object* v___y_1096_ = stack[7].m_obj;
lean_object* v___y_1097_ = stack[8].m_obj;
lean_object* v___y_1098_ = stack[9].m_obj;
lean_object* v_res_1141_;
v_res_1141_ = l_Lean_Meta_Match_simpH___lam__1(v_snd_1089_, v___x_1090_, v___x_1091_, v___x_1092_, v_a_1093_, v___x_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
stack->m_obj
 = v_res_1141_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__1___boxed(lean_object* v_snd_1142_, lean_object* v___x_1143_, lean_object* v___x_1144_, lean_object* v___x_1145_, lean_object* v_a_1146_, lean_object* v___x_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
uint8_t v___x_6503__boxed_1153_; lean_object* v_res_1154_; 
v___x_6503__boxed_1153_ = lean_unbox(v___x_1143_);
v_res_1154_ = l_Lean_Meta_Match_simpH___lam__1(v_snd_1142_, v___x_6503__boxed_1153_, v___x_1144_, v___x_1145_, v_a_1146_, v___x_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec_ref(v___x_1147_);
lean_dec(v___x_1145_);
lean_dec(v___x_1144_);
return v_res_1154_;
}
}
lean_object* l_Lean_Meta_Match_simpH___lam__2(lean_object* v_mvarId_1155_, lean_object* v___x_1156_, uint8_t v___x_1157_, lean_object* v_xs_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_MVarId_revert(v_mvarId_1155_, v___x_1156_, v___x_1157_, v___x_1157_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v_snd_1166_; lean_object* v___x_1167_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___x_1164_, 1);
v_snd_1166_ = lean_ctor_get(v_a_1165_, 1);
lean_inc_n(v_snd_1166_, 2);
lean_dec(v_a_1165_);
v___x_1167_ = l_Lean_MVarId_getType(v_snd_1166_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v___x_1169_ = lean_array_mk(v_xs_1158_);
v___x_1170_ = l_Array_reverse___redArg(v___x_1169_);
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = lean_array_get_size(v___x_1170_);
v___x_1173_ = lean_box(v___x_1157_);
lean_inc(v_snd_1166_);
v___f_1174_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH___lam__1___boxed), 11, 6);
lean_closure_set(v___f_1174_, 0, v_snd_1166_);
lean_closure_set(v___f_1174_, 1, v___x_1173_);
lean_closure_set(v___f_1174_, 2, v___x_1171_);
lean_closure_set(v___f_1174_, 3, v___x_1172_);
lean_closure_set(v___f_1174_, 4, v_a_1168_);
lean_closure_set(v___f_1174_, 5, v___x_1170_);
v___x_1175_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(v_snd_1166_, v___f_1174_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
return v___x_1175_;
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v_snd_1166_);
lean_dec(v_xs_1158_);
v_a_1176_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1167_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1167_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v_xs_1158_);
v_a_1184_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1164_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1164_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
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
LEAN_EXPORT void l_Lean_Meta_Match_simpH___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1155_ = stack[0].m_obj;
lean_object* v___x_1156_ = stack[1].m_obj;
uint8_t v___x_1157_ = stack[2].m_num;
lean_object* v_xs_1158_ = stack[3].m_obj;
lean_object* v___y_1159_ = stack[4].m_obj;
lean_object* v___y_1160_ = stack[5].m_obj;
lean_object* v___y_1161_ = stack[6].m_obj;
lean_object* v___y_1162_ = stack[7].m_obj;
lean_object* v_res_1192_;
v_res_1192_ = l_Lean_Meta_Match_simpH___lam__2(v_mvarId_1155_, v___x_1156_, v___x_1157_, v_xs_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
stack->m_obj
 = v_res_1192_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__2___boxed(lean_object* v_mvarId_1193_, lean_object* v___x_1194_, lean_object* v___x_1195_, lean_object* v_xs_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
uint8_t v___x_6674__boxed_1202_; lean_object* v_res_1203_; 
v___x_6674__boxed_1202_ = lean_unbox(v___x_1195_);
v_res_1203_ = l_Lean_Meta_Match_simpH___lam__2(v_mvarId_1193_, v___x_1194_, v___x_6674__boxed_1202_, v_xs_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
return v_res_1203_;
}
}
lean_object* l_Lean_Meta_Match_simpH___lam__3(lean_object* v_mvarId_1204_, lean_object* v___f_1205_, lean_object* v_numEqs_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; 
lean_inc(v_mvarId_1204_);
v___x_1212_ = l_Lean_MVarId_getType(v_mvarId_1204_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 1);
v___x_1214_ = 0;
v___x_1215_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(v_a_1213_, v___f_1205_, v___x_1214_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v_lctx_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
v_lctx_1217_ = lean_ctor_get(v___y_1207_, 2);
v___x_1218_ = l_Lean_LocalContext_getFVarIds(v_lctx_1217_);
v___x_1219_ = l_Lean_MVarId_tryClearMany(v_mvarId_1204_, v___x_1218_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec_ref(v___x_1218_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1219_, 1);
v___x_1221_ = lean_box(0);
v___x_1222_ = l_Lean_Meta_introNCore(v_a_1220_, v_a_1216_, v___x_1221_, v___x_1214_, v___x_1214_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v_fst_1224_; lean_object* v_snd_1225_; lean_object* v___x_1226_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v_fst_1224_ = lean_ctor_get(v_a_1223_, 0);
lean_inc(v_fst_1224_);
v_snd_1225_ = lean_ctor_get(v_a_1223_, 1);
lean_inc(v_snd_1225_);
lean_dec(v_a_1223_);
v___x_1226_ = l_Lean_Meta_introNCore(v_snd_1225_, v_numEqs_1206_, v___x_1221_, v___x_1214_, v___x_1214_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v_fst_1228_; lean_object* v_snd_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1226_, 1);
v_fst_1228_ = lean_ctor_get(v_a_1227_, 0);
lean_inc(v_fst_1228_);
v_snd_1229_ = lean_ctor_get(v_a_1227_, 1);
lean_inc(v_snd_1229_);
lean_dec(v_a_1227_);
v___x_1230_ = lean_array_to_list(v_fst_1224_);
v___x_1231_ = lean_array_to_list(v_fst_1228_);
v___x_1232_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1232_, 0, v_snd_1229_);
lean_ctor_set(v___x_1232_, 1, v___x_1230_);
lean_ctor_set(v___x_1232_, 2, v___x_1231_);
lean_ctor_set(v___x_1232_, 3, v___x_1221_);
v___x_1233_ = lean_st_mk_ref(v___x_1232_);
v___x_1234_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(v___x_1233_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1253_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1253_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1253_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = lean_st_ref_get(v___x_1233_);
lean_dec(v___x_1233_);
v___x_1240_ = lean_unbox(v_a_1235_);
lean_dec(v_a_1235_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
lean_dec(v___x_1239_);
v___x_1241_ = lean_box(0);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1241_);
v___x_1243_ = v___x_1237_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
else
{
lean_object* v_mvarId_1245_; lean_object* v_xs_1246_; lean_object* v_eqsNew_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___f_1251_; lean_object* v___x_1252_; 
lean_del_object(v___x_1237_);
v_mvarId_1245_ = lean_ctor_get(v___x_1239_, 0);
lean_inc_n(v_mvarId_1245_, 2);
v_xs_1246_ = lean_ctor_get(v___x_1239_, 1);
lean_inc(v_xs_1246_);
v_eqsNew_1247_ = lean_ctor_get(v___x_1239_, 3);
lean_inc(v_eqsNew_1247_);
lean_dec(v___x_1239_);
v___x_1248_ = l_List_reverse___redArg(v_eqsNew_1247_);
v___x_1249_ = lean_array_mk(v___x_1248_);
v___x_1250_ = lean_box(v___x_1214_);
v___f_1251_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1251_, 0, v_mvarId_1245_);
lean_closure_set(v___f_1251_, 1, v___x_1249_);
lean_closure_set(v___f_1251_, 2, v___x_1250_);
lean_closure_set(v___f_1251_, 3, v_xs_1246_);
v___x_1252_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(v_mvarId_1245_, v___f_1251_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
return v___x_1252_;
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec(v___x_1233_);
v_a_1254_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1234_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1234_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v_fst_1224_);
v_a_1262_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1226_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1226_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
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
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec(v_numEqs_1206_);
v_a_1270_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1222_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1222_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec(v_a_1216_);
lean_dec(v_numEqs_1206_);
v_a_1278_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1219_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1219_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec(v_numEqs_1206_);
lean_dec(v_mvarId_1204_);
v_a_1286_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1215_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1215_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v_numEqs_1206_);
lean_dec_ref(v___f_1205_);
lean_dec(v_mvarId_1204_);
v_a_1294_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1212_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1212_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
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
}
LEAN_EXPORT void l_Lean_Meta_Match_simpH___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1204_ = stack[0].m_obj;
lean_object* v___f_1205_ = stack[1].m_obj;
lean_object* v_numEqs_1206_ = stack[2].m_obj;
lean_object* v___y_1207_ = stack[3].m_obj;
lean_object* v___y_1208_ = stack[4].m_obj;
lean_object* v___y_1209_ = stack[5].m_obj;
lean_object* v___y_1210_ = stack[6].m_obj;
lean_object* v_res_1302_;
v_res_1302_ = l_Lean_Meta_Match_simpH___lam__3(v_mvarId_1204_, v___f_1205_, v_numEqs_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
stack->m_obj
 = v_res_1302_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___lam__3___boxed(lean_object* v_mvarId_1303_, lean_object* v___f_1304_, lean_object* v_numEqs_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_Meta_Match_simpH___lam__3(v_mvarId_1303_, v___f_1304_, v_numEqs_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
return v_res_1311_;
}
}
lean_object* l_Lean_Meta_Match_simpH(lean_object* v_mvarId_1312_, lean_object* v_numEqs_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v___y_1320_; lean_object* v___x_1337_; uint8_t v_transparency_1338_; lean_object* v___f_1339_; uint8_t v___x_1340_; uint8_t v___x_1341_; 
v___x_1337_ = l_Lean_Meta_Context_config(v_a_1314_);
v_transparency_1338_ = lean_ctor_get_uint8(v___x_1337_, 9);
lean_dec_ref(v___x_1337_);
lean_inc(v_numEqs_1313_);
v___f_1339_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_simpH___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1339_, 0, v_numEqs_1313_);
v___x_1340_ = 1;
v___x_1341_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1338_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_object* v_keyedConfig_1342_; uint8_t v_trackZetaDelta_1343_; lean_object* v_zetaDeltaSet_1344_; lean_object* v_lctx_1345_; lean_object* v_localInstances_1346_; lean_object* v_defEqCtx_x3f_1347_; lean_object* v_synthPendingDepth_1348_; lean_object* v_customCanUnfoldPredicate_x3f_1349_; uint8_t v_univApprox_1350_; uint8_t v_inTypeClassResolution_1351_; uint8_t v_cacheInferType_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v_keyedConfig_1342_ = lean_ctor_get(v_a_1314_, 0);
v_trackZetaDelta_1343_ = lean_ctor_get_uint8(v_a_1314_, sizeof(void*)*7);
v_zetaDeltaSet_1344_ = lean_ctor_get(v_a_1314_, 1);
v_lctx_1345_ = lean_ctor_get(v_a_1314_, 2);
v_localInstances_1346_ = lean_ctor_get(v_a_1314_, 3);
v_defEqCtx_x3f_1347_ = lean_ctor_get(v_a_1314_, 4);
v_synthPendingDepth_1348_ = lean_ctor_get(v_a_1314_, 5);
v_customCanUnfoldPredicate_x3f_1349_ = lean_ctor_get(v_a_1314_, 6);
v_univApprox_1350_ = lean_ctor_get_uint8(v_a_1314_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1351_ = lean_ctor_get_uint8(v_a_1314_, sizeof(void*)*7 + 2);
v_cacheInferType_1352_ = lean_ctor_get_uint8(v_a_1314_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1342_);
v___x_1353_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1340_, v_keyedConfig_1342_);
lean_inc(v_customCanUnfoldPredicate_x3f_1349_);
lean_inc(v_synthPendingDepth_1348_);
lean_inc(v_defEqCtx_x3f_1347_);
lean_inc_ref(v_localInstances_1346_);
lean_inc_ref(v_lctx_1345_);
lean_inc(v_zetaDeltaSet_1344_);
v___x_1354_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set(v___x_1354_, 1, v_zetaDeltaSet_1344_);
lean_ctor_set(v___x_1354_, 2, v_lctx_1345_);
lean_ctor_set(v___x_1354_, 3, v_localInstances_1346_);
lean_ctor_set(v___x_1354_, 4, v_defEqCtx_x3f_1347_);
lean_ctor_set(v___x_1354_, 5, v_synthPendingDepth_1348_);
lean_ctor_set(v___x_1354_, 6, v_customCanUnfoldPredicate_x3f_1349_);
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*7, v_trackZetaDelta_1343_);
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*7 + 1, v_univApprox_1350_);
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1351_);
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*7 + 3, v_cacheInferType_1352_);
v___x_1355_ = l_Lean_Meta_Match_simpH___lam__3(v_mvarId_1312_, v___f_1339_, v_numEqs_1313_, v___x_1354_, v_a_1315_, v_a_1316_, v_a_1317_);
lean_dec_ref_known(v___x_1354_, 7);
v___y_1320_ = v___x_1355_;
goto v___jp_1319_;
}
else
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_Meta_Match_simpH___lam__3(v_mvarId_1312_, v___f_1339_, v_numEqs_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
v___y_1320_ = v___x_1356_;
goto v___jp_1319_;
}
v___jp_1319_:
{
if (lean_obj_tag(v___y_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
v_a_1321_ = lean_ctor_get(v___y_1320_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___y_1320_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___y_1320_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___y_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
v_a_1329_ = lean_ctor_get(v___y_1320_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___y_1320_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___y_1320_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___y_1320_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_simpH_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1312_ = stack[0].m_obj;
lean_object* v_numEqs_1313_ = stack[1].m_obj;
lean_object* v_a_1314_ = stack[2].m_obj;
lean_object* v_a_1315_ = stack[3].m_obj;
lean_object* v_a_1316_ = stack[4].m_obj;
lean_object* v_a_1317_ = stack[5].m_obj;
lean_object* v_res_1357_;
v_res_1357_ = l_Lean_Meta_Match_simpH(v_mvarId_1312_, v_numEqs_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
stack->m_obj
 = v_res_1357_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH___boxed(lean_object* v_mvarId_1358_, lean_object* v_numEqs_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_Meta_Match_simpH(v_mvarId_1358_, v_numEqs_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
return v_res_1365_;
}
}
lean_object* l_Lean_Meta_Match_simpH_x3f(lean_object* v_h_1366_, lean_object* v_numEqs_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_box(0);
v___x_1374_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_h_1366_, v___x_1373_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v___x_1376_ = l_Lean_Expr_mvarId_x21(v_a_1375_);
lean_dec(v_a_1375_);
v___x_1377_ = l_Lean_Meta_Match_simpH(v___x_1376_, v_numEqs_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1411_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1411_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1411_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
if (lean_obj_tag(v_a_1378_) == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1382_ = lean_box(0);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1382_);
v___x_1384_ = v___x_1380_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
else
{
lean_object* v_val_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1410_; 
lean_del_object(v___x_1380_);
v_val_1386_ = lean_ctor_get(v_a_1378_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_a_1378_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1388_ = v_a_1378_;
v_isShared_1389_ = v_isSharedCheck_1410_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_val_1386_);
lean_dec(v_a_1378_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1410_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_MVarId_getType(v_val_1386_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1401_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1401_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1401_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v_a_1391_);
v___x_1396_ = v___x_1388_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1398_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1396_);
v___x_1398_ = v___x_1393_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_del_object(v___x_1388_);
v_a_1402_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1390_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1390_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
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
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
v_a_1412_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1377_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1377_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec(v_numEqs_1367_);
v_a_1420_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1374_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1374_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_simpH_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1366_ = stack[0].m_obj;
lean_object* v_numEqs_1367_ = stack[1].m_obj;
lean_object* v_a_1368_ = stack[2].m_obj;
lean_object* v_a_1369_ = stack[3].m_obj;
lean_object* v_a_1370_ = stack[4].m_obj;
lean_object* v_a_1371_ = stack[5].m_obj;
lean_object* v_res_1428_;
v_res_1428_ = l_Lean_Meta_Match_simpH_x3f(v_h_1366_, v_numEqs_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
stack->m_obj
 = v_res_1428_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_simpH_x3f___boxed(lean_object* v_h_1429_, lean_object* v_numEqs_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_Meta_Match_simpH_x3f(v_h_1429_, v_numEqs_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
return v_res_1436_;
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
