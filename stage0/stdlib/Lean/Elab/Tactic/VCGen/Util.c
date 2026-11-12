// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.Util
// Imports: public import Lean.Meta.Tactic.Grind.Main public import Lean.Elab.Tactic.VCGen.Context public import Lean.Elab.Tactic.VCGen.Reduce public import Lean.Meta.Sym.AlphaShareBuilder public import Lean.Meta.Sym.InstantiateMVarsS public import Lean.Meta.Sym.Intro public import Lean.Meta.Sym.Simp.Goal public import Lean.Meta.Sym.Simp.Telescope public import Lean.Meta.Sym.Util
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
lean_object* l_Lean_Meta_Sym_Pattern_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Sym_isDefEqS(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_processHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_intros(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_runSimp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_Name_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "synthInstanceOpt\?: too many arguments for `"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "[vcgen +debug] BackwardRule "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = " failed to apply to:"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "\nbut succeeded after `unfoldReducible`-normalization to:"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 116, .m_capacity = 116, .m_length = 115, .m_data = "\nAn earlier step is missing a normalization. Re-run with `set_option pp.all true` to see the structural difference."};
static const lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "<rule constructed from expression>"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_VCGen_isProgramName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_isProgramName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_numBindersToIntro(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_numBindersToIntro___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_introsHygienicN_collectBinders(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instantiateBinderDomains___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instantiateBinderDomains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instantiateBinderDomains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instantiateBinderDomains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " to goal"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "le_of_forall_le"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(101, 62, 242, 60, 214, 49, 44, 186)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "failed to apply "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "cleanupVC: failed to apply "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " to"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "left"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(12, 252, 227, 83, 88, 185, 40, 148)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "right"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__18_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(18, 204, 165, 192, 253, 41, 237, 145)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__20_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__20_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_put(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___redArg(v_e_30_, v___y_32_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___boxed(lean_object* v_e_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1(v_e_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___redArg(lean_object* v_k_44_, uint8_t v_allowLevelAssignments_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_45_, v_k_44_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_59_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_59_ == 0)
{
v___x_54_ = v___x_51_;
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v___x_51_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_a_52_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
else
{
lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
v_a_60_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v___x_51_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_51_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_a_60_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___redArg___boxed(lean_object* v_k_68_, lean_object* v_allowLevelAssignments_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_75_; lean_object* v_res_76_; 
v_allowLevelAssignments_boxed_75_ = lean_unbox(v_allowLevelAssignments_69_);
v_res_76_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___redArg(v_k_68_, v_allowLevelAssignments_boxed_75_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5(lean_object* v_00_u03b1_77_, lean_object* v_k_78_, uint8_t v_allowLevelAssignments_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___redArg(v_k_78_, v_allowLevelAssignments_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___boxed(lean_object* v_00_u03b1_86_, lean_object* v_k_87_, lean_object* v_allowLevelAssignments_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_94_; lean_object* v_res_95_; 
v_allowLevelAssignments_boxed_94_ = lean_unbox(v_allowLevelAssignments_88_);
v_res_95_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5(v_00_u03b1_86_, v_k_87_, v_allowLevelAssignments_boxed_94_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
return v_res_95_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__3(lean_object* v_as_96_, size_t v_i_97_, size_t v_stop_98_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = lean_usize_dec_eq(v_i_97_, v_stop_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = lean_array_uget_borrowed(v_as_96_, v_i_97_);
v___x_101_ = l_Lean_Expr_hasExprMVar(v___x_100_);
if (v___x_101_ == 0)
{
size_t v___x_102_; size_t v___x_103_; 
v___x_102_ = ((size_t)1ULL);
v___x_103_ = lean_usize_add(v_i_97_, v___x_102_);
v_i_97_ = v___x_103_;
goto _start;
}
else
{
return v___x_101_;
}
}
else
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__3___boxed(lean_object* v_as_106_, lean_object* v_i_107_, lean_object* v_stop_108_){
_start:
{
size_t v_i_boxed_109_; size_t v_stop_boxed_110_; uint8_t v_res_111_; lean_object* v_r_112_; 
v_i_boxed_109_ = lean_unbox_usize(v_i_107_);
lean_dec(v_i_107_);
v_stop_boxed_110_ = lean_unbox_usize(v_stop_108_);
lean_dec(v_stop_108_);
v_res_111_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__3(v_as_106_, v_i_boxed_109_, v_stop_boxed_110_);
lean_dec_ref(v_as_106_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0(lean_object* v_as_115_, size_t v_sz_116_, size_t v_i_117_, lean_object* v_b_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_a_125_; uint8_t v___x_129_; 
v___x_129_ = lean_usize_dec_lt(v_i_117_, v_sz_116_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v_b_118_);
return v___x_130_;
}
else
{
lean_object* v_snd_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_187_; 
v_snd_131_ = lean_ctor_get(v_b_118_, 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v_b_118_);
if (v_isSharedCheck_187_ == 0)
{
lean_object* v_unused_188_; 
v_unused_188_ = lean_ctor_get(v_b_118_, 0);
lean_dec(v_unused_188_);
v___x_133_ = v_b_118_;
v_isShared_134_ = v_isSharedCheck_187_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_snd_131_);
lean_dec(v_b_118_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_187_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v_array_135_; lean_object* v_start_136_; lean_object* v_stop_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v_array_135_ = lean_ctor_get(v_snd_131_, 0);
v_start_136_ = lean_ctor_get(v_snd_131_, 1);
v_stop_137_ = lean_ctor_get(v_snd_131_, 2);
v___x_138_ = lean_box(0);
v___x_139_ = lean_nat_dec_lt(v_start_136_, v_stop_137_);
if (v___x_139_ == 0)
{
lean_object* v___x_141_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_138_);
v___x_141_ = v___x_133_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_snd_131_);
v___x_141_ = v_reuseFailAlloc_143_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; 
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
else
{
lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_183_; 
lean_inc(v_stop_137_);
lean_inc(v_start_136_);
lean_inc_ref(v_array_135_);
v_isSharedCheck_183_ = !lean_is_exclusive(v_snd_131_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; lean_object* v_unused_185_; lean_object* v_unused_186_; 
v_unused_184_ = lean_ctor_get(v_snd_131_, 2);
lean_dec(v_unused_184_);
v_unused_185_ = lean_ctor_get(v_snd_131_, 1);
lean_dec(v_unused_185_);
v_unused_186_ = lean_ctor_get(v_snd_131_, 0);
lean_dec(v_unused_186_);
v___x_145_ = v_snd_131_;
v_isShared_146_ = v_isSharedCheck_183_;
goto v_resetjp_144_;
}
else
{
lean_dec(v_snd_131_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_183_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_147_ = lean_array_fget(v_array_135_, v_start_136_);
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_add(v_start_136_, v___x_148_);
lean_dec(v_start_136_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v___x_149_);
v___x_151_ = v___x_145_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_array_135_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v_stop_137_);
v___x_151_ = v_reuseFailAlloc_182_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
if (lean_obj_tag(v___x_147_) == 1)
{
lean_object* v_val_152_; lean_object* v_a_153_; lean_object* v___x_154_; 
v_val_152_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_val_152_);
lean_dec_ref_known(v___x_147_, 1);
v_a_153_ = lean_array_uget_borrowed(v_as_115_, v_i_117_);
lean_inc(v_a_153_);
v___x_154_ = l_Lean_Meta_isExprDefEq(v_a_153_, v_val_152_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_170_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_170_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_170_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_170_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
uint8_t v___x_159_; 
v___x_159_ = lean_unbox(v_a_155_);
lean_dec(v_a_155_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0___closed__0));
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_151_);
lean_ctor_set(v___x_133_, 0, v___x_160_);
v___x_162_ = v___x_133_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v___x_151_);
v___x_162_ = v_reuseFailAlloc_166_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_164_; 
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_162_);
v___x_164_ = v___x_157_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
else
{
lean_object* v___x_168_; 
lean_del_object(v___x_157_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_151_);
lean_ctor_set(v___x_133_, 0, v___x_138_);
v___x_168_ = v___x_133_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___x_151_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
v_a_125_ = v___x_168_;
goto v___jp_124_;
}
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec_ref(v___x_151_);
lean_del_object(v___x_133_);
v_a_171_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_154_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_154_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
else
{
lean_object* v___x_180_; 
lean_dec(v___x_147_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_151_);
lean_ctor_set(v___x_133_, 0, v___x_138_);
v___x_180_ = v___x_133_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___x_151_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
v_a_125_ = v___x_180_;
goto v___jp_124_;
}
}
}
}
}
}
}
v___jp_124_:
{
size_t v___x_126_; size_t v___x_127_; 
v___x_126_ = ((size_t)1ULL);
v___x_127_ = lean_usize_add(v_i_117_, v___x_126_);
v_i_117_ = v___x_127_;
v_b_118_ = v_a_125_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0___boxed(lean_object* v_as_189_, lean_object* v_sz_190_, lean_object* v_i_191_, lean_object* v_b_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
size_t v_sz_boxed_198_; size_t v_i_boxed_199_; lean_object* v_res_200_; 
v_sz_boxed_198_ = lean_unbox_usize(v_sz_190_);
lean_dec(v_sz_190_);
v_i_boxed_199_ = lean_unbox_usize(v_i_191_);
lean_dec(v_i_191_);
v_res_200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0(v_as_189_, v_sz_boxed_198_, v_i_boxed_199_, v_b_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec_ref(v_as_189_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4_spec__4(lean_object* v_msgData_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; lean_object* v_env_208_; uint8_t v___x_209_; lean_object* v_env_210_; lean_object* v___x_211_; lean_object* v_toCold_212_; lean_object* v_mctx_213_; lean_object* v_lctx_214_; lean_object* v_options_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_207_ = lean_st_ref_get(v___y_205_);
v_env_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc_ref(v_env_208_);
lean_dec(v___x_207_);
v___x_209_ = 0;
v_env_210_ = l_Lean_Environment_setRecordingDeps(v_env_208_, v___x_209_);
v___x_211_ = lean_st_ref_get(v___y_203_);
v_toCold_212_ = lean_ctor_get(v___y_204_, 0);
v_mctx_213_ = lean_ctor_get(v___x_211_, 0);
lean_inc_ref(v_mctx_213_);
lean_dec(v___x_211_);
v_lctx_214_ = lean_ctor_get(v___y_202_, 2);
v_options_215_ = lean_ctor_get(v_toCold_212_, 2);
lean_inc_ref(v_options_215_);
lean_inc_ref(v_lctx_214_);
v___x_216_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_216_, 0, v_env_210_);
lean_ctor_set(v___x_216_, 1, v_mctx_213_);
lean_ctor_set(v___x_216_, 2, v_lctx_214_);
lean_ctor_set(v___x_216_, 3, v_options_215_);
v___x_217_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v_msgData_201_);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4_spec__4___boxed(lean_object* v_msgData_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4_spec__4(v_msgData_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___redArg(lean_object* v_msg_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_ref_232_; lean_object* v___x_233_; lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_242_; 
v_ref_232_ = lean_ctor_get(v___y_229_, 2);
v___x_233_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4_spec__4(v_msg_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
v_a_234_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_242_ == 0)
{
v___x_236_ = v___x_233_;
v_isShared_237_ = v_isSharedCheck_242_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_233_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_242_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v___x_240_; 
lean_inc(v_ref_232_);
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v_ref_232_);
lean_ctor_set(v___x_238_, 1, v_a_234_);
if (v_isShared_237_ == 0)
{
lean_ctor_set_tag(v___x_236_, 1);
lean_ctor_set(v___x_236_, 0, v___x_238_);
v___x_240_ = v___x_236_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___redArg___boxed(lean_object* v_msg_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___redArg(v_msg_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__2(size_t v_sz_250_, size_t v_i_251_, lean_object* v_bs_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
uint8_t v___x_258_; 
v___x_258_ = lean_usize_dec_lt(v_i_251_, v_sz_250_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v_bs_252_);
return v___x_259_;
}
else
{
lean_object* v_v_260_; lean_object* v___x_261_; lean_object* v_bs_x27_262_; lean_object* v___x_263_; 
v_v_260_ = lean_array_uget(v_bs_252_, v_i_251_);
v___x_261_ = lean_unsigned_to_nat(0u);
v_bs_x27_262_ = lean_array_uset(v_bs_252_, v_i_251_, v___x_261_);
v___x_263_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___redArg(v_v_260_, v___y_254_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; size_t v___x_265_; size_t v___x_266_; lean_object* v___x_267_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v___x_263_, 1);
v___x_265_ = ((size_t)1ULL);
v___x_266_ = lean_usize_add(v_i_251_, v___x_265_);
v___x_267_ = lean_array_uset(v_bs_x27_262_, v_i_251_, v_a_264_);
v_i_251_ = v___x_266_;
v_bs_252_ = v___x_267_;
goto _start;
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec_ref(v_bs_x27_262_);
v_a_269_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_263_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_263_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__2___boxed(lean_object* v_sz_277_, lean_object* v_i_278_, lean_object* v_bs_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
size_t v_sz_boxed_285_; size_t v_i_boxed_286_; lean_object* v_res_287_; 
v_sz_boxed_285_ = lean_unbox_usize(v_sz_277_);
lean_dec(v_sz_277_);
v_i_boxed_286_ = lean_unbox_usize(v_i_278_);
lean_dec(v_i_278_);
v_res_287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__2(v_sz_boxed_285_, v_i_boxed_286_, v_bs_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
return v_res_287_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__0));
v___x_290_ = l_Lean_stringToMessageData(v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__2));
v___x_293_ = l_Lean_stringToMessageData(v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0(lean_object* v_cls_294_, lean_object* v_xs_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___x_310_; 
lean_inc(v_cls_294_);
v___x_310_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_cls_294_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_312_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc_n(v_a_311_, 2);
lean_dec_ref_known(v___x_310_, 1);
lean_inc(v___y_299_);
lean_inc_ref(v___y_298_);
lean_inc(v___y_297_);
lean_inc_ref(v___y_296_);
v___x_312_ = lean_infer_type(v_a_311_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref_known(v___x_312_, 1);
v___x_314_ = lean_box(0);
v___x_315_ = 0;
v___x_316_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_313_, v___x_314_, v___x_315_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v_fst_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_407_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v___x_316_, 1);
v_fst_318_ = lean_ctor_get(v_a_317_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v_a_317_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; 
v_unused_408_ = lean_ctor_get(v_a_317_, 1);
lean_dec(v_unused_408_);
v___x_320_ = v_a_317_;
v_isShared_321_ = v_isSharedCheck_407_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_fst_318_);
lean_dec(v_a_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_407_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_390_ = lean_array_get_size(v_fst_318_);
v___x_391_ = lean_array_get_size(v_xs_295_);
v___x_392_ = lean_nat_dec_lt(v___x_390_, v___x_391_);
if (v___x_392_ == 0)
{
lean_dec(v_cls_294_);
v___y_323_ = v___y_296_;
v___y_324_ = v___y_297_;
v___y_325_ = v___y_298_;
v___y_326_ = v___y_299_;
goto v___jp_322_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_del_object(v___x_320_);
lean_dec(v_fst_318_);
lean_dec(v_a_311_);
lean_dec_ref(v_xs_295_);
v___x_393_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__1, &l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__1);
v___x_394_ = l_Lean_MessageData_ofName(v_cls_294_);
v___x_395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3, &l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3);
v___x_397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___redArg(v___x_397_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
v___jp_322_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_array_get_size(v_xs_295_);
v___x_329_ = l_Array_toSubarray___redArg(v_xs_295_, v___x_327_, v___x_328_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v___x_329_);
lean_ctor_set(v___x_320_, 0, v___x_314_);
v___x_331_ = v___x_320_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_329_);
v___x_331_ = v_reuseFailAlloc_389_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
size_t v_sz_332_; size_t v___x_333_; lean_object* v___x_334_; 
v_sz_332_ = lean_array_size(v_fst_318_);
v___x_333_ = ((size_t)0ULL);
v___x_334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0(v_fst_318_, v_sz_332_, v___x_333_, v___x_331_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_380_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_380_ == 0)
{
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_380_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_380_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v_fst_339_; 
v_fst_339_ = lean_ctor_get(v_a_335_, 0);
lean_inc(v_fst_339_);
lean_dec(v_a_335_);
if (lean_obj_tag(v_fst_339_) == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; 
lean_del_object(v___x_337_);
v___x_340_ = l_Lean_mkAppN(v_a_311_, v_fst_318_);
v___x_341_ = l_Lean_Meta_synthInstance_x3f(v___x_340_, v___x_314_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_367_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_367_ == 0)
{
v___x_344_ = v___x_341_;
v_isShared_345_ = v_isSharedCheck_367_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_367_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
if (lean_obj_tag(v_a_342_) == 1)
{
lean_object* v_val_346_; lean_object* v___x_347_; 
lean_del_object(v___x_344_);
v_val_346_ = lean_ctor_get(v_a_342_, 0);
lean_inc(v_val_346_);
lean_dec_ref_known(v_a_342_, 1);
v___x_347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__2(v_sz_332_, v___x_333_, v_fst_318_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec_ref(v___y_323_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_349_; lean_object* v_a_350_; uint8_t v___x_351_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
v___x_349_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___redArg(v_val_346_, v___y_324_);
lean_dec(v___y_324_);
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_350_);
lean_dec_ref(v___x_349_);
v___x_351_ = l_Lean_Expr_hasExprMVar(v_a_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_array_get_size(v_a_348_);
v___x_353_ = lean_nat_dec_lt(v___x_327_, v___x_352_);
if (v___x_353_ == 0)
{
v___y_305_ = v_a_350_;
v___y_306_ = v_a_348_;
goto v___jp_304_;
}
else
{
if (v___x_353_ == 0)
{
v___y_305_ = v_a_350_;
v___y_306_ = v_a_348_;
goto v___jp_304_;
}
else
{
size_t v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_usize_of_nat(v___x_352_);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__3(v_a_348_, v___x_333_, v___x_354_);
if (v___x_355_ == 0)
{
v___y_305_ = v_a_350_;
v___y_306_ = v_a_348_;
goto v___jp_304_;
}
else
{
lean_dec(v_a_350_);
lean_dec(v_a_348_);
goto v___jp_301_;
}
}
}
}
else
{
lean_dec(v_a_350_);
lean_dec(v_a_348_);
goto v___jp_301_;
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec(v_val_346_);
lean_dec(v___y_324_);
v_a_356_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_347_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_347_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_object* v___x_365_; 
lean_dec(v_a_342_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v_fst_318_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_314_);
v___x_365_ = v___x_344_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_314_);
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
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v_fst_318_);
v_a_368_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_341_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_341_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
else
{
lean_object* v_val_376_; lean_object* v___x_378_; 
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v_fst_318_);
lean_dec(v_a_311_);
v_val_376_ = lean_ctor_get(v_fst_339_, 0);
lean_inc(v_val_376_);
lean_dec_ref_known(v_fst_339_, 1);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v_val_376_);
v___x_378_ = v___x_337_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_val_376_);
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
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v_fst_318_);
lean_dec(v_a_311_);
v_a_381_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_334_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_334_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
lean_dec(v_a_311_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec_ref(v_xs_295_);
lean_dec(v_cls_294_);
v_a_409_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_316_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_316_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec(v_a_311_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec_ref(v_xs_295_);
lean_dec(v_cls_294_);
v_a_417_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_312_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_312_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
else
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec_ref(v_xs_295_);
lean_dec(v_cls_294_);
v_a_425_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_310_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_310_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
v___jp_301_:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_box(0);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
v___jp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v___y_306_);
lean_ctor_set(v___x_307_, 1, v___y_305_);
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___boxed(lean_object* v_cls_433_, lean_object* v_xs_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0(v_cls_433_, v_xs_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f(lean_object* v_cls_441_, lean_object* v_xs_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___f_448_; uint8_t v___x_449_; lean_object* v___x_450_; 
v___f_448_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_448_, 0, v_cls_441_);
lean_closure_set(v___f_448_, 1, v_xs_442_);
v___x_449_ = 0;
v___x_450_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___redArg(v___f_448_, v___x_449_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___boxed(lean_object* v_cls_451_, lean_object* v_xs_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f(v_cls_451_, v_xs_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4(lean_object* v_00_u03b1_459_, lean_object* v_msg_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___redArg(v_msg_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___boxed(lean_object* v_00_u03b1_467_, lean_object* v_msg_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4(v_00_u03b1_467_, v_msg_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(lean_object* v_mvarId_475_, lean_object* v_x_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_475_, v_x_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
v_a_491_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_482_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_482_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg___boxed(lean_object* v_mvarId_499_, lean_object* v_x_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(v_mvarId_499_, v_x_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1(lean_object* v_00_u03b1_507_, lean_object* v_mvarId_508_, lean_object* v_x_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(v_mvarId_508_, v_x_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___boxed(lean_object* v_00_u03b1_516_, lean_object* v_mvarId_517_, lean_object* v_x_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1(v_00_u03b1_516_, v_mvarId_517_, v_x_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_525_, lean_object* v_x_526_, lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
lean_object* v_ks_529_; lean_object* v_vs_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_554_; 
v_ks_529_ = lean_ctor_get(v_x_525_, 0);
v_vs_530_ = lean_ctor_get(v_x_525_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v_x_525_);
if (v_isSharedCheck_554_ == 0)
{
v___x_532_ = v_x_525_;
v_isShared_533_ = v_isSharedCheck_554_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_vs_530_);
lean_inc(v_ks_529_);
lean_dec(v_x_525_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_554_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_534_ = lean_array_get_size(v_ks_529_);
v___x_535_ = lean_nat_dec_lt(v_x_526_, v___x_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
lean_dec(v_x_526_);
v___x_536_ = lean_array_push(v_ks_529_, v_x_527_);
v___x_537_ = lean_array_push(v_vs_530_, v_x_528_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 1, v___x_537_);
lean_ctor_set(v___x_532_, 0, v___x_536_);
v___x_539_ = v___x_532_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
else
{
lean_object* v_k_x27_541_; uint8_t v___x_542_; 
v_k_x27_541_ = lean_array_fget_borrowed(v_ks_529_, v_x_526_);
v___x_542_ = l_Lean_instBEqMVarId_beq(v_x_527_, v_k_x27_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_544_; 
if (v_isShared_533_ == 0)
{
v___x_544_ = v___x_532_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_ks_529_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_vs_530_);
v___x_544_ = v_reuseFailAlloc_548_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_unsigned_to_nat(1u);
v___x_546_ = lean_nat_add(v_x_526_, v___x_545_);
lean_dec(v_x_526_);
v_x_525_ = v___x_544_;
v_x_526_ = v___x_546_;
goto _start;
}
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_549_ = lean_array_fset(v_ks_529_, v_x_526_, v_x_527_);
v___x_550_ = lean_array_fset(v_vs_530_, v_x_526_, v_x_528_);
lean_dec(v_x_526_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 1, v___x_550_);
lean_ctor_set(v___x_532_, 0, v___x_549_);
v___x_552_ = v___x_532_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_555_, lean_object* v_k_556_, lean_object* v_v_557_){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_555_, v___x_558_, v_k_556_, v_v_557_);
return v___x_559_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(lean_object* v_x_561_, size_t v_x_562_, size_t v_x_563_, lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
if (lean_obj_tag(v_x_561_) == 0)
{
lean_object* v_es_566_; size_t v___x_567_; size_t v___x_568_; lean_object* v_j_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v_es_566_ = lean_ctor_get(v_x_561_, 0);
v___x_567_ = ((size_t)31ULL);
v___x_568_ = lean_usize_land(v_x_562_, v___x_567_);
v_j_569_ = lean_usize_to_nat(v___x_568_);
v___x_570_ = lean_array_get_size(v_es_566_);
v___x_571_ = lean_nat_dec_lt(v_j_569_, v___x_570_);
if (v___x_571_ == 0)
{
lean_dec(v_j_569_);
lean_dec(v_x_565_);
lean_dec(v_x_564_);
return v_x_561_;
}
else
{
lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_610_; 
lean_inc_ref(v_es_566_);
v_isSharedCheck_610_ = !lean_is_exclusive(v_x_561_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v_x_561_, 0);
lean_dec(v_unused_611_);
v___x_573_ = v_x_561_;
v_isShared_574_ = v_isSharedCheck_610_;
goto v_resetjp_572_;
}
else
{
lean_dec(v_x_561_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_610_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v_v_575_; lean_object* v___x_576_; lean_object* v_xs_x27_577_; lean_object* v___y_579_; 
v_v_575_ = lean_array_fget(v_es_566_, v_j_569_);
v___x_576_ = lean_box(0);
v_xs_x27_577_ = lean_array_fset(v_es_566_, v_j_569_, v___x_576_);
switch(lean_obj_tag(v_v_575_))
{
case 0:
{
lean_object* v_key_584_; lean_object* v_val_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_595_; 
v_key_584_ = lean_ctor_get(v_v_575_, 0);
v_val_585_ = lean_ctor_get(v_v_575_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v_v_575_);
if (v_isSharedCheck_595_ == 0)
{
v___x_587_ = v_v_575_;
v_isShared_588_ = v_isSharedCheck_595_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_val_585_);
lean_inc(v_key_584_);
lean_dec(v_v_575_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_595_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
uint8_t v___x_589_; 
v___x_589_ = l_Lean_instBEqMVarId_beq(v_x_564_, v_key_584_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; 
lean_del_object(v___x_587_);
v___x_590_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_584_, v_val_585_, v_x_564_, v_x_565_);
v___x_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
v___y_579_ = v___x_591_;
goto v___jp_578_;
}
else
{
lean_object* v___x_593_; 
lean_dec(v_val_585_);
lean_dec(v_key_584_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v_x_565_);
lean_ctor_set(v___x_587_, 0, v_x_564_);
v___x_593_ = v___x_587_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_x_564_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_x_565_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
v___y_579_ = v___x_593_;
goto v___jp_578_;
}
}
}
}
case 1:
{
lean_object* v_node_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_608_; 
v_node_596_ = lean_ctor_get(v_v_575_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v_v_575_);
if (v_isSharedCheck_608_ == 0)
{
v___x_598_ = v_v_575_;
v_isShared_599_ = v_isSharedCheck_608_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_node_596_);
lean_dec(v_v_575_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_608_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
size_t v___x_600_; size_t v___x_601_; size_t v___x_602_; size_t v___x_603_; lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_600_ = ((size_t)5ULL);
v___x_601_ = lean_usize_shift_right(v_x_562_, v___x_600_);
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_add(v_x_563_, v___x_602_);
v___x_604_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_node_596_, v___x_601_, v___x_603_, v_x_564_, v_x_565_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_604_);
v___x_606_ = v___x_598_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
v___y_579_ = v___x_606_;
goto v___jp_578_;
}
}
}
default: 
{
lean_object* v___x_609_; 
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v_x_564_);
lean_ctor_set(v___x_609_, 1, v_x_565_);
v___y_579_ = v___x_609_;
goto v___jp_578_;
}
}
v___jp_578_:
{
lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_580_ = lean_array_fset(v_xs_x27_577_, v_j_569_, v___y_579_);
lean_dec(v_j_569_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_580_);
v___x_582_ = v___x_573_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
else
{
lean_object* v_ks_612_; lean_object* v_vs_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_631_; 
v_ks_612_ = lean_ctor_get(v_x_561_, 0);
v_vs_613_ = lean_ctor_get(v_x_561_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_x_561_);
if (v_isSharedCheck_631_ == 0)
{
v___x_615_ = v_x_561_;
v_isShared_616_ = v_isSharedCheck_631_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_vs_613_);
lean_inc(v_ks_612_);
lean_dec(v_x_561_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_631_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_ks_612_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_vs_613_);
v___x_618_ = v_reuseFailAlloc_630_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v_newNode_619_; size_t v___x_620_; uint8_t v___x_621_; 
v_newNode_619_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3___redArg(v___x_618_, v_x_564_, v_x_565_);
v___x_620_ = ((size_t)7ULL);
v___x_621_ = lean_usize_dec_le(v___x_620_, v_x_563_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_622_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_619_);
v___x_623_ = lean_unsigned_to_nat(4u);
v___x_624_ = lean_nat_dec_lt(v___x_622_, v___x_623_);
lean_dec(v___x_622_);
if (v___x_624_ == 0)
{
lean_object* v_ks_625_; lean_object* v_vs_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_ks_625_ = lean_ctor_get(v_newNode_619_, 0);
lean_inc_ref(v_ks_625_);
v_vs_626_ = lean_ctor_get(v_newNode_619_, 1);
lean_inc_ref(v_vs_626_);
lean_dec_ref(v_newNode_619_);
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_629_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(v_x_563_, v_ks_625_, v_vs_626_, v___x_627_, v___x_628_);
lean_dec_ref(v_vs_626_);
lean_dec_ref(v_ks_625_);
return v___x_629_;
}
else
{
return v_newNode_619_;
}
}
else
{
return v_newNode_619_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_632_, lean_object* v_keys_633_, lean_object* v_vals_634_, lean_object* v_i_635_, lean_object* v_entries_636_){
_start:
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_array_get_size(v_keys_633_);
v___x_638_ = lean_nat_dec_lt(v_i_635_, v___x_637_);
if (v___x_638_ == 0)
{
lean_dec(v_i_635_);
return v_entries_636_;
}
else
{
lean_object* v_k_639_; lean_object* v_v_640_; uint64_t v___x_641_; size_t v_h_642_; size_t v___x_643_; lean_object* v___x_644_; size_t v___x_645_; size_t v___x_646_; size_t v___x_647_; size_t v_h_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_k_639_ = lean_array_fget_borrowed(v_keys_633_, v_i_635_);
v_v_640_ = lean_array_fget_borrowed(v_vals_634_, v_i_635_);
v___x_641_ = l_Lean_instHashableMVarId_hash(v_k_639_);
v_h_642_ = lean_uint64_to_usize(v___x_641_);
v___x_643_ = ((size_t)5ULL);
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = ((size_t)1ULL);
v___x_646_ = lean_usize_sub(v_depth_632_, v___x_645_);
v___x_647_ = lean_usize_mul(v___x_643_, v___x_646_);
v_h_648_ = lean_usize_shift_right(v_h_642_, v___x_647_);
v___x_649_ = lean_nat_add(v_i_635_, v___x_644_);
lean_dec(v_i_635_);
lean_inc(v_v_640_);
lean_inc(v_k_639_);
v___x_650_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_entries_636_, v_h_648_, v_depth_632_, v_k_639_, v_v_640_);
v_i_635_ = v___x_649_;
v_entries_636_ = v___x_650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_652_, lean_object* v_keys_653_, lean_object* v_vals_654_, lean_object* v_i_655_, lean_object* v_entries_656_){
_start:
{
size_t v_depth_boxed_657_; lean_object* v_res_658_; 
v_depth_boxed_657_ = lean_unbox_usize(v_depth_652_);
lean_dec(v_depth_652_);
v_res_658_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_657_, v_keys_653_, v_vals_654_, v_i_655_, v_entries_656_);
lean_dec_ref(v_vals_654_);
lean_dec_ref(v_keys_653_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_, lean_object* v_x_663_){
_start:
{
size_t v_x_1131__boxed_664_; size_t v_x_1132__boxed_665_; lean_object* v_res_666_; 
v_x_1131__boxed_664_ = lean_unbox_usize(v_x_660_);
lean_dec(v_x_660_);
v_x_1132__boxed_665_ = lean_unbox_usize(v_x_661_);
lean_dec(v_x_661_);
v_res_666_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_x_659_, v_x_1131__boxed_664_, v_x_1132__boxed_665_, v_x_662_, v_x_663_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(lean_object* v_x_667_, lean_object* v_x_668_, lean_object* v_x_669_){
_start:
{
uint64_t v___x_670_; size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
v___x_670_ = l_Lean_instHashableMVarId_hash(v_x_668_);
v___x_671_ = lean_uint64_to_usize(v___x_670_);
v___x_672_ = ((size_t)1ULL);
v___x_673_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_x_667_, v___x_671_, v___x_672_, v_x_668_, v_x_669_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(lean_object* v_mvarId_674_, lean_object* v_val_675_, lean_object* v___y_676_){
_start:
{
lean_object* v___x_678_; lean_object* v_mctx_679_; lean_object* v_cache_680_; lean_object* v_zetaDeltaFVarIds_681_; lean_object* v_postponed_682_; lean_object* v_diag_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_712_; 
v___x_678_ = lean_st_ref_take(v___y_676_);
v_mctx_679_ = lean_ctor_get(v___x_678_, 0);
v_cache_680_ = lean_ctor_get(v___x_678_, 1);
v_zetaDeltaFVarIds_681_ = lean_ctor_get(v___x_678_, 2);
v_postponed_682_ = lean_ctor_get(v___x_678_, 3);
v_diag_683_ = lean_ctor_get(v___x_678_, 4);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_712_ == 0)
{
v___x_685_ = v___x_678_;
v_isShared_686_ = v_isSharedCheck_712_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_diag_683_);
lean_inc(v_postponed_682_);
lean_inc(v_zetaDeltaFVarIds_681_);
lean_inc(v_cache_680_);
lean_inc(v_mctx_679_);
lean_dec(v___x_678_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_712_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v_depth_687_; lean_object* v_levelAssignDepth_688_; lean_object* v_lmvarCounter_689_; lean_object* v_mvarCounter_690_; lean_object* v_lDecls_691_; lean_object* v_decls_692_; lean_object* v_userNames_693_; lean_object* v_lAssignment_694_; lean_object* v_eAssignment_695_; lean_object* v_dAssignment_696_; lean_object* v_instanceTypedMVars_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_711_; 
v_depth_687_ = lean_ctor_get(v_mctx_679_, 0);
v_levelAssignDepth_688_ = lean_ctor_get(v_mctx_679_, 1);
v_lmvarCounter_689_ = lean_ctor_get(v_mctx_679_, 2);
v_mvarCounter_690_ = lean_ctor_get(v_mctx_679_, 3);
v_lDecls_691_ = lean_ctor_get(v_mctx_679_, 4);
v_decls_692_ = lean_ctor_get(v_mctx_679_, 5);
v_userNames_693_ = lean_ctor_get(v_mctx_679_, 6);
v_lAssignment_694_ = lean_ctor_get(v_mctx_679_, 7);
v_eAssignment_695_ = lean_ctor_get(v_mctx_679_, 8);
v_dAssignment_696_ = lean_ctor_get(v_mctx_679_, 9);
v_instanceTypedMVars_697_ = lean_ctor_get(v_mctx_679_, 10);
v_isSharedCheck_711_ = !lean_is_exclusive(v_mctx_679_);
if (v_isSharedCheck_711_ == 0)
{
v___x_699_ = v_mctx_679_;
v_isShared_700_ = v_isSharedCheck_711_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_instanceTypedMVars_697_);
lean_inc(v_dAssignment_696_);
lean_inc(v_eAssignment_695_);
lean_inc(v_lAssignment_694_);
lean_inc(v_userNames_693_);
lean_inc(v_decls_692_);
lean_inc(v_lDecls_691_);
lean_inc(v_mvarCounter_690_);
lean_inc(v_lmvarCounter_689_);
lean_inc(v_levelAssignDepth_688_);
lean_inc(v_depth_687_);
lean_dec(v_mctx_679_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_711_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_701_ = lean_box(0);
v___x_702_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(v_eAssignment_695_, v_mvarId_674_, v_val_675_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 8, v___x_702_);
v___x_704_ = v___x_699_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_depth_687_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_levelAssignDepth_688_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_lmvarCounter_689_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v_mvarCounter_690_);
lean_ctor_set(v_reuseFailAlloc_710_, 4, v_lDecls_691_);
lean_ctor_set(v_reuseFailAlloc_710_, 5, v_decls_692_);
lean_ctor_set(v_reuseFailAlloc_710_, 6, v_userNames_693_);
lean_ctor_set(v_reuseFailAlloc_710_, 7, v_lAssignment_694_);
lean_ctor_set(v_reuseFailAlloc_710_, 8, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_710_, 9, v_dAssignment_696_);
lean_ctor_set(v_reuseFailAlloc_710_, 10, v_instanceTypedMVars_697_);
v___x_704_ = v_reuseFailAlloc_710_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_706_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_704_);
v___x_706_ = v___x_685_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_cache_680_);
lean_ctor_set(v_reuseFailAlloc_709_, 2, v_zetaDeltaFVarIds_681_);
lean_ctor_set(v_reuseFailAlloc_709_, 3, v_postponed_682_);
lean_ctor_set(v_reuseFailAlloc_709_, 4, v_diag_683_);
v___x_706_ = v_reuseFailAlloc_709_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_st_ref_put(v___y_676_, v___x_706_);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_701_);
return v___x_708_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg___boxed(lean_object* v_mvarId_713_, lean_object* v_val_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(v_mvarId_713_, v_val_714_, v___y_715_);
lean_dec(v___y_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast___lam__0(lean_object* v_goal_718_, lean_object* v_targetNew_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; 
lean_inc(v_goal_718_);
v___x_725_ = l_Lean_MVarId_getTag(v_goal_718_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v___x_727_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_719_, v_a_726_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_737_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc_n(v_a_728_, 2);
lean_dec_ref_known(v___x_727_, 1);
v___x_729_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(v_goal_718_, v_a_728_, v___y_721_);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; 
v_unused_738_ = lean_ctor_get(v___x_729_, 0);
lean_dec(v_unused_738_);
v___x_731_ = v___x_729_;
v_isShared_732_ = v_isSharedCheck_737_;
goto v_resetjp_730_;
}
else
{
lean_dec(v___x_729_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_737_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_733_ = l_Lean_Expr_mvarId_x21(v_a_728_);
lean_dec(v_a_728_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_733_);
v___x_735_ = v___x_731_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec(v_goal_718_);
v_a_739_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_727_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_727_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec_ref(v_targetNew_719_);
lean_dec(v_goal_718_);
v_a_747_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_725_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_725_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast___lam__0___boxed(lean_object* v_goal_755_, lean_object* v_targetNew_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_MVarId_replaceTargetDefEqFast___lam__0(v_goal_755_, v_targetNew_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast(lean_object* v_goal_763_, lean_object* v_targetNew_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v___f_770_; lean_object* v___x_771_; 
lean_inc(v_goal_763_);
v___f_770_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetDefEqFast___lam__0___boxed), 7, 2);
lean_closure_set(v___f_770_, 0, v_goal_763_);
lean_closure_set(v___f_770_, 1, v_targetNew_764_);
v___x_771_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(v_goal_763_, v___f_770_, v_a_765_, v_a_766_, v_a_767_, v_a_768_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast___boxed(lean_object* v_goal_772_, lean_object* v_targetNew_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_772_, v_targetNew_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0(lean_object* v_mvarId_780_, lean_object* v_val_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(v_mvarId_780_, v_val_781_, v___y_783_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___boxed(lean_object* v_mvarId_788_, lean_object* v_val_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0(v_mvarId_788_, v_val_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0(lean_object* v_00_u03b2_796_, lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(v_x_797_, v_x_798_, v_x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_801_, lean_object* v_x_802_, size_t v_x_803_, size_t v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_x_802_, v_x_803_, v_x_804_, v_x_805_, v_x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_808_, lean_object* v_x_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
size_t v_x_1450__boxed_814_; size_t v_x_1451__boxed_815_; lean_object* v_res_816_; 
v_x_1450__boxed_814_ = lean_unbox_usize(v_x_810_);
lean_dec(v_x_810_);
v_x_1451__boxed_815_ = lean_unbox_usize(v_x_811_);
lean_dec(v_x_811_);
v_res_816_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2(v_00_u03b2_808_, v_x_809_, v_x_1450__boxed_814_, v_x_1451__boxed_815_, v_x_812_, v_x_813_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_817_, lean_object* v_n_818_, lean_object* v_k_819_, lean_object* v_v_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3___redArg(v_n_818_, v_k_819_, v_v_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_822_, size_t v_depth_823_, lean_object* v_keys_824_, lean_object* v_vals_825_, lean_object* v_heq_826_, lean_object* v_i_827_, lean_object* v_entries_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_823_, v_keys_824_, v_vals_825_, v_i_827_, v_entries_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_830_, lean_object* v_depth_831_, lean_object* v_keys_832_, lean_object* v_vals_833_, lean_object* v_heq_834_, lean_object* v_i_835_, lean_object* v_entries_836_){
_start:
{
size_t v_depth_boxed_837_; lean_object* v_res_838_; 
v_depth_boxed_837_ = lean_unbox_usize(v_depth_831_);
lean_dec(v_depth_831_);
v_res_838_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_830_, v_depth_boxed_837_, v_keys_832_, v_vals_833_, v_heq_834_, v_i_835_, v_entries_836_);
lean_dec_ref(v_vals_833_);
lean_dec_ref(v_keys_832_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_839_, lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_840_, v_x_841_, v_x_842_, v_x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon(lean_object* v_rule_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_expr_853_; lean_object* v_pattern_854_; lean_object* v_resultPos_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_879_; 
v_expr_853_ = lean_ctor_get(v_rule_845_, 0);
v_pattern_854_ = lean_ctor_get(v_rule_845_, 1);
v_resultPos_855_ = lean_ctor_get(v_rule_845_, 2);
v_isSharedCheck_879_ = !lean_is_exclusive(v_rule_845_);
if (v_isSharedCheck_879_ == 0)
{
v___x_857_ = v_rule_845_;
v_isShared_858_ = v_isSharedCheck_879_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_resultPos_855_);
lean_inc(v_pattern_854_);
lean_inc(v_expr_853_);
lean_dec(v_rule_845_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_879_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Meta_Sym_Pattern_shareCommon(v_pattern_854_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_870_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_870_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_870_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_870_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 1, v_a_860_);
v___x_865_ = v___x_857_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_expr_853_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_a_860_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_resultPos_855_);
v___x_865_ = v_reuseFailAlloc_869_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_867_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_865_);
v___x_867_ = v___x_862_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_del_object(v___x_857_);
lean_dec(v_resultPos_855_);
lean_dec_ref(v_expr_853_);
v_a_871_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_859_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_859_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon___boxed(lean_object* v_rule_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_rule_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(lean_object* v___y_889_, lean_object* v_mctx_890_, lean_object* v_cache_891_, lean_object* v_a_x3f_892_){
_start:
{
lean_object* v___x_894_; lean_object* v_zetaDeltaFVarIds_895_; lean_object* v_postponed_896_; lean_object* v_diag_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_907_; 
v___x_894_ = lean_st_ref_take(v___y_889_);
v_zetaDeltaFVarIds_895_ = lean_ctor_get(v___x_894_, 2);
v_postponed_896_ = lean_ctor_get(v___x_894_, 3);
v_diag_897_ = lean_ctor_get(v___x_894_, 4);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; lean_object* v_unused_909_; 
v_unused_908_ = lean_ctor_get(v___x_894_, 1);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v___x_894_, 0);
lean_dec(v_unused_909_);
v___x_899_ = v___x_894_;
v_isShared_900_ = v_isSharedCheck_907_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_diag_897_);
lean_inc(v_postponed_896_);
lean_inc(v_zetaDeltaFVarIds_895_);
lean_dec(v___x_894_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_907_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = lean_box(0);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 1, v_cache_891_);
lean_ctor_set(v___x_899_, 0, v_mctx_890_);
v___x_903_ = v___x_899_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_mctx_890_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_cache_891_);
lean_ctor_set(v_reuseFailAlloc_906_, 2, v_zetaDeltaFVarIds_895_);
lean_ctor_set(v_reuseFailAlloc_906_, 3, v_postponed_896_);
lean_ctor_set(v_reuseFailAlloc_906_, 4, v_diag_897_);
v___x_903_ = v_reuseFailAlloc_906_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_st_ref_put(v___y_889_, v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_901_);
return v___x_905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0___boxed(lean_object* v___y_910_, lean_object* v_mctx_911_, lean_object* v_cache_912_, lean_object* v_a_x3f_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_910_, v_mctx_911_, v_cache_912_, v_a_x3f_913_);
lean_dec(v_a_x3f_913_);
lean_dec(v___y_910_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(lean_object* v_x_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; lean_object* v_mctx_930_; lean_object* v___x_931_; lean_object* v_cache_932_; lean_object* v___x_933_; 
v___x_929_ = lean_st_ref_get(v___y_925_);
v_mctx_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc_ref(v_mctx_930_);
lean_dec(v___x_929_);
v___x_931_ = lean_st_ref_get(v___y_925_);
v_cache_932_ = lean_ctor_get(v___x_931_, 1);
lean_inc_ref(v_cache_932_);
lean_dec(v___x_931_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
lean_inc(v___y_919_);
lean_inc(v___y_918_);
lean_inc_ref(v___y_917_);
v___x_933_ = lean_apply_12(v_x_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, lean_box(0));
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_950_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_950_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_950_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_950_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
lean_inc(v_a_934_);
if (v_isShared_937_ == 0)
{
lean_ctor_set_tag(v___x_936_, 1);
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_949_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
v___x_940_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_925_, v_mctx_930_, v_cache_932_, v___x_939_);
lean_dec_ref(v___x_939_);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; 
v_unused_948_ = lean_ctor_get(v___x_940_, 0);
lean_dec(v_unused_948_);
v___x_942_ = v___x_940_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_dec(v___x_940_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v_a_934_);
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_934_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
v_a_951_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_933_, 1);
v___x_952_ = lean_box(0);
v___x_953_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_925_, v_mctx_930_, v_cache_932_, v___x_952_);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; 
v_unused_961_ = lean_ctor_get(v___x_953_, 0);
lean_dec(v_unused_961_);
v___x_955_ = v___x_953_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_dec(v___x_953_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set_tag(v___x_955_, 1);
lean_ctor_set(v___x_955_, 0, v_a_951_);
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_951_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___boxed(lean_object* v_x_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(lean_object* v_00_u03b1_976_, lean_object* v_x_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___boxed(lean_object* v_00_u03b1_991_, lean_object* v_x_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(v_00_u03b1_991_, v_x_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(lean_object* v_a_1006_, lean_object* v___x_1007_, lean_object* v_rule_1008_, uint8_t v___x_1009_, uint8_t v_debug_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1006_, v___x_1007_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v___x_1025_ = l_Lean_Expr_mvarId_x21(v_a_1024_);
lean_dec(v_a_1024_);
v___x_1026_ = l_Lean_Meta_Sym_BackwardRule_apply(v___x_1025_, v_rule_1008_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1039_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1039_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1039_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
if (lean_obj_tag(v_a_1027_) == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_box(v___x_1009_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1031_);
v___x_1033_ = v___x_1029_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
else
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
lean_dec_ref_known(v_a_1027_, 1);
v___x_1035_ = lean_box(v_debug_1010_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1035_);
v___x_1037_ = v___x_1029_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
v_a_1040_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1026_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1026_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec_ref(v_rule_1008_);
v_a_1048_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1023_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1023_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed(lean_object** _args){
lean_object* v_a_1056_ = _args[0];
lean_object* v___x_1057_ = _args[1];
lean_object* v_rule_1058_ = _args[2];
lean_object* v___x_1059_ = _args[3];
lean_object* v_debug_1060_ = _args[4];
lean_object* v___y_1061_ = _args[5];
lean_object* v___y_1062_ = _args[6];
lean_object* v___y_1063_ = _args[7];
lean_object* v___y_1064_ = _args[8];
lean_object* v___y_1065_ = _args[9];
lean_object* v___y_1066_ = _args[10];
lean_object* v___y_1067_ = _args[11];
lean_object* v___y_1068_ = _args[12];
lean_object* v___y_1069_ = _args[13];
lean_object* v___y_1070_ = _args[14];
lean_object* v___y_1071_ = _args[15];
lean_object* v___y_1072_ = _args[16];
_start:
{
uint8_t v___x_29547__boxed_1073_; uint8_t v_debug_boxed_1074_; lean_object* v_res_1075_; 
v___x_29547__boxed_1073_ = lean_unbox(v___x_1059_);
v_debug_boxed_1074_ = lean_unbox(v_debug_1060_);
v_res_1075_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(v_a_1056_, v___x_1057_, v_rule_1058_, v___x_29547__boxed_1073_, v_debug_boxed_1074_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(lean_object* v_msg_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_ref_1082_; lean_object* v___x_1083_; lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1092_; 
v_ref_1082_ = lean_ctor_get(v___y_1079_, 2);
v___x_1083_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4_spec__4(v_msg_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1092_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1092_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1090_; 
lean_inc(v_ref_1082_);
v___x_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1088_, 0, v_ref_1082_);
lean_ctor_set(v___x_1088_, 1, v_a_1084_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set_tag(v___x_1086_, 1);
lean_ctor_set(v___x_1086_, 0, v___x_1088_);
v___x_1090_ = v___x_1086_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg___boxed(lean_object* v_msg_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1099_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0));
v___x_1102_ = l_Lean_stringToMessageData(v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2));
v___x_1105_ = l_Lean_stringToMessageData(v___x_1104_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4));
v___x_1108_ = l_Lean_stringToMessageData(v___x_1107_);
return v___x_1108_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6));
v___x_1111_ = l_Lean_stringToMessageData(v___x_1110_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8));
v___x_1114_ = l_Lean_stringToMessageData(v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object* v_rule_1115_, lean_object* v_goal_1116_, lean_object* v_ruleDesc_x3f_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v___x_1130_; 
lean_inc_ref(v_rule_1115_);
lean_inc(v_goal_1116_);
v___x_1130_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_1116_, v_rule_1115_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
if (lean_obj_tag(v_a_1131_) == 0)
{
uint8_t v_debug_1132_; 
v_debug_1132_ = lean_ctor_get_uint8(v_a_1118_, sizeof(void*)*6 + 2);
if (v_debug_1132_ == 0)
{
lean_dec(v_ruleDesc_x3f_1117_);
lean_dec(v_goal_1116_);
lean_dec_ref(v_rule_1115_);
return v___x_1130_;
}
else
{
lean_object* v___x_1133_; 
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v___x_1133_ = l_Lean_MVarId_getType(v_goal_1116_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1135_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc_n(v_a_1134_, 2);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1135_ = l_Lean_Meta_Sym_unfoldReducible(v_a_1134_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1198_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1198_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1198_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_expr_eqv(v_a_1136_, v_a_1134_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___f_1144_; lean_object* v___x_1145_; 
lean_del_object(v___x_1138_);
v___x_1141_ = lean_box(0);
v___x_1142_ = lean_box(v___x_1140_);
v___x_1143_ = lean_box(v_debug_1132_);
lean_inc_ref(v_rule_1115_);
lean_inc(v_a_1136_);
v___f_1144_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed), 17, 5);
lean_closure_set(v___f_1144_, 0, v_a_1136_);
lean_closure_set(v___f_1144_, 1, v___x_1141_);
lean_closure_set(v___f_1144_, 2, v_rule_1115_);
lean_closure_set(v___f_1144_, 3, v___x_1142_);
lean_closure_set(v___f_1144_, 4, v___x_1143_);
v___x_1145_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v___f_1144_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1186_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1186_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1186_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___y_1151_; uint8_t v___x_1173_; 
v___x_1173_ = lean_unbox(v_a_1146_);
lean_dec(v_a_1146_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1175_; 
lean_dec(v_a_1136_);
lean_dec(v_a_1134_);
lean_dec(v_ruleDesc_x3f_1117_);
lean_dec_ref(v_rule_1115_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_a_1131_);
v___x_1175_ = v___x_1148_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1131_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
else
{
lean_del_object(v___x_1148_);
if (lean_obj_tag(v_ruleDesc_x3f_1117_) == 0)
{
lean_object* v_expr_1177_; lean_object* v___x_1178_; 
v_expr_1177_ = lean_ctor_get(v_rule_1115_, 0);
lean_inc_ref(v_expr_1177_);
lean_dec_ref(v_rule_1115_);
v___x_1178_ = l_Lean_Expr_getAppFn(v_expr_1177_);
lean_dec_ref(v_expr_1177_);
if (lean_obj_tag(v___x_1178_) == 4)
{
lean_object* v_declName_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v_declName_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_declName_1179_);
lean_dec_ref_known(v___x_1178_, 2);
v___x_1180_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3, &l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3);
v___x_1181_ = l_Lean_MessageData_ofConstName(v_declName_1179_, v___x_1140_);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
lean_ctor_set(v___x_1183_, 1, v___x_1180_);
v___y_1151_ = v___x_1183_;
goto v___jp_1150_;
}
else
{
lean_object* v___x_1184_; 
lean_dec_ref(v___x_1178_);
v___x_1184_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9);
v___y_1151_ = v___x_1184_;
goto v___jp_1150_;
}
}
else
{
lean_object* v_val_1185_; 
lean_dec_ref(v_rule_1115_);
v_val_1185_ = lean_ctor_get(v_ruleDesc_x3f_1117_, 0);
lean_inc(v_val_1185_);
lean_dec_ref_known(v_ruleDesc_x3f_1117_, 1);
v___y_1151_ = v_val_1185_;
goto v___jp_1150_;
}
}
v___jp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v___x_1152_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v___y_1151_);
v___x_1154_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = l_Lean_indentExpr(v_a_1134_);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_indentExpr(v_a_1136_);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1161_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_1163_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec(v_a_1136_);
lean_dec(v_a_1134_);
lean_dec(v_ruleDesc_x3f_1117_);
lean_dec_ref(v_rule_1115_);
v_a_1187_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1145_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1145_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
else
{
lean_object* v___x_1196_; 
lean_dec(v_a_1136_);
lean_dec(v_a_1134_);
lean_dec(v_ruleDesc_x3f_1117_);
lean_dec_ref(v_rule_1115_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v_a_1131_);
v___x_1196_ = v___x_1138_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1131_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec(v_a_1134_);
lean_dec(v_ruleDesc_x3f_1117_);
lean_dec_ref(v_rule_1115_);
v_a_1199_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1135_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1135_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec(v_ruleDesc_x3f_1117_);
lean_dec_ref(v_rule_1115_);
v_a_1207_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1133_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1133_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
else
{
lean_dec(v_ruleDesc_x3f_1117_);
lean_dec(v_goal_1116_);
lean_dec_ref(v_rule_1115_);
return v___x_1130_;
}
}
else
{
lean_dec(v_ruleDesc_x3f_1117_);
lean_dec(v_goal_1116_);
lean_dec_ref(v_rule_1115_);
return v___x_1130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___boxed(lean_object* v_rule_1215_, lean_object* v_goal_1216_, lean_object* v_ruleDesc_x3f_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_1215_, v_goal_1216_, v_ruleDesc_x3f_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(lean_object* v_00_u03b1_1231_, lean_object* v_msg_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_1232_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___boxed(lean_object* v_00_u03b1_1246_, lean_object* v_msg_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(v_00_u03b1_1246_, v_msg_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(lean_object* v_goal_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
uint8_t v_internalize_1273_; 
v_internalize_1273_ = lean_ctor_get_uint8(v_a_1262_, sizeof(void*)*6 + 3);
if (v_internalize_1273_ == 0)
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_goal_1261_);
return v___x_1274_;
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_box(0);
v___x_1276_ = l_Lean_Meta_Grind_processHypotheses(v_goal_1261_, v___x_1275_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
return v___x_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg___boxed(lean_object* v_goal_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses(lean_object* v_goal_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_1290_, v_a_1291_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___boxed(lean_object* v_goal_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_Elab_Tactic_VCGen_processHypotheses(v_goal_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
return v_res_1317_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_VCGen_isProgramName(lean_object* v_n_1318_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = l_Lean_Name_hasMacroScopes(v_n_1318_);
if (v___x_1319_ == 0)
{
uint8_t v___x_1320_; 
v___x_1320_ = l_Lean_Name_isImplementationDetail(v_n_1318_);
if (v___x_1320_ == 0)
{
uint8_t v___x_1321_; 
v___x_1321_ = 1;
return v___x_1321_;
}
else
{
return v___x_1319_;
}
}
else
{
uint8_t v___x_1322_; 
v___x_1322_ = 0;
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_isProgramName___boxed(lean_object* v_n_1323_){
_start:
{
uint8_t v_res_1324_; lean_object* v_r_1325_; 
v_res_1324_ = l_Lean_Elab_Tactic_VCGen_isProgramName(v_n_1323_);
lean_dec(v_n_1323_);
v_r_1325_ = lean_box(v_res_1324_);
return v_r_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_numBindersToIntro(lean_object* v_x_1326_){
_start:
{
switch(lean_obj_tag(v_x_1326_))
{
case 7:
{
lean_object* v_body_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v_body_1327_ = lean_ctor_get(v_x_1326_, 2);
v___x_1328_ = l_Lean_Elab_Tactic_VCGen_numBindersToIntro(v_body_1327_);
v___x_1329_ = lean_unsigned_to_nat(1u);
v___x_1330_ = lean_nat_add(v___x_1328_, v___x_1329_);
lean_dec(v___x_1328_);
return v___x_1330_;
}
case 8:
{
lean_object* v_body_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v_body_1331_ = lean_ctor_get(v_x_1326_, 3);
v___x_1332_ = l_Lean_Elab_Tactic_VCGen_numBindersToIntro(v_body_1331_);
v___x_1333_ = lean_unsigned_to_nat(1u);
v___x_1334_ = lean_nat_add(v___x_1332_, v___x_1333_);
lean_dec(v___x_1332_);
return v___x_1334_;
}
default: 
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_unsigned_to_nat(0u);
return v___x_1335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_numBindersToIntro___boxed(lean_object* v_x_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_Elab_Tactic_VCGen_numBindersToIntro(v_x_1336_);
lean_dec_ref(v_x_1336_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_introsHygienicN_collectBinders(lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_zero_1341_; uint8_t v_isZero_1342_; 
v_zero_1341_ = lean_unsigned_to_nat(0u);
v_isZero_1342_ = lean_nat_dec_eq(v_a_1338_, v_zero_1341_);
if (v_isZero_1342_ == 1)
{
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
return v_a_1340_;
}
else
{
lean_object* v_one_1343_; lean_object* v_n_1344_; 
v_one_1343_ = lean_unsigned_to_nat(1u);
v_n_1344_ = lean_nat_sub(v_a_1338_, v_one_1343_);
lean_dec(v_a_1338_);
switch(lean_obj_tag(v_a_1339_))
{
case 7:
{
lean_object* v_binderName_1345_; lean_object* v_body_1346_; lean_object* v___x_1347_; 
v_binderName_1345_ = lean_ctor_get(v_a_1339_, 0);
lean_inc(v_binderName_1345_);
v_body_1346_ = lean_ctor_get(v_a_1339_, 2);
lean_inc_ref(v_body_1346_);
lean_dec_ref_known(v_a_1339_, 3);
v___x_1347_ = lean_array_push(v_a_1340_, v_binderName_1345_);
v_a_1338_ = v_n_1344_;
v_a_1339_ = v_body_1346_;
v_a_1340_ = v___x_1347_;
goto _start;
}
case 8:
{
lean_object* v_declName_1349_; lean_object* v_body_1350_; lean_object* v___x_1351_; 
v_declName_1349_ = lean_ctor_get(v_a_1339_, 0);
lean_inc(v_declName_1349_);
v_body_1350_ = lean_ctor_get(v_a_1339_, 3);
lean_inc_ref(v_body_1350_);
lean_dec_ref_known(v_a_1339_, 4);
v___x_1351_ = lean_array_push(v_a_1340_, v_declName_1349_);
v_a_1338_ = v_n_1344_;
v_a_1339_ = v_body_1350_;
v_a_1340_ = v___x_1351_;
goto _start;
}
default: 
{
lean_dec(v_n_1344_);
lean_dec_ref(v_a_1339_);
return v_a_1340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0(lean_object* v_x_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1366_; 
lean_inc(v___y_1360_);
lean_inc_ref(v___y_1359_);
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
v___x_1366_ = lean_apply_12(v_x_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, lean_box(0));
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0___boxed(lean_object* v_x_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0(v_x_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(lean_object* v_mvarId_1381_, lean_object* v_x_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v___f_1395_; lean_object* v___x_1396_; 
lean_inc(v___y_1389_);
lean_inc_ref(v___y_1388_);
lean_inc(v___y_1387_);
lean_inc_ref(v___y_1386_);
lean_inc(v___y_1385_);
lean_inc(v___y_1384_);
lean_inc_ref(v___y_1383_);
v___f_1395_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1395_, 0, v_x_1382_);
lean_closure_set(v___f_1395_, 1, v___y_1383_);
lean_closure_set(v___f_1395_, 2, v___y_1384_);
lean_closure_set(v___f_1395_, 3, v___y_1385_);
lean_closure_set(v___f_1395_, 4, v___y_1386_);
lean_closure_set(v___f_1395_, 5, v___y_1387_);
lean_closure_set(v___f_1395_, 6, v___y_1388_);
lean_closure_set(v___f_1395_, 7, v___y_1389_);
v___x_1396_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1381_, v___f_1395_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
if (lean_obj_tag(v___x_1396_) == 0)
{
return v___x_1396_;
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___boxed(lean_object* v_mvarId_1405_, lean_object* v_x_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_mvarId_1405_, v_x_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1(lean_object* v_00_u03b1_1420_, lean_object* v_mvarId_1421_, lean_object* v_x_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_mvarId_1421_, v_x_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___boxed(lean_object* v_00_u03b1_1436_, lean_object* v_mvarId_1437_, lean_object* v_x_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1(v_00_u03b1_1436_, v_mvarId_1437_, v_x_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(lean_object* v_as_1452_, size_t v_sz_1453_, size_t v_i_1454_, lean_object* v_b_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
uint8_t v___x_1460_; 
v___x_1460_ = lean_usize_dec_lt(v_i_1454_, v_sz_1453_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1461_, 0, v_b_1455_);
return v___x_1461_;
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1463_; 
v_a_1462_ = lean_array_uget_borrowed(v_as_1452_, v_i_1454_);
lean_inc(v_a_1462_);
v___x_1463_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_a_1462_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; size_t v___x_1466_; size_t v___x_1467_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
v___x_1465_ = lean_array_push(v_b_1455_, v_a_1464_);
v___x_1466_ = ((size_t)1ULL);
v___x_1467_ = lean_usize_add(v_i_1454_, v___x_1466_);
v_i_1454_ = v___x_1467_;
v_b_1455_ = v___x_1465_;
goto _start;
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec_ref(v_b_1455_);
v_a_1469_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1463_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1463_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg___boxed(lean_object* v_as_1477_, lean_object* v_sz_1478_, lean_object* v_i_1479_, lean_object* v_b_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
size_t v_sz_boxed_1485_; size_t v_i_boxed_1486_; lean_object* v_res_1487_; 
v_sz_boxed_1485_ = lean_unbox_usize(v_sz_1478_);
lean_dec(v_sz_1478_);
v_i_boxed_1486_ = lean_unbox_usize(v_i_1479_);
lean_dec(v_i_1479_);
v_res_1487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(v_as_1477_, v_sz_boxed_1485_, v_i_boxed_1486_, v_b_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec_ref(v_as_1477_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0(lean_object* v_goal_1490_, lean_object* v_n_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v___x_1504_; 
lean_inc(v_goal_1490_);
v___x_1504_ = l_Lean_MVarId_getType(v_goal_1490_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1551_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1507_ = v___x_1504_;
v_isShared_1508_ = v_isSharedCheck_1551_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1504_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1551_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v_names_1510_; lean_object* v_binderNames_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1509_ = lean_unsigned_to_nat(0u);
v_names_1510_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___closed__0));
v_binderNames_1511_ = l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_introsHygienicN_collectBinders(v_n_1491_, v_a_1505_, v_names_1510_);
v___x_1512_ = lean_array_get_size(v_binderNames_1511_);
v___x_1513_ = lean_nat_dec_eq(v___x_1512_, v___x_1509_);
if (v___x_1513_ == 0)
{
uint8_t v___x_1514_; size_t v_sz_1515_; size_t v___x_1516_; lean_object* v___x_1517_; 
lean_del_object(v___x_1507_);
v___x_1514_ = 1;
v_sz_1515_ = lean_array_size(v_binderNames_1511_);
v___x_1516_ = ((size_t)0ULL);
v___x_1517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(v_binderNames_1511_, v_sz_1515_, v___x_1516_, v_names_1510_, v___y_1499_, v___y_1501_, v___y_1502_);
lean_dec_ref(v_binderNames_1511_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
lean_inc(v_goal_1490_);
v___x_1519_ = l_Lean_Meta_Sym_intros(v_goal_1490_, v_a_1518_, v___x_1514_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1531_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1522_ = v___x_1519_;
v_isShared_1523_ = v_isSharedCheck_1531_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1519_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1531_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
if (lean_obj_tag(v_a_1520_) == 1)
{
lean_object* v_mvarId_1524_; lean_object* v___x_1526_; 
lean_dec(v_goal_1490_);
v_mvarId_1524_ = lean_ctor_get(v_a_1520_, 1);
lean_inc(v_mvarId_1524_);
lean_dec_ref_known(v_a_1520_, 2);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v_mvarId_1524_);
v___x_1526_ = v___x_1522_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_mvarId_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
else
{
lean_object* v___x_1529_; 
lean_dec(v_a_1520_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v_goal_1490_);
v___x_1529_ = v___x_1522_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_goal_1490_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v_goal_1490_);
v_a_1532_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1519_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1519_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
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
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
lean_dec(v_goal_1490_);
v_a_1540_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1517_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1517_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
else
{
lean_object* v___x_1549_; 
lean_dec_ref(v_binderNames_1511_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v_goal_1490_);
v___x_1549_ = v___x_1507_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_goal_1490_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec(v_n_1491_);
lean_dec(v_goal_1490_);
v_a_1552_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1504_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1504_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___boxed(lean_object* v_goal_1560_, lean_object* v_n_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0(v_goal_1560_, v_n_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN(lean_object* v_goal_1575_, lean_object* v_n_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v___f_1589_; lean_object* v___x_1590_; 
lean_inc(v_goal_1575_);
v___f_1589_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___boxed), 14, 2);
lean_closure_set(v___f_1589_, 0, v_goal_1575_);
lean_closure_set(v___f_1589_, 1, v_n_1576_);
v___x_1590_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_goal_1575_, v___f_1589_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN___boxed(lean_object* v_goal_1591_, lean_object* v_n_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN(v_goal_1591_, v_n_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
lean_dec(v_a_1595_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0(lean_object* v_as_1606_, size_t v_sz_1607_, size_t v_i_1608_, lean_object* v_b_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(v_as_1606_, v_sz_1607_, v_i_1608_, v_b_1609_, v___y_1617_, v___y_1619_, v___y_1620_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___boxed(lean_object* v_as_1623_, lean_object* v_sz_1624_, lean_object* v_i_1625_, lean_object* v_b_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
size_t v_sz_boxed_1639_; size_t v_i_boxed_1640_; lean_object* v_res_1641_; 
v_sz_boxed_1639_ = lean_unbox_usize(v_sz_1624_);
lean_dec(v_sz_1624_);
v_i_boxed_1640_ = lean_unbox_usize(v_i_1625_);
lean_dec(v_i_1625_);
v_res_1641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0(v_as_1623_, v_sz_boxed_1639_, v_i_boxed_1640_, v_b_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec_ref(v_as_1623_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go_spec__0(lean_object* v_x_1642_, uint8_t v_bi_1643_, lean_object* v_t_1644_, lean_object* v_b_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v___y_1654_; lean_object* v___x_1657_; uint8_t v_debug_1658_; 
v___x_1657_ = lean_st_ref_get(v___y_1647_);
v_debug_1658_ = lean_ctor_get_uint8(v___x_1657_, sizeof(void*)*13);
lean_dec(v___x_1657_);
if (v_debug_1658_ == 0)
{
v___y_1654_ = v___y_1647_;
goto v___jp_1653_;
}
else
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1644_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v___x_1660_; 
lean_dec_ref_known(v___x_1659_, 1);
v___x_1660_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_dec_ref_known(v___x_1660_, 1);
v___y_1654_ = v___y_1647_;
goto v___jp_1653_;
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec_ref(v_b_1645_);
lean_dec_ref(v_t_1644_);
lean_dec(v_x_1642_);
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
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
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec_ref(v_b_1645_);
lean_dec_ref(v_t_1644_);
lean_dec(v_x_1642_);
v_a_1669_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1659_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1659_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
v___jp_1653_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = l_Lean_Expr_forallE___override(v_x_1642_, v_t_1644_, v_b_1645_, v_bi_1643_);
v___x_1656_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1655_, v___y_1654_);
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go_spec__0___boxed(lean_object* v_x_1677_, lean_object* v_bi_1678_, lean_object* v_t_1679_, lean_object* v_b_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
uint8_t v_bi_boxed_1688_; lean_object* v_res_1689_; 
v_bi_boxed_1688_ = lean_unbox(v_bi_1678_);
v_res_1689_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go_spec__0(v_x_1677_, v_bi_boxed_1688_, v_t_1679_, v_b_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go_spec__1(lean_object* v_x_1690_, lean_object* v_t_1691_, lean_object* v_v_1692_, lean_object* v_b_1693_, uint8_t v_nondep_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___y_1703_; lean_object* v___x_1706_; uint8_t v_debug_1707_; 
v___x_1706_ = lean_st_ref_get(v___y_1696_);
v_debug_1707_ = lean_ctor_get_uint8(v___x_1706_, sizeof(void*)*13);
lean_dec(v___x_1706_);
if (v_debug_1707_ == 0)
{
v___y_1703_ = v___y_1696_;
goto v___jp_1702_;
}
else
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1691_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v___x_1709_; 
lean_dec_ref_known(v___x_1708_, 1);
v___x_1709_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_v_1692_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v___x_1710_; 
lean_dec_ref_known(v___x_1709_, 1);
v___x_1710_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1693_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_dec_ref_known(v___x_1710_, 1);
v___y_1703_ = v___y_1696_;
goto v___jp_1702_;
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec_ref(v_b_1693_);
lean_dec_ref(v_v_1692_);
lean_dec_ref(v_t_1691_);
lean_dec(v_x_1690_);
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec_ref(v_b_1693_);
lean_dec_ref(v_v_1692_);
lean_dec_ref(v_t_1691_);
lean_dec(v_x_1690_);
v_a_1719_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1709_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1709_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec_ref(v_b_1693_);
lean_dec_ref(v_v_1692_);
lean_dec_ref(v_t_1691_);
lean_dec(v_x_1690_);
v_a_1727_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1708_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1708_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
v___jp_1702_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = l_Lean_Expr_letE___override(v_x_1690_, v_t_1691_, v_v_1692_, v_b_1693_, v_nondep_1694_);
v___x_1705_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1704_, v___y_1703_);
return v___x_1705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go_spec__1___boxed(lean_object* v_x_1735_, lean_object* v_t_1736_, lean_object* v_v_1737_, lean_object* v_b_1738_, lean_object* v_nondep_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
uint8_t v_nondep_boxed_1747_; lean_object* v_res_1748_; 
v_nondep_boxed_1747_ = lean_unbox(v_nondep_1739_);
v_res_1748_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go_spec__1(v_x_1735_, v_t_1736_, v_v_1737_, v_b_1738_, v_nondep_boxed_1747_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go(lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
switch(lean_obj_tag(v_a_1749_))
{
case 7:
{
lean_object* v_binderName_1757_; lean_object* v_binderType_1758_; lean_object* v_body_1759_; uint8_t v_binderInfo_1760_; lean_object* v___x_1761_; 
v_binderName_1757_ = lean_ctor_get(v_a_1749_, 0);
v_binderType_1758_ = lean_ctor_get(v_a_1749_, 1);
v_body_1759_ = lean_ctor_get(v_a_1749_, 2);
v_binderInfo_1760_ = lean_ctor_get_uint8(v_a_1749_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1758_);
v___x_1761_ = l_Lean_Meta_Sym_instantiateMVarsS(v_binderType_1758_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
lean_inc_ref(v_body_1759_);
v___x_1763_ = l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go(v_body_1759_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1779_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1766_ = v___x_1763_;
v_isShared_1767_ = v_isSharedCheck_1779_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1763_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1779_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
size_t v___x_1768_; size_t v___x_1769_; uint8_t v___x_1770_; 
v___x_1768_ = lean_ptr_addr(v_binderType_1758_);
v___x_1769_ = lean_ptr_addr(v_a_1762_);
v___x_1770_ = lean_usize_dec_eq(v___x_1768_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; 
lean_inc(v_binderName_1757_);
lean_del_object(v___x_1766_);
lean_dec_ref_known(v_a_1749_, 3);
v___x_1771_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go_spec__0(v_binderName_1757_, v_binderInfo_1760_, v_a_1762_, v_a_1764_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
return v___x_1771_;
}
else
{
size_t v___x_1772_; size_t v___x_1773_; uint8_t v___x_1774_; 
v___x_1772_ = lean_ptr_addr(v_body_1759_);
v___x_1773_ = lean_ptr_addr(v_a_1764_);
v___x_1774_ = lean_usize_dec_eq(v___x_1772_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; 
lean_inc(v_binderName_1757_);
lean_del_object(v___x_1766_);
lean_dec_ref_known(v_a_1749_, 3);
v___x_1775_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go_spec__0(v_binderName_1757_, v_binderInfo_1760_, v_a_1762_, v_a_1764_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
return v___x_1775_;
}
else
{
lean_object* v___x_1777_; 
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v_a_1749_);
v___x_1777_ = v___x_1766_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1749_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
else
{
lean_dec(v_a_1762_);
lean_dec_ref_known(v_a_1749_, 3);
return v___x_1763_;
}
}
else
{
lean_dec_ref_known(v_a_1749_, 3);
return v___x_1761_;
}
}
case 8:
{
lean_object* v_declName_1780_; lean_object* v_type_1781_; lean_object* v_value_1782_; lean_object* v_body_1783_; uint8_t v_nondep_1784_; lean_object* v___x_1785_; 
v_declName_1780_ = lean_ctor_get(v_a_1749_, 0);
v_type_1781_ = lean_ctor_get(v_a_1749_, 1);
v_value_1782_ = lean_ctor_get(v_a_1749_, 2);
v_body_1783_ = lean_ctor_get(v_a_1749_, 3);
v_nondep_1784_ = lean_ctor_get_uint8(v_a_1749_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1781_);
v___x_1785_ = l_Lean_Meta_Sym_instantiateMVarsS(v_type_1781_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1787_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref_known(v___x_1785_, 1);
lean_inc_ref(v_body_1783_);
v___x_1787_ = l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go(v_body_1783_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1807_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1807_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1807_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
size_t v___x_1792_; size_t v___x_1793_; uint8_t v___x_1794_; 
v___x_1792_ = lean_ptr_addr(v_type_1781_);
v___x_1793_ = lean_ptr_addr(v_a_1786_);
v___x_1794_ = lean_usize_dec_eq(v___x_1792_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; 
lean_inc_ref(v_value_1782_);
lean_inc(v_declName_1780_);
lean_del_object(v___x_1790_);
lean_dec_ref_known(v_a_1749_, 4);
v___x_1795_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go_spec__1(v_declName_1780_, v_a_1786_, v_value_1782_, v_a_1788_, v_nondep_1784_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
return v___x_1795_;
}
else
{
size_t v___x_1796_; size_t v___x_1797_; uint8_t v___x_1798_; 
v___x_1796_ = lean_ptr_addr(v_value_1782_);
v___x_1797_ = lean_ptr_addr(v_value_1782_);
v___x_1798_ = lean_usize_dec_eq(v___x_1796_, v___x_1797_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; 
lean_inc_ref(v_value_1782_);
lean_inc(v_declName_1780_);
lean_del_object(v___x_1790_);
lean_dec_ref_known(v_a_1749_, 4);
v___x_1799_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go_spec__1(v_declName_1780_, v_a_1786_, v_value_1782_, v_a_1788_, v_nondep_1784_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
return v___x_1799_;
}
else
{
size_t v___x_1800_; size_t v___x_1801_; uint8_t v___x_1802_; 
v___x_1800_ = lean_ptr_addr(v_body_1783_);
v___x_1801_ = lean_ptr_addr(v_a_1788_);
v___x_1802_ = lean_usize_dec_eq(v___x_1800_, v___x_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; 
lean_inc_ref(v_value_1782_);
lean_inc(v_declName_1780_);
lean_del_object(v___x_1790_);
lean_dec_ref_known(v_a_1749_, 4);
v___x_1803_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go_spec__1(v_declName_1780_, v_a_1786_, v_value_1782_, v_a_1788_, v_nondep_1784_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
return v___x_1803_;
}
else
{
lean_object* v___x_1805_; 
lean_dec(v_a_1788_);
lean_dec(v_a_1786_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v_a_1749_);
v___x_1805_ = v___x_1790_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1749_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1786_);
lean_dec_ref_known(v_a_1749_, 4);
return v___x_1787_;
}
}
else
{
lean_dec_ref_known(v_a_1749_, 4);
return v___x_1785_;
}
}
default: 
{
lean_object* v___x_1808_; 
v___x_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1808_, 0, v_a_1749_);
return v___x_1808_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go___boxed(lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go(v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instantiateBinderDomains___redArg(lean_object* v_goal_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v___x_1826_; 
lean_inc(v_goal_1818_);
v___x_1826_ = l_Lean_MVarId_getType(v_goal_1818_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1828_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc_n(v_a_1827_, 2);
lean_dec_ref_known(v___x_1826_, 1);
v___x_1828_ = l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_instantiateBinderDomains_go(v_a_1827_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1840_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1840_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1840_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
size_t v___x_1833_; size_t v___x_1834_; uint8_t v___x_1835_; 
v___x_1833_ = lean_ptr_addr(v_a_1829_);
v___x_1834_ = lean_ptr_addr(v_a_1827_);
lean_dec(v_a_1827_);
v___x_1835_ = lean_usize_dec_eq(v___x_1833_, v___x_1834_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; 
lean_del_object(v___x_1831_);
v___x_1836_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_1818_, v_a_1829_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
return v___x_1836_;
}
else
{
lean_object* v___x_1838_; 
lean_dec(v_a_1829_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v_goal_1818_);
v___x_1838_ = v___x_1831_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_goal_1818_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec(v_a_1827_);
lean_dec(v_goal_1818_);
v_a_1841_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1828_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1828_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_goal_1818_);
v_a_1849_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1826_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1826_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instantiateBinderDomains___redArg___boxed(lean_object* v_goal_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_Elab_Tactic_VCGen_instantiateBinderDomains___redArg(v_goal_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instantiateBinderDomains(lean_object* v_goal_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_Elab_Tactic_VCGen_instantiateBinderDomains___redArg(v_goal_1866_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instantiateBinderDomains___boxed(lean_object* v_goal_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_Elab_Tactic_VCGen_instantiateBinderDomains(v_goal_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec(v_a_1883_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic(lean_object* v_goal_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_Elab_Tactic_VCGen_instantiateBinderDomains___redArg(v_goal_1894_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1909_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc_n(v_a_1908_, 2);
lean_dec_ref_known(v___x_1907_, 1);
v___x_1909_ = l_Lean_MVarId_getType(v_a_1908_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1909_, 1);
v___x_1911_ = l_Lean_Elab_Tactic_VCGen_numBindersToIntro(v_a_1910_);
lean_dec(v_a_1910_);
v___x_1912_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN(v_a_1908_, v___x_1911_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
return v___x_1912_;
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec(v_a_1908_);
v_a_1913_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1909_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1909_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
else
{
return v___x_1907_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic___boxed(lean_object* v_goal_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_Elab_Tactic_VCGen_introsHygienic(v_goal_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
lean_dec(v_a_1928_);
lean_dec_ref(v_a_1927_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
lean_dec(v_a_1924_);
lean_dec(v_a_1923_);
lean_dec_ref(v_a_1922_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(lean_object* v_goal_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v_simpMethods_1945_; 
v_simpMethods_1945_ = lean_ctor_get(v_a_1936_, 3);
if (lean_obj_tag(v_simpMethods_1945_) == 1)
{
lean_object* v_val_1946_; lean_object* v___x_1947_; 
v_val_1946_ = lean_ctor_get(v_simpMethods_1945_, 0);
lean_inc(v_goal_1935_);
v___x_1947_ = l_Lean_MVarId_getType(v_goal_1935_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1947_, 1);
v___x_1949_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpTelescope___boxed), 11, 1);
lean_closure_set(v___x_1949_, 0, v_a_1948_);
lean_inc(v_val_1946_);
v___x_1950_ = l_Lean_Elab_Tactic_VCGen_runSimp___redArg(v_val_1946_, v___x_1949_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1952_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref_known(v___x_1950_, 1);
v___x_1952_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_a_1951_, v_goal_1935_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
return v___x_1952_;
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec(v_goal_1935_);
v_a_1953_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1950_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1950_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec(v_goal_1935_);
v_a_1961_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1947_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1947_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
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
lean_object* v___x_1969_; lean_object* v___x_1970_; 
lean_dec(v_goal_1935_);
v___x_1969_ = lean_box(0);
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___boxed(lean_object* v_goal_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(v_goal_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope(lean_object* v_goal_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(v_goal_1982_, v_a_1983_, v_a_1984_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___boxed(lean_object* v_goal_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope(v_goal_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
lean_dec(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
return v_res_2009_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__8));
v___x_2012_ = l_Lean_stringToMessageData(v___x_2011_);
return v___x_2012_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6(void){
_start:
{
uint8_t v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2020_ = 0;
v___x_2021_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__5));
v___x_2022_ = l_Lean_MessageData_ofConstName(v___x_2021_, v___x_2020_);
return v___x_2022_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__0));
v___x_2025_ = l_Lean_stringToMessageData(v___x_2024_);
return v___x_2025_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2026_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6);
v___x_2027_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1);
v___x_2028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
lean_ctor_set(v___x_2028_, 1, v___x_2026_);
return v___x_2028_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2029_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9);
v___x_2030_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7);
v___x_2031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
lean_ctor_set(v___x_2031_, 1, v___x_2029_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0(lean_object* v_goal_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___x_2055_; 
lean_inc(v_goal_2039_);
v___x_2055_ = l_Lean_MVarId_getType(v_goal_2039_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2156_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2156_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2156_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = l_Lean_Expr_cleanupAnnotations(v_a_2056_);
v___x_2070_ = l_Lean_Expr_isApp(v___x_2069_);
if (v___x_2070_ == 0)
{
lean_dec_ref(v___x_2069_);
lean_del_object(v___x_2058_);
lean_dec(v_a_2056_);
lean_dec(v_goal_2039_);
goto v___jp_2052_;
}
else
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2069_);
lean_dec_ref(v___x_2069_);
v___x_2072_ = l_Lean_Expr_isApp(v___x_2071_);
if (v___x_2072_ == 0)
{
lean_dec_ref(v___x_2071_);
lean_del_object(v___x_2058_);
lean_dec(v_a_2056_);
lean_dec(v_goal_2039_);
goto v___jp_2052_;
}
else
{
lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2073_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2071_);
lean_dec_ref(v___x_2071_);
v___x_2074_ = l_Lean_Expr_isApp(v___x_2073_);
if (v___x_2074_ == 0)
{
lean_dec_ref(v___x_2073_);
lean_del_object(v___x_2058_);
lean_dec(v_a_2056_);
lean_dec(v_goal_2039_);
goto v___jp_2052_;
}
else
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2073_);
lean_dec_ref(v___x_2073_);
v___x_2076_ = l_Lean_Expr_isApp(v___x_2075_);
if (v___x_2076_ == 0)
{
lean_dec_ref(v___x_2075_);
lean_del_object(v___x_2058_);
lean_dec(v_a_2056_);
lean_dec(v_goal_2039_);
goto v___jp_2052_;
}
else
{
lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2077_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2075_);
v___x_2078_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13));
v___x_2079_ = l_Lean_Expr_isConstOf(v___x_2077_, v___x_2078_);
lean_dec_ref(v___x_2077_);
if (v___x_2079_ == 0)
{
lean_dec_ref(v___x_2075_);
lean_del_object(v___x_2058_);
lean_dec(v_a_2056_);
lean_dec(v_goal_2039_);
goto v___jp_2052_;
}
else
{
lean_object* v_arg_2080_; uint8_t v___x_2081_; 
v_arg_2080_ = lean_ctor_get(v___x_2075_, 1);
lean_inc_ref(v_arg_2080_);
lean_dec_ref(v___x_2075_);
v___x_2081_ = l_Lean_Expr_isForall(v_arg_2080_);
lean_dec_ref(v_arg_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2084_; 
lean_dec(v_a_2056_);
lean_dec(v_goal_2039_);
v___x_2082_ = lean_box(0);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2082_);
v___x_2084_ = v___x_2058_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2082_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
else
{
lean_object* v_backwardRules_2086_; lean_object* v_rintros_2087_; lean_object* v_stateArgIntro_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
lean_del_object(v___x_2058_);
v_backwardRules_2086_ = lean_ctor_get(v___y_2040_, 0);
v_rintros_2087_ = lean_ctor_get(v___y_2040_, 2);
v_stateArgIntro_2088_ = lean_ctor_get(v_backwardRules_2086_, 1);
v___x_2089_ = lean_box(0);
lean_inc_ref(v_stateArgIntro_2088_);
v___x_2090_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_stateArgIntro_2088_, v_goal_2039_, v___x_2089_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2090_, 1);
if (lean_obj_tag(v_a_2091_) == 1)
{
lean_object* v_mvarIds_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2147_; 
v_mvarIds_2092_ = lean_ctor_get(v_a_2091_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_a_2091_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2094_ = v_a_2091_;
v_isShared_2095_ = v_isSharedCheck_2147_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_mvarIds_2092_);
lean_dec(v_a_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2147_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
if (lean_obj_tag(v_mvarIds_2092_) == 1)
{
lean_object* v_tail_2096_; 
v_tail_2096_ = lean_ctor_get(v_mvarIds_2092_, 1);
if (lean_obj_tag(v_tail_2096_) == 0)
{
lean_object* v_head_2097_; lean_object* v___x_2098_; lean_object* v_mctx_2099_; lean_object* v___x_2100_; 
lean_dec(v_a_2056_);
v_head_2097_ = lean_ctor_get(v_mvarIds_2092_, 0);
lean_inc_n(v_head_2097_, 2);
lean_dec_ref_known(v_mvarIds_2092_, 2);
v___x_2098_ = lean_st_ref_get(v___y_2048_);
v_mctx_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc_ref(v_mctx_2099_);
lean_dec(v___x_2098_);
v___x_2100_ = l_Lean_MVarId_getType(v_head_2097_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2138_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2103_ = v___x_2100_;
v_isShared_2104_ = v_isSharedCheck_2138_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2100_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2138_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2105_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_2099_, v_rintros_2087_, v_a_2101_);
lean_dec(v_a_2101_);
lean_dec_ref(v_mctx_2099_);
v___x_2106_ = lean_array_get_size(v___x_2105_);
lean_dec_ref(v___x_2105_);
v___x_2107_ = lean_unsigned_to_nat(0u);
v___x_2108_ = lean_nat_dec_eq(v___x_2106_, v___x_2107_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2110_; 
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v_head_2097_);
v___x_2110_ = v___x_2094_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_head_2097_);
v___x_2110_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2112_; 
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v___x_2110_);
v___x_2112_ = v___x_2103_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
else
{
lean_object* v___x_2115_; 
lean_del_object(v___x_2103_);
v___x_2115_ = l_Lean_Elab_Tactic_VCGen_introsHygienic(v_head_2097_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2117_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc_n(v_a_2116_, 2);
lean_dec_ref_known(v___x_2115_, 1);
v___x_2117_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs(v_a_2116_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
if (lean_obj_tag(v_a_2118_) == 0)
{
lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2128_; 
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2128_ == 0)
{
lean_object* v_unused_2129_; 
v_unused_2129_ = lean_ctor_get(v___x_2117_, 0);
lean_dec(v_unused_2129_);
v___x_2120_ = v___x_2117_;
v_isShared_2121_ = v_isSharedCheck_2128_;
goto v_resetjp_2119_;
}
else
{
lean_dec(v___x_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2128_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v_a_2116_);
v___x_2123_ = v___x_2094_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2116_);
v___x_2123_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2125_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2123_);
v___x_2125_ = v___x_2120_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_dec(v_a_2116_);
lean_del_object(v___x_2094_);
return v___x_2117_;
}
}
else
{
lean_dec(v_a_2116_);
lean_del_object(v___x_2094_);
return v___x_2117_;
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_del_object(v___x_2094_);
v_a_2130_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2115_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2115_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec_ref(v_mctx_2099_);
lean_dec(v_head_2097_);
lean_del_object(v___x_2094_);
v_a_2139_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2100_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2100_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2092_, 2);
lean_del_object(v___x_2094_);
v___y_2061_ = v___y_2047_;
v___y_2062_ = v___y_2048_;
v___y_2063_ = v___y_2049_;
v___y_2064_ = v___y_2050_;
goto v___jp_2060_;
}
}
else
{
lean_del_object(v___x_2094_);
lean_dec(v_mvarIds_2092_);
v___y_2061_ = v___y_2047_;
v___y_2062_ = v___y_2048_;
v___y_2063_ = v___y_2049_;
v___y_2064_ = v___y_2050_;
goto v___jp_2060_;
}
}
}
else
{
lean_dec(v_a_2091_);
v___y_2061_ = v___y_2047_;
v___y_2062_ = v___y_2048_;
v___y_2063_ = v___y_2049_;
v___y_2064_ = v___y_2050_;
goto v___jp_2060_;
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_a_2056_);
v_a_2148_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2090_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2090_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
}
}
}
}
v___jp_2060_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2065_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10);
v___x_2066_ = l_Lean_indentExpr(v_a_2056_);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2065_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v___x_2068_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_2067_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
return v___x_2068_;
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec(v_goal_2039_);
v_a_2157_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2055_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2055_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
v___jp_2052_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = lean_box(0);
v___x_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
return v___x_2054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___boxed(lean_object* v_goal_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0(v_goal_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs(lean_object* v_goal_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v___f_2192_; lean_object* v___x_2193_; 
lean_inc(v_goal_2179_);
v___f_2192_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2192_, 0, v_goal_2179_);
v___x_2193_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_goal_2179_, v___f_2192_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___boxed(lean_object* v_goal_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs(v_goal_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
lean_dec(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(lean_object* v_mvarId_2208_, lean_object* v_val_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v___x_2212_; lean_object* v_mctx_2213_; lean_object* v_cache_2214_; lean_object* v_zetaDeltaFVarIds_2215_; lean_object* v_postponed_2216_; lean_object* v_diag_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2246_; 
v___x_2212_ = lean_st_ref_take(v___y_2210_);
v_mctx_2213_ = lean_ctor_get(v___x_2212_, 0);
v_cache_2214_ = lean_ctor_get(v___x_2212_, 1);
v_zetaDeltaFVarIds_2215_ = lean_ctor_get(v___x_2212_, 2);
v_postponed_2216_ = lean_ctor_get(v___x_2212_, 3);
v_diag_2217_ = lean_ctor_get(v___x_2212_, 4);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2219_ = v___x_2212_;
v_isShared_2220_ = v_isSharedCheck_2246_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_diag_2217_);
lean_inc(v_postponed_2216_);
lean_inc(v_zetaDeltaFVarIds_2215_);
lean_inc(v_cache_2214_);
lean_inc(v_mctx_2213_);
lean_dec(v___x_2212_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2246_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v_depth_2221_; lean_object* v_levelAssignDepth_2222_; lean_object* v_lmvarCounter_2223_; lean_object* v_mvarCounter_2224_; lean_object* v_lDecls_2225_; lean_object* v_decls_2226_; lean_object* v_userNames_2227_; lean_object* v_lAssignment_2228_; lean_object* v_eAssignment_2229_; lean_object* v_dAssignment_2230_; lean_object* v_instanceTypedMVars_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2245_; 
v_depth_2221_ = lean_ctor_get(v_mctx_2213_, 0);
v_levelAssignDepth_2222_ = lean_ctor_get(v_mctx_2213_, 1);
v_lmvarCounter_2223_ = lean_ctor_get(v_mctx_2213_, 2);
v_mvarCounter_2224_ = lean_ctor_get(v_mctx_2213_, 3);
v_lDecls_2225_ = lean_ctor_get(v_mctx_2213_, 4);
v_decls_2226_ = lean_ctor_get(v_mctx_2213_, 5);
v_userNames_2227_ = lean_ctor_get(v_mctx_2213_, 6);
v_lAssignment_2228_ = lean_ctor_get(v_mctx_2213_, 7);
v_eAssignment_2229_ = lean_ctor_get(v_mctx_2213_, 8);
v_dAssignment_2230_ = lean_ctor_get(v_mctx_2213_, 9);
v_instanceTypedMVars_2231_ = lean_ctor_get(v_mctx_2213_, 10);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_mctx_2213_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2233_ = v_mctx_2213_;
v_isShared_2234_ = v_isSharedCheck_2245_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_instanceTypedMVars_2231_);
lean_inc(v_dAssignment_2230_);
lean_inc(v_eAssignment_2229_);
lean_inc(v_lAssignment_2228_);
lean_inc(v_userNames_2227_);
lean_inc(v_decls_2226_);
lean_inc(v_lDecls_2225_);
lean_inc(v_mvarCounter_2224_);
lean_inc(v_lmvarCounter_2223_);
lean_inc(v_levelAssignDepth_2222_);
lean_inc(v_depth_2221_);
lean_dec(v_mctx_2213_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2245_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2238_; 
v___x_2235_ = lean_box(0);
v___x_2236_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(v_eAssignment_2229_, v_mvarId_2208_, v_val_2209_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 8, v___x_2236_);
v___x_2238_ = v___x_2233_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_depth_2221_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_levelAssignDepth_2222_);
lean_ctor_set(v_reuseFailAlloc_2244_, 2, v_lmvarCounter_2223_);
lean_ctor_set(v_reuseFailAlloc_2244_, 3, v_mvarCounter_2224_);
lean_ctor_set(v_reuseFailAlloc_2244_, 4, v_lDecls_2225_);
lean_ctor_set(v_reuseFailAlloc_2244_, 5, v_decls_2226_);
lean_ctor_set(v_reuseFailAlloc_2244_, 6, v_userNames_2227_);
lean_ctor_set(v_reuseFailAlloc_2244_, 7, v_lAssignment_2228_);
lean_ctor_set(v_reuseFailAlloc_2244_, 8, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2244_, 9, v_dAssignment_2230_);
lean_ctor_set(v_reuseFailAlloc_2244_, 10, v_instanceTypedMVars_2231_);
v___x_2238_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
lean_object* v___x_2240_; 
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 0, v___x_2238_);
v___x_2240_ = v___x_2219_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2238_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_cache_2214_);
lean_ctor_set(v_reuseFailAlloc_2243_, 2, v_zetaDeltaFVarIds_2215_);
lean_ctor_set(v_reuseFailAlloc_2243_, 3, v_postponed_2216_);
lean_ctor_set(v_reuseFailAlloc_2243_, 4, v_diag_2217_);
v___x_2240_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = lean_st_ref_put(v___y_2210_, v___x_2240_);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2235_);
return v___x_2242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg___boxed(lean_object* v_mvarId_2247_, lean_object* v_val_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_mvarId_2247_, v_val_2248_, v___y_2249_);
lean_dec(v___y_2249_);
return v_res_2251_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__0));
v___x_2254_ = l_Lean_stringToMessageData(v___x_2253_);
return v___x_2254_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__3));
v___x_2258_ = l_Lean_stringToMessageData(v___x_2257_);
return v___x_2258_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = lean_box(0);
v___x_2273_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__8));
v___x_2274_ = l_Lean_mkConst(v___x_2273_, v___x_2272_);
return v___x_2274_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = lean_box(0);
v___x_2280_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__15));
v___x_2281_ = l_Lean_mkConst(v___x_2280_, v___x_2279_);
return v___x_2281_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = lean_box(0);
v___x_2287_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__18));
v___x_2288_ = l_Lean_mkConst(v___x_2287_, v___x_2286_);
return v___x_2288_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2292_ = lean_box(0);
v___x_2293_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__20));
v___x_2294_ = l_Lean_mkConst(v___x_2293_, v___x_2292_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0(lean_object* v_goal_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___y_2309_; lean_object* v___y_2310_; uint8_t v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v_g_2327_; lean_object* v_fst_2331_; lean_object* v_snd_2332_; lean_object* v___x_2561_; 
lean_inc(v_goal_2295_);
v___x_2561_ = l_Lean_MVarId_getType(v_goal_2295_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___x_2563_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
v___x_2563_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_a_2562_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2565_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc_n(v_a_2564_, 2);
lean_dec_ref_known(v___x_2563_, 1);
v___x_2565_ = l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(v_a_2564_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
if (lean_obj_tag(v_a_2566_) == 0)
{
v_fst_2331_ = v_goal_2295_;
v_snd_2332_ = v_a_2564_;
goto v___jp_2330_;
}
else
{
lean_object* v_val_2567_; lean_object* v___x_2568_; 
lean_dec(v_a_2564_);
v_val_2567_ = lean_ctor_get(v_a_2566_, 0);
lean_inc_n(v_val_2567_, 2);
lean_dec_ref_known(v_a_2566_, 1);
v___x_2568_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_2295_, v_val_2567_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2569_);
lean_dec_ref_known(v___x_2568_, 1);
v_fst_2331_ = v_a_2569_;
v_snd_2332_ = v_val_2567_;
goto v___jp_2330_;
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec(v_val_2567_);
v_a_2570_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2568_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2568_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec(v_a_2564_);
lean_dec(v_goal_2295_);
v_a_2578_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2565_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2565_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec(v_goal_2295_);
v_a_2586_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2563_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2563_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v_goal_2295_);
v_a_2594_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2561_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2561_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
v___jp_2308_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2316_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1);
v___x_2317_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__2));
lean_inc_ref(v___y_2309_);
v___x_2318_ = l_Lean_Name_mkStr2(v___y_2309_, v___x_2317_);
v___x_2319_ = l_Lean_MessageData_ofConstName(v___x_2318_, v___y_2311_);
v___x_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2316_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4);
v___x_2322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = l_Lean_indentExpr(v___y_2310_);
v___x_2324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2322_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
v___x_2325_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_2324_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
return v___x_2325_;
}
v___jp_2326_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2328_, 0, v_g_2327_);
v___x_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
return v___x_2329_;
}
v___jp_2330_:
{
lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__6));
v___x_2334_ = l_Lean_Expr_isAppOf(v_snd_2332_, v___x_2333_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2335_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__7));
v___x_2336_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__8));
v___x_2337_ = l_Lean_Expr_isAppOf(v_snd_2332_, v___x_2336_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___x_2338_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__10));
v___x_2339_ = lean_unsigned_to_nat(3u);
v___x_2340_ = l_Lean_Expr_isAppOfArity(v_snd_2332_, v___x_2338_, v___x_2339_);
if (v___x_2340_ == 0)
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
lean_dec_ref(v_snd_2332_);
v___x_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2341_, 0, v_fst_2331_);
v___x_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
return v___x_2342_;
}
else
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2343_ = l_Lean_Expr_appFn_x21(v_snd_2332_);
v___x_2344_ = l_Lean_Expr_appFn_x21(v___x_2343_);
v___x_2345_ = l_Lean_Expr_appArg_x21(v___x_2344_);
lean_dec_ref(v___x_2344_);
v___x_2346_ = l_Lean_Expr_appArg_x21(v___x_2343_);
lean_dec_ref(v___x_2343_);
v___x_2347_ = l_Lean_Expr_appArg_x21(v_snd_2332_);
lean_dec_ref(v_snd_2332_);
v___x_2348_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v___x_2346_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2350_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v___x_2350_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v___x_2347_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2352_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2350_, 1);
lean_inc_ref(v___x_2345_);
v___x_2352_ = l_Lean_Meta_getLevel(v___x_2345_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2352_, 1);
v___x_2354_ = lean_box(0);
v___x_2355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2355_, 0, v_a_2353_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
v___x_2356_ = l_Lean_mkConst(v___x_2338_, v___x_2355_);
lean_inc(v_a_2351_);
lean_inc(v_a_2349_);
lean_inc_ref(v___x_2345_);
v___x_2357_ = l_Lean_mkApp3(v___x_2356_, v___x_2345_, v_a_2349_, v_a_2351_);
v___x_2358_ = l_Lean_MVarId_replaceTargetDefEqFast(v_fst_2331_, v___x_2357_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2358_, 1);
v___x_2360_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___closed__0));
lean_inc(v_a_2349_);
v___x_2361_ = l_Lean_Meta_Sym_isDefEqS(v_a_2349_, v_a_2351_, v___x_2340_, v___x_2340_, v___x_2360_, v___x_2360_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2403_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2403_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2403_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
uint8_t v___x_2366_; 
v___x_2366_ = lean_unbox(v_a_2362_);
lean_dec(v_a_2362_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; lean_object* v___x_2369_; 
lean_dec(v_a_2349_);
lean_dec_ref(v___x_2345_);
v___x_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2367_, 0, v_a_2359_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2367_);
v___x_2369_ = v___x_2364_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
else
{
lean_object* v___x_2371_; 
lean_del_object(v___x_2364_);
lean_inc_ref(v___x_2345_);
v___x_2371_ = l_Lean_Meta_getLevel(v___x_2345_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v___x_2371_, 1);
v___x_2373_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__12));
v___x_2374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2374_, 0, v_a_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2354_);
v___x_2375_ = l_Lean_mkConst(v___x_2373_, v___x_2374_);
v___x_2376_ = l_Lean_mkAppB(v___x_2375_, v___x_2345_, v_a_2349_);
v___x_2377_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_a_2359_, v___x_2376_, v___y_2304_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2385_; 
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; 
v_unused_2386_ = lean_ctor_get(v___x_2377_, 0);
lean_dec(v_unused_2386_);
v___x_2379_ = v___x_2377_;
v_isShared_2380_ = v_isSharedCheck_2385_;
goto v_resetjp_2378_;
}
else
{
lean_dec(v___x_2377_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2385_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2381_ = lean_box(0);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2381_);
v___x_2383_ = v___x_2379_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
v_a_2387_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2377_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2377_);
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
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_dec(v_a_2359_);
lean_dec(v_a_2349_);
lean_dec_ref(v___x_2345_);
v_a_2395_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2371_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2371_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec(v_a_2359_);
lean_dec(v_a_2349_);
lean_dec_ref(v___x_2345_);
v_a_2404_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2361_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2361_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec(v_a_2351_);
lean_dec(v_a_2349_);
lean_dec_ref(v___x_2345_);
v_a_2412_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2358_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2358_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
lean_dec(v_a_2351_);
lean_dec(v_a_2349_);
lean_dec_ref(v___x_2345_);
lean_dec(v_fst_2331_);
v_a_2420_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2352_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2352_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v_a_2349_);
lean_dec_ref(v___x_2345_);
lean_dec(v_fst_2331_);
v_a_2428_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2350_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2350_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec_ref(v___x_2347_);
lean_dec_ref(v___x_2345_);
lean_dec(v_fst_2331_);
v_a_2436_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2348_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2348_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
}
else
{
lean_object* v_backwardRules_2444_; lean_object* v_andIntro_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v_backwardRules_2444_ = lean_ctor_get(v___y_2296_, 0);
v_andIntro_2445_ = lean_ctor_get(v_backwardRules_2444_, 8);
v___x_2446_ = lean_box(0);
lean_inc_ref(v_andIntro_2445_);
v___x_2447_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_andIntro_2445_, v_fst_2331_, v___x_2446_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_a_2448_);
lean_dec_ref_known(v___x_2447_, 1);
if (lean_obj_tag(v_a_2448_) == 1)
{
lean_object* v_mvarIds_2449_; 
v_mvarIds_2449_ = lean_ctor_get(v_a_2448_, 0);
lean_inc(v_mvarIds_2449_);
lean_dec_ref_known(v_a_2448_, 1);
if (lean_obj_tag(v_mvarIds_2449_) == 1)
{
lean_object* v_tail_2450_; 
v_tail_2450_ = lean_ctor_get(v_mvarIds_2449_, 1);
lean_inc(v_tail_2450_);
if (lean_obj_tag(v_tail_2450_) == 1)
{
lean_object* v_tail_2451_; 
v_tail_2451_ = lean_ctor_get(v_tail_2450_, 1);
if (lean_obj_tag(v_tail_2451_) == 0)
{
lean_object* v_head_2452_; lean_object* v_head_2453_; lean_object* v___x_2454_; 
lean_dec_ref(v_snd_2332_);
v_head_2452_ = lean_ctor_get(v_mvarIds_2449_, 0);
lean_inc(v_head_2452_);
lean_dec_ref_known(v_mvarIds_2449_, 2);
v_head_2453_ = lean_ctor_get(v_tail_2450_, 0);
lean_inc(v_head_2453_);
lean_dec_ref_known(v_tail_2450_, 2);
v___x_2454_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_head_2452_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2456_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2454_, 1);
v___x_2456_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_head_2453_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2456_) == 0)
{
if (lean_obj_tag(v_a_2455_) == 0)
{
lean_object* v_a_2457_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
if (lean_obj_tag(v_a_2457_) == 0)
{
return v___x_2456_;
}
else
{
lean_object* v_val_2458_; 
lean_inc_ref(v_a_2457_);
lean_dec_ref_known(v___x_2456_, 1);
v_val_2458_ = lean_ctor_get(v_a_2457_, 0);
lean_inc(v_val_2458_);
lean_dec_ref_known(v_a_2457_, 1);
v_g_2327_ = v_val_2458_;
goto v___jp_2326_;
}
}
else
{
lean_object* v_a_2459_; 
v_a_2459_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2456_, 1);
if (lean_obj_tag(v_a_2459_) == 0)
{
lean_object* v_val_2460_; 
v_val_2460_ = lean_ctor_get(v_a_2455_, 0);
lean_inc(v_val_2460_);
lean_dec_ref_known(v_a_2455_, 1);
v_g_2327_ = v_val_2460_;
goto v___jp_2326_;
}
else
{
lean_object* v_val_2461_; lean_object* v_val_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2533_; 
v_val_2461_ = lean_ctor_get(v_a_2455_, 0);
lean_inc(v_val_2461_);
lean_dec_ref_known(v_a_2455_, 1);
v_val_2462_ = lean_ctor_get(v_a_2459_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_a_2459_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2464_ = v_a_2459_;
v_isShared_2465_ = v_isSharedCheck_2533_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_val_2462_);
lean_dec(v_a_2459_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2533_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; 
lean_inc(v_val_2461_);
v___x_2466_ = l_Lean_MVarId_getType(v_val_2461_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2468_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v___x_2466_, 1);
lean_inc(v_val_2462_);
v___x_2468_ = l_Lean_MVarId_getType(v_val_2462_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc_n(v_a_2469_, 2);
lean_dec_ref_known(v___x_2468_, 1);
v___x_2470_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13);
lean_inc(v_a_2467_);
v___x_2471_ = l_Lean_mkAppB(v___x_2470_, v_a_2467_, v_a_2469_);
v___x_2472_ = lean_box(0);
v___x_2473_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2471_, v___x_2472_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc_n(v_a_2474_, 2);
lean_dec_ref_known(v___x_2473_, 1);
v___x_2475_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16);
lean_inc(v_a_2469_);
lean_inc(v_a_2467_);
v___x_2476_ = l_Lean_mkApp3(v___x_2475_, v_a_2467_, v_a_2469_, v_a_2474_);
v___x_2477_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_val_2461_, v___x_2476_, v___y_2304_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_dec_ref_known(v___x_2477_, 1);
v___x_2478_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19);
lean_inc(v_a_2474_);
v___x_2479_ = l_Lean_mkApp3(v___x_2478_, v_a_2467_, v_a_2469_, v_a_2474_);
v___x_2480_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_val_2462_, v___x_2479_, v___y_2304_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2491_; 
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2491_ == 0)
{
lean_object* v_unused_2492_; 
v_unused_2492_ = lean_ctor_get(v___x_2480_, 0);
lean_dec(v_unused_2492_);
v___x_2482_ = v___x_2480_;
v_isShared_2483_ = v_isSharedCheck_2491_;
goto v_resetjp_2481_;
}
else
{
lean_dec(v___x_2480_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2491_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; lean_object* v___x_2486_; 
v___x_2484_ = l_Lean_Expr_mvarId_x21(v_a_2474_);
lean_dec(v_a_2474_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2484_);
v___x_2486_ = v___x_2464_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2484_);
v___x_2486_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2488_; 
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v___x_2486_);
v___x_2488_ = v___x_2482_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2486_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec(v_a_2474_);
lean_del_object(v___x_2464_);
v_a_2493_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2480_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2480_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec(v_a_2474_);
lean_dec(v_a_2469_);
lean_dec(v_a_2467_);
lean_del_object(v___x_2464_);
lean_dec(v_val_2462_);
v_a_2501_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2477_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2477_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
lean_dec(v_a_2469_);
lean_dec(v_a_2467_);
lean_del_object(v___x_2464_);
lean_dec(v_val_2462_);
lean_dec(v_val_2461_);
v_a_2509_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2473_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2473_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_dec(v_a_2467_);
lean_del_object(v___x_2464_);
lean_dec(v_val_2462_);
lean_dec(v_val_2461_);
v_a_2517_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2468_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2468_);
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
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_del_object(v___x_2464_);
lean_dec(v_val_2462_);
lean_dec(v_val_2461_);
v_a_2525_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2466_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2466_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2455_);
return v___x_2456_;
}
}
else
{
lean_dec(v_head_2453_);
return v___x_2454_;
}
}
else
{
lean_dec_ref_known(v_tail_2450_, 2);
lean_dec_ref_known(v_mvarIds_2449_, 2);
v___y_2309_ = v___x_2335_;
v___y_2310_ = v_snd_2332_;
v___y_2311_ = v___x_2334_;
v___y_2312_ = v___y_2303_;
v___y_2313_ = v___y_2304_;
v___y_2314_ = v___y_2305_;
v___y_2315_ = v___y_2306_;
goto v___jp_2308_;
}
}
else
{
lean_dec(v_tail_2450_);
lean_dec_ref_known(v_mvarIds_2449_, 2);
v___y_2309_ = v___x_2335_;
v___y_2310_ = v_snd_2332_;
v___y_2311_ = v___x_2334_;
v___y_2312_ = v___y_2303_;
v___y_2313_ = v___y_2304_;
v___y_2314_ = v___y_2305_;
v___y_2315_ = v___y_2306_;
goto v___jp_2308_;
}
}
else
{
lean_dec(v_mvarIds_2449_);
v___y_2309_ = v___x_2335_;
v___y_2310_ = v_snd_2332_;
v___y_2311_ = v___x_2334_;
v___y_2312_ = v___y_2303_;
v___y_2313_ = v___y_2304_;
v___y_2314_ = v___y_2305_;
v___y_2315_ = v___y_2306_;
goto v___jp_2308_;
}
}
else
{
lean_dec(v_a_2448_);
v___y_2309_ = v___x_2335_;
v___y_2310_ = v_snd_2332_;
v___y_2311_ = v___x_2334_;
v___y_2312_ = v___y_2303_;
v___y_2313_ = v___y_2304_;
v___y_2314_ = v___y_2305_;
v___y_2315_ = v___y_2306_;
goto v___jp_2308_;
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec_ref(v_snd_2332_);
v_a_2534_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2447_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2447_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_dec_ref(v_snd_2332_);
v___x_2542_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21);
v___x_2543_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_fst_2331_, v___x_2542_, v___y_2304_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2551_; 
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2551_ == 0)
{
lean_object* v_unused_2552_; 
v_unused_2552_ = lean_ctor_get(v___x_2543_, 0);
lean_dec(v_unused_2552_);
v___x_2545_ = v___x_2543_;
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
else
{
lean_dec(v___x_2543_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; lean_object* v___x_2549_; 
v___x_2547_ = lean_box(0);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2547_);
v___x_2549_ = v___x_2545_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
v_a_2553_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2543_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2543_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___boxed(lean_object* v_goal_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0(v_goal_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC(lean_object* v_goal_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_){
_start:
{
lean_object* v___f_2629_; lean_object* v___x_2630_; 
lean_inc(v_goal_2616_);
v___f_2629_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2629_, 0, v_goal_2616_);
v___x_2630_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_goal_2616_, v___f_2629_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___boxed(lean_object* v_goal_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_goal_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
lean_dec(v_a_2638_);
lean_dec_ref(v_a_2637_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0(lean_object* v_mvarId_2645_, lean_object* v_val_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_mvarId_2645_, v_val_2646_, v___y_2655_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___boxed(lean_object* v_mvarId_2660_, lean_object* v_val_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0(v_mvarId_2660_, v_val_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
return v_res_2674_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Reduce(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Goal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Telescope(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Goal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_VCGen_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_Reduce(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Goal(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Telescope(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_VCGen_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Goal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_VCGen_Util(builtin);
}
#ifdef __cplusplus
}
#endif
