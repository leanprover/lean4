// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.Util
// Imports: public import Lean.Meta.Tactic.Grind.Main public import Lean.Elab.Tactic.VCGen.Context public import Lean.Elab.Tactic.VCGen.Reduce public import Lean.Meta.Sym.AlphaShareBuilder public import Lean.Meta.Sym.Intro public import Lean.Meta.Sym.Simp.Goal public import Lean.Meta.Sym.Simp.Telescope public import Lean.Meta.Sym.Util
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Pattern_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_VCGen_numBindersToIntro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_numBindersToIntro___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_numBindersToIntro___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_numBindersToIntro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_numBindersToIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_numBindersToIntro___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_numBindersToIntro___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simpTelescope___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_308_; lean_object* v___y_309_; uint8_t v___y_310_; lean_object* v___x_313_; 
lean_inc(v_cls_294_);
v___x_313_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_cls_294_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_315_; 
v_a_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc_n(v_a_314_, 2);
lean_dec_ref_known(v___x_313_, 1);
lean_inc(v___y_299_);
lean_inc_ref(v___y_298_);
lean_inc(v___y_297_);
lean_inc_ref(v___y_296_);
v___x_315_ = lean_infer_type(v_a_314_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_317_; uint8_t v___x_318_; lean_object* v___x_319_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_a_316_);
lean_dec_ref_known(v___x_315_, 1);
v___x_317_ = lean_box(0);
v___x_318_ = 0;
v___x_319_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_316_, v___x_317_, v___x_318_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v_fst_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_410_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref_known(v___x_319_, 1);
v_fst_321_ = lean_ctor_get(v_a_320_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v_a_320_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v_a_320_, 1);
lean_dec(v_unused_411_);
v___x_323_ = v_a_320_;
v_isShared_324_ = v_isSharedCheck_410_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_fst_321_);
lean_dec(v_a_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_410_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_393_ = lean_array_get_size(v_fst_321_);
v___x_394_ = lean_array_get_size(v_xs_295_);
v___x_395_ = lean_nat_dec_lt(v___x_393_, v___x_394_);
if (v___x_395_ == 0)
{
lean_dec(v_cls_294_);
v___y_326_ = v___y_296_;
v___y_327_ = v___y_297_;
v___y_328_ = v___y_298_;
v___y_329_ = v___y_299_;
goto v___jp_325_;
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_del_object(v___x_323_);
lean_dec(v_fst_321_);
lean_dec(v_a_314_);
lean_dec_ref(v_xs_295_);
v___x_396_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__1, &l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__1);
v___x_397_ = l_Lean_MessageData_ofName(v_cls_294_);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3, &l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3);
v___x_400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___redArg(v___x_400_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
v___jp_325_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_array_get_size(v_xs_295_);
v___x_332_ = l_Array_toSubarray___redArg(v_xs_295_, v___x_330_, v___x_331_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v___x_332_);
lean_ctor_set(v___x_323_, 0, v___x_317_);
v___x_334_ = v___x_323_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v___x_332_);
v___x_334_ = v_reuseFailAlloc_392_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
size_t v_sz_335_; size_t v___x_336_; lean_object* v___x_337_; 
v_sz_335_ = lean_array_size(v_fst_321_);
v___x_336_ = ((size_t)0ULL);
v___x_337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0(v_fst_321_, v_sz_335_, v___x_336_, v___x_334_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_383_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_383_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_383_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_383_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_fst_342_; 
v_fst_342_ = lean_ctor_get(v_a_338_, 0);
lean_inc(v_fst_342_);
lean_dec(v_a_338_);
if (lean_obj_tag(v_fst_342_) == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_del_object(v___x_340_);
v___x_343_ = l_Lean_mkAppN(v_a_314_, v_fst_321_);
v___x_344_ = l_Lean_Meta_synthInstance_x3f(v___x_343_, v___x_317_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_370_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_370_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_370_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_370_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
if (lean_obj_tag(v_a_345_) == 1)
{
lean_object* v_val_349_; lean_object* v___x_350_; 
lean_del_object(v___x_347_);
v_val_349_ = lean_ctor_get(v_a_345_, 0);
lean_inc(v_val_349_);
lean_dec_ref_known(v_a_345_, 1);
v___x_350_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__2(v_sz_335_, v___x_336_, v_fst_321_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec_ref(v___y_326_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_352_; lean_object* v_a_353_; uint8_t v___x_354_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_a_351_);
lean_dec_ref_known(v___x_350_, 1);
v___x_352_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___redArg(v_val_349_, v___y_327_);
lean_dec(v___y_327_);
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref(v___x_352_);
v___x_354_ = l_Lean_Expr_hasExprMVar(v_a_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = lean_array_get_size(v_a_351_);
v___x_356_ = lean_nat_dec_lt(v___x_330_, v___x_355_);
if (v___x_356_ == 0)
{
v___y_302_ = v_a_353_;
v___y_303_ = v_a_351_;
goto v___jp_301_;
}
else
{
if (v___x_356_ == 0)
{
v___y_302_ = v_a_353_;
v___y_303_ = v_a_351_;
goto v___jp_301_;
}
else
{
size_t v___x_357_; uint8_t v___x_358_; 
v___x_357_ = lean_usize_of_nat(v___x_355_);
v___x_358_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__3(v_a_351_, v___x_336_, v___x_357_);
v___y_308_ = v_a_353_;
v___y_309_ = v_a_351_;
v___y_310_ = v___x_358_;
goto v___jp_307_;
}
}
}
else
{
v___y_308_ = v_a_353_;
v___y_309_ = v_a_351_;
v___y_310_ = v___x_354_;
goto v___jp_307_;
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec(v_val_349_);
lean_dec(v___y_327_);
v_a_359_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_350_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_350_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
else
{
lean_object* v___x_368_; 
lean_dec(v_a_345_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v_fst_321_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_317_);
v___x_368_ = v___x_347_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_317_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v_fst_321_);
v_a_371_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_344_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_344_);
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
else
{
lean_object* v_val_379_; lean_object* v___x_381_; 
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v_fst_321_);
lean_dec(v_a_314_);
v_val_379_ = lean_ctor_get(v_fst_342_, 0);
lean_inc(v_val_379_);
lean_dec_ref_known(v_fst_342_, 1);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v_val_379_);
v___x_381_ = v___x_340_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_val_379_);
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
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v_fst_321_);
lean_dec(v_a_314_);
v_a_384_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_337_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_337_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec(v_a_314_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec_ref(v_xs_295_);
lean_dec(v_cls_294_);
v_a_412_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_319_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_319_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec(v_a_314_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec_ref(v_xs_295_);
lean_dec(v_cls_294_);
v_a_420_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_315_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_315_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec_ref(v_xs_295_);
lean_dec(v_cls_294_);
v_a_428_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_313_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_313_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
v___jp_301_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v___y_303_);
lean_ctor_set(v___x_304_, 1, v___y_302_);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
v___jp_307_:
{
if (v___y_310_ == 0)
{
v___y_302_ = v___y_308_;
v___y_303_ = v___y_309_;
goto v___jp_301_;
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec_ref(v___y_309_);
lean_dec_ref(v___y_308_);
v___x_311_ = lean_box(0);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___boxed(lean_object* v_cls_436_, lean_object* v_xs_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0(v_cls_436_, v_xs_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f(lean_object* v_cls_444_, lean_object* v_xs_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___f_451_; uint8_t v___x_452_; lean_object* v___x_453_; 
v___f_451_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_451_, 0, v_cls_444_);
lean_closure_set(v___f_451_, 1, v_xs_445_);
v___x_452_ = 0;
v___x_453_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___redArg(v___f_451_, v___x_452_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___boxed(lean_object* v_cls_454_, lean_object* v_xs_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f(v_cls_454_, v_xs_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4(lean_object* v_00_u03b1_462_, lean_object* v_msg_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___redArg(v_msg_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___boxed(lean_object* v_00_u03b1_470_, lean_object* v_msg_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4(v_00_u03b1_470_, v_msg_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(lean_object* v_mvarId_478_, lean_object* v_x_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_478_, v_x_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
v_a_494_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_485_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_485_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg___boxed(lean_object* v_mvarId_502_, lean_object* v_x_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(v_mvarId_502_, v_x_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1(lean_object* v_00_u03b1_510_, lean_object* v_mvarId_511_, lean_object* v_x_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(v_mvarId_511_, v_x_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___boxed(lean_object* v_00_u03b1_519_, lean_object* v_mvarId_520_, lean_object* v_x_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1(v_00_u03b1_519_, v_mvarId_520_, v_x_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_528_, lean_object* v_x_529_, lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
lean_object* v_ks_532_; lean_object* v_vs_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_557_; 
v_ks_532_ = lean_ctor_get(v_x_528_, 0);
v_vs_533_ = lean_ctor_get(v_x_528_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_x_528_);
if (v_isSharedCheck_557_ == 0)
{
v___x_535_ = v_x_528_;
v_isShared_536_ = v_isSharedCheck_557_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_vs_533_);
lean_inc(v_ks_532_);
lean_dec(v_x_528_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_557_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_537_ = lean_array_get_size(v_ks_532_);
v___x_538_ = lean_nat_dec_lt(v_x_529_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
lean_dec(v_x_529_);
v___x_539_ = lean_array_push(v_ks_532_, v_x_530_);
v___x_540_ = lean_array_push(v_vs_533_, v_x_531_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v___x_540_);
lean_ctor_set(v___x_535_, 0, v___x_539_);
v___x_542_ = v___x_535_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
else
{
lean_object* v_k_x27_544_; uint8_t v___x_545_; 
v_k_x27_544_ = lean_array_fget_borrowed(v_ks_532_, v_x_529_);
v___x_545_ = l_Lean_instBEqMVarId_beq(v_x_530_, v_k_x27_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_547_; 
if (v_isShared_536_ == 0)
{
v___x_547_ = v___x_535_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_ks_532_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_vs_533_);
v___x_547_ = v_reuseFailAlloc_551_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_unsigned_to_nat(1u);
v___x_549_ = lean_nat_add(v_x_529_, v___x_548_);
lean_dec(v_x_529_);
v_x_528_ = v___x_547_;
v_x_529_ = v___x_549_;
goto _start;
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_552_ = lean_array_fset(v_ks_532_, v_x_529_, v_x_530_);
v___x_553_ = lean_array_fset(v_vs_533_, v_x_529_, v_x_531_);
lean_dec(v_x_529_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v___x_553_);
lean_ctor_set(v___x_535_, 0, v___x_552_);
v___x_555_ = v___x_535_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_558_, lean_object* v_k_559_, lean_object* v_v_560_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_558_, v___x_561_, v_k_559_, v_v_560_);
return v___x_562_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(lean_object* v_x_564_, size_t v_x_565_, size_t v_x_566_, lean_object* v_x_567_, lean_object* v_x_568_){
_start:
{
if (lean_obj_tag(v_x_564_) == 0)
{
lean_object* v_es_569_; size_t v___x_570_; size_t v___x_571_; lean_object* v_j_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v_es_569_ = lean_ctor_get(v_x_564_, 0);
v___x_570_ = ((size_t)31ULL);
v___x_571_ = lean_usize_land(v_x_565_, v___x_570_);
v_j_572_ = lean_usize_to_nat(v___x_571_);
v___x_573_ = lean_array_get_size(v_es_569_);
v___x_574_ = lean_nat_dec_lt(v_j_572_, v___x_573_);
if (v___x_574_ == 0)
{
lean_dec(v_j_572_);
lean_dec(v_x_568_);
lean_dec(v_x_567_);
return v_x_564_;
}
else
{
lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_613_; 
lean_inc_ref(v_es_569_);
v_isSharedCheck_613_ = !lean_is_exclusive(v_x_564_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v_x_564_, 0);
lean_dec(v_unused_614_);
v___x_576_ = v_x_564_;
v_isShared_577_ = v_isSharedCheck_613_;
goto v_resetjp_575_;
}
else
{
lean_dec(v_x_564_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_613_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v_v_578_; lean_object* v___x_579_; lean_object* v_xs_x27_580_; lean_object* v___y_582_; 
v_v_578_ = lean_array_fget(v_es_569_, v_j_572_);
v___x_579_ = lean_box(0);
v_xs_x27_580_ = lean_array_fset(v_es_569_, v_j_572_, v___x_579_);
switch(lean_obj_tag(v_v_578_))
{
case 0:
{
lean_object* v_key_587_; lean_object* v_val_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_598_; 
v_key_587_ = lean_ctor_get(v_v_578_, 0);
v_val_588_ = lean_ctor_get(v_v_578_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v_v_578_);
if (v_isSharedCheck_598_ == 0)
{
v___x_590_ = v_v_578_;
v_isShared_591_ = v_isSharedCheck_598_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_val_588_);
lean_inc(v_key_587_);
lean_dec(v_v_578_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_598_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
uint8_t v___x_592_; 
v___x_592_ = l_Lean_instBEqMVarId_beq(v_x_567_, v_key_587_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_del_object(v___x_590_);
v___x_593_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_587_, v_val_588_, v_x_567_, v_x_568_);
v___x_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
v___y_582_ = v___x_594_;
goto v___jp_581_;
}
else
{
lean_object* v___x_596_; 
lean_dec(v_val_588_);
lean_dec(v_key_587_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v_x_568_);
lean_ctor_set(v___x_590_, 0, v_x_567_);
v___x_596_ = v___x_590_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_x_567_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_x_568_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
v___y_582_ = v___x_596_;
goto v___jp_581_;
}
}
}
}
case 1:
{
lean_object* v_node_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_611_; 
v_node_599_ = lean_ctor_get(v_v_578_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_v_578_);
if (v_isSharedCheck_611_ == 0)
{
v___x_601_ = v_v_578_;
v_isShared_602_ = v_isSharedCheck_611_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_node_599_);
lean_dec(v_v_578_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_611_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
size_t v___x_603_; size_t v___x_604_; size_t v___x_605_; size_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_603_ = ((size_t)5ULL);
v___x_604_ = lean_usize_shift_right(v_x_565_, v___x_603_);
v___x_605_ = ((size_t)1ULL);
v___x_606_ = lean_usize_add(v_x_566_, v___x_605_);
v___x_607_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_node_599_, v___x_604_, v___x_606_, v_x_567_, v_x_568_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_607_);
v___x_609_ = v___x_601_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
v___y_582_ = v___x_609_;
goto v___jp_581_;
}
}
}
default: 
{
lean_object* v___x_612_; 
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v_x_567_);
lean_ctor_set(v___x_612_, 1, v_x_568_);
v___y_582_ = v___x_612_;
goto v___jp_581_;
}
}
v___jp_581_:
{
lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_583_ = lean_array_fset(v_xs_x27_580_, v_j_572_, v___y_582_);
lean_dec(v_j_572_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_583_);
v___x_585_ = v___x_576_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
else
{
lean_object* v_ks_615_; lean_object* v_vs_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_634_; 
v_ks_615_ = lean_ctor_get(v_x_564_, 0);
v_vs_616_ = lean_ctor_get(v_x_564_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_x_564_);
if (v_isSharedCheck_634_ == 0)
{
v___x_618_ = v_x_564_;
v_isShared_619_ = v_isSharedCheck_634_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_vs_616_);
lean_inc(v_ks_615_);
lean_dec(v_x_564_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_634_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_ks_615_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_vs_616_);
v___x_621_ = v_reuseFailAlloc_633_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v_newNode_622_; size_t v___x_623_; uint8_t v___x_624_; 
v_newNode_622_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3___redArg(v___x_621_, v_x_567_, v_x_568_);
v___x_623_ = ((size_t)7ULL);
v___x_624_ = lean_usize_dec_le(v___x_623_, v_x_566_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_622_);
v___x_626_ = lean_unsigned_to_nat(4u);
v___x_627_ = lean_nat_dec_lt(v___x_625_, v___x_626_);
lean_dec(v___x_625_);
if (v___x_627_ == 0)
{
lean_object* v_ks_628_; lean_object* v_vs_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_ks_628_ = lean_ctor_get(v_newNode_622_, 0);
lean_inc_ref(v_ks_628_);
v_vs_629_ = lean_ctor_get(v_newNode_622_, 1);
lean_inc_ref(v_vs_629_);
lean_dec_ref(v_newNode_622_);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_632_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(v_x_566_, v_ks_628_, v_vs_629_, v___x_630_, v___x_631_);
lean_dec_ref(v_vs_629_);
lean_dec_ref(v_ks_628_);
return v___x_632_;
}
else
{
return v_newNode_622_;
}
}
else
{
return v_newNode_622_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_635_, lean_object* v_keys_636_, lean_object* v_vals_637_, lean_object* v_i_638_, lean_object* v_entries_639_){
_start:
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = lean_array_get_size(v_keys_636_);
v___x_641_ = lean_nat_dec_lt(v_i_638_, v___x_640_);
if (v___x_641_ == 0)
{
lean_dec(v_i_638_);
return v_entries_639_;
}
else
{
lean_object* v_k_642_; lean_object* v_v_643_; uint64_t v___x_644_; size_t v_h_645_; size_t v___x_646_; lean_object* v___x_647_; size_t v___x_648_; size_t v___x_649_; size_t v___x_650_; size_t v_h_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_k_642_ = lean_array_fget_borrowed(v_keys_636_, v_i_638_);
v_v_643_ = lean_array_fget_borrowed(v_vals_637_, v_i_638_);
v___x_644_ = l_Lean_instHashableMVarId_hash(v_k_642_);
v_h_645_ = lean_uint64_to_usize(v___x_644_);
v___x_646_ = ((size_t)5ULL);
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_sub(v_depth_635_, v___x_648_);
v___x_650_ = lean_usize_mul(v___x_646_, v___x_649_);
v_h_651_ = lean_usize_shift_right(v_h_645_, v___x_650_);
v___x_652_ = lean_nat_add(v_i_638_, v___x_647_);
lean_dec(v_i_638_);
lean_inc(v_v_643_);
lean_inc(v_k_642_);
v___x_653_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_entries_639_, v_h_651_, v_depth_635_, v_k_642_, v_v_643_);
v_i_638_ = v___x_652_;
v_entries_639_ = v___x_653_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_655_, lean_object* v_keys_656_, lean_object* v_vals_657_, lean_object* v_i_658_, lean_object* v_entries_659_){
_start:
{
size_t v_depth_boxed_660_; lean_object* v_res_661_; 
v_depth_boxed_660_ = lean_unbox_usize(v_depth_655_);
lean_dec(v_depth_655_);
v_res_661_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_660_, v_keys_656_, v_vals_657_, v_i_658_, v_entries_659_);
lean_dec_ref(v_vals_657_);
lean_dec_ref(v_keys_656_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_662_, lean_object* v_x_663_, lean_object* v_x_664_, lean_object* v_x_665_, lean_object* v_x_666_){
_start:
{
size_t v_x_1135__boxed_667_; size_t v_x_1136__boxed_668_; lean_object* v_res_669_; 
v_x_1135__boxed_667_ = lean_unbox_usize(v_x_663_);
lean_dec(v_x_663_);
v_x_1136__boxed_668_ = lean_unbox_usize(v_x_664_);
lean_dec(v_x_664_);
v_res_669_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_x_662_, v_x_1135__boxed_667_, v_x_1136__boxed_668_, v_x_665_, v_x_666_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(lean_object* v_x_670_, lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
uint64_t v___x_673_; size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
v___x_673_ = l_Lean_instHashableMVarId_hash(v_x_671_);
v___x_674_ = lean_uint64_to_usize(v___x_673_);
v___x_675_ = ((size_t)1ULL);
v___x_676_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_x_670_, v___x_674_, v___x_675_, v_x_671_, v_x_672_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(lean_object* v_mvarId_677_, lean_object* v_val_678_, lean_object* v___y_679_){
_start:
{
lean_object* v___x_681_; lean_object* v_mctx_682_; lean_object* v_cache_683_; lean_object* v_zetaDeltaFVarIds_684_; lean_object* v_postponed_685_; lean_object* v_diag_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_716_; 
v___x_681_ = lean_st_ref_take(v___y_679_);
v_mctx_682_ = lean_ctor_get(v___x_681_, 0);
v_cache_683_ = lean_ctor_get(v___x_681_, 1);
v_zetaDeltaFVarIds_684_ = lean_ctor_get(v___x_681_, 2);
v_postponed_685_ = lean_ctor_get(v___x_681_, 3);
v_diag_686_ = lean_ctor_get(v___x_681_, 4);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_716_ == 0)
{
v___x_688_ = v___x_681_;
v_isShared_689_ = v_isSharedCheck_716_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_diag_686_);
lean_inc(v_postponed_685_);
lean_inc(v_zetaDeltaFVarIds_684_);
lean_inc(v_cache_683_);
lean_inc(v_mctx_682_);
lean_dec(v___x_681_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_716_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_depth_690_; lean_object* v_levelAssignDepth_691_; lean_object* v_lmvarCounter_692_; lean_object* v_mvarCounter_693_; lean_object* v_lDecls_694_; lean_object* v_decls_695_; lean_object* v_userNames_696_; lean_object* v_lAssignment_697_; lean_object* v_eAssignment_698_; lean_object* v_dAssignment_699_; lean_object* v_instanceTypedMVars_700_; lean_object* v_synthNormMemo_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_715_; 
v_depth_690_ = lean_ctor_get(v_mctx_682_, 0);
v_levelAssignDepth_691_ = lean_ctor_get(v_mctx_682_, 1);
v_lmvarCounter_692_ = lean_ctor_get(v_mctx_682_, 2);
v_mvarCounter_693_ = lean_ctor_get(v_mctx_682_, 3);
v_lDecls_694_ = lean_ctor_get(v_mctx_682_, 4);
v_decls_695_ = lean_ctor_get(v_mctx_682_, 5);
v_userNames_696_ = lean_ctor_get(v_mctx_682_, 6);
v_lAssignment_697_ = lean_ctor_get(v_mctx_682_, 7);
v_eAssignment_698_ = lean_ctor_get(v_mctx_682_, 8);
v_dAssignment_699_ = lean_ctor_get(v_mctx_682_, 9);
v_instanceTypedMVars_700_ = lean_ctor_get(v_mctx_682_, 10);
v_synthNormMemo_701_ = lean_ctor_get(v_mctx_682_, 11);
v_isSharedCheck_715_ = !lean_is_exclusive(v_mctx_682_);
if (v_isSharedCheck_715_ == 0)
{
v___x_703_ = v_mctx_682_;
v_isShared_704_ = v_isSharedCheck_715_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_synthNormMemo_701_);
lean_inc(v_instanceTypedMVars_700_);
lean_inc(v_dAssignment_699_);
lean_inc(v_eAssignment_698_);
lean_inc(v_lAssignment_697_);
lean_inc(v_userNames_696_);
lean_inc(v_decls_695_);
lean_inc(v_lDecls_694_);
lean_inc(v_mvarCounter_693_);
lean_inc(v_lmvarCounter_692_);
lean_inc(v_levelAssignDepth_691_);
lean_inc(v_depth_690_);
lean_dec(v_mctx_682_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_715_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_705_ = lean_box(0);
v___x_706_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(v_eAssignment_698_, v_mvarId_677_, v_val_678_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 8, v___x_706_);
v___x_708_ = v___x_703_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_depth_690_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_levelAssignDepth_691_);
lean_ctor_set(v_reuseFailAlloc_714_, 2, v_lmvarCounter_692_);
lean_ctor_set(v_reuseFailAlloc_714_, 3, v_mvarCounter_693_);
lean_ctor_set(v_reuseFailAlloc_714_, 4, v_lDecls_694_);
lean_ctor_set(v_reuseFailAlloc_714_, 5, v_decls_695_);
lean_ctor_set(v_reuseFailAlloc_714_, 6, v_userNames_696_);
lean_ctor_set(v_reuseFailAlloc_714_, 7, v_lAssignment_697_);
lean_ctor_set(v_reuseFailAlloc_714_, 8, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_714_, 9, v_dAssignment_699_);
lean_ctor_set(v_reuseFailAlloc_714_, 10, v_instanceTypedMVars_700_);
lean_ctor_set(v_reuseFailAlloc_714_, 11, v_synthNormMemo_701_);
v___x_708_ = v_reuseFailAlloc_714_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_710_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_708_);
v___x_710_ = v___x_688_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_cache_683_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v_zetaDeltaFVarIds_684_);
lean_ctor_set(v_reuseFailAlloc_713_, 3, v_postponed_685_);
lean_ctor_set(v_reuseFailAlloc_713_, 4, v_diag_686_);
v___x_710_ = v_reuseFailAlloc_713_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_st_ref_put(v___y_679_, v___x_710_);
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_705_);
return v___x_712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg___boxed(lean_object* v_mvarId_717_, lean_object* v_val_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(v_mvarId_717_, v_val_718_, v___y_719_);
lean_dec(v___y_719_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast___lam__0(lean_object* v_goal_722_, lean_object* v_targetNew_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; 
lean_inc(v_goal_722_);
v___x_729_ = l_Lean_MVarId_getTag(v_goal_722_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
v___x_731_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_723_, v_a_730_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_741_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc_n(v_a_732_, 2);
lean_dec_ref_known(v___x_731_, 1);
v___x_733_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(v_goal_722_, v_a_732_, v___y_725_);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v___x_733_, 0);
lean_dec(v_unused_742_);
v___x_735_ = v___x_733_;
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
else
{
lean_dec(v___x_733_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = l_Lean_Expr_mvarId_x21(v_a_732_);
lean_dec(v_a_732_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_737_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec(v_goal_722_);
v_a_743_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_731_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_731_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref(v_targetNew_723_);
lean_dec(v_goal_722_);
v_a_751_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_729_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_729_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast___lam__0___boxed(lean_object* v_goal_759_, lean_object* v_targetNew_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_MVarId_replaceTargetDefEqFast___lam__0(v_goal_759_, v_targetNew_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast(lean_object* v_goal_767_, lean_object* v_targetNew_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v___f_774_; lean_object* v___x_775_; 
lean_inc(v_goal_767_);
v___f_774_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetDefEqFast___lam__0___boxed), 7, 2);
lean_closure_set(v___f_774_, 0, v_goal_767_);
lean_closure_set(v___f_774_, 1, v_targetNew_768_);
v___x_775_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(v_goal_767_, v___f_774_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast___boxed(lean_object* v_goal_776_, lean_object* v_targetNew_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_776_, v_targetNew_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0(lean_object* v_mvarId_784_, lean_object* v_val_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(v_mvarId_784_, v_val_785_, v___y_787_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___boxed(lean_object* v_mvarId_792_, lean_object* v_val_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0(v_mvarId_792_, v_val_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0(lean_object* v_00_u03b2_800_, lean_object* v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(v_x_801_, v_x_802_, v_x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_805_, lean_object* v_x_806_, size_t v_x_807_, size_t v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_x_806_, v_x_807_, v_x_808_, v_x_809_, v_x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_812_, lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v_x_815_, lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
size_t v_x_1454__boxed_818_; size_t v_x_1455__boxed_819_; lean_object* v_res_820_; 
v_x_1454__boxed_818_ = lean_unbox_usize(v_x_814_);
lean_dec(v_x_814_);
v_x_1455__boxed_819_ = lean_unbox_usize(v_x_815_);
lean_dec(v_x_815_);
v_res_820_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2(v_00_u03b2_812_, v_x_813_, v_x_1454__boxed_818_, v_x_1455__boxed_819_, v_x_816_, v_x_817_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_821_, lean_object* v_n_822_, lean_object* v_k_823_, lean_object* v_v_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3___redArg(v_n_822_, v_k_823_, v_v_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_826_, size_t v_depth_827_, lean_object* v_keys_828_, lean_object* v_vals_829_, lean_object* v_heq_830_, lean_object* v_i_831_, lean_object* v_entries_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_827_, v_keys_828_, v_vals_829_, v_i_831_, v_entries_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_834_, lean_object* v_depth_835_, lean_object* v_keys_836_, lean_object* v_vals_837_, lean_object* v_heq_838_, lean_object* v_i_839_, lean_object* v_entries_840_){
_start:
{
size_t v_depth_boxed_841_; lean_object* v_res_842_; 
v_depth_boxed_841_ = lean_unbox_usize(v_depth_835_);
lean_dec(v_depth_835_);
v_res_842_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_834_, v_depth_boxed_841_, v_keys_836_, v_vals_837_, v_heq_838_, v_i_839_, v_entries_840_);
lean_dec_ref(v_vals_837_);
lean_dec_ref(v_keys_836_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_843_, lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_x_846_, lean_object* v_x_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_844_, v_x_845_, v_x_846_, v_x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon(lean_object* v_rule_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_expr_857_; lean_object* v_pattern_858_; lean_object* v_resultPos_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_883_; 
v_expr_857_ = lean_ctor_get(v_rule_849_, 0);
v_pattern_858_ = lean_ctor_get(v_rule_849_, 1);
v_resultPos_859_ = lean_ctor_get(v_rule_849_, 2);
v_isSharedCheck_883_ = !lean_is_exclusive(v_rule_849_);
if (v_isSharedCheck_883_ == 0)
{
v___x_861_ = v_rule_849_;
v_isShared_862_ = v_isSharedCheck_883_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_resultPos_859_);
lean_inc(v_pattern_858_);
lean_inc(v_expr_857_);
lean_dec(v_rule_849_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_883_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_Meta_Sym_Pattern_shareCommon(v_pattern_858_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_874_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_874_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_874_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_874_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 1, v_a_864_);
v___x_869_ = v___x_861_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_expr_857_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_a_864_);
lean_ctor_set(v_reuseFailAlloc_873_, 2, v_resultPos_859_);
v___x_869_ = v_reuseFailAlloc_873_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_871_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_869_);
v___x_871_ = v___x_866_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_del_object(v___x_861_);
lean_dec(v_resultPos_859_);
lean_dec_ref(v_expr_857_);
v_a_875_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_863_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_863_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon___boxed(lean_object* v_rule_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_rule_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(lean_object* v___y_893_, lean_object* v_mctx_894_, lean_object* v_cache_895_, lean_object* v_a_x3f_896_){
_start:
{
lean_object* v___x_898_; lean_object* v_zetaDeltaFVarIds_899_; lean_object* v_postponed_900_; lean_object* v_diag_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_911_; 
v___x_898_ = lean_st_ref_take(v___y_893_);
v_zetaDeltaFVarIds_899_ = lean_ctor_get(v___x_898_, 2);
v_postponed_900_ = lean_ctor_get(v___x_898_, 3);
v_diag_901_ = lean_ctor_get(v___x_898_, 4);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; lean_object* v_unused_913_; 
v_unused_912_ = lean_ctor_get(v___x_898_, 1);
lean_dec(v_unused_912_);
v_unused_913_ = lean_ctor_get(v___x_898_, 0);
lean_dec(v_unused_913_);
v___x_903_ = v___x_898_;
v_isShared_904_ = v_isSharedCheck_911_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_diag_901_);
lean_inc(v_postponed_900_);
lean_inc(v_zetaDeltaFVarIds_899_);
lean_dec(v___x_898_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_911_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_905_ = lean_box(0);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 1, v_cache_895_);
lean_ctor_set(v___x_903_, 0, v_mctx_894_);
v___x_907_ = v___x_903_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_mctx_894_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_cache_895_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_zetaDeltaFVarIds_899_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_postponed_900_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v_diag_901_);
v___x_907_ = v_reuseFailAlloc_910_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_st_ref_put(v___y_893_, v___x_907_);
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_905_);
return v___x_909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0___boxed(lean_object* v___y_914_, lean_object* v_mctx_915_, lean_object* v_cache_916_, lean_object* v_a_x3f_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_914_, v_mctx_915_, v_cache_916_, v_a_x3f_917_);
lean_dec(v_a_x3f_917_);
lean_dec(v___y_914_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(lean_object* v_x_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; lean_object* v_mctx_934_; lean_object* v___x_935_; lean_object* v_cache_936_; lean_object* v___x_937_; 
v___x_933_ = lean_st_ref_get(v___y_929_);
v_mctx_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc_ref(v_mctx_934_);
lean_dec(v___x_933_);
v___x_935_ = lean_st_ref_get(v___y_929_);
v_cache_936_ = lean_ctor_get(v___x_935_, 1);
lean_inc_ref(v_cache_936_);
lean_dec(v___x_935_);
lean_inc(v___y_931_);
lean_inc_ref(v___y_930_);
lean_inc(v___y_929_);
lean_inc_ref(v___y_928_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc(v___y_922_);
lean_inc_ref(v___y_921_);
v___x_937_ = lean_apply_12(v_x_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, lean_box(0));
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_954_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_954_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_954_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_954_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
lean_inc(v_a_938_);
if (v_isShared_941_ == 0)
{
lean_ctor_set_tag(v___x_940_, 1);
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_953_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
v___x_944_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_929_, v_mctx_934_, v_cache_936_, v___x_943_);
lean_dec_ref(v___x_943_);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; 
v_unused_952_ = lean_ctor_get(v___x_944_, 0);
lean_dec(v_unused_952_);
v___x_946_ = v___x_944_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_dec(v___x_944_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v_a_938_);
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_938_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_955_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_937_, 1);
v___x_956_ = lean_box(0);
v___x_957_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_929_, v_mctx_934_, v_cache_936_, v___x_956_);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v___x_957_, 0);
lean_dec(v_unused_965_);
v___x_959_ = v___x_957_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_dec(v___x_957_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 1);
lean_ctor_set(v___x_959_, 0, v_a_955_);
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_955_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___boxed(lean_object* v_x_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(lean_object* v_00_u03b1_980_, lean_object* v_x_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___boxed(lean_object* v_00_u03b1_995_, lean_object* v_x_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(v_00_u03b1_995_, v_x_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(lean_object* v_a_1010_, lean_object* v___x_1011_, lean_object* v_rule_1012_, uint8_t v___x_1013_, uint8_t v_debug_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1010_, v___x_1011_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v___x_1029_ = l_Lean_Expr_mvarId_x21(v_a_1028_);
lean_dec(v_a_1028_);
v___x_1030_ = l_Lean_Meta_Sym_BackwardRule_apply(v___x_1029_, v_rule_1012_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1043_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1043_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1043_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
if (lean_obj_tag(v_a_1031_) == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1035_ = lean_box(v___x_1013_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1035_);
v___x_1037_ = v___x_1033_;
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
else
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
lean_dec_ref_known(v_a_1031_, 1);
v___x_1039_ = lean_box(v_debug_1014_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1039_);
v___x_1041_ = v___x_1033_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
v_a_1044_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1030_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1030_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec_ref(v_rule_1012_);
v_a_1052_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1027_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1027_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed(lean_object** _args){
lean_object* v_a_1060_ = _args[0];
lean_object* v___x_1061_ = _args[1];
lean_object* v_rule_1062_ = _args[2];
lean_object* v___x_1063_ = _args[3];
lean_object* v_debug_1064_ = _args[4];
lean_object* v___y_1065_ = _args[5];
lean_object* v___y_1066_ = _args[6];
lean_object* v___y_1067_ = _args[7];
lean_object* v___y_1068_ = _args[8];
lean_object* v___y_1069_ = _args[9];
lean_object* v___y_1070_ = _args[10];
lean_object* v___y_1071_ = _args[11];
lean_object* v___y_1072_ = _args[12];
lean_object* v___y_1073_ = _args[13];
lean_object* v___y_1074_ = _args[14];
lean_object* v___y_1075_ = _args[15];
lean_object* v___y_1076_ = _args[16];
_start:
{
uint8_t v___x_29546__boxed_1077_; uint8_t v_debug_boxed_1078_; lean_object* v_res_1079_; 
v___x_29546__boxed_1077_ = lean_unbox(v___x_1063_);
v_debug_boxed_1078_ = lean_unbox(v_debug_1064_);
v_res_1079_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(v_a_1060_, v___x_1061_, v_rule_1062_, v___x_29546__boxed_1077_, v_debug_boxed_1078_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(lean_object* v_msg_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_ref_1086_; lean_object* v___x_1087_; lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1096_; 
v_ref_1086_ = lean_ctor_get(v___y_1083_, 2);
v___x_1087_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4_spec__4(v_msg_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
lean_inc(v_ref_1086_);
v___x_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1092_, 0, v_ref_1086_);
lean_ctor_set(v___x_1092_, 1, v_a_1088_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set_tag(v___x_1090_, 1);
lean_ctor_set(v___x_1090_, 0, v___x_1092_);
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg___boxed(lean_object* v_msg_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
return v_res_1103_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0));
v___x_1106_ = l_Lean_stringToMessageData(v___x_1105_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2));
v___x_1109_ = l_Lean_stringToMessageData(v___x_1108_);
return v___x_1109_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4));
v___x_1112_ = l_Lean_stringToMessageData(v___x_1111_);
return v___x_1112_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6));
v___x_1115_ = l_Lean_stringToMessageData(v___x_1114_);
return v___x_1115_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8));
v___x_1118_ = l_Lean_stringToMessageData(v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object* v_rule_1119_, lean_object* v_goal_1120_, lean_object* v_ruleDesc_x3f_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v___x_1134_; 
lean_inc_ref(v_rule_1119_);
lean_inc(v_goal_1120_);
v___x_1134_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_1120_, v_rule_1119_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
if (lean_obj_tag(v_a_1135_) == 0)
{
uint8_t v_debug_1136_; 
v_debug_1136_ = lean_ctor_get_uint8(v_a_1122_, sizeof(void*)*5 + 2);
if (v_debug_1136_ == 0)
{
lean_dec(v_ruleDesc_x3f_1121_);
lean_dec(v_goal_1120_);
lean_dec_ref(v_rule_1119_);
return v___x_1134_;
}
else
{
lean_object* v___x_1137_; 
lean_inc(v_a_1135_);
lean_dec_ref_known(v___x_1134_, 1);
v___x_1137_ = l_Lean_MVarId_getType(v_goal_1120_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1139_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc_n(v_a_1138_, 2);
lean_dec_ref_known(v___x_1137_, 1);
v___x_1139_ = l_Lean_Meta_Sym_unfoldReducible(v_a_1138_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1202_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1202_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1202_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
uint8_t v___x_1144_; 
v___x_1144_ = lean_expr_eqv(v_a_1140_, v_a_1138_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___f_1148_; lean_object* v___x_1149_; 
lean_del_object(v___x_1142_);
v___x_1145_ = lean_box(0);
v___x_1146_ = lean_box(v___x_1144_);
v___x_1147_ = lean_box(v_debug_1136_);
lean_inc_ref(v_rule_1119_);
lean_inc(v_a_1140_);
v___f_1148_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed), 17, 5);
lean_closure_set(v___f_1148_, 0, v_a_1140_);
lean_closure_set(v___f_1148_, 1, v___x_1145_);
lean_closure_set(v___f_1148_, 2, v_rule_1119_);
lean_closure_set(v___f_1148_, 3, v___x_1146_);
lean_closure_set(v___f_1148_, 4, v___x_1147_);
v___x_1149_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v___f_1148_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1190_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1190_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1190_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___y_1155_; uint8_t v___x_1177_; 
v___x_1177_ = lean_unbox(v_a_1150_);
lean_dec(v_a_1150_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1179_; 
lean_dec(v_a_1140_);
lean_dec(v_a_1138_);
lean_dec(v_ruleDesc_x3f_1121_);
lean_dec_ref(v_rule_1119_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v_a_1135_);
v___x_1179_ = v___x_1152_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1135_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
else
{
lean_del_object(v___x_1152_);
if (lean_obj_tag(v_ruleDesc_x3f_1121_) == 0)
{
lean_object* v_expr_1181_; lean_object* v___x_1182_; 
v_expr_1181_ = lean_ctor_get(v_rule_1119_, 0);
lean_inc_ref(v_expr_1181_);
lean_dec_ref(v_rule_1119_);
v___x_1182_ = l_Lean_Expr_getAppFn(v_expr_1181_);
lean_dec_ref(v_expr_1181_);
if (lean_obj_tag(v___x_1182_) == 4)
{
lean_object* v_declName_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v_declName_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_declName_1183_);
lean_dec_ref_known(v___x_1182_, 2);
v___x_1184_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3, &l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3);
v___x_1185_ = l_Lean_MessageData_ofConstName(v_declName_1183_, v___x_1144_);
v___x_1186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1184_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v___x_1184_);
v___y_1155_ = v___x_1187_;
goto v___jp_1154_;
}
else
{
lean_object* v___x_1188_; 
lean_dec_ref(v___x_1182_);
v___x_1188_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9);
v___y_1155_ = v___x_1188_;
goto v___jp_1154_;
}
}
else
{
lean_object* v_val_1189_; 
lean_dec_ref(v_rule_1119_);
v_val_1189_ = lean_ctor_get(v_ruleDesc_x3f_1121_, 0);
lean_inc(v_val_1189_);
lean_dec_ref_known(v_ruleDesc_x3f_1121_, 1);
v___y_1155_ = v_val_1189_;
goto v___jp_1154_;
}
}
v___jp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
v___x_1156_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v___y_1155_);
v___x_1158_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_indentExpr(v_a_1138_);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1161_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = l_Lean_indentExpr(v_a_1140_);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7);
v___x_1167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_1167_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec(v_a_1140_);
lean_dec(v_a_1138_);
lean_dec(v_ruleDesc_x3f_1121_);
lean_dec_ref(v_rule_1119_);
v_a_1191_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1149_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1149_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
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
lean_object* v___x_1200_; 
lean_dec(v_a_1140_);
lean_dec(v_a_1138_);
lean_dec(v_ruleDesc_x3f_1121_);
lean_dec_ref(v_rule_1119_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v_a_1135_);
v___x_1200_ = v___x_1142_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1135_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec(v_a_1138_);
lean_dec(v_ruleDesc_x3f_1121_);
lean_dec_ref(v_rule_1119_);
v_a_1203_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1139_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1139_);
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
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec(v_ruleDesc_x3f_1121_);
lean_dec_ref(v_rule_1119_);
v_a_1211_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1137_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1137_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
else
{
lean_dec(v_ruleDesc_x3f_1121_);
lean_dec(v_goal_1120_);
lean_dec_ref(v_rule_1119_);
return v___x_1134_;
}
}
else
{
lean_dec(v_ruleDesc_x3f_1121_);
lean_dec(v_goal_1120_);
lean_dec_ref(v_rule_1119_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___boxed(lean_object* v_rule_1219_, lean_object* v_goal_1220_, lean_object* v_ruleDesc_x3f_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_1219_, v_goal_1220_, v_ruleDesc_x3f_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(lean_object* v_00_u03b1_1235_, lean_object* v_msg_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_1236_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___boxed(lean_object* v_00_u03b1_1250_, lean_object* v_msg_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(v_00_u03b1_1250_, v_msg_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(lean_object* v_goal_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
uint8_t v_internalize_1277_; 
v_internalize_1277_ = lean_ctor_get_uint8(v_a_1266_, sizeof(void*)*5 + 3);
if (v_internalize_1277_ == 0)
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v_goal_1265_);
return v___x_1278_;
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_box(0);
v___x_1280_ = l_Lean_Meta_Grind_processHypotheses(v_goal_1265_, v___x_1279_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
return v___x_1280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg___boxed(lean_object* v_goal_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses(lean_object* v_goal_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_1294_, v_a_1295_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___boxed(lean_object* v_goal_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_Elab_Tactic_VCGen_processHypotheses(v_goal_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
return v_res_1321_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_VCGen_isProgramName(lean_object* v_n_1322_){
_start:
{
uint8_t v___x_1323_; 
v___x_1323_ = l_Lean_Name_hasMacroScopes(v_n_1322_);
if (v___x_1323_ == 0)
{
uint8_t v___x_1324_; 
v___x_1324_ = l_Lean_Name_isImplementationDetail(v_n_1322_);
if (v___x_1324_ == 0)
{
uint8_t v___x_1325_; 
v___x_1325_ = 1;
return v___x_1325_;
}
else
{
return v___x_1323_;
}
}
else
{
uint8_t v___x_1326_; 
v___x_1326_ = 0;
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_isProgramName___boxed(lean_object* v_n_1327_){
_start:
{
uint8_t v_res_1328_; lean_object* v_r_1329_; 
v_res_1328_ = l_Lean_Elab_Tactic_VCGen_isProgramName(v_n_1327_);
lean_dec(v_n_1327_);
v_r_1329_ = lean_box(v_res_1328_);
return v_r_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_numBindersToIntro(lean_object* v_x_1333_){
_start:
{
switch(lean_obj_tag(v_x_1333_))
{
case 7:
{
lean_object* v_binderType_1334_; lean_object* v_body_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v_binderType_1334_ = lean_ctor_get(v_x_1333_, 1);
v_body_1335_ = lean_ctor_get(v_x_1333_, 2);
v___x_1336_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_numBindersToIntro___closed__1));
v___x_1337_ = l_Lean_Expr_isAppOf(v_binderType_1334_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = l_Lean_Elab_Tactic_VCGen_numBindersToIntro(v_body_1335_);
v___x_1339_ = lean_unsigned_to_nat(1u);
v___x_1340_ = lean_nat_add(v___x_1338_, v___x_1339_);
lean_dec(v___x_1338_);
return v___x_1340_;
}
else
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_unsigned_to_nat(0u);
return v___x_1341_;
}
}
case 8:
{
lean_object* v_body_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_body_1342_ = lean_ctor_get(v_x_1333_, 3);
v___x_1343_ = l_Lean_Elab_Tactic_VCGen_numBindersToIntro(v_body_1342_);
v___x_1344_ = lean_unsigned_to_nat(1u);
v___x_1345_ = lean_nat_add(v___x_1343_, v___x_1344_);
lean_dec(v___x_1343_);
return v___x_1345_;
}
default: 
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_unsigned_to_nat(0u);
return v___x_1346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_numBindersToIntro___boxed(lean_object* v_x_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_Elab_Tactic_VCGen_numBindersToIntro(v_x_1347_);
lean_dec_ref(v_x_1347_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_introsHygienicN_collectBinders(lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_zero_1352_; uint8_t v_isZero_1353_; 
v_zero_1352_ = lean_unsigned_to_nat(0u);
v_isZero_1353_ = lean_nat_dec_eq(v_a_1349_, v_zero_1352_);
if (v_isZero_1353_ == 1)
{
lean_dec_ref(v_a_1350_);
lean_dec(v_a_1349_);
return v_a_1351_;
}
else
{
lean_object* v_one_1354_; lean_object* v_n_1355_; 
v_one_1354_ = lean_unsigned_to_nat(1u);
v_n_1355_ = lean_nat_sub(v_a_1349_, v_one_1354_);
lean_dec(v_a_1349_);
switch(lean_obj_tag(v_a_1350_))
{
case 7:
{
lean_object* v_binderName_1356_; lean_object* v_body_1357_; lean_object* v___x_1358_; 
v_binderName_1356_ = lean_ctor_get(v_a_1350_, 0);
lean_inc(v_binderName_1356_);
v_body_1357_ = lean_ctor_get(v_a_1350_, 2);
lean_inc_ref(v_body_1357_);
lean_dec_ref_known(v_a_1350_, 3);
v___x_1358_ = lean_array_push(v_a_1351_, v_binderName_1356_);
v_a_1349_ = v_n_1355_;
v_a_1350_ = v_body_1357_;
v_a_1351_ = v___x_1358_;
goto _start;
}
case 8:
{
lean_object* v_declName_1360_; lean_object* v_body_1361_; lean_object* v___x_1362_; 
v_declName_1360_ = lean_ctor_get(v_a_1350_, 0);
lean_inc(v_declName_1360_);
v_body_1361_ = lean_ctor_get(v_a_1350_, 3);
lean_inc_ref(v_body_1361_);
lean_dec_ref_known(v_a_1350_, 4);
v___x_1362_ = lean_array_push(v_a_1351_, v_declName_1360_);
v_a_1349_ = v_n_1355_;
v_a_1350_ = v_body_1361_;
v_a_1351_ = v___x_1362_;
goto _start;
}
default: 
{
lean_dec(v_n_1355_);
lean_dec_ref(v_a_1350_);
return v_a_1351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0(lean_object* v_x_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___x_1377_; 
lean_inc(v___y_1371_);
lean_inc_ref(v___y_1370_);
lean_inc(v___y_1369_);
lean_inc_ref(v___y_1368_);
lean_inc(v___y_1367_);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
v___x_1377_ = lean_apply_12(v_x_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, lean_box(0));
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0___boxed(lean_object* v_x_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0(v_x_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(lean_object* v_mvarId_1392_, lean_object* v_x_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___f_1406_; lean_object* v___x_1407_; 
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
lean_inc(v___y_1398_);
lean_inc_ref(v___y_1397_);
lean_inc(v___y_1396_);
lean_inc(v___y_1395_);
lean_inc_ref(v___y_1394_);
v___f_1406_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1406_, 0, v_x_1393_);
lean_closure_set(v___f_1406_, 1, v___y_1394_);
lean_closure_set(v___f_1406_, 2, v___y_1395_);
lean_closure_set(v___f_1406_, 3, v___y_1396_);
lean_closure_set(v___f_1406_, 4, v___y_1397_);
lean_closure_set(v___f_1406_, 5, v___y_1398_);
lean_closure_set(v___f_1406_, 6, v___y_1399_);
lean_closure_set(v___f_1406_, 7, v___y_1400_);
v___x_1407_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1392_, v___f_1406_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1407_) == 0)
{
return v___x_1407_;
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___boxed(lean_object* v_mvarId_1416_, lean_object* v_x_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_mvarId_1416_, v_x_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1(lean_object* v_00_u03b1_1431_, lean_object* v_mvarId_1432_, lean_object* v_x_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_mvarId_1432_, v_x_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___boxed(lean_object* v_00_u03b1_1447_, lean_object* v_mvarId_1448_, lean_object* v_x_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1(v_00_u03b1_1447_, v_mvarId_1448_, v_x_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(lean_object* v_as_1463_, size_t v_sz_1464_, size_t v_i_1465_, lean_object* v_b_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
uint8_t v___x_1471_; 
v___x_1471_ = lean_usize_dec_lt(v_i_1465_, v_sz_1464_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v_b_1466_);
return v___x_1472_;
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1474_; 
v_a_1473_ = lean_array_uget_borrowed(v_as_1463_, v_i_1465_);
lean_inc(v_a_1473_);
v___x_1474_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_a_1473_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1476_; size_t v___x_1477_; size_t v___x_1478_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
v___x_1476_ = lean_array_push(v_b_1466_, v_a_1475_);
v___x_1477_ = ((size_t)1ULL);
v___x_1478_ = lean_usize_add(v_i_1465_, v___x_1477_);
v_i_1465_ = v___x_1478_;
v_b_1466_ = v___x_1476_;
goto _start;
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v_b_1466_);
v_a_1480_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1474_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1474_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg___boxed(lean_object* v_as_1488_, lean_object* v_sz_1489_, lean_object* v_i_1490_, lean_object* v_b_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
size_t v_sz_boxed_1496_; size_t v_i_boxed_1497_; lean_object* v_res_1498_; 
v_sz_boxed_1496_ = lean_unbox_usize(v_sz_1489_);
lean_dec(v_sz_1489_);
v_i_boxed_1497_ = lean_unbox_usize(v_i_1490_);
lean_dec(v_i_1490_);
v_res_1498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(v_as_1488_, v_sz_boxed_1496_, v_i_boxed_1497_, v_b_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec_ref(v_as_1488_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0(lean_object* v_goal_1501_, lean_object* v_n_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___x_1515_; 
lean_inc(v_goal_1501_);
v___x_1515_ = l_Lean_MVarId_getType(v_goal_1501_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1562_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1562_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1562_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v_names_1521_; lean_object* v_binderNames_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1520_ = lean_unsigned_to_nat(0u);
v_names_1521_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___closed__0));
v_binderNames_1522_ = l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_introsHygienicN_collectBinders(v_n_1502_, v_a_1516_, v_names_1521_);
v___x_1523_ = lean_array_get_size(v_binderNames_1522_);
v___x_1524_ = lean_nat_dec_eq(v___x_1523_, v___x_1520_);
if (v___x_1524_ == 0)
{
uint8_t v___x_1525_; size_t v_sz_1526_; size_t v___x_1527_; lean_object* v___x_1528_; 
lean_del_object(v___x_1518_);
v___x_1525_ = 1;
v_sz_1526_ = lean_array_size(v_binderNames_1522_);
v___x_1527_ = ((size_t)0ULL);
v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(v_binderNames_1522_, v_sz_1526_, v___x_1527_, v_names_1521_, v___y_1510_, v___y_1512_, v___y_1513_);
lean_dec_ref(v_binderNames_1522_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
lean_inc(v_goal_1501_);
v___x_1530_ = l_Lean_Meta_Sym_intros(v_goal_1501_, v_a_1529_, v___x_1525_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1542_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1533_ = v___x_1530_;
v_isShared_1534_ = v_isSharedCheck_1542_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1530_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1542_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
if (lean_obj_tag(v_a_1531_) == 1)
{
lean_object* v_mvarId_1535_; lean_object* v___x_1537_; 
lean_dec(v_goal_1501_);
v_mvarId_1535_ = lean_ctor_get(v_a_1531_, 1);
lean_inc(v_mvarId_1535_);
lean_dec_ref_known(v_a_1531_, 2);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v_mvarId_1535_);
v___x_1537_ = v___x_1533_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_mvarId_1535_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
else
{
lean_object* v___x_1540_; 
lean_dec(v_a_1531_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v_goal_1501_);
v___x_1540_ = v___x_1533_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_goal_1501_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_dec(v_goal_1501_);
v_a_1543_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1530_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1530_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec(v_goal_1501_);
v_a_1551_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1528_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1528_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
else
{
lean_object* v___x_1560_; 
lean_dec_ref(v_binderNames_1522_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v_goal_1501_);
v___x_1560_ = v___x_1518_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_goal_1501_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v_n_1502_);
lean_dec(v_goal_1501_);
v_a_1563_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1515_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1515_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___boxed(lean_object* v_goal_1571_, lean_object* v_n_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0(v_goal_1571_, v_n_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN(lean_object* v_goal_1586_, lean_object* v_n_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v___f_1600_; lean_object* v___x_1601_; 
lean_inc(v_goal_1586_);
v___f_1600_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___boxed), 14, 2);
lean_closure_set(v___f_1600_, 0, v_goal_1586_);
lean_closure_set(v___f_1600_, 1, v_n_1587_);
v___x_1601_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_goal_1586_, v___f_1600_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN___boxed(lean_object* v_goal_1602_, lean_object* v_n_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN(v_goal_1602_, v_n_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec_ref(v_a_1609_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0(lean_object* v_as_1617_, size_t v_sz_1618_, size_t v_i_1619_, lean_object* v_b_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(v_as_1617_, v_sz_1618_, v_i_1619_, v_b_1620_, v___y_1628_, v___y_1630_, v___y_1631_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___boxed(lean_object* v_as_1634_, lean_object* v_sz_1635_, lean_object* v_i_1636_, lean_object* v_b_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
size_t v_sz_boxed_1650_; size_t v_i_boxed_1651_; lean_object* v_res_1652_; 
v_sz_boxed_1650_ = lean_unbox_usize(v_sz_1635_);
lean_dec(v_sz_1635_);
v_i_boxed_1651_ = lean_unbox_usize(v_i_1636_);
lean_dec(v_i_1636_);
v_res_1652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0(v_as_1634_, v_sz_boxed_1650_, v_i_boxed_1651_, v_b_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec_ref(v_as_1634_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic(lean_object* v_goal_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v___x_1666_; 
lean_inc(v_goal_1653_);
v___x_1666_ = l_Lean_MVarId_getType(v_goal_1653_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v___x_1668_ = l_Lean_Elab_Tactic_VCGen_numBindersToIntro(v_a_1667_);
lean_dec(v_a_1667_);
v___x_1669_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN(v_goal_1653_, v___x_1668_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
return v___x_1669_;
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_goal_1653_);
v_a_1670_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1666_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1666_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic___boxed(lean_object* v_goal_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Elab_Tactic_VCGen_introsHygienic(v_goal_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(lean_object* v_goal_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_hypSimpMethods_1706_; 
v_hypSimpMethods_1706_ = lean_ctor_get(v_a_1697_, 2);
if (lean_obj_tag(v_hypSimpMethods_1706_) == 1)
{
lean_object* v_val_1707_; lean_object* v_post_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v_val_1707_ = lean_ctor_get(v_hypSimpMethods_1706_, 0);
v_post_1708_ = lean_ctor_get(v_val_1707_, 1);
v___x_1709_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__0));
lean_inc_ref(v_post_1708_);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
lean_ctor_set(v___x_1710_, 1, v_post_1708_);
lean_inc(v_goal_1696_);
v___x_1711_ = l_Lean_MVarId_getType(v_goal_1696_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1713_; lean_object* v_simpState_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1712_);
lean_dec_ref_known(v___x_1711_, 1);
v___x_1713_ = lean_st_ref_get(v_a_1698_);
v_simpState_1714_ = lean_ctor_get(v___x_1713_, 7);
lean_inc_ref(v_simpState_1714_);
lean_dec(v___x_1713_);
v___x_1715_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_1715_, 0, v_a_1712_);
v___x_1716_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__1));
v___x_1717_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_1715_, v___x_1710_, v___x_1716_, v_simpState_1714_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v_fst_1719_; lean_object* v_snd_1720_; lean_object* v___x_1721_; lean_object* v_specBackwardRuleCache_1722_; lean_object* v_splitBackwardRuleCache_1723_; lean_object* v_latticeBackwardRuleCache_1724_; lean_object* v_frameBackwardRuleCache_1725_; lean_object* v_frameDB_1726_; lean_object* v_invariants_1727_; lean_object* v_vcs_1728_; lean_object* v_fuel_1729_; lean_object* v_inlineHandledInvariants_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1739_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
v_fst_1719_ = lean_ctor_get(v_a_1718_, 0);
lean_inc(v_fst_1719_);
v_snd_1720_ = lean_ctor_get(v_a_1718_, 1);
lean_inc(v_snd_1720_);
lean_dec(v_a_1718_);
v___x_1721_ = lean_st_ref_take(v_a_1698_);
v_specBackwardRuleCache_1722_ = lean_ctor_get(v___x_1721_, 0);
v_splitBackwardRuleCache_1723_ = lean_ctor_get(v___x_1721_, 1);
v_latticeBackwardRuleCache_1724_ = lean_ctor_get(v___x_1721_, 2);
v_frameBackwardRuleCache_1725_ = lean_ctor_get(v___x_1721_, 3);
v_frameDB_1726_ = lean_ctor_get(v___x_1721_, 4);
v_invariants_1727_ = lean_ctor_get(v___x_1721_, 5);
v_vcs_1728_ = lean_ctor_get(v___x_1721_, 6);
v_fuel_1729_ = lean_ctor_get(v___x_1721_, 8);
v_inlineHandledInvariants_1730_ = lean_ctor_get(v___x_1721_, 9);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1739_ == 0)
{
lean_object* v_unused_1740_; 
v_unused_1740_ = lean_ctor_get(v___x_1721_, 7);
lean_dec(v_unused_1740_);
v___x_1732_ = v___x_1721_;
v_isShared_1733_ = v_isSharedCheck_1739_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_inlineHandledInvariants_1730_);
lean_inc(v_fuel_1729_);
lean_inc(v_vcs_1728_);
lean_inc(v_invariants_1727_);
lean_inc(v_frameDB_1726_);
lean_inc(v_frameBackwardRuleCache_1725_);
lean_inc(v_latticeBackwardRuleCache_1724_);
lean_inc(v_splitBackwardRuleCache_1723_);
lean_inc(v_specBackwardRuleCache_1722_);
lean_dec(v___x_1721_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1739_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 7, v_snd_1720_);
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_specBackwardRuleCache_1722_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v_splitBackwardRuleCache_1723_);
lean_ctor_set(v_reuseFailAlloc_1738_, 2, v_latticeBackwardRuleCache_1724_);
lean_ctor_set(v_reuseFailAlloc_1738_, 3, v_frameBackwardRuleCache_1725_);
lean_ctor_set(v_reuseFailAlloc_1738_, 4, v_frameDB_1726_);
lean_ctor_set(v_reuseFailAlloc_1738_, 5, v_invariants_1727_);
lean_ctor_set(v_reuseFailAlloc_1738_, 6, v_vcs_1728_);
lean_ctor_set(v_reuseFailAlloc_1738_, 7, v_snd_1720_);
lean_ctor_set(v_reuseFailAlloc_1738_, 8, v_fuel_1729_);
lean_ctor_set(v_reuseFailAlloc_1738_, 9, v_inlineHandledInvariants_1730_);
v___x_1735_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = lean_st_ref_put(v_a_1698_, v___x_1735_);
v___x_1737_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_fst_1719_, v_goal_1696_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_1737_;
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec(v_goal_1696_);
v_a_1741_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1717_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1717_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_dec_ref_known(v___x_1710_, 2);
lean_dec(v_goal_1696_);
v_a_1749_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1711_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1711_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_dec(v_goal_1696_);
v___x_1757_ = lean_box(0);
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___boxed(lean_object* v_goal_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(v_goal_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
lean_dec(v_a_1767_);
lean_dec_ref(v_a_1766_);
lean_dec(v_a_1765_);
lean_dec_ref(v_a_1764_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope(lean_object* v_goal_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(v_goal_1770_, v_a_1771_, v_a_1772_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___boxed(lean_object* v_goal_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope(v_goal_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_a_1787_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
return v_res_1797_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__8));
v___x_1800_ = l_Lean_stringToMessageData(v___x_1799_);
return v___x_1800_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6(void){
_start:
{
uint8_t v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = 0;
v___x_1809_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__5));
v___x_1810_ = l_Lean_MessageData_ofConstName(v___x_1809_, v___x_1808_);
return v___x_1810_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__0));
v___x_1813_ = l_Lean_stringToMessageData(v___x_1812_);
return v___x_1813_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6);
v___x_1815_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1);
v___x_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
lean_ctor_set(v___x_1816_, 1, v___x_1814_);
return v___x_1816_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9);
v___x_1818_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7);
v___x_1819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
lean_ctor_set(v___x_1819_, 1, v___x_1817_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0(lean_object* v_goal_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___x_1843_; 
lean_inc(v_goal_1827_);
v___x_1843_ = l_Lean_MVarId_getType(v_goal_1827_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1917_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1917_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1917_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___x_1857_; uint8_t v___x_1858_; 
lean_inc(v_a_1844_);
v___x_1857_ = l_Lean_Expr_cleanupAnnotations(v_a_1844_);
v___x_1858_ = l_Lean_Expr_isApp(v___x_1857_);
if (v___x_1858_ == 0)
{
lean_dec_ref(v___x_1857_);
lean_del_object(v___x_1846_);
lean_dec(v_a_1844_);
lean_dec(v_goal_1827_);
goto v___jp_1840_;
}
else
{
lean_object* v___x_1859_; uint8_t v___x_1860_; 
v___x_1859_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1857_);
v___x_1860_ = l_Lean_Expr_isApp(v___x_1859_);
if (v___x_1860_ == 0)
{
lean_dec_ref(v___x_1859_);
lean_del_object(v___x_1846_);
lean_dec(v_a_1844_);
lean_dec(v_goal_1827_);
goto v___jp_1840_;
}
else
{
lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1859_);
v___x_1862_ = l_Lean_Expr_isApp(v___x_1861_);
if (v___x_1862_ == 0)
{
lean_dec_ref(v___x_1861_);
lean_del_object(v___x_1846_);
lean_dec(v_a_1844_);
lean_dec(v_goal_1827_);
goto v___jp_1840_;
}
else
{
lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1863_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1861_);
v___x_1864_ = l_Lean_Expr_isApp(v___x_1863_);
if (v___x_1864_ == 0)
{
lean_dec_ref(v___x_1863_);
lean_del_object(v___x_1846_);
lean_dec(v_a_1844_);
lean_dec(v_goal_1827_);
goto v___jp_1840_;
}
else
{
lean_object* v_arg_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v_arg_1865_ = lean_ctor_get(v___x_1863_, 1);
lean_inc_ref(v_arg_1865_);
v___x_1866_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1863_);
v___x_1867_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13));
v___x_1868_ = l_Lean_Expr_isConstOf(v___x_1866_, v___x_1867_);
lean_dec_ref(v___x_1866_);
if (v___x_1868_ == 0)
{
lean_dec_ref(v_arg_1865_);
lean_del_object(v___x_1846_);
lean_dec(v_a_1844_);
lean_dec(v_goal_1827_);
goto v___jp_1840_;
}
else
{
uint8_t v___x_1869_; 
v___x_1869_ = l_Lean_Expr_isForall(v_arg_1865_);
lean_dec_ref(v_arg_1865_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
lean_dec(v_a_1844_);
lean_dec(v_goal_1827_);
v___x_1870_ = lean_box(0);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1870_);
v___x_1872_ = v___x_1846_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
else
{
lean_object* v_backwardRules_1874_; lean_object* v_stateArgIntro_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_del_object(v___x_1846_);
v_backwardRules_1874_ = lean_ctor_get(v___y_1828_, 0);
v_stateArgIntro_1875_ = lean_ctor_get(v_backwardRules_1874_, 1);
v___x_1876_ = lean_box(0);
lean_inc_ref(v_stateArgIntro_1875_);
v___x_1877_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_stateArgIntro_1875_, v_goal_1827_, v___x_1876_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v___x_1877_, 1);
if (lean_obj_tag(v_a_1878_) == 1)
{
lean_object* v_mvarIds_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1908_; 
v_mvarIds_1879_ = lean_ctor_get(v_a_1878_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_a_1878_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1881_ = v_a_1878_;
v_isShared_1882_ = v_isSharedCheck_1908_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_mvarIds_1879_);
lean_dec(v_a_1878_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1908_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
if (lean_obj_tag(v_mvarIds_1879_) == 1)
{
lean_object* v_tail_1883_; 
v_tail_1883_ = lean_ctor_get(v_mvarIds_1879_, 1);
if (lean_obj_tag(v_tail_1883_) == 0)
{
lean_object* v_head_1884_; lean_object* v___x_1885_; 
lean_dec(v_a_1844_);
v_head_1884_ = lean_ctor_get(v_mvarIds_1879_, 0);
lean_inc(v_head_1884_);
lean_dec_ref_known(v_mvarIds_1879_, 2);
v___x_1885_ = l_Lean_Elab_Tactic_VCGen_introsHygienic(v_head_1884_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1887_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc_n(v_a_1886_, 2);
lean_dec_ref_known(v___x_1885_, 1);
v___x_1887_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs(v_a_1886_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
if (lean_obj_tag(v_a_1888_) == 0)
{
lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1898_; 
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1898_ == 0)
{
lean_object* v_unused_1899_; 
v_unused_1899_ = lean_ctor_get(v___x_1887_, 0);
lean_dec(v_unused_1899_);
v___x_1890_ = v___x_1887_;
v_isShared_1891_ = v_isSharedCheck_1898_;
goto v_resetjp_1889_;
}
else
{
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1898_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v_a_1886_);
v___x_1893_ = v___x_1881_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1886_);
v___x_1893_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
lean_object* v___x_1895_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1893_);
v___x_1895_ = v___x_1890_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
else
{
lean_dec(v_a_1886_);
lean_del_object(v___x_1881_);
return v___x_1887_;
}
}
else
{
lean_dec(v_a_1886_);
lean_del_object(v___x_1881_);
return v___x_1887_;
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_del_object(v___x_1881_);
v_a_1900_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1885_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1885_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_1879_, 2);
lean_del_object(v___x_1881_);
v___y_1849_ = v___y_1835_;
v___y_1850_ = v___y_1836_;
v___y_1851_ = v___y_1837_;
v___y_1852_ = v___y_1838_;
goto v___jp_1848_;
}
}
else
{
lean_del_object(v___x_1881_);
lean_dec(v_mvarIds_1879_);
v___y_1849_ = v___y_1835_;
v___y_1850_ = v___y_1836_;
v___y_1851_ = v___y_1837_;
v___y_1852_ = v___y_1838_;
goto v___jp_1848_;
}
}
}
else
{
lean_dec(v_a_1878_);
v___y_1849_ = v___y_1835_;
v___y_1850_ = v___y_1836_;
v___y_1851_ = v___y_1837_;
v___y_1852_ = v___y_1838_;
goto v___jp_1848_;
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v_a_1844_);
v_a_1909_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1877_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1877_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
}
}
}
}
v___jp_1848_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1853_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10);
v___x_1854_ = l_Lean_indentExpr(v_a_1844_);
v___x_1855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1853_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_1855_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
return v___x_1856_;
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec(v_goal_1827_);
v_a_1918_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1843_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1843_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
v___jp_1840_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = lean_box(0);
v___x_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
return v___x_1842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___boxed(lean_object* v_goal_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0(v_goal_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs(lean_object* v_goal_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v___f_1953_; lean_object* v___x_1954_; 
lean_inc(v_goal_1940_);
v___f_1953_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___boxed), 13, 1);
lean_closure_set(v___f_1953_, 0, v_goal_1940_);
v___x_1954_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_goal_1940_, v___f_1953_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___boxed(lean_object* v_goal_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs(v_goal_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_);
lean_dec(v_a_1966_);
lean_dec_ref(v_a_1965_);
lean_dec(v_a_1964_);
lean_dec_ref(v_a_1963_);
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
lean_dec(v_a_1958_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg(lean_object* v_e_1969_, lean_object* v___y_1970_){
_start:
{
uint8_t v___x_1972_; 
v___x_1972_ = l_Lean_Expr_hasMVar(v_e_1969_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; 
v___x_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1973_, 0, v_e_1969_);
return v___x_1973_;
}
else
{
lean_object* v___x_1974_; lean_object* v_mctx_1975_; lean_object* v___x_1976_; lean_object* v_fst_1977_; lean_object* v_snd_1978_; lean_object* v___x_1979_; lean_object* v_cache_1980_; lean_object* v_zetaDeltaFVarIds_1981_; lean_object* v_postponed_1982_; lean_object* v_diag_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1992_; 
v___x_1974_ = lean_st_ref_get(v___y_1970_);
v_mctx_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc_ref(v_mctx_1975_);
lean_dec(v___x_1974_);
v___x_1976_ = l_Lean_instantiateMVarsCore(v_mctx_1975_, v_e_1969_);
v_fst_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_fst_1977_);
v_snd_1978_ = lean_ctor_get(v___x_1976_, 1);
lean_inc(v_snd_1978_);
lean_dec_ref(v___x_1976_);
v___x_1979_ = lean_st_ref_take(v___y_1970_);
v_cache_1980_ = lean_ctor_get(v___x_1979_, 1);
v_zetaDeltaFVarIds_1981_ = lean_ctor_get(v___x_1979_, 2);
v_postponed_1982_ = lean_ctor_get(v___x_1979_, 3);
v_diag_1983_ = lean_ctor_get(v___x_1979_, 4);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v___x_1979_, 0);
lean_dec(v_unused_1993_);
v___x_1985_ = v___x_1979_;
v_isShared_1986_ = v_isSharedCheck_1992_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_diag_1983_);
lean_inc(v_postponed_1982_);
lean_inc(v_zetaDeltaFVarIds_1981_);
lean_inc(v_cache_1980_);
lean_dec(v___x_1979_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1992_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v_snd_1978_);
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_snd_1978_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_cache_1980_);
lean_ctor_set(v_reuseFailAlloc_1991_, 2, v_zetaDeltaFVarIds_1981_);
lean_ctor_set(v_reuseFailAlloc_1991_, 3, v_postponed_1982_);
lean_ctor_set(v_reuseFailAlloc_1991_, 4, v_diag_1983_);
v___x_1988_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_st_ref_put(v___y_1970_, v___x_1988_);
v___x_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1990_, 0, v_fst_1977_);
return v___x_1990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg___boxed(lean_object* v_e_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg(v_e_1994_, v___y_1995_);
lean_dec(v___y_1995_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1(lean_object* v_e_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg(v_e_1998_, v___y_2007_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___boxed(lean_object* v_e_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1(v_e_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(lean_object* v_mvarId_2026_, lean_object* v_val_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___x_2030_; lean_object* v_mctx_2031_; lean_object* v_cache_2032_; lean_object* v_zetaDeltaFVarIds_2033_; lean_object* v_postponed_2034_; lean_object* v_diag_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2065_; 
v___x_2030_ = lean_st_ref_take(v___y_2028_);
v_mctx_2031_ = lean_ctor_get(v___x_2030_, 0);
v_cache_2032_ = lean_ctor_get(v___x_2030_, 1);
v_zetaDeltaFVarIds_2033_ = lean_ctor_get(v___x_2030_, 2);
v_postponed_2034_ = lean_ctor_get(v___x_2030_, 3);
v_diag_2035_ = lean_ctor_get(v___x_2030_, 4);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2037_ = v___x_2030_;
v_isShared_2038_ = v_isSharedCheck_2065_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_diag_2035_);
lean_inc(v_postponed_2034_);
lean_inc(v_zetaDeltaFVarIds_2033_);
lean_inc(v_cache_2032_);
lean_inc(v_mctx_2031_);
lean_dec(v___x_2030_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2065_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v_depth_2039_; lean_object* v_levelAssignDepth_2040_; lean_object* v_lmvarCounter_2041_; lean_object* v_mvarCounter_2042_; lean_object* v_lDecls_2043_; lean_object* v_decls_2044_; lean_object* v_userNames_2045_; lean_object* v_lAssignment_2046_; lean_object* v_eAssignment_2047_; lean_object* v_dAssignment_2048_; lean_object* v_instanceTypedMVars_2049_; lean_object* v_synthNormMemo_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2064_; 
v_depth_2039_ = lean_ctor_get(v_mctx_2031_, 0);
v_levelAssignDepth_2040_ = lean_ctor_get(v_mctx_2031_, 1);
v_lmvarCounter_2041_ = lean_ctor_get(v_mctx_2031_, 2);
v_mvarCounter_2042_ = lean_ctor_get(v_mctx_2031_, 3);
v_lDecls_2043_ = lean_ctor_get(v_mctx_2031_, 4);
v_decls_2044_ = lean_ctor_get(v_mctx_2031_, 5);
v_userNames_2045_ = lean_ctor_get(v_mctx_2031_, 6);
v_lAssignment_2046_ = lean_ctor_get(v_mctx_2031_, 7);
v_eAssignment_2047_ = lean_ctor_get(v_mctx_2031_, 8);
v_dAssignment_2048_ = lean_ctor_get(v_mctx_2031_, 9);
v_instanceTypedMVars_2049_ = lean_ctor_get(v_mctx_2031_, 10);
v_synthNormMemo_2050_ = lean_ctor_get(v_mctx_2031_, 11);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_mctx_2031_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2052_ = v_mctx_2031_;
v_isShared_2053_ = v_isSharedCheck_2064_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_synthNormMemo_2050_);
lean_inc(v_instanceTypedMVars_2049_);
lean_inc(v_dAssignment_2048_);
lean_inc(v_eAssignment_2047_);
lean_inc(v_lAssignment_2046_);
lean_inc(v_userNames_2045_);
lean_inc(v_decls_2044_);
lean_inc(v_lDecls_2043_);
lean_inc(v_mvarCounter_2042_);
lean_inc(v_lmvarCounter_2041_);
lean_inc(v_levelAssignDepth_2040_);
lean_inc(v_depth_2039_);
lean_dec(v_mctx_2031_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2064_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2054_ = lean_box(0);
v___x_2055_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(v_eAssignment_2047_, v_mvarId_2026_, v_val_2027_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 8, v___x_2055_);
v___x_2057_ = v___x_2052_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_depth_2039_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_levelAssignDepth_2040_);
lean_ctor_set(v_reuseFailAlloc_2063_, 2, v_lmvarCounter_2041_);
lean_ctor_set(v_reuseFailAlloc_2063_, 3, v_mvarCounter_2042_);
lean_ctor_set(v_reuseFailAlloc_2063_, 4, v_lDecls_2043_);
lean_ctor_set(v_reuseFailAlloc_2063_, 5, v_decls_2044_);
lean_ctor_set(v_reuseFailAlloc_2063_, 6, v_userNames_2045_);
lean_ctor_set(v_reuseFailAlloc_2063_, 7, v_lAssignment_2046_);
lean_ctor_set(v_reuseFailAlloc_2063_, 8, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2063_, 9, v_dAssignment_2048_);
lean_ctor_set(v_reuseFailAlloc_2063_, 10, v_instanceTypedMVars_2049_);
lean_ctor_set(v_reuseFailAlloc_2063_, 11, v_synthNormMemo_2050_);
v___x_2057_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2059_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2057_);
v___x_2059_ = v___x_2037_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_cache_2032_);
lean_ctor_set(v_reuseFailAlloc_2062_, 2, v_zetaDeltaFVarIds_2033_);
lean_ctor_set(v_reuseFailAlloc_2062_, 3, v_postponed_2034_);
lean_ctor_set(v_reuseFailAlloc_2062_, 4, v_diag_2035_);
v___x_2059_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = lean_st_ref_put(v___y_2028_, v___x_2059_);
v___x_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2054_);
return v___x_2061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg___boxed(lean_object* v_mvarId_2066_, lean_object* v_val_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_mvarId_2066_, v_val_2067_, v___y_2068_);
lean_dec(v___y_2068_);
return v_res_2070_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__0));
v___x_2073_ = l_Lean_stringToMessageData(v___x_2072_);
return v___x_2073_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__3));
v___x_2077_ = l_Lean_stringToMessageData(v___x_2076_);
return v___x_2077_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__8));
v___x_2093_ = l_Lean_mkConst(v___x_2092_, v___x_2091_);
return v___x_2093_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = lean_box(0);
v___x_2099_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__15));
v___x_2100_ = l_Lean_mkConst(v___x_2099_, v___x_2098_);
return v___x_2100_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2105_ = lean_box(0);
v___x_2106_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__18));
v___x_2107_ = l_Lean_mkConst(v___x_2106_, v___x_2105_);
return v___x_2107_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = lean_box(0);
v___x_2112_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__20));
v___x_2113_ = l_Lean_mkConst(v___x_2112_, v___x_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0(lean_object* v_goal_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v___y_2128_; lean_object* v___y_2129_; uint8_t v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v_g_2146_; lean_object* v_fst_2150_; lean_object* v_snd_2151_; lean_object* v___x_2380_; 
lean_inc(v_goal_2114_);
v___x_2380_ = l_Lean_MVarId_getType(v_goal_2114_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2382_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v___x_2382_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg(v_a_2381_, v___y_2123_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2384_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc_n(v_a_2383_, 2);
lean_dec_ref_known(v___x_2382_, 1);
v___x_2384_ = l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(v_a_2383_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2384_, 1);
if (lean_obj_tag(v_a_2385_) == 0)
{
v_fst_2150_ = v_goal_2114_;
v_snd_2151_ = v_a_2383_;
goto v___jp_2149_;
}
else
{
lean_object* v_val_2386_; lean_object* v___x_2387_; 
lean_dec(v_a_2383_);
v_val_2386_ = lean_ctor_get(v_a_2385_, 0);
lean_inc_n(v_val_2386_, 2);
lean_dec_ref_known(v_a_2385_, 1);
v___x_2387_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_2114_, v_val_2386_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2387_, 1);
v_fst_2150_ = v_a_2388_;
v_snd_2151_ = v_val_2386_;
goto v___jp_2149_;
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec(v_val_2386_);
v_a_2389_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2387_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2387_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec(v_a_2383_);
lean_dec(v_goal_2114_);
v_a_2397_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2384_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2384_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec(v_goal_2114_);
v_a_2405_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2382_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2382_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_dec(v_goal_2114_);
v_a_2413_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2380_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2380_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
v___jp_2127_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2135_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1);
v___x_2136_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__2));
lean_inc_ref(v___y_2128_);
v___x_2137_ = l_Lean_Name_mkStr2(v___y_2128_, v___x_2136_);
v___x_2138_ = l_Lean_MessageData_ofConstName(v___x_2137_, v___y_2130_);
v___x_2139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2135_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4);
v___x_2141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = l_Lean_indentExpr(v___y_2129_);
v___x_2143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_2143_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
return v___x_2144_;
}
v___jp_2145_:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2147_, 0, v_g_2146_);
v___x_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
return v___x_2148_;
}
v___jp_2149_:
{
lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2152_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__6));
v___x_2153_ = l_Lean_Expr_isAppOf(v_snd_2151_, v___x_2152_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2154_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__7));
v___x_2155_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__8));
v___x_2156_ = l_Lean_Expr_isAppOf(v_snd_2151_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2157_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__10));
v___x_2158_ = lean_unsigned_to_nat(3u);
v___x_2159_ = l_Lean_Expr_isAppOfArity(v_snd_2151_, v___x_2157_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
lean_dec_ref(v_snd_2151_);
v___x_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2160_, 0, v_fst_2150_);
v___x_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
return v___x_2161_;
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2162_ = l_Lean_Expr_appFn_x21(v_snd_2151_);
v___x_2163_ = l_Lean_Expr_appFn_x21(v___x_2162_);
v___x_2164_ = l_Lean_Expr_appArg_x21(v___x_2163_);
lean_dec_ref(v___x_2163_);
v___x_2165_ = l_Lean_Expr_appArg_x21(v___x_2162_);
lean_dec_ref(v___x_2162_);
v___x_2166_ = l_Lean_Expr_appArg_x21(v_snd_2151_);
lean_dec_ref(v_snd_2151_);
v___x_2167_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v___x_2165_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2169_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
v___x_2169_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v___x_2166_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2171_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
lean_inc_ref(v___x_2164_);
v___x_2171_ = l_Lean_Meta_getLevel(v___x_2164_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2171_, 1);
v___x_2173_ = lean_box(0);
v___x_2174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2174_, 0, v_a_2172_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
v___x_2175_ = l_Lean_mkConst(v___x_2157_, v___x_2174_);
lean_inc(v_a_2170_);
lean_inc(v_a_2168_);
lean_inc_ref(v___x_2164_);
v___x_2176_ = l_Lean_mkApp3(v___x_2175_, v___x_2164_, v_a_2168_, v_a_2170_);
v___x_2177_ = l_Lean_MVarId_replaceTargetDefEqFast(v_fst_2150_, v___x_2176_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v___x_2179_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___closed__0));
lean_inc(v_a_2168_);
v___x_2180_ = l_Lean_Meta_Sym_isDefEqS(v_a_2168_, v_a_2170_, v___x_2159_, v___x_2159_, v___x_2179_, v___x_2179_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2222_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2222_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2222_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
uint8_t v___x_2185_; 
v___x_2185_ = lean_unbox(v_a_2181_);
lean_dec(v_a_2181_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2188_; 
lean_dec(v_a_2168_);
lean_dec_ref(v___x_2164_);
v___x_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2186_, 0, v_a_2178_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2186_);
v___x_2188_ = v___x_2183_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2186_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
else
{
lean_object* v___x_2190_; 
lean_del_object(v___x_2183_);
lean_inc_ref(v___x_2164_);
v___x_2190_ = l_Lean_Meta_getLevel(v___x_2164_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2190_, 1);
v___x_2192_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__12));
v___x_2193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2193_, 0, v_a_2191_);
lean_ctor_set(v___x_2193_, 1, v___x_2173_);
v___x_2194_ = l_Lean_mkConst(v___x_2192_, v___x_2193_);
v___x_2195_ = l_Lean_mkAppB(v___x_2194_, v___x_2164_, v_a_2168_);
v___x_2196_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_a_2178_, v___x_2195_, v___y_2123_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2204_; 
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2204_ == 0)
{
lean_object* v_unused_2205_; 
v_unused_2205_ = lean_ctor_get(v___x_2196_, 0);
lean_dec(v_unused_2205_);
v___x_2198_ = v___x_2196_;
v_isShared_2199_ = v_isSharedCheck_2204_;
goto v_resetjp_2197_;
}
else
{
lean_dec(v___x_2196_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2204_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2200_; lean_object* v___x_2202_; 
v___x_2200_ = lean_box(0);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 0, v___x_2200_);
v___x_2202_ = v___x_2198_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
v_a_2206_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2196_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2196_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_a_2178_);
lean_dec(v_a_2168_);
lean_dec_ref(v___x_2164_);
v_a_2214_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2190_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2190_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v_a_2178_);
lean_dec(v_a_2168_);
lean_dec_ref(v___x_2164_);
v_a_2223_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2180_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2180_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec(v_a_2170_);
lean_dec(v_a_2168_);
lean_dec_ref(v___x_2164_);
v_a_2231_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2177_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2177_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v_a_2170_);
lean_dec(v_a_2168_);
lean_dec_ref(v___x_2164_);
lean_dec(v_fst_2150_);
v_a_2239_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2171_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2171_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v_a_2168_);
lean_dec_ref(v___x_2164_);
lean_dec(v_fst_2150_);
v_a_2247_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2169_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2169_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec_ref(v___x_2166_);
lean_dec_ref(v___x_2164_);
lean_dec(v_fst_2150_);
v_a_2255_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2167_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2167_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
else
{
lean_object* v_backwardRules_2263_; lean_object* v_andIntro_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v_backwardRules_2263_ = lean_ctor_get(v___y_2115_, 0);
v_andIntro_2264_ = lean_ctor_get(v_backwardRules_2263_, 8);
v___x_2265_ = lean_box(0);
lean_inc_ref(v_andIntro_2264_);
v___x_2266_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_andIntro_2264_, v_fst_2150_, v___x_2265_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2266_, 1);
if (lean_obj_tag(v_a_2267_) == 1)
{
lean_object* v_mvarIds_2268_; 
v_mvarIds_2268_ = lean_ctor_get(v_a_2267_, 0);
lean_inc(v_mvarIds_2268_);
lean_dec_ref_known(v_a_2267_, 1);
if (lean_obj_tag(v_mvarIds_2268_) == 1)
{
lean_object* v_tail_2269_; 
v_tail_2269_ = lean_ctor_get(v_mvarIds_2268_, 1);
lean_inc(v_tail_2269_);
if (lean_obj_tag(v_tail_2269_) == 1)
{
lean_object* v_tail_2270_; 
v_tail_2270_ = lean_ctor_get(v_tail_2269_, 1);
if (lean_obj_tag(v_tail_2270_) == 0)
{
lean_object* v_head_2271_; lean_object* v_head_2272_; lean_object* v___x_2273_; 
lean_dec_ref(v_snd_2151_);
v_head_2271_ = lean_ctor_get(v_mvarIds_2268_, 0);
lean_inc(v_head_2271_);
lean_dec_ref_known(v_mvarIds_2268_, 2);
v_head_2272_ = lean_ctor_get(v_tail_2269_, 0);
lean_inc(v_head_2272_);
lean_dec_ref_known(v_tail_2269_, 2);
v___x_2273_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_head_2271_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2275_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref_known(v___x_2273_, 1);
v___x_2275_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_head_2272_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2275_) == 0)
{
if (lean_obj_tag(v_a_2274_) == 0)
{
lean_object* v_a_2276_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
if (lean_obj_tag(v_a_2276_) == 0)
{
return v___x_2275_;
}
else
{
lean_object* v_val_2277_; 
lean_inc_ref(v_a_2276_);
lean_dec_ref_known(v___x_2275_, 1);
v_val_2277_ = lean_ctor_get(v_a_2276_, 0);
lean_inc(v_val_2277_);
lean_dec_ref_known(v_a_2276_, 1);
v_g_2146_ = v_val_2277_;
goto v___jp_2145_;
}
}
else
{
lean_object* v_a_2278_; 
v_a_2278_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2278_);
lean_dec_ref_known(v___x_2275_, 1);
if (lean_obj_tag(v_a_2278_) == 0)
{
lean_object* v_val_2279_; 
v_val_2279_ = lean_ctor_get(v_a_2274_, 0);
lean_inc(v_val_2279_);
lean_dec_ref_known(v_a_2274_, 1);
v_g_2146_ = v_val_2279_;
goto v___jp_2145_;
}
else
{
lean_object* v_val_2280_; lean_object* v_val_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2352_; 
v_val_2280_ = lean_ctor_get(v_a_2274_, 0);
lean_inc(v_val_2280_);
lean_dec_ref_known(v_a_2274_, 1);
v_val_2281_ = lean_ctor_get(v_a_2278_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v_a_2278_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2283_ = v_a_2278_;
v_isShared_2284_ = v_isSharedCheck_2352_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_val_2281_);
lean_dec(v_a_2278_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2352_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; 
lean_inc(v_val_2280_);
v___x_2285_ = l_Lean_MVarId_getType(v_val_2280_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2285_, 1);
lean_inc(v_val_2281_);
v___x_2287_ = l_Lean_MVarId_getType(v_val_2281_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc_n(v_a_2288_, 2);
lean_dec_ref_known(v___x_2287_, 1);
v___x_2289_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13);
lean_inc(v_a_2286_);
v___x_2290_ = l_Lean_mkAppB(v___x_2289_, v_a_2286_, v_a_2288_);
v___x_2291_ = lean_box(0);
v___x_2292_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2290_, v___x_2291_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc_n(v_a_2293_, 2);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2294_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16);
lean_inc(v_a_2288_);
lean_inc(v_a_2286_);
v___x_2295_ = l_Lean_mkApp3(v___x_2294_, v_a_2286_, v_a_2288_, v_a_2293_);
v___x_2296_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_val_2280_, v___x_2295_, v___y_2123_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
lean_dec_ref_known(v___x_2296_, 1);
v___x_2297_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19);
lean_inc(v_a_2293_);
v___x_2298_ = l_Lean_mkApp3(v___x_2297_, v_a_2286_, v_a_2288_, v_a_2293_);
v___x_2299_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_val_2281_, v___x_2298_, v___y_2123_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2310_; 
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2310_ == 0)
{
lean_object* v_unused_2311_; 
v_unused_2311_ = lean_ctor_get(v___x_2299_, 0);
lean_dec(v_unused_2311_);
v___x_2301_ = v___x_2299_;
v_isShared_2302_ = v_isSharedCheck_2310_;
goto v_resetjp_2300_;
}
else
{
lean_dec(v___x_2299_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2310_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2303_; lean_object* v___x_2305_; 
v___x_2303_ = l_Lean_Expr_mvarId_x21(v_a_2293_);
lean_dec(v_a_2293_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v___x_2303_);
v___x_2305_ = v___x_2283_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2307_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2305_);
v___x_2307_ = v___x_2301_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec(v_a_2293_);
lean_del_object(v___x_2283_);
v_a_2312_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2299_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2299_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec(v_a_2293_);
lean_dec(v_a_2288_);
lean_dec(v_a_2286_);
lean_del_object(v___x_2283_);
lean_dec(v_val_2281_);
v_a_2320_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2296_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2296_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_a_2288_);
lean_dec(v_a_2286_);
lean_del_object(v___x_2283_);
lean_dec(v_val_2281_);
lean_dec(v_val_2280_);
v_a_2328_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2292_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2292_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec(v_a_2286_);
lean_del_object(v___x_2283_);
lean_dec(v_val_2281_);
lean_dec(v_val_2280_);
v_a_2336_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2287_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2287_);
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
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_del_object(v___x_2283_);
lean_dec(v_val_2281_);
lean_dec(v_val_2280_);
v_a_2344_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2285_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2285_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2274_);
return v___x_2275_;
}
}
else
{
lean_dec(v_head_2272_);
return v___x_2273_;
}
}
else
{
lean_dec_ref_known(v_tail_2269_, 2);
lean_dec_ref_known(v_mvarIds_2268_, 2);
v___y_2128_ = v___x_2154_;
v___y_2129_ = v_snd_2151_;
v___y_2130_ = v___x_2153_;
v___y_2131_ = v___y_2122_;
v___y_2132_ = v___y_2123_;
v___y_2133_ = v___y_2124_;
v___y_2134_ = v___y_2125_;
goto v___jp_2127_;
}
}
else
{
lean_dec_ref_known(v_mvarIds_2268_, 2);
lean_dec(v_tail_2269_);
v___y_2128_ = v___x_2154_;
v___y_2129_ = v_snd_2151_;
v___y_2130_ = v___x_2153_;
v___y_2131_ = v___y_2122_;
v___y_2132_ = v___y_2123_;
v___y_2133_ = v___y_2124_;
v___y_2134_ = v___y_2125_;
goto v___jp_2127_;
}
}
else
{
lean_dec(v_mvarIds_2268_);
v___y_2128_ = v___x_2154_;
v___y_2129_ = v_snd_2151_;
v___y_2130_ = v___x_2153_;
v___y_2131_ = v___y_2122_;
v___y_2132_ = v___y_2123_;
v___y_2133_ = v___y_2124_;
v___y_2134_ = v___y_2125_;
goto v___jp_2127_;
}
}
else
{
lean_dec(v_a_2267_);
v___y_2128_ = v___x_2154_;
v___y_2129_ = v_snd_2151_;
v___y_2130_ = v___x_2153_;
v___y_2131_ = v___y_2122_;
v___y_2132_ = v___y_2123_;
v___y_2133_ = v___y_2124_;
v___y_2134_ = v___y_2125_;
goto v___jp_2127_;
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec_ref(v_snd_2151_);
v_a_2353_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2266_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2266_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
lean_dec_ref(v_snd_2151_);
v___x_2361_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21);
v___x_2362_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_fst_2150_, v___x_2361_, v___y_2123_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2370_; 
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2370_ == 0)
{
lean_object* v_unused_2371_; 
v_unused_2371_ = lean_ctor_get(v___x_2362_, 0);
lean_dec(v_unused_2371_);
v___x_2364_ = v___x_2362_;
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
else
{
lean_dec(v___x_2362_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2368_; 
v___x_2366_ = lean_box(0);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2366_);
v___x_2368_ = v___x_2364_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
v_a_2372_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2362_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2362_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___boxed(lean_object* v_goal_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0(v_goal_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC(lean_object* v_goal_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_){
_start:
{
lean_object* v___f_2448_; lean_object* v___x_2449_; 
lean_inc(v_goal_2435_);
v___f_2448_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2448_, 0, v_goal_2435_);
v___x_2449_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_goal_2435_, v___f_2448_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___boxed(lean_object* v_goal_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_goal_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0(lean_object* v_mvarId_2464_, lean_object* v_val_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_mvarId_2464_, v_val_2465_, v___y_2474_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___boxed(lean_object* v_mvarId_2479_, lean_object* v_val_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0(v_mvarId_2479_, v_val_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
return v_res_2493_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Reduce(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
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
