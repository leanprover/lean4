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
v___y_305_ = v_a_348_;
v___y_306_ = v_a_350_;
goto v___jp_304_;
}
else
{
if (v___x_353_ == 0)
{
v___y_305_ = v_a_348_;
v___y_306_ = v_a_350_;
goto v___jp_304_;
}
else
{
size_t v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_usize_of_nat(v___x_352_);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__3(v_a_348_, v___x_333_, v___x_354_);
if (v___x_355_ == 0)
{
v___y_305_ = v_a_348_;
v___y_306_ = v_a_350_;
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
lean_ctor_set(v___x_307_, 0, v___y_305_);
lean_ctor_set(v___x_307_, 1, v___y_306_);
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
size_t v_x_1135__boxed_664_; size_t v_x_1136__boxed_665_; lean_object* v_res_666_; 
v_x_1135__boxed_664_ = lean_unbox_usize(v_x_660_);
lean_dec(v_x_660_);
v_x_1136__boxed_665_ = lean_unbox_usize(v_x_661_);
lean_dec(v_x_661_);
v_res_666_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_x_659_, v_x_1135__boxed_664_, v_x_1136__boxed_665_, v_x_662_, v_x_663_);
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
lean_object* v___x_678_; lean_object* v_mctx_679_; lean_object* v_cache_680_; lean_object* v_zetaDeltaFVarIds_681_; lean_object* v_postponed_682_; lean_object* v_diag_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_713_; 
v___x_678_ = lean_st_ref_take(v___y_676_);
v_mctx_679_ = lean_ctor_get(v___x_678_, 0);
v_cache_680_ = lean_ctor_get(v___x_678_, 1);
v_zetaDeltaFVarIds_681_ = lean_ctor_get(v___x_678_, 2);
v_postponed_682_ = lean_ctor_get(v___x_678_, 3);
v_diag_683_ = lean_ctor_get(v___x_678_, 4);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_713_ == 0)
{
v___x_685_ = v___x_678_;
v_isShared_686_ = v_isSharedCheck_713_;
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
v_isShared_686_ = v_isSharedCheck_713_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v_depth_687_; lean_object* v_levelAssignDepth_688_; lean_object* v_lmvarCounter_689_; lean_object* v_mvarCounter_690_; lean_object* v_lDecls_691_; lean_object* v_decls_692_; lean_object* v_userNames_693_; lean_object* v_lAssignment_694_; lean_object* v_eAssignment_695_; lean_object* v_dAssignment_696_; lean_object* v_instanceTypedMVars_697_; lean_object* v_synthNormMemo_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_712_; 
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
v_synthNormMemo_698_ = lean_ctor_get(v_mctx_679_, 11);
v_isSharedCheck_712_ = !lean_is_exclusive(v_mctx_679_);
if (v_isSharedCheck_712_ == 0)
{
v___x_700_ = v_mctx_679_;
v_isShared_701_ = v_isSharedCheck_712_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_synthNormMemo_698_);
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
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_712_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_702_ = lean_box(0);
v___x_703_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(v_eAssignment_695_, v_mvarId_674_, v_val_675_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 8, v___x_703_);
v___x_705_ = v___x_700_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_depth_687_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_levelAssignDepth_688_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v_lmvarCounter_689_);
lean_ctor_set(v_reuseFailAlloc_711_, 3, v_mvarCounter_690_);
lean_ctor_set(v_reuseFailAlloc_711_, 4, v_lDecls_691_);
lean_ctor_set(v_reuseFailAlloc_711_, 5, v_decls_692_);
lean_ctor_set(v_reuseFailAlloc_711_, 6, v_userNames_693_);
lean_ctor_set(v_reuseFailAlloc_711_, 7, v_lAssignment_694_);
lean_ctor_set(v_reuseFailAlloc_711_, 8, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_711_, 9, v_dAssignment_696_);
lean_ctor_set(v_reuseFailAlloc_711_, 10, v_instanceTypedMVars_697_);
lean_ctor_set(v_reuseFailAlloc_711_, 11, v_synthNormMemo_698_);
v___x_705_ = v_reuseFailAlloc_711_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_707_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_705_);
v___x_707_ = v___x_685_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_cache_680_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_zetaDeltaFVarIds_681_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v_postponed_682_);
lean_ctor_set(v_reuseFailAlloc_710_, 4, v_diag_683_);
v___x_707_ = v_reuseFailAlloc_710_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_st_ref_put(v___y_676_, v___x_707_);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_702_);
return v___x_709_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg___boxed(lean_object* v_mvarId_714_, lean_object* v_val_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(v_mvarId_714_, v_val_715_, v___y_716_);
lean_dec(v___y_716_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast___lam__0(lean_object* v_goal_719_, lean_object* v_targetNew_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; 
lean_inc(v_goal_719_);
v___x_726_ = l_Lean_MVarId_getTag(v_goal_719_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_728_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
v___x_728_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_720_, v_a_727_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_738_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc_n(v_a_729_, 2);
lean_dec_ref_known(v___x_728_, 1);
v___x_730_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(v_goal_719_, v_a_729_, v___y_722_);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; 
v_unused_739_ = lean_ctor_get(v___x_730_, 0);
lean_dec(v_unused_739_);
v___x_732_ = v___x_730_;
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
else
{
lean_dec(v___x_730_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_734_ = l_Lean_Expr_mvarId_x21(v_a_729_);
lean_dec(v_a_729_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_734_);
v___x_736_ = v___x_732_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v_goal_719_);
v_a_740_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_728_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_728_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec_ref(v_targetNew_720_);
lean_dec(v_goal_719_);
v_a_748_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_726_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_726_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast___lam__0___boxed(lean_object* v_goal_756_, lean_object* v_targetNew_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_MVarId_replaceTargetDefEqFast___lam__0(v_goal_756_, v_targetNew_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast(lean_object* v_goal_764_, lean_object* v_targetNew_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___f_771_; lean_object* v___x_772_; 
lean_inc(v_goal_764_);
v___f_771_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetDefEqFast___lam__0___boxed), 7, 2);
lean_closure_set(v___f_771_, 0, v_goal_764_);
lean_closure_set(v___f_771_, 1, v_targetNew_765_);
v___x_772_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(v_goal_764_, v___f_771_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast___boxed(lean_object* v_goal_773_, lean_object* v_targetNew_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_773_, v_targetNew_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0(lean_object* v_mvarId_781_, lean_object* v_val_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(v_mvarId_781_, v_val_782_, v___y_784_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___boxed(lean_object* v_mvarId_789_, lean_object* v_val_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0(v_mvarId_789_, v_val_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0(lean_object* v_00_u03b2_797_, lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(v_x_798_, v_x_799_, v_x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_802_, lean_object* v_x_803_, size_t v_x_804_, size_t v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_x_803_, v_x_804_, v_x_805_, v_x_806_, v_x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
size_t v_x_1454__boxed_815_; size_t v_x_1455__boxed_816_; lean_object* v_res_817_; 
v_x_1454__boxed_815_ = lean_unbox_usize(v_x_811_);
lean_dec(v_x_811_);
v_x_1455__boxed_816_ = lean_unbox_usize(v_x_812_);
lean_dec(v_x_812_);
v_res_817_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2(v_00_u03b2_809_, v_x_810_, v_x_1454__boxed_815_, v_x_1455__boxed_816_, v_x_813_, v_x_814_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_818_, lean_object* v_n_819_, lean_object* v_k_820_, lean_object* v_v_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3___redArg(v_n_819_, v_k_820_, v_v_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_823_, size_t v_depth_824_, lean_object* v_keys_825_, lean_object* v_vals_826_, lean_object* v_heq_827_, lean_object* v_i_828_, lean_object* v_entries_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_824_, v_keys_825_, v_vals_826_, v_i_828_, v_entries_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_831_, lean_object* v_depth_832_, lean_object* v_keys_833_, lean_object* v_vals_834_, lean_object* v_heq_835_, lean_object* v_i_836_, lean_object* v_entries_837_){
_start:
{
size_t v_depth_boxed_838_; lean_object* v_res_839_; 
v_depth_boxed_838_ = lean_unbox_usize(v_depth_832_);
lean_dec(v_depth_832_);
v_res_839_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_831_, v_depth_boxed_838_, v_keys_833_, v_vals_834_, v_heq_835_, v_i_836_, v_entries_837_);
lean_dec_ref(v_vals_834_);
lean_dec_ref(v_keys_833_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_841_, v_x_842_, v_x_843_, v_x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon(lean_object* v_rule_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_expr_854_; lean_object* v_pattern_855_; lean_object* v_resultPos_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_880_; 
v_expr_854_ = lean_ctor_get(v_rule_846_, 0);
v_pattern_855_ = lean_ctor_get(v_rule_846_, 1);
v_resultPos_856_ = lean_ctor_get(v_rule_846_, 2);
v_isSharedCheck_880_ = !lean_is_exclusive(v_rule_846_);
if (v_isSharedCheck_880_ == 0)
{
v___x_858_ = v_rule_846_;
v_isShared_859_ = v_isSharedCheck_880_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_resultPos_856_);
lean_inc(v_pattern_855_);
lean_inc(v_expr_854_);
lean_dec(v_rule_846_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_880_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Meta_Sym_Pattern_shareCommon(v_pattern_855_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_871_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_871_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_871_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_871_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 1, v_a_861_);
v___x_866_ = v___x_858_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_expr_854_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_a_861_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_resultPos_856_);
v___x_866_ = v_reuseFailAlloc_870_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_868_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_866_);
v___x_868_ = v___x_863_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_del_object(v___x_858_);
lean_dec(v_resultPos_856_);
lean_dec_ref(v_expr_854_);
v_a_872_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_860_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_860_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon___boxed(lean_object* v_rule_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_rule_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(lean_object* v___y_890_, lean_object* v_mctx_891_, lean_object* v_cache_892_, lean_object* v_a_x3f_893_){
_start:
{
lean_object* v___x_895_; lean_object* v_zetaDeltaFVarIds_896_; lean_object* v_postponed_897_; lean_object* v_diag_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_908_; 
v___x_895_ = lean_st_ref_take(v___y_890_);
v_zetaDeltaFVarIds_896_ = lean_ctor_get(v___x_895_, 2);
v_postponed_897_ = lean_ctor_get(v___x_895_, 3);
v_diag_898_ = lean_ctor_get(v___x_895_, 4);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; lean_object* v_unused_910_; 
v_unused_909_ = lean_ctor_get(v___x_895_, 1);
lean_dec(v_unused_909_);
v_unused_910_ = lean_ctor_get(v___x_895_, 0);
lean_dec(v_unused_910_);
v___x_900_ = v___x_895_;
v_isShared_901_ = v_isSharedCheck_908_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_diag_898_);
lean_inc(v_postponed_897_);
lean_inc(v_zetaDeltaFVarIds_896_);
lean_dec(v___x_895_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_908_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_902_ = lean_box(0);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 1, v_cache_892_);
lean_ctor_set(v___x_900_, 0, v_mctx_891_);
v___x_904_ = v___x_900_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_mctx_891_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_cache_892_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_zetaDeltaFVarIds_896_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v_postponed_897_);
lean_ctor_set(v_reuseFailAlloc_907_, 4, v_diag_898_);
v___x_904_ = v_reuseFailAlloc_907_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_st_ref_put(v___y_890_, v___x_904_);
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_902_);
return v___x_906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0___boxed(lean_object* v___y_911_, lean_object* v_mctx_912_, lean_object* v_cache_913_, lean_object* v_a_x3f_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_911_, v_mctx_912_, v_cache_913_, v_a_x3f_914_);
lean_dec(v_a_x3f_914_);
lean_dec(v___y_911_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(lean_object* v_x_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; lean_object* v_mctx_931_; lean_object* v___x_932_; lean_object* v_cache_933_; lean_object* v___x_934_; 
v___x_930_ = lean_st_ref_get(v___y_926_);
v_mctx_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc_ref(v_mctx_931_);
lean_dec(v___x_930_);
v___x_932_ = lean_st_ref_get(v___y_926_);
v_cache_933_ = lean_ctor_get(v___x_932_, 1);
lean_inc_ref(v_cache_933_);
lean_dec(v___x_932_);
lean_inc(v___y_928_);
lean_inc_ref(v___y_927_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
lean_inc(v___y_922_);
lean_inc_ref(v___y_921_);
lean_inc(v___y_920_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
v___x_934_ = lean_apply_12(v_x_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, lean_box(0));
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_951_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_951_ == 0)
{
v___x_937_ = v___x_934_;
v_isShared_938_ = v_isSharedCheck_951_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_951_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
lean_inc(v_a_935_);
if (v_isShared_938_ == 0)
{
lean_ctor_set_tag(v___x_937_, 1);
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_950_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
v___x_941_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_926_, v_mctx_931_, v_cache_933_, v___x_940_);
lean_dec_ref(v___x_940_);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v___x_941_, 0);
lean_dec(v_unused_949_);
v___x_943_ = v___x_941_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_dec(v___x_941_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v_a_935_);
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_935_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
v_a_952_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_934_, 1);
v___x_953_ = lean_box(0);
v___x_954_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_926_, v_mctx_931_, v_cache_933_, v___x_953_);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; 
v_unused_962_ = lean_ctor_get(v___x_954_, 0);
lean_dec(v_unused_962_);
v___x_956_ = v___x_954_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_dec(v___x_954_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set_tag(v___x_956_, 1);
lean_ctor_set(v___x_956_, 0, v_a_952_);
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_952_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___boxed(lean_object* v_x_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(lean_object* v_00_u03b1_977_, lean_object* v_x_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___boxed(lean_object* v_00_u03b1_992_, lean_object* v_x_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(v_00_u03b1_992_, v_x_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(lean_object* v_a_1007_, lean_object* v___x_1008_, lean_object* v_rule_1009_, uint8_t v___x_1010_, uint8_t v_debug_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1007_, v___x_1008_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v___x_1026_ = l_Lean_Expr_mvarId_x21(v_a_1025_);
lean_dec(v_a_1025_);
v___x_1027_ = l_Lean_Meta_Sym_BackwardRule_apply(v___x_1026_, v_rule_1009_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1040_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1040_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1040_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
if (lean_obj_tag(v_a_1028_) == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1032_ = lean_box(v___x_1010_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1032_);
v___x_1034_ = v___x_1030_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
else
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
lean_dec_ref_known(v_a_1028_, 1);
v___x_1036_ = lean_box(v_debug_1011_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1036_);
v___x_1038_ = v___x_1030_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
v_a_1041_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1027_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1027_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec_ref(v_rule_1009_);
v_a_1049_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1024_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1024_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed(lean_object** _args){
lean_object* v_a_1057_ = _args[0];
lean_object* v___x_1058_ = _args[1];
lean_object* v_rule_1059_ = _args[2];
lean_object* v___x_1060_ = _args[3];
lean_object* v_debug_1061_ = _args[4];
lean_object* v___y_1062_ = _args[5];
lean_object* v___y_1063_ = _args[6];
lean_object* v___y_1064_ = _args[7];
lean_object* v___y_1065_ = _args[8];
lean_object* v___y_1066_ = _args[9];
lean_object* v___y_1067_ = _args[10];
lean_object* v___y_1068_ = _args[11];
lean_object* v___y_1069_ = _args[12];
lean_object* v___y_1070_ = _args[13];
lean_object* v___y_1071_ = _args[14];
lean_object* v___y_1072_ = _args[15];
lean_object* v___y_1073_ = _args[16];
_start:
{
uint8_t v___x_29547__boxed_1074_; uint8_t v_debug_boxed_1075_; lean_object* v_res_1076_; 
v___x_29547__boxed_1074_ = lean_unbox(v___x_1060_);
v_debug_boxed_1075_ = lean_unbox(v_debug_1061_);
v_res_1076_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(v_a_1057_, v___x_1058_, v_rule_1059_, v___x_29547__boxed_1074_, v_debug_boxed_1075_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(lean_object* v_msg_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_ref_1083_; lean_object* v___x_1084_; lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1093_; 
v_ref_1083_ = lean_ctor_get(v___y_1080_, 2);
v___x_1084_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4_spec__4(v_msg_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
lean_inc(v_ref_1083_);
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v_ref_1083_);
lean_ctor_set(v___x_1089_, 1, v_a_1085_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set_tag(v___x_1087_, 1);
lean_ctor_set(v___x_1087_, 0, v___x_1089_);
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg___boxed(lean_object* v_msg_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
return v_res_1100_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0));
v___x_1103_ = l_Lean_stringToMessageData(v___x_1102_);
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2));
v___x_1106_ = l_Lean_stringToMessageData(v___x_1105_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4));
v___x_1109_ = l_Lean_stringToMessageData(v___x_1108_);
return v___x_1109_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6));
v___x_1112_ = l_Lean_stringToMessageData(v___x_1111_);
return v___x_1112_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8));
v___x_1115_ = l_Lean_stringToMessageData(v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object* v_rule_1116_, lean_object* v_goal_1117_, lean_object* v_ruleDesc_x3f_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v___x_1131_; 
lean_inc_ref(v_rule_1116_);
lean_inc(v_goal_1117_);
v___x_1131_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_1117_, v_rule_1116_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
if (lean_obj_tag(v_a_1132_) == 0)
{
uint8_t v_debug_1133_; 
v_debug_1133_ = lean_ctor_get_uint8(v_a_1119_, sizeof(void*)*5 + 2);
if (v_debug_1133_ == 0)
{
lean_dec(v_ruleDesc_x3f_1118_);
lean_dec(v_goal_1117_);
lean_dec_ref(v_rule_1116_);
return v___x_1131_;
}
else
{
lean_object* v___x_1134_; 
lean_inc(v_a_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v___x_1134_ = l_Lean_MVarId_getType(v_goal_1117_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1136_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc_n(v_a_1135_, 2);
lean_dec_ref_known(v___x_1134_, 1);
v___x_1136_ = l_Lean_Meta_Sym_unfoldReducible(v_a_1135_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1199_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1139_ = v___x_1136_;
v_isShared_1140_ = v_isSharedCheck_1199_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1136_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1199_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
uint8_t v___x_1141_; 
v___x_1141_ = lean_expr_eqv(v_a_1137_, v_a_1135_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___f_1145_; lean_object* v___x_1146_; 
lean_del_object(v___x_1139_);
v___x_1142_ = lean_box(0);
v___x_1143_ = lean_box(v___x_1141_);
v___x_1144_ = lean_box(v_debug_1133_);
lean_inc_ref(v_rule_1116_);
lean_inc(v_a_1137_);
v___f_1145_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed), 17, 5);
lean_closure_set(v___f_1145_, 0, v_a_1137_);
lean_closure_set(v___f_1145_, 1, v___x_1142_);
lean_closure_set(v___f_1145_, 2, v_rule_1116_);
lean_closure_set(v___f_1145_, 3, v___x_1143_);
lean_closure_set(v___f_1145_, 4, v___x_1144_);
v___x_1146_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v___f_1145_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1187_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1187_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1187_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___y_1152_; uint8_t v___x_1174_; 
v___x_1174_ = lean_unbox(v_a_1147_);
lean_dec(v_a_1147_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1176_; 
lean_dec(v_a_1137_);
lean_dec(v_a_1135_);
lean_dec(v_ruleDesc_x3f_1118_);
lean_dec_ref(v_rule_1116_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v_a_1132_);
v___x_1176_ = v___x_1149_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1132_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
else
{
lean_del_object(v___x_1149_);
if (lean_obj_tag(v_ruleDesc_x3f_1118_) == 0)
{
lean_object* v_expr_1178_; lean_object* v___x_1179_; 
v_expr_1178_ = lean_ctor_get(v_rule_1116_, 0);
lean_inc_ref(v_expr_1178_);
lean_dec_ref(v_rule_1116_);
v___x_1179_ = l_Lean_Expr_getAppFn(v_expr_1178_);
lean_dec_ref(v_expr_1178_);
if (lean_obj_tag(v___x_1179_) == 4)
{
lean_object* v_declName_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_declName_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_declName_1180_);
lean_dec_ref_known(v___x_1179_, 2);
v___x_1181_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3, &l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3);
v___x_1182_ = l_Lean_MessageData_ofConstName(v_declName_1180_, v___x_1141_);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v___x_1181_);
v___y_1152_ = v___x_1184_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1185_; 
lean_dec_ref(v___x_1179_);
v___x_1185_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9);
v___y_1152_ = v___x_1185_;
goto v___jp_1151_;
}
}
else
{
lean_object* v_val_1186_; 
lean_dec_ref(v_rule_1116_);
v_val_1186_ = lean_ctor_get(v_ruleDesc_x3f_1118_, 0);
lean_inc(v_val_1186_);
lean_dec_ref_known(v_ruleDesc_x3f_1118_, 1);
v___y_1152_ = v_val_1186_;
goto v___jp_1151_;
}
}
v___jp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
v___x_1153_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v___y_1152_);
v___x_1155_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l_Lean_indentExpr(v_a_1135_);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = l_Lean_indentExpr(v_a_1137_);
v___x_1162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7);
v___x_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_1164_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
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
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec(v_a_1137_);
lean_dec(v_a_1135_);
lean_dec(v_ruleDesc_x3f_1118_);
lean_dec_ref(v_rule_1116_);
v_a_1188_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1146_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1146_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_object* v___x_1197_; 
lean_dec(v_a_1137_);
lean_dec(v_a_1135_);
lean_dec(v_ruleDesc_x3f_1118_);
lean_dec_ref(v_rule_1116_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v_a_1132_);
v___x_1197_ = v___x_1139_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1132_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec(v_a_1135_);
lean_dec(v_ruleDesc_x3f_1118_);
lean_dec_ref(v_rule_1116_);
v_a_1200_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1136_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1136_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec(v_ruleDesc_x3f_1118_);
lean_dec_ref(v_rule_1116_);
v_a_1208_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1134_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1134_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
else
{
lean_dec(v_ruleDesc_x3f_1118_);
lean_dec(v_goal_1117_);
lean_dec_ref(v_rule_1116_);
return v___x_1131_;
}
}
else
{
lean_dec(v_ruleDesc_x3f_1118_);
lean_dec(v_goal_1117_);
lean_dec_ref(v_rule_1116_);
return v___x_1131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___boxed(lean_object* v_rule_1216_, lean_object* v_goal_1217_, lean_object* v_ruleDesc_x3f_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_1216_, v_goal_1217_, v_ruleDesc_x3f_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(lean_object* v_00_u03b1_1232_, lean_object* v_msg_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_1233_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___boxed(lean_object* v_00_u03b1_1247_, lean_object* v_msg_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(v_00_u03b1_1247_, v_msg_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(lean_object* v_goal_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
uint8_t v_internalize_1274_; 
v_internalize_1274_ = lean_ctor_get_uint8(v_a_1263_, sizeof(void*)*5 + 3);
if (v_internalize_1274_ == 0)
{
lean_object* v___x_1275_; 
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v_goal_1262_);
return v___x_1275_;
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_box(0);
v___x_1277_ = l_Lean_Meta_Grind_processHypotheses(v_goal_1262_, v___x_1276_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg___boxed(lean_object* v_goal_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses(lean_object* v_goal_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_1291_, v_a_1292_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___boxed(lean_object* v_goal_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_Elab_Tactic_VCGen_processHypotheses(v_goal_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
return v_res_1318_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_VCGen_isProgramName(lean_object* v_n_1319_){
_start:
{
uint8_t v___x_1320_; 
v___x_1320_ = l_Lean_Name_hasMacroScopes(v_n_1319_);
if (v___x_1320_ == 0)
{
uint8_t v___x_1321_; 
v___x_1321_ = l_Lean_Name_isImplementationDetail(v_n_1319_);
if (v___x_1321_ == 0)
{
uint8_t v___x_1322_; 
v___x_1322_ = 1;
return v___x_1322_;
}
else
{
return v___x_1320_;
}
}
else
{
uint8_t v___x_1323_; 
v___x_1323_ = 0;
return v___x_1323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_isProgramName___boxed(lean_object* v_n_1324_){
_start:
{
uint8_t v_res_1325_; lean_object* v_r_1326_; 
v_res_1325_ = l_Lean_Elab_Tactic_VCGen_isProgramName(v_n_1324_);
lean_dec(v_n_1324_);
v_r_1326_ = lean_box(v_res_1325_);
return v_r_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_numBindersToIntro(lean_object* v_x_1330_){
_start:
{
switch(lean_obj_tag(v_x_1330_))
{
case 7:
{
lean_object* v_binderType_1331_; lean_object* v_body_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v_binderType_1331_ = lean_ctor_get(v_x_1330_, 1);
v_body_1332_ = lean_ctor_get(v_x_1330_, 2);
v___x_1333_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_numBindersToIntro___closed__1));
v___x_1334_ = l_Lean_Expr_isAppOf(v_binderType_1331_, v___x_1333_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1335_ = l_Lean_Elab_Tactic_VCGen_numBindersToIntro(v_body_1332_);
v___x_1336_ = lean_unsigned_to_nat(1u);
v___x_1337_ = lean_nat_add(v___x_1335_, v___x_1336_);
lean_dec(v___x_1335_);
return v___x_1337_;
}
else
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_unsigned_to_nat(0u);
return v___x_1338_;
}
}
case 8:
{
lean_object* v_body_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_body_1339_ = lean_ctor_get(v_x_1330_, 3);
v___x_1340_ = l_Lean_Elab_Tactic_VCGen_numBindersToIntro(v_body_1339_);
v___x_1341_ = lean_unsigned_to_nat(1u);
v___x_1342_ = lean_nat_add(v___x_1340_, v___x_1341_);
lean_dec(v___x_1340_);
return v___x_1342_;
}
default: 
{
lean_object* v___x_1343_; 
v___x_1343_ = lean_unsigned_to_nat(0u);
return v___x_1343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_numBindersToIntro___boxed(lean_object* v_x_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_Elab_Tactic_VCGen_numBindersToIntro(v_x_1344_);
lean_dec_ref(v_x_1344_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_introsHygienicN_collectBinders(lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_zero_1349_; uint8_t v_isZero_1350_; 
v_zero_1349_ = lean_unsigned_to_nat(0u);
v_isZero_1350_ = lean_nat_dec_eq(v_a_1346_, v_zero_1349_);
if (v_isZero_1350_ == 1)
{
lean_dec_ref(v_a_1347_);
lean_dec(v_a_1346_);
return v_a_1348_;
}
else
{
lean_object* v_one_1351_; lean_object* v_n_1352_; 
v_one_1351_ = lean_unsigned_to_nat(1u);
v_n_1352_ = lean_nat_sub(v_a_1346_, v_one_1351_);
lean_dec(v_a_1346_);
switch(lean_obj_tag(v_a_1347_))
{
case 7:
{
lean_object* v_binderName_1353_; lean_object* v_body_1354_; lean_object* v___x_1355_; 
v_binderName_1353_ = lean_ctor_get(v_a_1347_, 0);
lean_inc(v_binderName_1353_);
v_body_1354_ = lean_ctor_get(v_a_1347_, 2);
lean_inc_ref(v_body_1354_);
lean_dec_ref_known(v_a_1347_, 3);
v___x_1355_ = lean_array_push(v_a_1348_, v_binderName_1353_);
v_a_1346_ = v_n_1352_;
v_a_1347_ = v_body_1354_;
v_a_1348_ = v___x_1355_;
goto _start;
}
case 8:
{
lean_object* v_declName_1357_; lean_object* v_body_1358_; lean_object* v___x_1359_; 
v_declName_1357_ = lean_ctor_get(v_a_1347_, 0);
lean_inc(v_declName_1357_);
v_body_1358_ = lean_ctor_get(v_a_1347_, 3);
lean_inc_ref(v_body_1358_);
lean_dec_ref_known(v_a_1347_, 4);
v___x_1359_ = lean_array_push(v_a_1348_, v_declName_1357_);
v_a_1346_ = v_n_1352_;
v_a_1347_ = v_body_1358_;
v_a_1348_ = v___x_1359_;
goto _start;
}
default: 
{
lean_dec(v_n_1352_);
lean_dec_ref(v_a_1347_);
return v_a_1348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0(lean_object* v_x_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; 
lean_inc(v___y_1368_);
lean_inc_ref(v___y_1367_);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
lean_inc(v___y_1364_);
lean_inc(v___y_1363_);
lean_inc_ref(v___y_1362_);
v___x_1374_ = lean_apply_12(v_x_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, lean_box(0));
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0___boxed(lean_object* v_x_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0(v_x_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(lean_object* v_mvarId_1389_, lean_object* v_x_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___f_1403_; lean_object* v___x_1404_; 
lean_inc(v___y_1397_);
lean_inc_ref(v___y_1396_);
lean_inc(v___y_1395_);
lean_inc_ref(v___y_1394_);
lean_inc(v___y_1393_);
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
v___f_1403_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1403_, 0, v_x_1390_);
lean_closure_set(v___f_1403_, 1, v___y_1391_);
lean_closure_set(v___f_1403_, 2, v___y_1392_);
lean_closure_set(v___f_1403_, 3, v___y_1393_);
lean_closure_set(v___f_1403_, 4, v___y_1394_);
lean_closure_set(v___f_1403_, 5, v___y_1395_);
lean_closure_set(v___f_1403_, 6, v___y_1396_);
lean_closure_set(v___f_1403_, 7, v___y_1397_);
v___x_1404_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1389_, v___f_1403_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
if (lean_obj_tag(v___x_1404_) == 0)
{
return v___x_1404_;
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___boxed(lean_object* v_mvarId_1413_, lean_object* v_x_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_mvarId_1413_, v_x_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1(lean_object* v_00_u03b1_1428_, lean_object* v_mvarId_1429_, lean_object* v_x_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_mvarId_1429_, v_x_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___boxed(lean_object* v_00_u03b1_1444_, lean_object* v_mvarId_1445_, lean_object* v_x_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1(v_00_u03b1_1444_, v_mvarId_1445_, v_x_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(lean_object* v_as_1460_, size_t v_sz_1461_, size_t v_i_1462_, lean_object* v_b_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
uint8_t v___x_1468_; 
v___x_1468_ = lean_usize_dec_lt(v_i_1462_, v_sz_1461_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v_b_1463_);
return v___x_1469_;
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1471_; 
v_a_1470_ = lean_array_uget_borrowed(v_as_1460_, v_i_1462_);
lean_inc(v_a_1470_);
v___x_1471_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_a_1470_, v___y_1464_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1473_; size_t v___x_1474_; size_t v___x_1475_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1471_, 1);
v___x_1473_ = lean_array_push(v_b_1463_, v_a_1472_);
v___x_1474_ = ((size_t)1ULL);
v___x_1475_ = lean_usize_add(v_i_1462_, v___x_1474_);
v_i_1462_ = v___x_1475_;
v_b_1463_ = v___x_1473_;
goto _start;
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec_ref(v_b_1463_);
v_a_1477_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1471_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1471_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg___boxed(lean_object* v_as_1485_, lean_object* v_sz_1486_, lean_object* v_i_1487_, lean_object* v_b_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
size_t v_sz_boxed_1493_; size_t v_i_boxed_1494_; lean_object* v_res_1495_; 
v_sz_boxed_1493_ = lean_unbox_usize(v_sz_1486_);
lean_dec(v_sz_1486_);
v_i_boxed_1494_ = lean_unbox_usize(v_i_1487_);
lean_dec(v_i_1487_);
v_res_1495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(v_as_1485_, v_sz_boxed_1493_, v_i_boxed_1494_, v_b_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec_ref(v_as_1485_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0(lean_object* v_goal_1498_, lean_object* v_n_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; 
lean_inc(v_goal_1498_);
v___x_1512_ = l_Lean_MVarId_getType(v_goal_1498_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1559_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1515_ = v___x_1512_;
v_isShared_1516_ = v_isSharedCheck_1559_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1559_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v_names_1518_; lean_object* v_binderNames_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___x_1517_ = lean_unsigned_to_nat(0u);
v_names_1518_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___closed__0));
v_binderNames_1519_ = l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_introsHygienicN_collectBinders(v_n_1499_, v_a_1513_, v_names_1518_);
v___x_1520_ = lean_array_get_size(v_binderNames_1519_);
v___x_1521_ = lean_nat_dec_eq(v___x_1520_, v___x_1517_);
if (v___x_1521_ == 0)
{
uint8_t v___x_1522_; size_t v_sz_1523_; size_t v___x_1524_; lean_object* v___x_1525_; 
lean_del_object(v___x_1515_);
v___x_1522_ = 1;
v_sz_1523_ = lean_array_size(v_binderNames_1519_);
v___x_1524_ = ((size_t)0ULL);
v___x_1525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(v_binderNames_1519_, v_sz_1523_, v___x_1524_, v_names_1518_, v___y_1507_, v___y_1509_, v___y_1510_);
lean_dec_ref(v_binderNames_1519_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; lean_object* v___x_1527_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1526_);
lean_dec_ref_known(v___x_1525_, 1);
lean_inc(v_goal_1498_);
v___x_1527_ = l_Lean_Meta_Sym_intros(v_goal_1498_, v_a_1526_, v___x_1522_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1539_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1530_ = v___x_1527_;
v_isShared_1531_ = v_isSharedCheck_1539_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1527_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1539_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
if (lean_obj_tag(v_a_1528_) == 1)
{
lean_object* v_mvarId_1532_; lean_object* v___x_1534_; 
lean_dec(v_goal_1498_);
v_mvarId_1532_ = lean_ctor_get(v_a_1528_, 1);
lean_inc(v_mvarId_1532_);
lean_dec_ref_known(v_a_1528_, 2);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v_mvarId_1532_);
v___x_1534_ = v___x_1530_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_mvarId_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
else
{
lean_object* v___x_1537_; 
lean_dec(v_a_1528_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v_goal_1498_);
v___x_1537_ = v___x_1530_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_goal_1498_);
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
lean_dec(v_goal_1498_);
v_a_1540_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1527_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1527_);
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
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec(v_goal_1498_);
v_a_1548_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1525_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1525_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
else
{
lean_object* v___x_1557_; 
lean_dec_ref(v_binderNames_1519_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v_goal_1498_);
v___x_1557_ = v___x_1515_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_goal_1498_);
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
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec(v_n_1499_);
lean_dec(v_goal_1498_);
v_a_1560_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1512_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1512_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___boxed(lean_object* v_goal_1568_, lean_object* v_n_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0(v_goal_1568_, v_n_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN(lean_object* v_goal_1583_, lean_object* v_n_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v___f_1597_; lean_object* v___x_1598_; 
lean_inc(v_goal_1583_);
v___f_1597_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___boxed), 14, 2);
lean_closure_set(v___f_1597_, 0, v_goal_1583_);
lean_closure_set(v___f_1597_, 1, v_n_1584_);
v___x_1598_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_goal_1583_, v___f_1597_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN___boxed(lean_object* v_goal_1599_, lean_object* v_n_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN(v_goal_1599_, v_n_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0(lean_object* v_as_1614_, size_t v_sz_1615_, size_t v_i_1616_, lean_object* v_b_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(v_as_1614_, v_sz_1615_, v_i_1616_, v_b_1617_, v___y_1625_, v___y_1627_, v___y_1628_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___boxed(lean_object* v_as_1631_, lean_object* v_sz_1632_, lean_object* v_i_1633_, lean_object* v_b_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
size_t v_sz_boxed_1647_; size_t v_i_boxed_1648_; lean_object* v_res_1649_; 
v_sz_boxed_1647_ = lean_unbox_usize(v_sz_1632_);
lean_dec(v_sz_1632_);
v_i_boxed_1648_ = lean_unbox_usize(v_i_1633_);
lean_dec(v_i_1633_);
v_res_1649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0(v_as_1631_, v_sz_boxed_1647_, v_i_boxed_1648_, v_b_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec_ref(v_as_1631_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic(lean_object* v_goal_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v___x_1663_; 
lean_inc(v_goal_1650_);
v___x_1663_ = l_Lean_MVarId_getType(v_goal_1650_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
v___x_1665_ = l_Lean_Elab_Tactic_VCGen_numBindersToIntro(v_a_1664_);
lean_dec(v_a_1664_);
v___x_1666_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN(v_goal_1650_, v___x_1665_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
return v___x_1666_;
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec(v_goal_1650_);
v_a_1667_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1663_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1663_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic___boxed(lean_object* v_goal_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_Elab_Tactic_VCGen_introsHygienic(v_goal_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(lean_object* v_goal_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v_hypSimpMethods_1703_; 
v_hypSimpMethods_1703_ = lean_ctor_get(v_a_1694_, 2);
if (lean_obj_tag(v_hypSimpMethods_1703_) == 1)
{
lean_object* v_val_1704_; lean_object* v_post_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_val_1704_ = lean_ctor_get(v_hypSimpMethods_1703_, 0);
v_post_1705_ = lean_ctor_get(v_val_1704_, 1);
v___x_1706_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__0));
lean_inc_ref(v_post_1705_);
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
lean_ctor_set(v___x_1707_, 1, v_post_1705_);
lean_inc(v_goal_1693_);
v___x_1708_ = l_Lean_MVarId_getType(v_goal_1693_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1710_; lean_object* v_simpState_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v___x_1708_, 1);
v___x_1710_ = lean_st_ref_get(v_a_1695_);
v_simpState_1711_ = lean_ctor_get(v___x_1710_, 7);
lean_inc_ref(v_simpState_1711_);
lean_dec(v___x_1710_);
v___x_1712_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_1712_, 0, v_a_1709_);
v___x_1713_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__1));
v___x_1714_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_1712_, v___x_1707_, v___x_1713_, v_simpState_1711_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v_fst_1716_; lean_object* v_snd_1717_; lean_object* v___x_1718_; lean_object* v_specBackwardRuleCache_1719_; lean_object* v_splitBackwardRuleCache_1720_; lean_object* v_latticeBackwardRuleCache_1721_; lean_object* v_frameBackwardRuleCache_1722_; lean_object* v_frameDB_1723_; lean_object* v_invariants_1724_; lean_object* v_vcs_1725_; lean_object* v_fuel_1726_; lean_object* v_inlineHandledInvariants_1727_; lean_object* v_pendingJoinPoints_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1737_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
lean_dec_ref_known(v___x_1714_, 1);
v_fst_1716_ = lean_ctor_get(v_a_1715_, 0);
lean_inc(v_fst_1716_);
v_snd_1717_ = lean_ctor_get(v_a_1715_, 1);
lean_inc(v_snd_1717_);
lean_dec(v_a_1715_);
v___x_1718_ = lean_st_ref_take(v_a_1695_);
v_specBackwardRuleCache_1719_ = lean_ctor_get(v___x_1718_, 0);
v_splitBackwardRuleCache_1720_ = lean_ctor_get(v___x_1718_, 1);
v_latticeBackwardRuleCache_1721_ = lean_ctor_get(v___x_1718_, 2);
v_frameBackwardRuleCache_1722_ = lean_ctor_get(v___x_1718_, 3);
v_frameDB_1723_ = lean_ctor_get(v___x_1718_, 4);
v_invariants_1724_ = lean_ctor_get(v___x_1718_, 5);
v_vcs_1725_ = lean_ctor_get(v___x_1718_, 6);
v_fuel_1726_ = lean_ctor_get(v___x_1718_, 8);
v_inlineHandledInvariants_1727_ = lean_ctor_get(v___x_1718_, 9);
v_pendingJoinPoints_1728_ = lean_ctor_get(v___x_1718_, 10);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1737_ == 0)
{
lean_object* v_unused_1738_; 
v_unused_1738_ = lean_ctor_get(v___x_1718_, 7);
lean_dec(v_unused_1738_);
v___x_1730_ = v___x_1718_;
v_isShared_1731_ = v_isSharedCheck_1737_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_pendingJoinPoints_1728_);
lean_inc(v_inlineHandledInvariants_1727_);
lean_inc(v_fuel_1726_);
lean_inc(v_vcs_1725_);
lean_inc(v_invariants_1724_);
lean_inc(v_frameDB_1723_);
lean_inc(v_frameBackwardRuleCache_1722_);
lean_inc(v_latticeBackwardRuleCache_1721_);
lean_inc(v_splitBackwardRuleCache_1720_);
lean_inc(v_specBackwardRuleCache_1719_);
lean_dec(v___x_1718_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1737_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 7, v_snd_1717_);
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_specBackwardRuleCache_1719_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_splitBackwardRuleCache_1720_);
lean_ctor_set(v_reuseFailAlloc_1736_, 2, v_latticeBackwardRuleCache_1721_);
lean_ctor_set(v_reuseFailAlloc_1736_, 3, v_frameBackwardRuleCache_1722_);
lean_ctor_set(v_reuseFailAlloc_1736_, 4, v_frameDB_1723_);
lean_ctor_set(v_reuseFailAlloc_1736_, 5, v_invariants_1724_);
lean_ctor_set(v_reuseFailAlloc_1736_, 6, v_vcs_1725_);
lean_ctor_set(v_reuseFailAlloc_1736_, 7, v_snd_1717_);
lean_ctor_set(v_reuseFailAlloc_1736_, 8, v_fuel_1726_);
lean_ctor_set(v_reuseFailAlloc_1736_, 9, v_inlineHandledInvariants_1727_);
lean_ctor_set(v_reuseFailAlloc_1736_, 10, v_pendingJoinPoints_1728_);
v___x_1733_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_st_ref_put(v_a_1695_, v___x_1733_);
v___x_1735_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_fst_1716_, v_goal_1693_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_1735_;
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec(v_goal_1693_);
v_a_1739_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1714_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1714_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec_ref_known(v___x_1707_, 2);
lean_dec(v_goal_1693_);
v_a_1747_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1708_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1708_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec(v_goal_1693_);
v___x_1755_ = lean_box(0);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___boxed(lean_object* v_goal_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(v_goal_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_);
lean_dec(v_a_1765_);
lean_dec_ref(v_a_1764_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope(lean_object* v_goal_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(v_goal_1768_, v_a_1769_, v_a_1770_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___boxed(lean_object* v_goal_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope(v_goal_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
return v_res_1795_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__8));
v___x_1798_ = l_Lean_stringToMessageData(v___x_1797_);
return v___x_1798_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6(void){
_start:
{
uint8_t v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1806_ = 0;
v___x_1807_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__5));
v___x_1808_ = l_Lean_MessageData_ofConstName(v___x_1807_, v___x_1806_);
return v___x_1808_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__0));
v___x_1811_ = l_Lean_stringToMessageData(v___x_1810_);
return v___x_1811_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6);
v___x_1813_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1);
v___x_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
lean_ctor_set(v___x_1814_, 1, v___x_1812_);
return v___x_1814_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9);
v___x_1816_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7);
v___x_1817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
lean_ctor_set(v___x_1817_, 1, v___x_1815_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0(lean_object* v_goal_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v___x_1841_; 
lean_inc(v_goal_1825_);
v___x_1841_ = l_Lean_MVarId_getType(v_goal_1825_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1915_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1915_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1915_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1855_ = l_Lean_Expr_cleanupAnnotations(v_a_1842_);
v___x_1856_ = l_Lean_Expr_isApp(v___x_1855_);
if (v___x_1856_ == 0)
{
lean_dec_ref(v___x_1855_);
lean_del_object(v___x_1844_);
lean_dec(v_a_1842_);
lean_dec(v_goal_1825_);
goto v___jp_1838_;
}
else
{
lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1857_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1855_);
lean_dec_ref(v___x_1855_);
v___x_1858_ = l_Lean_Expr_isApp(v___x_1857_);
if (v___x_1858_ == 0)
{
lean_dec_ref(v___x_1857_);
lean_del_object(v___x_1844_);
lean_dec(v_a_1842_);
lean_dec(v_goal_1825_);
goto v___jp_1838_;
}
else
{
lean_object* v___x_1859_; uint8_t v___x_1860_; 
v___x_1859_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1857_);
lean_dec_ref(v___x_1857_);
v___x_1860_ = l_Lean_Expr_isApp(v___x_1859_);
if (v___x_1860_ == 0)
{
lean_dec_ref(v___x_1859_);
lean_del_object(v___x_1844_);
lean_dec(v_a_1842_);
lean_dec(v_goal_1825_);
goto v___jp_1838_;
}
else
{
lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1859_);
lean_dec_ref(v___x_1859_);
v___x_1862_ = l_Lean_Expr_isApp(v___x_1861_);
if (v___x_1862_ == 0)
{
lean_dec_ref(v___x_1861_);
lean_del_object(v___x_1844_);
lean_dec(v_a_1842_);
lean_dec(v_goal_1825_);
goto v___jp_1838_;
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1863_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1861_);
v___x_1864_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13));
v___x_1865_ = l_Lean_Expr_isConstOf(v___x_1863_, v___x_1864_);
lean_dec_ref(v___x_1863_);
if (v___x_1865_ == 0)
{
lean_dec_ref(v___x_1861_);
lean_del_object(v___x_1844_);
lean_dec(v_a_1842_);
lean_dec(v_goal_1825_);
goto v___jp_1838_;
}
else
{
lean_object* v_arg_1866_; uint8_t v___x_1867_; 
v_arg_1866_ = lean_ctor_get(v___x_1861_, 1);
lean_inc_ref(v_arg_1866_);
lean_dec_ref(v___x_1861_);
v___x_1867_ = l_Lean_Expr_isForall(v_arg_1866_);
lean_dec_ref(v_arg_1866_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1870_; 
lean_dec(v_a_1842_);
lean_dec(v_goal_1825_);
v___x_1868_ = lean_box(0);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1868_);
v___x_1870_ = v___x_1844_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
else
{
lean_object* v_backwardRules_1872_; lean_object* v_stateArgIntro_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_del_object(v___x_1844_);
v_backwardRules_1872_ = lean_ctor_get(v___y_1826_, 0);
v_stateArgIntro_1873_ = lean_ctor_get(v_backwardRules_1872_, 1);
v___x_1874_ = lean_box(0);
lean_inc_ref(v_stateArgIntro_1873_);
v___x_1875_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_stateArgIntro_1873_, v_goal_1825_, v___x_1874_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_a_1876_);
lean_dec_ref_known(v___x_1875_, 1);
if (lean_obj_tag(v_a_1876_) == 1)
{
lean_object* v_mvarIds_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1906_; 
v_mvarIds_1877_ = lean_ctor_get(v_a_1876_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v_a_1876_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1879_ = v_a_1876_;
v_isShared_1880_ = v_isSharedCheck_1906_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_mvarIds_1877_);
lean_dec(v_a_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1906_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
if (lean_obj_tag(v_mvarIds_1877_) == 1)
{
lean_object* v_tail_1881_; 
v_tail_1881_ = lean_ctor_get(v_mvarIds_1877_, 1);
if (lean_obj_tag(v_tail_1881_) == 0)
{
lean_object* v_head_1882_; lean_object* v___x_1883_; 
lean_dec(v_a_1842_);
v_head_1882_ = lean_ctor_get(v_mvarIds_1877_, 0);
lean_inc(v_head_1882_);
lean_dec_ref_known(v_mvarIds_1877_, 2);
v___x_1883_ = l_Lean_Elab_Tactic_VCGen_introsHygienic(v_head_1882_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1885_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc_n(v_a_1884_, 2);
lean_dec_ref_known(v___x_1883_, 1);
v___x_1885_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs(v_a_1884_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
if (lean_obj_tag(v_a_1886_) == 0)
{
lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1896_; 
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1896_ == 0)
{
lean_object* v_unused_1897_; 
v_unused_1897_ = lean_ctor_get(v___x_1885_, 0);
lean_dec(v_unused_1897_);
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1896_;
goto v_resetjp_1887_;
}
else
{
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1896_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v_a_1884_);
v___x_1891_ = v___x_1879_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1884_);
v___x_1891_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1893_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1891_);
v___x_1893_ = v___x_1888_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
else
{
lean_dec(v_a_1884_);
lean_del_object(v___x_1879_);
return v___x_1885_;
}
}
else
{
lean_dec(v_a_1884_);
lean_del_object(v___x_1879_);
return v___x_1885_;
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_del_object(v___x_1879_);
v_a_1898_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1883_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1883_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_1877_, 2);
lean_del_object(v___x_1879_);
v___y_1847_ = v___y_1833_;
v___y_1848_ = v___y_1834_;
v___y_1849_ = v___y_1835_;
v___y_1850_ = v___y_1836_;
goto v___jp_1846_;
}
}
else
{
lean_del_object(v___x_1879_);
lean_dec(v_mvarIds_1877_);
v___y_1847_ = v___y_1833_;
v___y_1848_ = v___y_1834_;
v___y_1849_ = v___y_1835_;
v___y_1850_ = v___y_1836_;
goto v___jp_1846_;
}
}
}
else
{
lean_dec(v_a_1876_);
v___y_1847_ = v___y_1833_;
v___y_1848_ = v___y_1834_;
v___y_1849_ = v___y_1835_;
v___y_1850_ = v___y_1836_;
goto v___jp_1846_;
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_dec(v_a_1842_);
v_a_1907_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1875_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1875_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
}
}
}
}
}
v___jp_1846_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1851_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10);
v___x_1852_ = l_Lean_indentExpr(v_a_1842_);
v___x_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1851_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_1853_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
return v___x_1854_;
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_goal_1825_);
v_a_1916_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1841_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1841_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
v___jp_1838_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_box(0);
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
return v___x_1840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___boxed(lean_object* v_goal_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0(v_goal_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs(lean_object* v_goal_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v___f_1951_; lean_object* v___x_1952_; 
lean_inc(v_goal_1938_);
v___f_1951_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___boxed), 13, 1);
lean_closure_set(v___f_1951_, 0, v_goal_1938_);
v___x_1952_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_goal_1938_, v___f_1951_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___boxed(lean_object* v_goal_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs(v_goal_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
lean_dec(v_a_1964_);
lean_dec_ref(v_a_1963_);
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg(lean_object* v_e_1967_, lean_object* v___y_1968_){
_start:
{
uint8_t v___x_1970_; 
v___x_1970_ = l_Lean_Expr_hasMVar(v_e_1967_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v_e_1967_);
return v___x_1971_;
}
else
{
lean_object* v___x_1972_; lean_object* v_mctx_1973_; lean_object* v___x_1974_; lean_object* v_fst_1975_; lean_object* v_snd_1976_; lean_object* v___x_1977_; lean_object* v_cache_1978_; lean_object* v_zetaDeltaFVarIds_1979_; lean_object* v_postponed_1980_; lean_object* v_diag_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1990_; 
v___x_1972_ = lean_st_ref_get(v___y_1968_);
v_mctx_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc_ref(v_mctx_1973_);
lean_dec(v___x_1972_);
v___x_1974_ = l_Lean_instantiateMVarsCore(v_mctx_1973_, v_e_1967_);
v_fst_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_fst_1975_);
v_snd_1976_ = lean_ctor_get(v___x_1974_, 1);
lean_inc(v_snd_1976_);
lean_dec_ref(v___x_1974_);
v___x_1977_ = lean_st_ref_take(v___y_1968_);
v_cache_1978_ = lean_ctor_get(v___x_1977_, 1);
v_zetaDeltaFVarIds_1979_ = lean_ctor_get(v___x_1977_, 2);
v_postponed_1980_ = lean_ctor_get(v___x_1977_, 3);
v_diag_1981_ = lean_ctor_get(v___x_1977_, 4);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1990_ == 0)
{
lean_object* v_unused_1991_; 
v_unused_1991_ = lean_ctor_get(v___x_1977_, 0);
lean_dec(v_unused_1991_);
v___x_1983_ = v___x_1977_;
v_isShared_1984_ = v_isSharedCheck_1990_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_diag_1981_);
lean_inc(v_postponed_1980_);
lean_inc(v_zetaDeltaFVarIds_1979_);
lean_inc(v_cache_1978_);
lean_dec(v___x_1977_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1990_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v_snd_1976_);
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_snd_1976_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_cache_1978_);
lean_ctor_set(v_reuseFailAlloc_1989_, 2, v_zetaDeltaFVarIds_1979_);
lean_ctor_set(v_reuseFailAlloc_1989_, 3, v_postponed_1980_);
lean_ctor_set(v_reuseFailAlloc_1989_, 4, v_diag_1981_);
v___x_1986_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = lean_st_ref_put(v___y_1968_, v___x_1986_);
v___x_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1988_, 0, v_fst_1975_);
return v___x_1988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg___boxed(lean_object* v_e_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg(v_e_1992_, v___y_1993_);
lean_dec(v___y_1993_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1(lean_object* v_e_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg(v_e_1996_, v___y_2005_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___boxed(lean_object* v_e_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1(v_e_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(lean_object* v_mvarId_2024_, lean_object* v_val_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v___x_2028_; lean_object* v_mctx_2029_; lean_object* v_cache_2030_; lean_object* v_zetaDeltaFVarIds_2031_; lean_object* v_postponed_2032_; lean_object* v_diag_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2063_; 
v___x_2028_ = lean_st_ref_take(v___y_2026_);
v_mctx_2029_ = lean_ctor_get(v___x_2028_, 0);
v_cache_2030_ = lean_ctor_get(v___x_2028_, 1);
v_zetaDeltaFVarIds_2031_ = lean_ctor_get(v___x_2028_, 2);
v_postponed_2032_ = lean_ctor_get(v___x_2028_, 3);
v_diag_2033_ = lean_ctor_get(v___x_2028_, 4);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2035_ = v___x_2028_;
v_isShared_2036_ = v_isSharedCheck_2063_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_diag_2033_);
lean_inc(v_postponed_2032_);
lean_inc(v_zetaDeltaFVarIds_2031_);
lean_inc(v_cache_2030_);
lean_inc(v_mctx_2029_);
lean_dec(v___x_2028_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2063_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v_depth_2037_; lean_object* v_levelAssignDepth_2038_; lean_object* v_lmvarCounter_2039_; lean_object* v_mvarCounter_2040_; lean_object* v_lDecls_2041_; lean_object* v_decls_2042_; lean_object* v_userNames_2043_; lean_object* v_lAssignment_2044_; lean_object* v_eAssignment_2045_; lean_object* v_dAssignment_2046_; lean_object* v_instanceTypedMVars_2047_; lean_object* v_synthNormMemo_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2062_; 
v_depth_2037_ = lean_ctor_get(v_mctx_2029_, 0);
v_levelAssignDepth_2038_ = lean_ctor_get(v_mctx_2029_, 1);
v_lmvarCounter_2039_ = lean_ctor_get(v_mctx_2029_, 2);
v_mvarCounter_2040_ = lean_ctor_get(v_mctx_2029_, 3);
v_lDecls_2041_ = lean_ctor_get(v_mctx_2029_, 4);
v_decls_2042_ = lean_ctor_get(v_mctx_2029_, 5);
v_userNames_2043_ = lean_ctor_get(v_mctx_2029_, 6);
v_lAssignment_2044_ = lean_ctor_get(v_mctx_2029_, 7);
v_eAssignment_2045_ = lean_ctor_get(v_mctx_2029_, 8);
v_dAssignment_2046_ = lean_ctor_get(v_mctx_2029_, 9);
v_instanceTypedMVars_2047_ = lean_ctor_get(v_mctx_2029_, 10);
v_synthNormMemo_2048_ = lean_ctor_get(v_mctx_2029_, 11);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_mctx_2029_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2050_ = v_mctx_2029_;
v_isShared_2051_ = v_isSharedCheck_2062_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_synthNormMemo_2048_);
lean_inc(v_instanceTypedMVars_2047_);
lean_inc(v_dAssignment_2046_);
lean_inc(v_eAssignment_2045_);
lean_inc(v_lAssignment_2044_);
lean_inc(v_userNames_2043_);
lean_inc(v_decls_2042_);
lean_inc(v_lDecls_2041_);
lean_inc(v_mvarCounter_2040_);
lean_inc(v_lmvarCounter_2039_);
lean_inc(v_levelAssignDepth_2038_);
lean_inc(v_depth_2037_);
lean_dec(v_mctx_2029_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2062_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2052_ = lean_box(0);
v___x_2053_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(v_eAssignment_2045_, v_mvarId_2024_, v_val_2025_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 8, v___x_2053_);
v___x_2055_ = v___x_2050_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_depth_2037_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_levelAssignDepth_2038_);
lean_ctor_set(v_reuseFailAlloc_2061_, 2, v_lmvarCounter_2039_);
lean_ctor_set(v_reuseFailAlloc_2061_, 3, v_mvarCounter_2040_);
lean_ctor_set(v_reuseFailAlloc_2061_, 4, v_lDecls_2041_);
lean_ctor_set(v_reuseFailAlloc_2061_, 5, v_decls_2042_);
lean_ctor_set(v_reuseFailAlloc_2061_, 6, v_userNames_2043_);
lean_ctor_set(v_reuseFailAlloc_2061_, 7, v_lAssignment_2044_);
lean_ctor_set(v_reuseFailAlloc_2061_, 8, v___x_2053_);
lean_ctor_set(v_reuseFailAlloc_2061_, 9, v_dAssignment_2046_);
lean_ctor_set(v_reuseFailAlloc_2061_, 10, v_instanceTypedMVars_2047_);
lean_ctor_set(v_reuseFailAlloc_2061_, 11, v_synthNormMemo_2048_);
v___x_2055_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2057_; 
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2055_);
v___x_2057_ = v___x_2035_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_cache_2030_);
lean_ctor_set(v_reuseFailAlloc_2060_, 2, v_zetaDeltaFVarIds_2031_);
lean_ctor_set(v_reuseFailAlloc_2060_, 3, v_postponed_2032_);
lean_ctor_set(v_reuseFailAlloc_2060_, 4, v_diag_2033_);
v___x_2057_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = lean_st_ref_put(v___y_2026_, v___x_2057_);
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2052_);
return v___x_2059_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg___boxed(lean_object* v_mvarId_2064_, lean_object* v_val_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_mvarId_2064_, v_val_2065_, v___y_2066_);
lean_dec(v___y_2066_);
return v_res_2068_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__0));
v___x_2071_ = l_Lean_stringToMessageData(v___x_2070_);
return v___x_2071_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__3));
v___x_2075_ = l_Lean_stringToMessageData(v___x_2074_);
return v___x_2075_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = lean_box(0);
v___x_2090_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__8));
v___x_2091_ = l_Lean_mkConst(v___x_2090_, v___x_2089_);
return v___x_2091_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = lean_box(0);
v___x_2097_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__15));
v___x_2098_ = l_Lean_mkConst(v___x_2097_, v___x_2096_);
return v___x_2098_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2103_ = lean_box(0);
v___x_2104_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__18));
v___x_2105_ = l_Lean_mkConst(v___x_2104_, v___x_2103_);
return v___x_2105_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21(void){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2109_ = lean_box(0);
v___x_2110_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__20));
v___x_2111_ = l_Lean_mkConst(v___x_2110_, v___x_2109_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0(lean_object* v_goal_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___y_2126_; lean_object* v___y_2127_; uint8_t v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v_g_2144_; lean_object* v_fst_2148_; lean_object* v_snd_2149_; lean_object* v___x_2378_; 
lean_inc(v_goal_2112_);
v___x_2378_ = l_Lean_MVarId_getType(v_goal_2112_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2380_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
v___x_2380_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg(v_a_2379_, v___y_2121_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2382_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc_n(v_a_2381_, 2);
lean_dec_ref_known(v___x_2380_, 1);
v___x_2382_ = l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(v_a_2381_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2382_, 1);
if (lean_obj_tag(v_a_2383_) == 0)
{
v_fst_2148_ = v_goal_2112_;
v_snd_2149_ = v_a_2381_;
goto v___jp_2147_;
}
else
{
lean_object* v_val_2384_; lean_object* v___x_2385_; 
lean_dec(v_a_2381_);
v_val_2384_ = lean_ctor_get(v_a_2383_, 0);
lean_inc_n(v_val_2384_, 2);
lean_dec_ref_known(v_a_2383_, 1);
v___x_2385_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_2112_, v_val_2384_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2386_);
lean_dec_ref_known(v___x_2385_, 1);
v_fst_2148_ = v_a_2386_;
v_snd_2149_ = v_val_2384_;
goto v___jp_2147_;
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec(v_val_2384_);
v_a_2387_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2385_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2385_);
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
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_dec(v_a_2381_);
lean_dec(v_goal_2112_);
v_a_2395_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2382_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2382_);
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
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
lean_dec(v_goal_2112_);
v_a_2403_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v___x_2380_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2380_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_dec(v_goal_2112_);
v_a_2411_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2378_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2378_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
v___jp_2125_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2133_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1);
v___x_2134_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__2));
lean_inc_ref(v___y_2126_);
v___x_2135_ = l_Lean_Name_mkStr2(v___y_2126_, v___x_2134_);
v___x_2136_ = l_Lean_MessageData_ofConstName(v___x_2135_, v___y_2128_);
v___x_2137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2133_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4);
v___x_2139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2137_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = l_Lean_indentExpr(v___y_2127_);
v___x_2141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_2141_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
return v___x_2142_;
}
v___jp_2143_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2145_, 0, v_g_2144_);
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
return v___x_2146_;
}
v___jp_2147_:
{
lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2150_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__6));
v___x_2151_ = l_Lean_Expr_isAppOf(v_snd_2149_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; 
v___x_2152_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__7));
v___x_2153_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__8));
v___x_2154_ = l_Lean_Expr_isAppOf(v_snd_2149_, v___x_2153_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; 
v___x_2155_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__10));
v___x_2156_ = lean_unsigned_to_nat(3u);
v___x_2157_ = l_Lean_Expr_isAppOfArity(v_snd_2149_, v___x_2155_, v___x_2156_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
lean_dec_ref(v_snd_2149_);
v___x_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2158_, 0, v_fst_2148_);
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
return v___x_2159_;
}
else
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2160_ = l_Lean_Expr_appFn_x21(v_snd_2149_);
v___x_2161_ = l_Lean_Expr_appFn_x21(v___x_2160_);
v___x_2162_ = l_Lean_Expr_appArg_x21(v___x_2161_);
lean_dec_ref(v___x_2161_);
v___x_2163_ = l_Lean_Expr_appArg_x21(v___x_2160_);
lean_dec_ref(v___x_2160_);
v___x_2164_ = l_Lean_Expr_appArg_x21(v_snd_2149_);
lean_dec_ref(v_snd_2149_);
v___x_2165_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v___x_2163_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v___x_2167_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2165_, 1);
v___x_2167_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v___x_2164_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2169_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
lean_inc_ref(v___x_2162_);
v___x_2169_ = l_Lean_Meta_getLevel(v___x_2162_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
v___x_2171_ = lean_box(0);
v___x_2172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2172_, 0, v_a_2170_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = l_Lean_mkConst(v___x_2155_, v___x_2172_);
lean_inc(v_a_2168_);
lean_inc(v_a_2166_);
lean_inc_ref(v___x_2162_);
v___x_2174_ = l_Lean_mkApp3(v___x_2173_, v___x_2162_, v_a_2166_, v_a_2168_);
v___x_2175_ = l_Lean_MVarId_replaceTargetDefEqFast(v_fst_2148_, v___x_2174_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2177_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___closed__0));
lean_inc(v_a_2166_);
v___x_2178_ = l_Lean_Meta_Sym_isDefEqS(v_a_2166_, v_a_2168_, v___x_2157_, v___x_2157_, v___x_2177_, v___x_2177_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2220_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2220_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2220_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
uint8_t v___x_2183_; 
v___x_2183_ = lean_unbox(v_a_2179_);
lean_dec(v_a_2179_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2186_; 
lean_dec(v_a_2166_);
lean_dec_ref(v___x_2162_);
v___x_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2184_, 0, v_a_2176_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2184_);
v___x_2186_ = v___x_2181_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
else
{
lean_object* v___x_2188_; 
lean_del_object(v___x_2181_);
lean_inc_ref(v___x_2162_);
v___x_2188_ = l_Lean_Meta_getLevel(v___x_2162_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2188_, 1);
v___x_2190_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__12));
v___x_2191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2191_, 0, v_a_2189_);
lean_ctor_set(v___x_2191_, 1, v___x_2171_);
v___x_2192_ = l_Lean_mkConst(v___x_2190_, v___x_2191_);
v___x_2193_ = l_Lean_mkAppB(v___x_2192_, v___x_2162_, v_a_2166_);
v___x_2194_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_a_2176_, v___x_2193_, v___y_2121_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2202_; 
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2202_ == 0)
{
lean_object* v_unused_2203_; 
v_unused_2203_ = lean_ctor_get(v___x_2194_, 0);
lean_dec(v_unused_2203_);
v___x_2196_ = v___x_2194_;
v_isShared_2197_ = v_isSharedCheck_2202_;
goto v_resetjp_2195_;
}
else
{
lean_dec(v___x_2194_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2202_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2198_ = lean_box(0);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 0, v___x_2198_);
v___x_2200_ = v___x_2196_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
v_a_2204_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2194_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2194_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v_a_2176_);
lean_dec(v_a_2166_);
lean_dec_ref(v___x_2162_);
v_a_2212_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2188_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2188_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec(v_a_2176_);
lean_dec(v_a_2166_);
lean_dec_ref(v___x_2162_);
v_a_2221_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2178_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2178_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec(v_a_2168_);
lean_dec(v_a_2166_);
lean_dec_ref(v___x_2162_);
v_a_2229_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2175_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2175_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_dec(v_a_2168_);
lean_dec(v_a_2166_);
lean_dec_ref(v___x_2162_);
lean_dec(v_fst_2148_);
v_a_2237_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2169_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2169_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec(v_a_2166_);
lean_dec_ref(v___x_2162_);
lean_dec(v_fst_2148_);
v_a_2245_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2167_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2167_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec_ref(v___x_2164_);
lean_dec_ref(v___x_2162_);
lean_dec(v_fst_2148_);
v_a_2253_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2165_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2165_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
}
else
{
lean_object* v_backwardRules_2261_; lean_object* v_andIntro_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v_backwardRules_2261_ = lean_ctor_get(v___y_2113_, 0);
v_andIntro_2262_ = lean_ctor_get(v_backwardRules_2261_, 8);
v___x_2263_ = lean_box(0);
lean_inc_ref(v_andIntro_2262_);
v___x_2264_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_andIntro_2262_, v_fst_2148_, v___x_2263_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2264_, 1);
if (lean_obj_tag(v_a_2265_) == 1)
{
lean_object* v_mvarIds_2266_; 
v_mvarIds_2266_ = lean_ctor_get(v_a_2265_, 0);
lean_inc(v_mvarIds_2266_);
lean_dec_ref_known(v_a_2265_, 1);
if (lean_obj_tag(v_mvarIds_2266_) == 1)
{
lean_object* v_tail_2267_; 
v_tail_2267_ = lean_ctor_get(v_mvarIds_2266_, 1);
lean_inc(v_tail_2267_);
if (lean_obj_tag(v_tail_2267_) == 1)
{
lean_object* v_tail_2268_; 
v_tail_2268_ = lean_ctor_get(v_tail_2267_, 1);
if (lean_obj_tag(v_tail_2268_) == 0)
{
lean_object* v_head_2269_; lean_object* v_head_2270_; lean_object* v___x_2271_; 
lean_dec_ref(v_snd_2149_);
v_head_2269_ = lean_ctor_get(v_mvarIds_2266_, 0);
lean_inc(v_head_2269_);
lean_dec_ref_known(v_mvarIds_2266_, 2);
v_head_2270_ = lean_ctor_get(v_tail_2267_, 0);
lean_inc(v_head_2270_);
lean_dec_ref_known(v_tail_2267_, 2);
v___x_2271_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_head_2269_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2273_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v___x_2271_, 1);
v___x_2273_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_head_2270_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2273_) == 0)
{
if (lean_obj_tag(v_a_2272_) == 0)
{
lean_object* v_a_2274_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
if (lean_obj_tag(v_a_2274_) == 0)
{
return v___x_2273_;
}
else
{
lean_object* v_val_2275_; 
lean_inc_ref(v_a_2274_);
lean_dec_ref_known(v___x_2273_, 1);
v_val_2275_ = lean_ctor_get(v_a_2274_, 0);
lean_inc(v_val_2275_);
lean_dec_ref_known(v_a_2274_, 1);
v_g_2144_ = v_val_2275_;
goto v___jp_2143_;
}
}
else
{
lean_object* v_a_2276_; 
v_a_2276_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___x_2273_, 1);
if (lean_obj_tag(v_a_2276_) == 0)
{
lean_object* v_val_2277_; 
v_val_2277_ = lean_ctor_get(v_a_2272_, 0);
lean_inc(v_val_2277_);
lean_dec_ref_known(v_a_2272_, 1);
v_g_2144_ = v_val_2277_;
goto v___jp_2143_;
}
else
{
lean_object* v_val_2278_; lean_object* v_val_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2350_; 
v_val_2278_ = lean_ctor_get(v_a_2272_, 0);
lean_inc(v_val_2278_);
lean_dec_ref_known(v_a_2272_, 1);
v_val_2279_ = lean_ctor_get(v_a_2276_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v_a_2276_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2281_ = v_a_2276_;
v_isShared_2282_ = v_isSharedCheck_2350_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_val_2279_);
lean_dec(v_a_2276_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2350_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2283_; 
lean_inc(v_val_2278_);
v___x_2283_ = l_Lean_MVarId_getType(v_val_2278_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2285_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2283_, 1);
lean_inc(v_val_2279_);
v___x_2285_ = l_Lean_MVarId_getType(v_val_2279_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc_n(v_a_2286_, 2);
lean_dec_ref_known(v___x_2285_, 1);
v___x_2287_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13);
lean_inc(v_a_2284_);
v___x_2288_ = l_Lean_mkAppB(v___x_2287_, v_a_2284_, v_a_2286_);
v___x_2289_ = lean_box(0);
v___x_2290_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2288_, v___x_2289_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc_n(v_a_2291_, 2);
lean_dec_ref_known(v___x_2290_, 1);
v___x_2292_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16);
lean_inc(v_a_2286_);
lean_inc(v_a_2284_);
v___x_2293_ = l_Lean_mkApp3(v___x_2292_, v_a_2284_, v_a_2286_, v_a_2291_);
v___x_2294_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_val_2278_, v___x_2293_, v___y_2121_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
lean_dec_ref_known(v___x_2294_, 1);
v___x_2295_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19);
lean_inc(v_a_2291_);
v___x_2296_ = l_Lean_mkApp3(v___x_2295_, v_a_2284_, v_a_2286_, v_a_2291_);
v___x_2297_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_val_2279_, v___x_2296_, v___y_2121_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2308_; 
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; 
v_unused_2309_ = lean_ctor_get(v___x_2297_, 0);
lean_dec(v_unused_2309_);
v___x_2299_ = v___x_2297_;
v_isShared_2300_ = v_isSharedCheck_2308_;
goto v_resetjp_2298_;
}
else
{
lean_dec(v___x_2297_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2308_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2301_ = l_Lean_Expr_mvarId_x21(v_a_2291_);
lean_dec(v_a_2291_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2301_);
v___x_2303_ = v___x_2281_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2301_);
v___x_2303_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2305_; 
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v___x_2303_);
v___x_2305_ = v___x_2299_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec(v_a_2291_);
lean_del_object(v___x_2281_);
v_a_2310_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2297_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2297_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec(v_a_2291_);
lean_dec(v_a_2286_);
lean_dec(v_a_2284_);
lean_del_object(v___x_2281_);
lean_dec(v_val_2279_);
v_a_2318_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2294_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2294_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_dec(v_a_2286_);
lean_dec(v_a_2284_);
lean_del_object(v___x_2281_);
lean_dec(v_val_2279_);
lean_dec(v_val_2278_);
v_a_2326_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2290_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2290_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v_a_2284_);
lean_del_object(v___x_2281_);
lean_dec(v_val_2279_);
lean_dec(v_val_2278_);
v_a_2334_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2285_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2285_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_del_object(v___x_2281_);
lean_dec(v_val_2279_);
lean_dec(v_val_2278_);
v_a_2342_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2283_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2283_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2272_);
return v___x_2273_;
}
}
else
{
lean_dec(v_head_2270_);
return v___x_2271_;
}
}
else
{
lean_dec_ref_known(v_tail_2267_, 2);
lean_dec_ref_known(v_mvarIds_2266_, 2);
v___y_2126_ = v___x_2152_;
v___y_2127_ = v_snd_2149_;
v___y_2128_ = v___x_2151_;
v___y_2129_ = v___y_2120_;
v___y_2130_ = v___y_2121_;
v___y_2131_ = v___y_2122_;
v___y_2132_ = v___y_2123_;
goto v___jp_2125_;
}
}
else
{
lean_dec_ref_known(v_mvarIds_2266_, 2);
lean_dec(v_tail_2267_);
v___y_2126_ = v___x_2152_;
v___y_2127_ = v_snd_2149_;
v___y_2128_ = v___x_2151_;
v___y_2129_ = v___y_2120_;
v___y_2130_ = v___y_2121_;
v___y_2131_ = v___y_2122_;
v___y_2132_ = v___y_2123_;
goto v___jp_2125_;
}
}
else
{
lean_dec(v_mvarIds_2266_);
v___y_2126_ = v___x_2152_;
v___y_2127_ = v_snd_2149_;
v___y_2128_ = v___x_2151_;
v___y_2129_ = v___y_2120_;
v___y_2130_ = v___y_2121_;
v___y_2131_ = v___y_2122_;
v___y_2132_ = v___y_2123_;
goto v___jp_2125_;
}
}
else
{
lean_dec(v_a_2265_);
v___y_2126_ = v___x_2152_;
v___y_2127_ = v_snd_2149_;
v___y_2128_ = v___x_2151_;
v___y_2129_ = v___y_2120_;
v___y_2130_ = v___y_2121_;
v___y_2131_ = v___y_2122_;
v___y_2132_ = v___y_2123_;
goto v___jp_2125_;
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec_ref(v_snd_2149_);
v_a_2351_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2264_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2264_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
lean_dec_ref(v_snd_2149_);
v___x_2359_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21);
v___x_2360_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_fst_2148_, v___x_2359_, v___y_2121_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2368_; 
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2368_ == 0)
{
lean_object* v_unused_2369_; 
v_unused_2369_ = lean_ctor_get(v___x_2360_, 0);
lean_dec(v_unused_2369_);
v___x_2362_ = v___x_2360_;
v_isShared_2363_ = v_isSharedCheck_2368_;
goto v_resetjp_2361_;
}
else
{
lean_dec(v___x_2360_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2368_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2364_; lean_object* v___x_2366_; 
v___x_2364_ = lean_box(0);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v___x_2364_);
v___x_2366_ = v___x_2362_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
v_a_2370_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2360_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2360_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___boxed(lean_object* v_goal_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0(v_goal_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC(lean_object* v_goal_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v___f_2446_; lean_object* v___x_2447_; 
lean_inc(v_goal_2433_);
v___f_2446_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2446_, 0, v_goal_2433_);
v___x_2447_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_goal_2433_, v___f_2446_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___boxed(lean_object* v_goal_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_goal_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec(v_a_2450_);
lean_dec_ref(v_a_2449_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0(lean_object* v_mvarId_2462_, lean_object* v_val_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v___x_2476_; 
v___x_2476_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_mvarId_2462_, v_val_2463_, v___y_2472_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___boxed(lean_object* v_mvarId_2477_, lean_object* v_val_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0(v_mvarId_2477_, v_val_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
return v_res_2491_;
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
