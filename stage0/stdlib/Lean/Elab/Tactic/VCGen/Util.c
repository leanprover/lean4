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
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___redArg(v_e_31_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v_res_38_;
v_res_38_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___boxed(lean_object* v_e_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1(v_e_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_45_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___redArg(lean_object* v_k_46_, uint8_t v_allowLevelAssignments_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_47_, v_k_46_, v___y_48_, v___y_49_, v___y_50_, v___y_51_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v___x_53_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_53_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_54_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
else
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_69_; 
v_a_62_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_69_ == 0)
{
v___x_64_ = v___x_53_;
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_53_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_46_ = stack[0].m_obj;
uint8_t v_allowLevelAssignments_47_ = stack[1].m_num;
lean_object* v___y_48_ = stack[2].m_obj;
lean_object* v___y_49_ = stack[3].m_obj;
lean_object* v___y_50_ = stack[4].m_obj;
lean_object* v___y_51_ = stack[5].m_obj;
lean_object* v_res_70_;
v_res_70_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___redArg(v_k_46_, v_allowLevelAssignments_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_);
stack->m_obj
 = v_res_70_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___redArg___boxed(lean_object* v_k_71_, lean_object* v_allowLevelAssignments_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_78_; lean_object* v_res_79_; 
v_allowLevelAssignments_boxed_78_ = lean_unbox(v_allowLevelAssignments_72_);
v_res_79_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___redArg(v_k_71_, v_allowLevelAssignments_boxed_78_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
return v_res_79_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5(lean_object* v_00_u03b1_80_, lean_object* v_k_81_, uint8_t v_allowLevelAssignments_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___redArg(v_k_81_, v_allowLevelAssignments_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
return v___x_88_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_81_ = stack[1].m_obj;
uint8_t v_allowLevelAssignments_82_ = stack[2].m_num;
lean_object* v___y_83_ = stack[3].m_obj;
lean_object* v___y_84_ = stack[4].m_obj;
lean_object* v___y_85_ = stack[5].m_obj;
lean_object* v___y_86_ = stack[6].m_obj;
lean_object* v_res_89_;
v_res_89_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5(lean_box(0), v_k_81_, v_allowLevelAssignments_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
stack->m_obj
 = v_res_89_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___boxed(lean_object* v_00_u03b1_90_, lean_object* v_k_91_, lean_object* v_allowLevelAssignments_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_98_; lean_object* v_res_99_; 
v_allowLevelAssignments_boxed_98_ = lean_unbox(v_allowLevelAssignments_92_);
v_res_99_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5(v_00_u03b1_90_, v_k_91_, v_allowLevelAssignments_boxed_98_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
return v_res_99_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__3(lean_object* v_as_100_, size_t v_i_101_, size_t v_stop_102_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = lean_usize_dec_eq(v_i_101_, v_stop_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_array_uget_borrowed(v_as_100_, v_i_101_);
v___x_105_ = l_Lean_Expr_hasExprMVar(v___x_104_);
if (v___x_105_ == 0)
{
size_t v___x_106_; size_t v___x_107_; 
v___x_106_ = ((size_t)1ULL);
v___x_107_ = lean_usize_add(v_i_101_, v___x_106_);
v_i_101_ = v___x_107_;
goto _start;
}
else
{
return v___x_105_;
}
}
else
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_100_ = stack[0].m_obj;
size_t v_i_101_ = stack[1].m_num;
size_t v_stop_102_ = stack[2].m_num;
uint8_t v_res_110_;
v_res_110_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__3(v_as_100_, v_i_101_, v_stop_102_);
stack->m_num = v_res_110_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__3___boxed(lean_object* v_as_111_, lean_object* v_i_112_, lean_object* v_stop_113_){
_start:
{
size_t v_i_boxed_114_; size_t v_stop_boxed_115_; uint8_t v_res_116_; lean_object* v_r_117_; 
v_i_boxed_114_ = lean_unbox_usize(v_i_112_);
lean_dec(v_i_112_);
v_stop_boxed_115_ = lean_unbox_usize(v_stop_113_);
lean_dec(v_stop_113_);
v_res_116_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__3(v_as_111_, v_i_boxed_114_, v_stop_boxed_115_);
lean_dec_ref(v_as_111_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0(lean_object* v_as_120_, size_t v_sz_121_, size_t v_i_122_, lean_object* v_b_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_a_130_; uint8_t v___x_134_; 
v___x_134_ = lean_usize_dec_lt(v_i_122_, v_sz_121_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; 
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v_b_123_);
return v___x_135_;
}
else
{
lean_object* v_snd_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_192_; 
v_snd_136_ = lean_ctor_get(v_b_123_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v_b_123_);
if (v_isSharedCheck_192_ == 0)
{
lean_object* v_unused_193_; 
v_unused_193_ = lean_ctor_get(v_b_123_, 0);
lean_dec(v_unused_193_);
v___x_138_ = v_b_123_;
v_isShared_139_ = v_isSharedCheck_192_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_snd_136_);
lean_dec(v_b_123_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_192_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v_array_140_; lean_object* v_start_141_; lean_object* v_stop_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v_array_140_ = lean_ctor_get(v_snd_136_, 0);
v_start_141_ = lean_ctor_get(v_snd_136_, 1);
v_stop_142_ = lean_ctor_get(v_snd_136_, 2);
v___x_143_ = lean_box(0);
v___x_144_ = lean_nat_dec_lt(v_start_141_, v_stop_142_);
if (v___x_144_ == 0)
{
lean_object* v___x_146_; 
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v___x_143_);
v___x_146_ = v___x_138_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_snd_136_);
v___x_146_ = v_reuseFailAlloc_148_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
else
{
lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_188_; 
lean_inc(v_stop_142_);
lean_inc(v_start_141_);
lean_inc_ref(v_array_140_);
v_isSharedCheck_188_ = !lean_is_exclusive(v_snd_136_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; lean_object* v_unused_190_; lean_object* v_unused_191_; 
v_unused_189_ = lean_ctor_get(v_snd_136_, 2);
lean_dec(v_unused_189_);
v_unused_190_ = lean_ctor_get(v_snd_136_, 1);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v_snd_136_, 0);
lean_dec(v_unused_191_);
v___x_150_ = v_snd_136_;
v_isShared_151_ = v_isSharedCheck_188_;
goto v_resetjp_149_;
}
else
{
lean_dec(v_snd_136_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_188_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_152_ = lean_array_fget(v_array_140_, v_start_141_);
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = lean_nat_add(v_start_141_, v___x_153_);
lean_dec(v_start_141_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v___x_154_);
v___x_156_ = v___x_150_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_array_140_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_187_, 2, v_stop_142_);
v___x_156_ = v_reuseFailAlloc_187_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
if (lean_obj_tag(v___x_152_) == 1)
{
lean_object* v_val_157_; lean_object* v_a_158_; lean_object* v___x_159_; 
v_val_157_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_val_157_);
lean_dec_ref_known(v___x_152_, 1);
v_a_158_ = lean_array_uget_borrowed(v_as_120_, v_i_122_);
lean_inc(v_a_158_);
v___x_159_ = l_Lean_Meta_isExprDefEq(v_a_158_, v_val_157_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_175_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_175_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_175_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_175_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
uint8_t v___x_164_; 
v___x_164_ = lean_unbox(v_a_160_);
lean_dec(v_a_160_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_165_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0___closed__0));
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 1, v___x_156_);
lean_ctor_set(v___x_138_, 0, v___x_165_);
v___x_167_ = v___x_138_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_156_);
v___x_167_ = v_reuseFailAlloc_171_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_169_; 
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_167_);
v___x_169_ = v___x_162_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
else
{
lean_object* v___x_173_; 
lean_del_object(v___x_162_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 1, v___x_156_);
lean_ctor_set(v___x_138_, 0, v___x_143_);
v___x_173_ = v___x_138_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v___x_156_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
v_a_130_ = v___x_173_;
goto v___jp_129_;
}
}
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
lean_dec_ref(v___x_156_);
lean_del_object(v___x_138_);
v_a_176_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_159_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_159_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
else
{
lean_object* v___x_185_; 
lean_dec(v___x_152_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 1, v___x_156_);
lean_ctor_set(v___x_138_, 0, v___x_143_);
v___x_185_ = v___x_138_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v___x_156_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
v_a_130_ = v___x_185_;
goto v___jp_129_;
}
}
}
}
}
}
}
v___jp_129_:
{
size_t v___x_131_; size_t v___x_132_; 
v___x_131_ = ((size_t)1ULL);
v___x_132_ = lean_usize_add(v_i_122_, v___x_131_);
v_i_122_ = v___x_132_;
v_b_123_ = v_a_130_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_120_ = stack[0].m_obj;
size_t v_sz_121_ = stack[1].m_num;
size_t v_i_122_ = stack[2].m_num;
lean_object* v_b_123_ = stack[3].m_obj;
lean_object* v___y_124_ = stack[4].m_obj;
lean_object* v___y_125_ = stack[5].m_obj;
lean_object* v___y_126_ = stack[6].m_obj;
lean_object* v___y_127_ = stack[7].m_obj;
lean_object* v_res_194_;
v_res_194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0(v_as_120_, v_sz_121_, v_i_122_, v_b_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0___boxed(lean_object* v_as_195_, lean_object* v_sz_196_, lean_object* v_i_197_, lean_object* v_b_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
size_t v_sz_boxed_204_; size_t v_i_boxed_205_; lean_object* v_res_206_; 
v_sz_boxed_204_ = lean_unbox_usize(v_sz_196_);
lean_dec(v_sz_196_);
v_i_boxed_205_ = lean_unbox_usize(v_i_197_);
lean_dec(v_i_197_);
v_res_206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0(v_as_195_, v_sz_boxed_204_, v_i_boxed_205_, v_b_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec_ref(v_as_195_);
return v_res_206_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4_spec__4(lean_object* v_msgData_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; lean_object* v_env_214_; uint8_t v___x_215_; lean_object* v_env_216_; lean_object* v___x_217_; lean_object* v_toCold_218_; lean_object* v_mctx_219_; lean_object* v_lctx_220_; lean_object* v_options_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_213_ = lean_st_ref_get(v___y_211_);
v_env_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc_ref(v_env_214_);
lean_dec(v___x_213_);
v___x_215_ = 0;
v_env_216_ = l_Lean_Environment_setRecordingDeps(v_env_214_, v___x_215_);
v___x_217_ = lean_st_ref_get(v___y_209_);
v_toCold_218_ = lean_ctor_get(v___y_210_, 0);
v_mctx_219_ = lean_ctor_get(v___x_217_, 0);
lean_inc_ref(v_mctx_219_);
lean_dec(v___x_217_);
v_lctx_220_ = lean_ctor_get(v___y_208_, 2);
v_options_221_ = lean_ctor_get(v_toCold_218_, 2);
lean_inc_ref(v_options_221_);
lean_inc_ref(v_lctx_220_);
v___x_222_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_222_, 0, v_env_216_);
lean_ctor_set(v___x_222_, 1, v_mctx_219_);
lean_ctor_set(v___x_222_, 2, v_lctx_220_);
lean_ctor_set(v___x_222_, 3, v_options_221_);
v___x_223_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v_msgData_207_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_207_ = stack[0].m_obj;
lean_object* v___y_208_ = stack[1].m_obj;
lean_object* v___y_209_ = stack[2].m_obj;
lean_object* v___y_210_ = stack[3].m_obj;
lean_object* v___y_211_ = stack[4].m_obj;
lean_object* v_res_225_;
v_res_225_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4_spec__4(v_msgData_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
stack->m_obj
 = v_res_225_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4_spec__4___boxed(lean_object* v_msgData_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4_spec__4(v_msgData_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
return v_res_232_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___redArg(lean_object* v_msg_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_ref_239_; lean_object* v___x_240_; lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_249_; 
v_ref_239_ = lean_ctor_get(v___y_236_, 2);
v___x_240_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4_spec__4(v_msg_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_249_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_247_; 
lean_inc(v_ref_239_);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v_ref_239_);
lean_ctor_set(v___x_245_, 1, v_a_241_);
if (v_isShared_244_ == 0)
{
lean_ctor_set_tag(v___x_243_, 1);
lean_ctor_set(v___x_243_, 0, v___x_245_);
v___x_247_ = v___x_243_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_233_ = stack[0].m_obj;
lean_object* v___y_234_ = stack[1].m_obj;
lean_object* v___y_235_ = stack[2].m_obj;
lean_object* v___y_236_ = stack[3].m_obj;
lean_object* v___y_237_ = stack[4].m_obj;
lean_object* v_res_250_;
v_res_250_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___redArg(v_msg_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
stack->m_obj
 = v_res_250_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___redArg___boxed(lean_object* v_msg_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___redArg(v_msg_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
return v_res_257_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__2(size_t v_sz_258_, size_t v_i_259_, lean_object* v_bs_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
uint8_t v___x_266_; 
v___x_266_ = lean_usize_dec_lt(v_i_259_, v_sz_258_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v_bs_260_);
return v___x_267_;
}
else
{
lean_object* v_v_268_; lean_object* v___x_269_; lean_object* v_bs_x27_270_; lean_object* v___x_271_; 
v_v_268_ = lean_array_uget(v_bs_260_, v_i_259_);
v___x_269_ = lean_unsigned_to_nat(0u);
v_bs_x27_270_ = lean_array_uset(v_bs_260_, v_i_259_, v___x_269_);
v___x_271_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___redArg(v_v_268_, v___y_262_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; size_t v___x_273_; size_t v___x_274_; lean_object* v___x_275_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_271_, 1);
v___x_273_ = ((size_t)1ULL);
v___x_274_ = lean_usize_add(v_i_259_, v___x_273_);
v___x_275_ = lean_array_uset(v_bs_x27_270_, v_i_259_, v_a_272_);
v_i_259_ = v___x_274_;
v_bs_260_ = v___x_275_;
goto _start;
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec_ref(v_bs_x27_270_);
v_a_277_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_271_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_271_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
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
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_258_ = stack[0].m_num;
size_t v_i_259_ = stack[1].m_num;
lean_object* v_bs_260_ = stack[2].m_obj;
lean_object* v___y_261_ = stack[3].m_obj;
lean_object* v___y_262_ = stack[4].m_obj;
lean_object* v___y_263_ = stack[5].m_obj;
lean_object* v___y_264_ = stack[6].m_obj;
lean_object* v_res_285_;
v_res_285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__2(v_sz_258_, v_i_259_, v_bs_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
stack->m_obj
 = v_res_285_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__2___boxed(lean_object* v_sz_286_, lean_object* v_i_287_, lean_object* v_bs_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
size_t v_sz_boxed_294_; size_t v_i_boxed_295_; lean_object* v_res_296_; 
v_sz_boxed_294_ = lean_unbox_usize(v_sz_286_);
lean_dec(v_sz_286_);
v_i_boxed_295_ = lean_unbox_usize(v_i_287_);
lean_dec(v_i_287_);
v_res_296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__2(v_sz_boxed_294_, v_i_boxed_295_, v_bs_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
return v_res_296_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__0));
v___x_299_ = l_Lean_stringToMessageData(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__2));
v___x_302_ = l_Lean_stringToMessageData(v___x_301_);
return v___x_302_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0(lean_object* v_cls_303_, lean_object* v_xs_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_317_; lean_object* v___y_318_; uint8_t v___y_319_; lean_object* v___x_322_; 
lean_inc(v_cls_303_);
v___x_322_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_cls_303_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_324_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc_n(v_a_323_, 2);
lean_dec_ref_known(v___x_322_, 1);
lean_inc(v___y_308_);
lean_inc_ref(v___y_307_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
v___x_324_ = lean_infer_type(v_a_323_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_326_; uint8_t v___x_327_; lean_object* v___x_328_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_324_, 1);
v___x_326_ = lean_box(0);
v___x_327_ = 0;
v___x_328_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_325_, v___x_326_, v___x_327_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v_fst_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_419_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref_known(v___x_328_, 1);
v_fst_330_ = lean_ctor_get(v_a_329_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v_a_329_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v_a_329_, 1);
lean_dec(v_unused_420_);
v___x_332_ = v_a_329_;
v_isShared_333_ = v_isSharedCheck_419_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_fst_330_);
lean_dec(v_a_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_419_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_402_ = lean_array_get_size(v_fst_330_);
v___x_403_ = lean_array_get_size(v_xs_304_);
v___x_404_ = lean_nat_dec_lt(v___x_402_, v___x_403_);
if (v___x_404_ == 0)
{
lean_dec(v_cls_303_);
v___y_335_ = v___y_305_;
v___y_336_ = v___y_306_;
v___y_337_ = v___y_307_;
v___y_338_ = v___y_308_;
goto v___jp_334_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_del_object(v___x_332_);
lean_dec(v_fst_330_);
lean_dec(v_a_323_);
lean_dec_ref(v_xs_304_);
v___x_405_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__1, &l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__1);
v___x_406_ = l_Lean_MessageData_ofName(v_cls_303_);
v___x_407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3, &l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3);
v___x_409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___redArg(v___x_409_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
v_a_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
v___jp_334_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_array_get_size(v_xs_304_);
v___x_341_ = l_Array_toSubarray___redArg(v_xs_304_, v___x_339_, v___x_340_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v___x_341_);
lean_ctor_set(v___x_332_, 0, v___x_326_);
v___x_343_ = v___x_332_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v___x_341_);
v___x_343_ = v_reuseFailAlloc_401_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
size_t v_sz_344_; size_t v___x_345_; lean_object* v___x_346_; 
v_sz_344_ = lean_array_size(v_fst_330_);
v___x_345_ = ((size_t)0ULL);
v___x_346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__0(v_fst_330_, v_sz_344_, v___x_345_, v___x_343_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_392_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_392_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_392_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_392_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v_fst_351_; 
v_fst_351_ = lean_ctor_get(v_a_347_, 0);
lean_inc(v_fst_351_);
lean_dec(v_a_347_);
if (lean_obj_tag(v_fst_351_) == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
lean_del_object(v___x_349_);
v___x_352_ = l_Lean_mkAppN(v_a_323_, v_fst_330_);
v___x_353_ = l_Lean_Meta_synthInstance_x3f(v___x_352_, v___x_326_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_379_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_379_ == 0)
{
v___x_356_ = v___x_353_;
v_isShared_357_ = v_isSharedCheck_379_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_379_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
if (lean_obj_tag(v_a_354_) == 1)
{
lean_object* v_val_358_; lean_object* v___x_359_; 
lean_del_object(v___x_356_);
v_val_358_ = lean_ctor_get(v_a_354_, 0);
lean_inc(v_val_358_);
lean_dec_ref_known(v_a_354_, 1);
v___x_359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__2(v_sz_344_, v___x_345_, v_fst_330_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec_ref(v___y_335_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_361_; lean_object* v_a_362_; uint8_t v___x_363_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v___x_359_, 1);
v___x_361_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__1___redArg(v_val_358_, v___y_336_);
lean_dec(v___y_336_);
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref(v___x_361_);
v___x_363_ = l_Lean_Expr_hasExprMVar(v_a_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_364_ = lean_array_get_size(v_a_360_);
v___x_365_ = lean_nat_dec_lt(v___x_339_, v___x_364_);
if (v___x_365_ == 0)
{
v___y_311_ = v_a_362_;
v___y_312_ = v_a_360_;
goto v___jp_310_;
}
else
{
if (v___x_365_ == 0)
{
v___y_311_ = v_a_362_;
v___y_312_ = v_a_360_;
goto v___jp_310_;
}
else
{
size_t v___x_366_; uint8_t v___x_367_; 
v___x_366_ = lean_usize_of_nat(v___x_364_);
v___x_367_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__3(v_a_360_, v___x_345_, v___x_366_);
v___y_317_ = v_a_362_;
v___y_318_ = v_a_360_;
v___y_319_ = v___x_367_;
goto v___jp_316_;
}
}
}
else
{
v___y_317_ = v_a_362_;
v___y_318_ = v_a_360_;
v___y_319_ = v___x_363_;
goto v___jp_316_;
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec(v_val_358_);
lean_dec(v___y_336_);
v_a_368_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_359_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_359_);
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
lean_object* v___x_377_; 
lean_dec(v_a_354_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v_fst_330_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_326_);
v___x_377_ = v___x_356_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_326_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v_fst_330_);
v_a_380_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_353_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_353_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
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
else
{
lean_object* v_val_388_; lean_object* v___x_390_; 
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v_fst_330_);
lean_dec(v_a_323_);
v_val_388_ = lean_ctor_get(v_fst_351_, 0);
lean_inc(v_val_388_);
lean_dec_ref_known(v_fst_351_, 1);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v_val_388_);
v___x_390_ = v___x_349_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_val_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v_fst_330_);
lean_dec(v_a_323_);
v_a_393_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_346_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_346_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_dec(v_a_323_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec_ref(v_xs_304_);
lean_dec(v_cls_303_);
v_a_421_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_328_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_328_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec(v_a_323_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec_ref(v_xs_304_);
lean_dec(v_cls_303_);
v_a_429_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_324_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_324_);
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
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec_ref(v_xs_304_);
lean_dec(v_cls_303_);
v_a_437_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_322_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_322_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
v___jp_310_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___y_312_);
lean_ctor_set(v___x_313_, 1, v___y_311_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
v___jp_316_:
{
if (v___y_319_ == 0)
{
v___y_311_ = v___y_317_;
v___y_312_ = v___y_318_;
goto v___jp_310_;
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; 
lean_dec_ref(v___y_318_);
lean_dec_ref(v___y_317_);
v___x_320_ = lean_box(0);
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
return v___x_321_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_303_ = stack[0].m_obj;
lean_object* v_xs_304_ = stack[1].m_obj;
lean_object* v___y_305_ = stack[2].m_obj;
lean_object* v___y_306_ = stack[3].m_obj;
lean_object* v___y_307_ = stack[4].m_obj;
lean_object* v___y_308_ = stack[5].m_obj;
lean_object* v_res_445_;
v_res_445_ = l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0(v_cls_303_, v_xs_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___boxed(lean_object* v_cls_446_, lean_object* v_xs_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0(v_cls_446_, v_xs_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
return v_res_453_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f(lean_object* v_cls_454_, lean_object* v_xs_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v___f_461_; uint8_t v___x_462_; lean_object* v___x_463_; 
v___f_461_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_461_, 0, v_cls_454_);
lean_closure_set(v___f_461_, 1, v_xs_455_);
v___x_462_ = 0;
v___x_463_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__5___redArg(v___f_461_, v___x_462_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
return v___x_463_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_454_ = stack[0].m_obj;
lean_object* v_xs_455_ = stack[1].m_obj;
lean_object* v_a_456_ = stack[2].m_obj;
lean_object* v_a_457_ = stack[3].m_obj;
lean_object* v_a_458_ = stack[4].m_obj;
lean_object* v_a_459_ = stack[5].m_obj;
lean_object* v_res_464_;
v_res_464_ = l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f(v_cls_454_, v_xs_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
stack->m_obj
 = v_res_464_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___boxed(lean_object* v_cls_465_, lean_object* v_xs_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f(v_cls_465_, v_xs_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
return v_res_472_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4(lean_object* v_00_u03b1_473_, lean_object* v_msg_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___redArg(v_msg_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
return v___x_480_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_474_ = stack[1].m_obj;
lean_object* v___y_475_ = stack[2].m_obj;
lean_object* v___y_476_ = stack[3].m_obj;
lean_object* v___y_477_ = stack[4].m_obj;
lean_object* v___y_478_ = stack[5].m_obj;
lean_object* v_res_481_;
v_res_481_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4(lean_box(0), v_msg_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
stack->m_obj
 = v_res_481_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4___boxed(lean_object* v_00_u03b1_482_, lean_object* v_msg_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4(v_00_u03b1_482_, v_msg_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
return v_res_489_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(lean_object* v_mvarId_490_, lean_object* v_x_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_490_, v_x_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
v_a_506_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_497_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_497_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_490_ = stack[0].m_obj;
lean_object* v_x_491_ = stack[1].m_obj;
lean_object* v___y_492_ = stack[2].m_obj;
lean_object* v___y_493_ = stack[3].m_obj;
lean_object* v___y_494_ = stack[4].m_obj;
lean_object* v___y_495_ = stack[5].m_obj;
lean_object* v_res_514_;
v_res_514_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(v_mvarId_490_, v_x_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
stack->m_obj
 = v_res_514_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg___boxed(lean_object* v_mvarId_515_, lean_object* v_x_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(v_mvarId_515_, v_x_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
return v_res_522_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1(lean_object* v_00_u03b1_523_, lean_object* v_mvarId_524_, lean_object* v_x_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(v_mvarId_524_, v_x_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
return v___x_531_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_524_ = stack[1].m_obj;
lean_object* v_x_525_ = stack[2].m_obj;
lean_object* v___y_526_ = stack[3].m_obj;
lean_object* v___y_527_ = stack[4].m_obj;
lean_object* v___y_528_ = stack[5].m_obj;
lean_object* v___y_529_ = stack[6].m_obj;
lean_object* v_res_532_;
v_res_532_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1(lean_box(0), v_mvarId_524_, v_x_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
stack->m_obj
 = v_res_532_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___boxed(lean_object* v_00_u03b1_533_, lean_object* v_mvarId_534_, lean_object* v_x_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1(v_00_u03b1_533_, v_mvarId_534_, v_x_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_542_, lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
lean_object* v_ks_546_; lean_object* v_vs_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_571_; 
v_ks_546_ = lean_ctor_get(v_x_542_, 0);
v_vs_547_ = lean_ctor_get(v_x_542_, 1);
v_isSharedCheck_571_ = !lean_is_exclusive(v_x_542_);
if (v_isSharedCheck_571_ == 0)
{
v___x_549_ = v_x_542_;
v_isShared_550_ = v_isSharedCheck_571_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_vs_547_);
lean_inc(v_ks_546_);
lean_dec(v_x_542_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_571_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_551_ = lean_array_get_size(v_ks_546_);
v___x_552_ = lean_nat_dec_lt(v_x_543_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
lean_dec(v_x_543_);
v___x_553_ = lean_array_push(v_ks_546_, v_x_544_);
v___x_554_ = lean_array_push(v_vs_547_, v_x_545_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v___x_554_);
lean_ctor_set(v___x_549_, 0, v___x_553_);
v___x_556_ = v___x_549_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
else
{
lean_object* v_k_x27_558_; uint8_t v___x_559_; 
v_k_x27_558_ = lean_array_fget_borrowed(v_ks_546_, v_x_543_);
v___x_559_ = l_Lean_instBEqMVarId_beq(v_x_544_, v_k_x27_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_561_; 
if (v_isShared_550_ == 0)
{
v___x_561_ = v___x_549_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_ks_546_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_vs_547_);
v___x_561_ = v_reuseFailAlloc_565_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_x_543_, v___x_562_);
lean_dec(v_x_543_);
v_x_542_ = v___x_561_;
v_x_543_ = v___x_563_;
goto _start;
}
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_566_ = lean_array_fset(v_ks_546_, v_x_543_, v_x_544_);
v___x_567_ = lean_array_fset(v_vs_547_, v_x_543_, v_x_545_);
lean_dec(v_x_543_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v___x_567_);
lean_ctor_set(v___x_549_, 0, v___x_566_);
v___x_569_ = v___x_549_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_572_, lean_object* v_k_573_, lean_object* v_v_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_572_, v___x_575_, v_k_573_, v_v_574_);
return v___x_576_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_577_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(lean_object* v_x_578_, size_t v_x_579_, size_t v_x_580_, lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_578_) == 0)
{
lean_object* v_es_583_; size_t v___x_584_; size_t v___x_585_; lean_object* v_j_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v_es_583_ = lean_ctor_get(v_x_578_, 0);
v___x_584_ = ((size_t)31ULL);
v___x_585_ = lean_usize_land(v_x_579_, v___x_584_);
v_j_586_ = lean_usize_to_nat(v___x_585_);
v___x_587_ = lean_array_get_size(v_es_583_);
v___x_588_ = lean_nat_dec_lt(v_j_586_, v___x_587_);
if (v___x_588_ == 0)
{
lean_dec(v_j_586_);
lean_dec(v_x_582_);
lean_dec(v_x_581_);
return v_x_578_;
}
else
{
lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_627_; 
lean_inc_ref(v_es_583_);
v_isSharedCheck_627_ = !lean_is_exclusive(v_x_578_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v_x_578_, 0);
lean_dec(v_unused_628_);
v___x_590_ = v_x_578_;
v_isShared_591_ = v_isSharedCheck_627_;
goto v_resetjp_589_;
}
else
{
lean_dec(v_x_578_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_627_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v_v_592_; lean_object* v___x_593_; lean_object* v_xs_x27_594_; lean_object* v___y_596_; 
v_v_592_ = lean_array_fget(v_es_583_, v_j_586_);
v___x_593_ = lean_box(0);
v_xs_x27_594_ = lean_array_fset(v_es_583_, v_j_586_, v___x_593_);
switch(lean_obj_tag(v_v_592_))
{
case 0:
{
lean_object* v_key_601_; lean_object* v_val_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_612_; 
v_key_601_ = lean_ctor_get(v_v_592_, 0);
v_val_602_ = lean_ctor_get(v_v_592_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_v_592_);
if (v_isSharedCheck_612_ == 0)
{
v___x_604_ = v_v_592_;
v_isShared_605_ = v_isSharedCheck_612_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_val_602_);
lean_inc(v_key_601_);
lean_dec(v_v_592_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_612_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
uint8_t v___x_606_; 
v___x_606_ = l_Lean_instBEqMVarId_beq(v_x_581_, v_key_601_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; 
lean_del_object(v___x_604_);
v___x_607_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_601_, v_val_602_, v_x_581_, v_x_582_);
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
v___y_596_ = v___x_608_;
goto v___jp_595_;
}
else
{
lean_object* v___x_610_; 
lean_dec(v_val_602_);
lean_dec(v_key_601_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v_x_582_);
lean_ctor_set(v___x_604_, 0, v_x_581_);
v___x_610_ = v___x_604_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_x_581_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_x_582_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
v___y_596_ = v___x_610_;
goto v___jp_595_;
}
}
}
}
case 1:
{
lean_object* v_node_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_625_; 
v_node_613_ = lean_ctor_get(v_v_592_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v_v_592_);
if (v_isSharedCheck_625_ == 0)
{
v___x_615_ = v_v_592_;
v_isShared_616_ = v_isSharedCheck_625_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_node_613_);
lean_dec(v_v_592_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_625_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
size_t v___x_617_; size_t v___x_618_; size_t v___x_619_; size_t v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_617_ = ((size_t)5ULL);
v___x_618_ = lean_usize_shift_right(v_x_579_, v___x_617_);
v___x_619_ = ((size_t)1ULL);
v___x_620_ = lean_usize_add(v_x_580_, v___x_619_);
v___x_621_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_node_613_, v___x_618_, v___x_620_, v_x_581_, v_x_582_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_621_);
v___x_623_ = v___x_615_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
v___y_596_ = v___x_623_;
goto v___jp_595_;
}
}
}
default: 
{
lean_object* v___x_626_; 
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v_x_581_);
lean_ctor_set(v___x_626_, 1, v_x_582_);
v___y_596_ = v___x_626_;
goto v___jp_595_;
}
}
v___jp_595_:
{
lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_597_ = lean_array_fset(v_xs_x27_594_, v_j_586_, v___y_596_);
lean_dec(v_j_586_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_597_);
v___x_599_ = v___x_590_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
else
{
lean_object* v_ks_629_; lean_object* v_vs_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_648_; 
v_ks_629_ = lean_ctor_get(v_x_578_, 0);
v_vs_630_ = lean_ctor_get(v_x_578_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v_x_578_);
if (v_isSharedCheck_648_ == 0)
{
v___x_632_ = v_x_578_;
v_isShared_633_ = v_isSharedCheck_648_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_vs_630_);
lean_inc(v_ks_629_);
lean_dec(v_x_578_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_648_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_ks_629_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_vs_630_);
v___x_635_ = v_reuseFailAlloc_647_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v_newNode_636_; size_t v___x_637_; uint8_t v___x_638_; 
v_newNode_636_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3___redArg(v___x_635_, v_x_581_, v_x_582_);
v___x_637_ = ((size_t)7ULL);
v___x_638_ = lean_usize_dec_le(v___x_637_, v_x_580_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_639_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_636_);
v___x_640_ = lean_unsigned_to_nat(4u);
v___x_641_ = lean_nat_dec_lt(v___x_639_, v___x_640_);
lean_dec(v___x_639_);
if (v___x_641_ == 0)
{
lean_object* v_ks_642_; lean_object* v_vs_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v_ks_642_ = lean_ctor_get(v_newNode_636_, 0);
lean_inc_ref(v_ks_642_);
v_vs_643_ = lean_ctor_get(v_newNode_636_, 1);
lean_inc_ref(v_vs_643_);
lean_dec_ref(v_newNode_636_);
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_645_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_646_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(v_x_580_, v_ks_642_, v_vs_643_, v___x_644_, v___x_645_);
lean_dec_ref(v_vs_643_);
lean_dec_ref(v_ks_642_);
return v___x_646_;
}
else
{
return v_newNode_636_;
}
}
else
{
return v_newNode_636_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_578_ = stack[0].m_obj;
size_t v_x_579_ = stack[1].m_num;
size_t v_x_580_ = stack[2].m_num;
lean_object* v_x_581_ = stack[3].m_obj;
lean_object* v_x_582_ = stack[4].m_obj;
lean_object* v_res_649_;
v_res_649_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_x_578_, v_x_579_, v_x_580_, v_x_581_, v_x_582_);
stack->m_obj
 = v_res_649_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_650_, lean_object* v_keys_651_, lean_object* v_vals_652_, lean_object* v_i_653_, lean_object* v_entries_654_){
_start:
{
lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_655_ = lean_array_get_size(v_keys_651_);
v___x_656_ = lean_nat_dec_lt(v_i_653_, v___x_655_);
if (v___x_656_ == 0)
{
lean_dec(v_i_653_);
return v_entries_654_;
}
else
{
lean_object* v_k_657_; lean_object* v_v_658_; uint64_t v___x_659_; size_t v_h_660_; size_t v___x_661_; lean_object* v___x_662_; size_t v___x_663_; size_t v___x_664_; size_t v___x_665_; size_t v_h_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_k_657_ = lean_array_fget_borrowed(v_keys_651_, v_i_653_);
v_v_658_ = lean_array_fget_borrowed(v_vals_652_, v_i_653_);
v___x_659_ = l_Lean_instHashableMVarId_hash(v_k_657_);
v_h_660_ = lean_uint64_to_usize(v___x_659_);
v___x_661_ = ((size_t)5ULL);
v___x_662_ = lean_unsigned_to_nat(1u);
v___x_663_ = ((size_t)1ULL);
v___x_664_ = lean_usize_sub(v_depth_650_, v___x_663_);
v___x_665_ = lean_usize_mul(v___x_661_, v___x_664_);
v_h_666_ = lean_usize_shift_right(v_h_660_, v___x_665_);
v___x_667_ = lean_nat_add(v_i_653_, v___x_662_);
lean_dec(v_i_653_);
lean_inc(v_v_658_);
lean_inc(v_k_657_);
v___x_668_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_entries_654_, v_h_666_, v_depth_650_, v_k_657_, v_v_658_);
v_i_653_ = v___x_667_;
v_entries_654_ = v___x_668_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_650_ = stack[0].m_num;
lean_object* v_keys_651_ = stack[1].m_obj;
lean_object* v_vals_652_ = stack[2].m_obj;
lean_object* v_i_653_ = stack[3].m_obj;
lean_object* v_entries_654_ = stack[4].m_obj;
lean_object* v_res_670_;
v_res_670_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_650_, v_keys_651_, v_vals_652_, v_i_653_, v_entries_654_);
stack->m_obj
 = v_res_670_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_671_, lean_object* v_keys_672_, lean_object* v_vals_673_, lean_object* v_i_674_, lean_object* v_entries_675_){
_start:
{
size_t v_depth_boxed_676_; lean_object* v_res_677_; 
v_depth_boxed_676_ = lean_unbox_usize(v_depth_671_);
lean_dec(v_depth_671_);
v_res_677_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_676_, v_keys_672_, v_vals_673_, v_i_674_, v_entries_675_);
lean_dec_ref(v_vals_673_);
lean_dec_ref(v_keys_672_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
size_t v_x_1204__boxed_683_; size_t v_x_1205__boxed_684_; lean_object* v_res_685_; 
v_x_1204__boxed_683_ = lean_unbox_usize(v_x_679_);
lean_dec(v_x_679_);
v_x_1205__boxed_684_ = lean_unbox_usize(v_x_680_);
lean_dec(v_x_680_);
v_res_685_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_x_678_, v_x_1204__boxed_683_, v_x_1205__boxed_684_, v_x_681_, v_x_682_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(lean_object* v_x_686_, lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
uint64_t v___x_689_; size_t v___x_690_; size_t v___x_691_; lean_object* v___x_692_; 
v___x_689_ = l_Lean_instHashableMVarId_hash(v_x_687_);
v___x_690_ = lean_uint64_to_usize(v___x_689_);
v___x_691_ = ((size_t)1ULL);
v___x_692_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_x_686_, v___x_690_, v___x_691_, v_x_687_, v_x_688_);
return v___x_692_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(lean_object* v_mvarId_693_, lean_object* v_val_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; lean_object* v_mctx_698_; lean_object* v_cache_699_; lean_object* v_zetaDeltaFVarIds_700_; lean_object* v_postponed_701_; lean_object* v_diag_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_732_; 
v___x_697_ = lean_st_ref_take(v___y_695_);
v_mctx_698_ = lean_ctor_get(v___x_697_, 0);
v_cache_699_ = lean_ctor_get(v___x_697_, 1);
v_zetaDeltaFVarIds_700_ = lean_ctor_get(v___x_697_, 2);
v_postponed_701_ = lean_ctor_get(v___x_697_, 3);
v_diag_702_ = lean_ctor_get(v___x_697_, 4);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_732_ == 0)
{
v___x_704_ = v___x_697_;
v_isShared_705_ = v_isSharedCheck_732_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_diag_702_);
lean_inc(v_postponed_701_);
lean_inc(v_zetaDeltaFVarIds_700_);
lean_inc(v_cache_699_);
lean_inc(v_mctx_698_);
lean_dec(v___x_697_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_732_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v_depth_706_; lean_object* v_levelAssignDepth_707_; lean_object* v_lmvarCounter_708_; lean_object* v_mvarCounter_709_; lean_object* v_lDecls_710_; lean_object* v_decls_711_; lean_object* v_userNames_712_; lean_object* v_lAssignment_713_; lean_object* v_eAssignment_714_; lean_object* v_dAssignment_715_; lean_object* v_instanceTypedMVars_716_; lean_object* v_synthNormMemo_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_731_; 
v_depth_706_ = lean_ctor_get(v_mctx_698_, 0);
v_levelAssignDepth_707_ = lean_ctor_get(v_mctx_698_, 1);
v_lmvarCounter_708_ = lean_ctor_get(v_mctx_698_, 2);
v_mvarCounter_709_ = lean_ctor_get(v_mctx_698_, 3);
v_lDecls_710_ = lean_ctor_get(v_mctx_698_, 4);
v_decls_711_ = lean_ctor_get(v_mctx_698_, 5);
v_userNames_712_ = lean_ctor_get(v_mctx_698_, 6);
v_lAssignment_713_ = lean_ctor_get(v_mctx_698_, 7);
v_eAssignment_714_ = lean_ctor_get(v_mctx_698_, 8);
v_dAssignment_715_ = lean_ctor_get(v_mctx_698_, 9);
v_instanceTypedMVars_716_ = lean_ctor_get(v_mctx_698_, 10);
v_synthNormMemo_717_ = lean_ctor_get(v_mctx_698_, 11);
v_isSharedCheck_731_ = !lean_is_exclusive(v_mctx_698_);
if (v_isSharedCheck_731_ == 0)
{
v___x_719_ = v_mctx_698_;
v_isShared_720_ = v_isSharedCheck_731_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_synthNormMemo_717_);
lean_inc(v_instanceTypedMVars_716_);
lean_inc(v_dAssignment_715_);
lean_inc(v_eAssignment_714_);
lean_inc(v_lAssignment_713_);
lean_inc(v_userNames_712_);
lean_inc(v_decls_711_);
lean_inc(v_lDecls_710_);
lean_inc(v_mvarCounter_709_);
lean_inc(v_lmvarCounter_708_);
lean_inc(v_levelAssignDepth_707_);
lean_inc(v_depth_706_);
lean_dec(v_mctx_698_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_731_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_721_ = lean_box(0);
v___x_722_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(v_eAssignment_714_, v_mvarId_693_, v_val_694_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 8, v___x_722_);
v___x_724_ = v___x_719_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_depth_706_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_levelAssignDepth_707_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_lmvarCounter_708_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_mvarCounter_709_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v_lDecls_710_);
lean_ctor_set(v_reuseFailAlloc_730_, 5, v_decls_711_);
lean_ctor_set(v_reuseFailAlloc_730_, 6, v_userNames_712_);
lean_ctor_set(v_reuseFailAlloc_730_, 7, v_lAssignment_713_);
lean_ctor_set(v_reuseFailAlloc_730_, 8, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_730_, 9, v_dAssignment_715_);
lean_ctor_set(v_reuseFailAlloc_730_, 10, v_instanceTypedMVars_716_);
lean_ctor_set(v_reuseFailAlloc_730_, 11, v_synthNormMemo_717_);
v___x_724_ = v_reuseFailAlloc_730_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_726_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_724_);
v___x_726_ = v___x_704_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_cache_699_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v_zetaDeltaFVarIds_700_);
lean_ctor_set(v_reuseFailAlloc_729_, 3, v_postponed_701_);
lean_ctor_set(v_reuseFailAlloc_729_, 4, v_diag_702_);
v___x_726_ = v_reuseFailAlloc_729_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_st_ref_put(v___y_695_, v___x_726_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_721_);
return v___x_728_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_693_ = stack[0].m_obj;
lean_object* v_val_694_ = stack[1].m_obj;
lean_object* v___y_695_ = stack[2].m_obj;
lean_object* v_res_733_;
v_res_733_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(v_mvarId_693_, v_val_694_, v___y_695_);
stack->m_obj
 = v_res_733_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg___boxed(lean_object* v_mvarId_734_, lean_object* v_val_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(v_mvarId_734_, v_val_735_, v___y_736_);
lean_dec(v___y_736_);
return v_res_738_;
}
}
lean_object* l_Lean_MVarId_replaceTargetDefEqFast___lam__0(lean_object* v_goal_739_, lean_object* v_targetNew_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_746_; 
lean_inc(v_goal_739_);
v___x_746_ = l_Lean_MVarId_getTag(v_goal_739_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_748_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_740_, v_a_747_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_758_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc_n(v_a_749_, 2);
lean_dec_ref_known(v___x_748_, 1);
v___x_750_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(v_goal_739_, v_a_749_, v___y_742_);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v___x_750_, 0);
lean_dec(v_unused_759_);
v___x_752_ = v___x_750_;
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
else
{
lean_dec(v___x_750_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_754_ = l_Lean_Expr_mvarId_x21(v_a_749_);
lean_dec(v_a_749_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_754_);
v___x_756_ = v___x_752_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec(v_goal_739_);
v_a_760_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_748_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_748_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec_ref(v_targetNew_740_);
lean_dec(v_goal_739_);
v_a_768_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_746_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_746_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_replaceTargetDefEqFast___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_739_ = stack[0].m_obj;
lean_object* v_targetNew_740_ = stack[1].m_obj;
lean_object* v___y_741_ = stack[2].m_obj;
lean_object* v___y_742_ = stack[3].m_obj;
lean_object* v___y_743_ = stack[4].m_obj;
lean_object* v___y_744_ = stack[5].m_obj;
lean_object* v_res_776_;
v_res_776_ = l_Lean_MVarId_replaceTargetDefEqFast___lam__0(v_goal_739_, v_targetNew_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
stack->m_obj
 = v_res_776_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast___lam__0___boxed(lean_object* v_goal_777_, lean_object* v_targetNew_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_MVarId_replaceTargetDefEqFast___lam__0(v_goal_777_, v_targetNew_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
return v_res_784_;
}
}
lean_object* l_Lean_MVarId_replaceTargetDefEqFast(lean_object* v_goal_785_, lean_object* v_targetNew_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v___f_792_; lean_object* v___x_793_; 
lean_inc(v_goal_785_);
v___f_792_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetDefEqFast___lam__0___boxed), 7, 2);
lean_closure_set(v___f_792_, 0, v_goal_785_);
lean_closure_set(v___f_792_, 1, v_targetNew_786_);
v___x_793_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(v_goal_785_, v___f_792_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
return v___x_793_;
}
}
LEAN_EXPORT void l_Lean_MVarId_replaceTargetDefEqFast_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_785_ = stack[0].m_obj;
lean_object* v_targetNew_786_ = stack[1].m_obj;
lean_object* v_a_787_ = stack[2].m_obj;
lean_object* v_a_788_ = stack[3].m_obj;
lean_object* v_a_789_ = stack[4].m_obj;
lean_object* v_a_790_ = stack[5].m_obj;
lean_object* v_res_794_;
v_res_794_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_785_, v_targetNew_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
stack->m_obj
 = v_res_794_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast___boxed(lean_object* v_goal_795_, lean_object* v_targetNew_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_795_, v_targetNew_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
return v_res_802_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0(lean_object* v_mvarId_803_, lean_object* v_val_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(v_mvarId_803_, v_val_804_, v___y_806_);
return v___x_810_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_803_ = stack[0].m_obj;
lean_object* v_val_804_ = stack[1].m_obj;
lean_object* v___y_805_ = stack[2].m_obj;
lean_object* v___y_806_ = stack[3].m_obj;
lean_object* v___y_807_ = stack[4].m_obj;
lean_object* v___y_808_ = stack[5].m_obj;
lean_object* v_res_811_;
v_res_811_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0(v_mvarId_803_, v_val_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
stack->m_obj
 = v_res_811_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___boxed(lean_object* v_mvarId_812_, lean_object* v_val_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0(v_mvarId_812_, v_val_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0(lean_object* v_00_u03b2_820_, lean_object* v_x_821_, lean_object* v_x_822_, lean_object* v_x_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(v_x_821_, v_x_822_, v_x_823_);
return v___x_824_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_825_, lean_object* v_x_826_, size_t v_x_827_, size_t v_x_828_, lean_object* v_x_829_, lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_x_826_, v_x_827_, v_x_828_, v_x_829_, v_x_830_);
return v___x_831_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_826_ = stack[1].m_obj;
size_t v_x_827_ = stack[2].m_num;
size_t v_x_828_ = stack[3].m_num;
lean_object* v_x_829_ = stack[4].m_obj;
lean_object* v_x_830_ = stack[5].m_obj;
lean_object* v_res_832_;
v_res_832_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2(lean_box(0), v_x_826_, v_x_827_, v_x_828_, v_x_829_, v_x_830_);
stack->m_obj
 = v_res_832_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_833_, lean_object* v_x_834_, lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_){
_start:
{
size_t v_x_1696__boxed_839_; size_t v_x_1697__boxed_840_; lean_object* v_res_841_; 
v_x_1696__boxed_839_ = lean_unbox_usize(v_x_835_);
lean_dec(v_x_835_);
v_x_1697__boxed_840_ = lean_unbox_usize(v_x_836_);
lean_dec(v_x_836_);
v_res_841_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2(v_00_u03b2_833_, v_x_834_, v_x_1696__boxed_839_, v_x_1697__boxed_840_, v_x_837_, v_x_838_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_842_, lean_object* v_n_843_, lean_object* v_k_844_, lean_object* v_v_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3___redArg(v_n_843_, v_k_844_, v_v_845_);
return v___x_846_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_847_, size_t v_depth_848_, lean_object* v_keys_849_, lean_object* v_vals_850_, lean_object* v_heq_851_, lean_object* v_i_852_, lean_object* v_entries_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_848_, v_keys_849_, v_vals_850_, v_i_852_, v_entries_853_);
return v___x_854_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_depth_848_ = stack[1].m_num;
lean_object* v_keys_849_ = stack[2].m_obj;
lean_object* v_vals_850_ = stack[3].m_obj;
lean_object* v_i_852_ = stack[5].m_obj;
lean_object* v_entries_853_ = stack[6].m_obj;
lean_object* v_res_855_;
v_res_855_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4(lean_box(0), v_depth_848_, v_keys_849_, v_vals_850_, lean_box(0), v_i_852_, v_entries_853_);
stack->m_obj
 = v_res_855_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_856_, lean_object* v_depth_857_, lean_object* v_keys_858_, lean_object* v_vals_859_, lean_object* v_heq_860_, lean_object* v_i_861_, lean_object* v_entries_862_){
_start:
{
size_t v_depth_boxed_863_; lean_object* v_res_864_; 
v_depth_boxed_863_ = lean_unbox_usize(v_depth_857_);
lean_dec(v_depth_857_);
v_res_864_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_856_, v_depth_boxed_863_, v_keys_858_, v_vals_859_, v_heq_860_, v_i_861_, v_entries_862_);
lean_dec_ref(v_vals_859_);
lean_dec_ref(v_keys_858_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_865_, lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_866_, v_x_867_, v_x_868_, v_x_869_);
return v___x_870_;
}
}
lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon(lean_object* v_rule_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_expr_879_; lean_object* v_pattern_880_; lean_object* v_resultPos_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_905_; 
v_expr_879_ = lean_ctor_get(v_rule_871_, 0);
v_pattern_880_ = lean_ctor_get(v_rule_871_, 1);
v_resultPos_881_ = lean_ctor_get(v_rule_871_, 2);
v_isSharedCheck_905_ = !lean_is_exclusive(v_rule_871_);
if (v_isSharedCheck_905_ == 0)
{
v___x_883_ = v_rule_871_;
v_isShared_884_ = v_isSharedCheck_905_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_resultPos_881_);
lean_inc(v_pattern_880_);
lean_inc(v_expr_879_);
lean_dec(v_rule_871_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_905_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_Meta_Sym_Pattern_shareCommon(v_pattern_880_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_896_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_896_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_896_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_896_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 1, v_a_886_);
v___x_891_ = v___x_883_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_expr_879_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_a_886_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_resultPos_881_);
v___x_891_ = v_reuseFailAlloc_895_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_893_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_891_);
v___x_893_ = v___x_888_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_del_object(v___x_883_);
lean_dec(v_resultPos_881_);
lean_dec_ref(v_expr_879_);
v_a_897_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_885_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_885_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_BackwardRule_shareCommon_0interp(lean_interpreter_value* stack)
{
lean_object* v_rule_871_ = stack[0].m_obj;
lean_object* v_a_872_ = stack[1].m_obj;
lean_object* v_a_873_ = stack[2].m_obj;
lean_object* v_a_874_ = stack[3].m_obj;
lean_object* v_a_875_ = stack[4].m_obj;
lean_object* v_a_876_ = stack[5].m_obj;
lean_object* v_a_877_ = stack[6].m_obj;
lean_object* v_res_906_;
v_res_906_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_rule_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
stack->m_obj
 = v_res_906_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon___boxed(lean_object* v_rule_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_rule_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
return v_res_915_;
}
}
lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(lean_object* v___y_916_, lean_object* v_mctx_917_, lean_object* v_cache_918_, lean_object* v_a_x3f_919_){
_start:
{
lean_object* v___x_921_; lean_object* v_zetaDeltaFVarIds_922_; lean_object* v_postponed_923_; lean_object* v_diag_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_934_; 
v___x_921_ = lean_st_ref_take(v___y_916_);
v_zetaDeltaFVarIds_922_ = lean_ctor_get(v___x_921_, 2);
v_postponed_923_ = lean_ctor_get(v___x_921_, 3);
v_diag_924_ = lean_ctor_get(v___x_921_, 4);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; lean_object* v_unused_936_; 
v_unused_935_ = lean_ctor_get(v___x_921_, 1);
lean_dec(v_unused_935_);
v_unused_936_ = lean_ctor_get(v___x_921_, 0);
lean_dec(v_unused_936_);
v___x_926_ = v___x_921_;
v_isShared_927_ = v_isSharedCheck_934_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_diag_924_);
lean_inc(v_postponed_923_);
lean_inc(v_zetaDeltaFVarIds_922_);
lean_dec(v___x_921_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_934_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_928_ = lean_box(0);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v_cache_918_);
lean_ctor_set(v___x_926_, 0, v_mctx_917_);
v___x_930_ = v___x_926_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_mctx_917_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_cache_918_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_zetaDeltaFVarIds_922_);
lean_ctor_set(v_reuseFailAlloc_933_, 3, v_postponed_923_);
lean_ctor_set(v_reuseFailAlloc_933_, 4, v_diag_924_);
v___x_930_ = v_reuseFailAlloc_933_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lean_st_ref_put(v___y_916_, v___x_930_);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_928_);
return v___x_932_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_916_ = stack[0].m_obj;
lean_object* v_mctx_917_ = stack[1].m_obj;
lean_object* v_cache_918_ = stack[2].m_obj;
lean_object* v_a_x3f_919_ = stack[3].m_obj;
lean_object* v_res_937_;
v_res_937_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_916_, v_mctx_917_, v_cache_918_, v_a_x3f_919_);
stack->m_obj
 = v_res_937_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0___boxed(lean_object* v___y_938_, lean_object* v_mctx_939_, lean_object* v_cache_940_, lean_object* v_a_x3f_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_938_, v_mctx_939_, v_cache_940_, v_a_x3f_941_);
lean_dec(v_a_x3f_941_);
lean_dec(v___y_938_);
return v_res_943_;
}
}
lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(lean_object* v_x_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; lean_object* v_mctx_958_; lean_object* v___x_959_; lean_object* v_cache_960_; lean_object* v___x_961_; 
v___x_957_ = lean_st_ref_get(v___y_953_);
v_mctx_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc_ref(v_mctx_958_);
lean_dec(v___x_957_);
v___x_959_ = lean_st_ref_get(v___y_953_);
v_cache_960_ = lean_ctor_get(v___x_959_, 1);
lean_inc_ref(v_cache_960_);
lean_dec(v___x_959_);
lean_inc(v___y_955_);
lean_inc_ref(v___y_954_);
lean_inc(v___y_953_);
lean_inc_ref(v___y_952_);
lean_inc(v___y_951_);
lean_inc_ref(v___y_950_);
lean_inc(v___y_949_);
lean_inc_ref(v___y_948_);
lean_inc(v___y_947_);
lean_inc(v___y_946_);
lean_inc_ref(v___y_945_);
v___x_961_ = lean_apply_12(v_x_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, lean_box(0));
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_978_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_978_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_978_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_978_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
lean_inc(v_a_962_);
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 1);
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_977_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
v___x_968_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_953_, v_mctx_958_, v_cache_960_, v___x_967_);
lean_dec_ref(v___x_967_);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; 
v_unused_976_ = lean_ctor_get(v___x_968_, 0);
lean_dec(v_unused_976_);
v___x_970_ = v___x_968_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_dec(v___x_968_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v_a_962_);
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_962_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
else
{
lean_object* v_a_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
v_a_979_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_961_, 1);
v___x_980_ = lean_box(0);
v___x_981_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_953_, v_mctx_958_, v_cache_960_, v___x_980_);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; 
v_unused_989_ = lean_ctor_get(v___x_981_, 0);
lean_dec(v_unused_989_);
v___x_983_ = v___x_981_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_dec(v___x_981_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 1);
lean_ctor_set(v___x_983_, 0, v_a_979_);
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_979_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_944_ = stack[0].m_obj;
lean_object* v___y_945_ = stack[1].m_obj;
lean_object* v___y_946_ = stack[2].m_obj;
lean_object* v___y_947_ = stack[3].m_obj;
lean_object* v___y_948_ = stack[4].m_obj;
lean_object* v___y_949_ = stack[5].m_obj;
lean_object* v___y_950_ = stack[6].m_obj;
lean_object* v___y_951_ = stack[7].m_obj;
lean_object* v___y_952_ = stack[8].m_obj;
lean_object* v___y_953_ = stack[9].m_obj;
lean_object* v___y_954_ = stack[10].m_obj;
lean_object* v___y_955_ = stack[11].m_obj;
lean_object* v_res_990_;
v_res_990_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
stack->m_obj
 = v_res_990_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___boxed(lean_object* v_x_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
return v_res_1004_;
}
}
lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(lean_object* v_00_u03b1_1005_, lean_object* v_x_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
return v___x_1019_;
}
}
LEAN_EXPORT void l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1006_ = stack[1].m_obj;
lean_object* v___y_1007_ = stack[2].m_obj;
lean_object* v___y_1008_ = stack[3].m_obj;
lean_object* v___y_1009_ = stack[4].m_obj;
lean_object* v___y_1010_ = stack[5].m_obj;
lean_object* v___y_1011_ = stack[6].m_obj;
lean_object* v___y_1012_ = stack[7].m_obj;
lean_object* v___y_1013_ = stack[8].m_obj;
lean_object* v___y_1014_ = stack[9].m_obj;
lean_object* v___y_1015_ = stack[10].m_obj;
lean_object* v___y_1016_ = stack[11].m_obj;
lean_object* v___y_1017_ = stack[12].m_obj;
lean_object* v_res_1020_;
v_res_1020_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(lean_box(0), v_x_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
stack->m_obj
 = v_res_1020_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___boxed(lean_object* v_00_u03b1_1021_, lean_object* v_x_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(v_00_u03b1_1021_, v_x_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
return v_res_1035_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(lean_object* v_a_1036_, lean_object* v___x_1037_, lean_object* v_rule_1038_, uint8_t v___x_1039_, uint8_t v_debug_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1036_, v___x_1037_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1053_, 1);
v___x_1055_ = l_Lean_Expr_mvarId_x21(v_a_1054_);
lean_dec(v_a_1054_);
v___x_1056_ = l_Lean_Meta_Sym_BackwardRule_apply(v___x_1055_, v_rule_1038_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1069_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1069_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1069_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
if (lean_obj_tag(v_a_1057_) == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1061_ = lean_box(v___x_1039_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v___x_1061_);
v___x_1063_ = v___x_1059_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
lean_dec_ref_known(v_a_1057_, 1);
v___x_1065_ = lean_box(v_debug_1040_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v___x_1065_);
v___x_1067_ = v___x_1059_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
v_a_1070_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1056_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1056_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec_ref(v_rule_1038_);
v_a_1078_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1053_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1053_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1036_ = stack[0].m_obj;
lean_object* v___x_1037_ = stack[1].m_obj;
lean_object* v_rule_1038_ = stack[2].m_obj;
uint8_t v___x_1039_ = stack[3].m_num;
uint8_t v_debug_1040_ = stack[4].m_num;
lean_object* v___y_1041_ = stack[5].m_obj;
lean_object* v___y_1042_ = stack[6].m_obj;
lean_object* v___y_1043_ = stack[7].m_obj;
lean_object* v___y_1044_ = stack[8].m_obj;
lean_object* v___y_1045_ = stack[9].m_obj;
lean_object* v___y_1046_ = stack[10].m_obj;
lean_object* v___y_1047_ = stack[11].m_obj;
lean_object* v___y_1048_ = stack[12].m_obj;
lean_object* v___y_1049_ = stack[13].m_obj;
lean_object* v___y_1050_ = stack[14].m_obj;
lean_object* v___y_1051_ = stack[15].m_obj;
lean_object* v_res_1086_;
v_res_1086_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(v_a_1036_, v___x_1037_, v_rule_1038_, v___x_1039_, v_debug_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
stack->m_obj
 = v_res_1086_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed(lean_object** _args){
lean_object* v_a_1087_ = _args[0];
lean_object* v___x_1088_ = _args[1];
lean_object* v_rule_1089_ = _args[2];
lean_object* v___x_1090_ = _args[3];
lean_object* v_debug_1091_ = _args[4];
lean_object* v___y_1092_ = _args[5];
lean_object* v___y_1093_ = _args[6];
lean_object* v___y_1094_ = _args[7];
lean_object* v___y_1095_ = _args[8];
lean_object* v___y_1096_ = _args[9];
lean_object* v___y_1097_ = _args[10];
lean_object* v___y_1098_ = _args[11];
lean_object* v___y_1099_ = _args[12];
lean_object* v___y_1100_ = _args[13];
lean_object* v___y_1101_ = _args[14];
lean_object* v___y_1102_ = _args[15];
lean_object* v___y_1103_ = _args[16];
_start:
{
uint8_t v___x_29643__boxed_1104_; uint8_t v_debug_boxed_1105_; lean_object* v_res_1106_; 
v___x_29643__boxed_1104_ = lean_unbox(v___x_1090_);
v_debug_boxed_1105_ = lean_unbox(v_debug_1091_);
v_res_1106_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(v_a_1087_, v___x_1088_, v_rule_1089_, v___x_29643__boxed_1104_, v_debug_boxed_1105_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1106_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(lean_object* v_msg_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_ref_1113_; lean_object* v___x_1114_; lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1123_; 
v_ref_1113_ = lean_ctor_get(v___y_1110_, 2);
v___x_1114_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f_spec__4_spec__4(v_msg_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1123_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1123_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1121_; 
lean_inc(v_ref_1113_);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v_ref_1113_);
lean_ctor_set(v___x_1119_, 1, v_a_1115_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set_tag(v___x_1117_, 1);
lean_ctor_set(v___x_1117_, 0, v___x_1119_);
v___x_1121_ = v___x_1117_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1107_ = stack[0].m_obj;
lean_object* v___y_1108_ = stack[1].m_obj;
lean_object* v___y_1109_ = stack[2].m_obj;
lean_object* v___y_1110_ = stack[3].m_obj;
lean_object* v___y_1111_ = stack[4].m_obj;
lean_object* v_res_1124_;
v_res_1124_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
stack->m_obj
 = v_res_1124_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg___boxed(lean_object* v_msg_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1131_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0));
v___x_1134_ = l_Lean_stringToMessageData(v___x_1133_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2));
v___x_1137_ = l_Lean_stringToMessageData(v___x_1136_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4));
v___x_1140_ = l_Lean_stringToMessageData(v___x_1139_);
return v___x_1140_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6));
v___x_1143_ = l_Lean_stringToMessageData(v___x_1142_);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8));
v___x_1146_ = l_Lean_stringToMessageData(v___x_1145_);
return v___x_1146_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object* v_rule_1147_, lean_object* v_goal_1148_, lean_object* v_ruleDesc_x3f_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___x_1162_; 
lean_inc_ref(v_rule_1147_);
lean_inc(v_goal_1148_);
v___x_1162_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_1148_, v_rule_1147_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
if (lean_obj_tag(v_a_1163_) == 0)
{
uint8_t v_debug_1164_; 
v_debug_1164_ = lean_ctor_get_uint8(v_a_1150_, sizeof(void*)*5 + 2);
if (v_debug_1164_ == 0)
{
lean_dec(v_ruleDesc_x3f_1149_);
lean_dec(v_goal_1148_);
lean_dec_ref(v_rule_1147_);
return v___x_1162_;
}
else
{
lean_object* v___x_1165_; 
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1165_ = l_Lean_MVarId_getType(v_goal_1148_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1167_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc_n(v_a_1166_, 2);
lean_dec_ref_known(v___x_1165_, 1);
v___x_1167_ = l_Lean_Meta_Sym_unfoldReducible(v_a_1166_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1230_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1230_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1230_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
uint8_t v___x_1172_; 
v___x_1172_ = lean_expr_eqv(v_a_1168_, v_a_1166_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___f_1176_; lean_object* v___x_1177_; 
lean_del_object(v___x_1170_);
v___x_1173_ = lean_box(0);
v___x_1174_ = lean_box(v___x_1172_);
v___x_1175_ = lean_box(v_debug_1164_);
lean_inc_ref(v_rule_1147_);
lean_inc(v_a_1168_);
v___f_1176_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed), 17, 5);
lean_closure_set(v___f_1176_, 0, v_a_1168_);
lean_closure_set(v___f_1176_, 1, v___x_1173_);
lean_closure_set(v___f_1176_, 2, v_rule_1147_);
lean_closure_set(v___f_1176_, 3, v___x_1174_);
lean_closure_set(v___f_1176_, 4, v___x_1175_);
v___x_1177_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v___f_1176_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1218_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1218_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1218_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___y_1183_; uint8_t v___x_1205_; 
v___x_1205_ = lean_unbox(v_a_1178_);
lean_dec(v_a_1178_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1207_; 
lean_dec(v_a_1168_);
lean_dec(v_a_1166_);
lean_dec(v_ruleDesc_x3f_1149_);
lean_dec_ref(v_rule_1147_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v_a_1163_);
v___x_1207_ = v___x_1180_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1163_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
else
{
lean_del_object(v___x_1180_);
if (lean_obj_tag(v_ruleDesc_x3f_1149_) == 0)
{
lean_object* v_expr_1209_; lean_object* v___x_1210_; 
v_expr_1209_ = lean_ctor_get(v_rule_1147_, 0);
lean_inc_ref(v_expr_1209_);
lean_dec_ref(v_rule_1147_);
v___x_1210_ = l_Lean_Expr_getAppFn(v_expr_1209_);
lean_dec_ref(v_expr_1209_);
if (lean_obj_tag(v___x_1210_) == 4)
{
lean_object* v_declName_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_declName_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_declName_1211_);
lean_dec_ref_known(v___x_1210_, 2);
v___x_1212_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3, &l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_synthInstanceOpt_x3f___lam__0___closed__3);
v___x_1213_ = l_Lean_MessageData_ofConstName(v_declName_1211_, v___x_1172_);
v___x_1214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1212_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v___x_1212_);
v___y_1183_ = v___x_1215_;
goto v___jp_1182_;
}
else
{
lean_object* v___x_1216_; 
lean_dec_ref(v___x_1210_);
v___x_1216_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9);
v___y_1183_ = v___x_1216_;
goto v___jp_1182_;
}
}
else
{
lean_object* v_val_1217_; 
lean_dec_ref(v_rule_1147_);
v_val_1217_ = lean_ctor_get(v_ruleDesc_x3f_1149_, 0);
lean_inc(v_val_1217_);
lean_dec_ref_known(v_ruleDesc_x3f_1149_, 1);
v___y_1183_ = v_val_1217_;
goto v___jp_1182_;
}
}
v___jp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
v___x_1184_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1);
v___x_1185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v___y_1183_);
v___x_1186_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3);
v___x_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = l_Lean_indentExpr(v_a_1166_);
v___x_1189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5);
v___x_1191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = l_Lean_indentExpr(v_a_1168_);
v___x_1193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7);
v___x_1195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_1195_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1196_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1196_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec(v_a_1168_);
lean_dec(v_a_1166_);
lean_dec(v_ruleDesc_x3f_1149_);
lean_dec_ref(v_rule_1147_);
v_a_1219_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1177_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1177_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
else
{
lean_object* v___x_1228_; 
lean_dec(v_a_1168_);
lean_dec(v_a_1166_);
lean_dec(v_ruleDesc_x3f_1149_);
lean_dec_ref(v_rule_1147_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v_a_1163_);
v___x_1228_ = v___x_1170_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1163_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_a_1166_);
lean_dec(v_ruleDesc_x3f_1149_);
lean_dec_ref(v_rule_1147_);
v_a_1231_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1167_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1167_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec(v_ruleDesc_x3f_1149_);
lean_dec_ref(v_rule_1147_);
v_a_1239_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1165_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1165_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
else
{
lean_dec(v_ruleDesc_x3f_1149_);
lean_dec(v_goal_1148_);
lean_dec_ref(v_rule_1147_);
return v___x_1162_;
}
}
else
{
lean_dec(v_ruleDesc_x3f_1149_);
lean_dec(v_goal_1148_);
lean_dec_ref(v_rule_1147_);
return v___x_1162_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_0interp(lean_interpreter_value* stack)
{
lean_object* v_rule_1147_ = stack[0].m_obj;
lean_object* v_goal_1148_ = stack[1].m_obj;
lean_object* v_ruleDesc_x3f_1149_ = stack[2].m_obj;
lean_object* v_a_1150_ = stack[3].m_obj;
lean_object* v_a_1151_ = stack[4].m_obj;
lean_object* v_a_1152_ = stack[5].m_obj;
lean_object* v_a_1153_ = stack[6].m_obj;
lean_object* v_a_1154_ = stack[7].m_obj;
lean_object* v_a_1155_ = stack[8].m_obj;
lean_object* v_a_1156_ = stack[9].m_obj;
lean_object* v_a_1157_ = stack[10].m_obj;
lean_object* v_a_1158_ = stack[11].m_obj;
lean_object* v_a_1159_ = stack[12].m_obj;
lean_object* v_a_1160_ = stack[13].m_obj;
lean_object* v_res_1247_;
v_res_1247_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_1147_, v_goal_1148_, v_ruleDesc_x3f_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
stack->m_obj
 = v_res_1247_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___boxed(lean_object* v_rule_1248_, lean_object* v_goal_1249_, lean_object* v_ruleDesc_x3f_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_1248_, v_goal_1249_, v_ruleDesc_x3f_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
lean_dec(v_a_1253_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
return v_res_1263_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(lean_object* v_00_u03b1_1264_, lean_object* v_msg_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_1265_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
return v___x_1278_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1265_ = stack[1].m_obj;
lean_object* v___y_1266_ = stack[2].m_obj;
lean_object* v___y_1267_ = stack[3].m_obj;
lean_object* v___y_1268_ = stack[4].m_obj;
lean_object* v___y_1269_ = stack[5].m_obj;
lean_object* v___y_1270_ = stack[6].m_obj;
lean_object* v___y_1271_ = stack[7].m_obj;
lean_object* v___y_1272_ = stack[8].m_obj;
lean_object* v___y_1273_ = stack[9].m_obj;
lean_object* v___y_1274_ = stack[10].m_obj;
lean_object* v___y_1275_ = stack[11].m_obj;
lean_object* v___y_1276_ = stack[12].m_obj;
lean_object* v_res_1279_;
v_res_1279_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(lean_box(0), v_msg_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
stack->m_obj
 = v_res_1279_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___boxed(lean_object* v_00_u03b1_1280_, lean_object* v_msg_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(v_00_u03b1_1280_, v_msg_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
return v_res_1294_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(lean_object* v_goal_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
uint8_t v_internalize_1307_; 
v_internalize_1307_ = lean_ctor_get_uint8(v_a_1296_, sizeof(void*)*5 + 3);
if (v_internalize_1307_ == 0)
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1308_, 0, v_goal_1295_);
return v___x_1308_;
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_box(0);
v___x_1310_ = l_Lean_Meta_Grind_processHypotheses(v_goal_1295_, v___x_1309_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
return v___x_1310_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1295_ = stack[0].m_obj;
lean_object* v_a_1296_ = stack[1].m_obj;
lean_object* v_a_1297_ = stack[2].m_obj;
lean_object* v_a_1298_ = stack[3].m_obj;
lean_object* v_a_1299_ = stack[4].m_obj;
lean_object* v_a_1300_ = stack[5].m_obj;
lean_object* v_a_1301_ = stack[6].m_obj;
lean_object* v_a_1302_ = stack[7].m_obj;
lean_object* v_a_1303_ = stack[8].m_obj;
lean_object* v_a_1304_ = stack[9].m_obj;
lean_object* v_a_1305_ = stack[10].m_obj;
lean_object* v_res_1311_;
v_res_1311_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
stack->m_obj
 = v_res_1311_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg___boxed(lean_object* v_goal_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
return v_res_1324_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses(lean_object* v_goal_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_1325_, v_a_1326_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
return v___x_1338_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_processHypotheses_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1325_ = stack[0].m_obj;
lean_object* v_a_1326_ = stack[1].m_obj;
lean_object* v_a_1327_ = stack[2].m_obj;
lean_object* v_a_1328_ = stack[3].m_obj;
lean_object* v_a_1329_ = stack[4].m_obj;
lean_object* v_a_1330_ = stack[5].m_obj;
lean_object* v_a_1331_ = stack[6].m_obj;
lean_object* v_a_1332_ = stack[7].m_obj;
lean_object* v_a_1333_ = stack[8].m_obj;
lean_object* v_a_1334_ = stack[9].m_obj;
lean_object* v_a_1335_ = stack[10].m_obj;
lean_object* v_a_1336_ = stack[11].m_obj;
lean_object* v_res_1339_;
v_res_1339_ = l_Lean_Elab_Tactic_VCGen_processHypotheses(v_goal_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
stack->m_obj
 = v_res_1339_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___boxed(lean_object* v_goal_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_Elab_Tactic_VCGen_processHypotheses(v_goal_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_a_1343_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
return v_res_1353_;
}
}
uint8_t l_Lean_Elab_Tactic_VCGen_isProgramName(lean_object* v_n_1354_){
_start:
{
uint8_t v___x_1355_; 
v___x_1355_ = l_Lean_Name_hasMacroScopes(v_n_1354_);
if (v___x_1355_ == 0)
{
uint8_t v___x_1356_; 
v___x_1356_ = l_Lean_Name_isImplementationDetail(v_n_1354_);
if (v___x_1356_ == 0)
{
uint8_t v___x_1357_; 
v___x_1357_ = 1;
return v___x_1357_;
}
else
{
return v___x_1355_;
}
}
else
{
uint8_t v___x_1358_; 
v___x_1358_ = 0;
return v___x_1358_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_isProgramName_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1354_ = stack[0].m_obj;
uint8_t v_res_1359_;
v_res_1359_ = l_Lean_Elab_Tactic_VCGen_isProgramName(v_n_1354_);
stack->m_num = v_res_1359_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_isProgramName___boxed(lean_object* v_n_1360_){
_start:
{
uint8_t v_res_1361_; lean_object* v_r_1362_; 
v_res_1361_ = l_Lean_Elab_Tactic_VCGen_isProgramName(v_n_1360_);
lean_dec(v_n_1360_);
v_r_1362_ = lean_box(v_res_1361_);
return v_r_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_numBindersToIntro(lean_object* v_x_1366_){
_start:
{
switch(lean_obj_tag(v_x_1366_))
{
case 7:
{
lean_object* v_binderType_1367_; lean_object* v_body_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v_binderType_1367_ = lean_ctor_get(v_x_1366_, 1);
v_body_1368_ = lean_ctor_get(v_x_1366_, 2);
v___x_1369_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_numBindersToIntro___closed__1));
v___x_1370_ = l_Lean_Expr_isAppOf(v_binderType_1367_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = l_Lean_Elab_Tactic_VCGen_numBindersToIntro(v_body_1368_);
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = lean_nat_add(v___x_1371_, v___x_1372_);
lean_dec(v___x_1371_);
return v___x_1373_;
}
else
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_unsigned_to_nat(0u);
return v___x_1374_;
}
}
case 8:
{
lean_object* v_body_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v_body_1375_ = lean_ctor_get(v_x_1366_, 3);
v___x_1376_ = l_Lean_Elab_Tactic_VCGen_numBindersToIntro(v_body_1375_);
v___x_1377_ = lean_unsigned_to_nat(1u);
v___x_1378_ = lean_nat_add(v___x_1376_, v___x_1377_);
lean_dec(v___x_1376_);
return v___x_1378_;
}
default: 
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_unsigned_to_nat(0u);
return v___x_1379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_numBindersToIntro___boxed(lean_object* v_x_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_Elab_Tactic_VCGen_numBindersToIntro(v_x_1380_);
lean_dec_ref(v_x_1380_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_introsHygienicN_collectBinders(lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v_zero_1385_; uint8_t v_isZero_1386_; 
v_zero_1385_ = lean_unsigned_to_nat(0u);
v_isZero_1386_ = lean_nat_dec_eq(v_a_1382_, v_zero_1385_);
if (v_isZero_1386_ == 1)
{
lean_dec_ref(v_a_1383_);
lean_dec(v_a_1382_);
return v_a_1384_;
}
else
{
lean_object* v_one_1387_; lean_object* v_n_1388_; 
v_one_1387_ = lean_unsigned_to_nat(1u);
v_n_1388_ = lean_nat_sub(v_a_1382_, v_one_1387_);
lean_dec(v_a_1382_);
switch(lean_obj_tag(v_a_1383_))
{
case 7:
{
lean_object* v_binderName_1389_; lean_object* v_body_1390_; lean_object* v___x_1391_; 
v_binderName_1389_ = lean_ctor_get(v_a_1383_, 0);
lean_inc(v_binderName_1389_);
v_body_1390_ = lean_ctor_get(v_a_1383_, 2);
lean_inc_ref(v_body_1390_);
lean_dec_ref_known(v_a_1383_, 3);
v___x_1391_ = lean_array_push(v_a_1384_, v_binderName_1389_);
v_a_1382_ = v_n_1388_;
v_a_1383_ = v_body_1390_;
v_a_1384_ = v___x_1391_;
goto _start;
}
case 8:
{
lean_object* v_declName_1393_; lean_object* v_body_1394_; lean_object* v___x_1395_; 
v_declName_1393_ = lean_ctor_get(v_a_1383_, 0);
lean_inc(v_declName_1393_);
v_body_1394_ = lean_ctor_get(v_a_1383_, 3);
lean_inc_ref(v_body_1394_);
lean_dec_ref_known(v_a_1383_, 4);
v___x_1395_ = lean_array_push(v_a_1384_, v_declName_1393_);
v_a_1382_ = v_n_1388_;
v_a_1383_ = v_body_1394_;
v_a_1384_ = v___x_1395_;
goto _start;
}
default: 
{
lean_dec(v_n_1388_);
lean_dec_ref(v_a_1383_);
return v_a_1384_;
}
}
}
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0(lean_object* v_x_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; 
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
lean_inc(v___y_1400_);
lean_inc(v___y_1399_);
lean_inc_ref(v___y_1398_);
v___x_1410_ = lean_apply_12(v_x_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, lean_box(0));
return v___x_1410_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1397_ = stack[0].m_obj;
lean_object* v___y_1398_ = stack[1].m_obj;
lean_object* v___y_1399_ = stack[2].m_obj;
lean_object* v___y_1400_ = stack[3].m_obj;
lean_object* v___y_1401_ = stack[4].m_obj;
lean_object* v___y_1402_ = stack[5].m_obj;
lean_object* v___y_1403_ = stack[6].m_obj;
lean_object* v___y_1404_ = stack[7].m_obj;
lean_object* v___y_1405_ = stack[8].m_obj;
lean_object* v___y_1406_ = stack[9].m_obj;
lean_object* v___y_1407_ = stack[10].m_obj;
lean_object* v___y_1408_ = stack[11].m_obj;
lean_object* v_res_1411_;
v_res_1411_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0(v_x_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
stack->m_obj
 = v_res_1411_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0___boxed(lean_object* v_x_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0(v_x_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1425_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(lean_object* v_mvarId_1426_, lean_object* v_x_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___f_1440_; lean_object* v___x_1441_; 
lean_inc(v___y_1434_);
lean_inc_ref(v___y_1433_);
lean_inc(v___y_1432_);
lean_inc_ref(v___y_1431_);
lean_inc(v___y_1430_);
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1428_);
v___f_1440_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1440_, 0, v_x_1427_);
lean_closure_set(v___f_1440_, 1, v___y_1428_);
lean_closure_set(v___f_1440_, 2, v___y_1429_);
lean_closure_set(v___f_1440_, 3, v___y_1430_);
lean_closure_set(v___f_1440_, 4, v___y_1431_);
lean_closure_set(v___f_1440_, 5, v___y_1432_);
lean_closure_set(v___f_1440_, 6, v___y_1433_);
lean_closure_set(v___f_1440_, 7, v___y_1434_);
v___x_1441_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1426_, v___f_1440_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1441_) == 0)
{
return v___x_1441_;
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1426_ = stack[0].m_obj;
lean_object* v_x_1427_ = stack[1].m_obj;
lean_object* v___y_1428_ = stack[2].m_obj;
lean_object* v___y_1429_ = stack[3].m_obj;
lean_object* v___y_1430_ = stack[4].m_obj;
lean_object* v___y_1431_ = stack[5].m_obj;
lean_object* v___y_1432_ = stack[6].m_obj;
lean_object* v___y_1433_ = stack[7].m_obj;
lean_object* v___y_1434_ = stack[8].m_obj;
lean_object* v___y_1435_ = stack[9].m_obj;
lean_object* v___y_1436_ = stack[10].m_obj;
lean_object* v___y_1437_ = stack[11].m_obj;
lean_object* v___y_1438_ = stack[12].m_obj;
lean_object* v_res_1450_;
v_res_1450_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_mvarId_1426_, v_x_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
stack->m_obj
 = v_res_1450_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg___boxed(lean_object* v_mvarId_1451_, lean_object* v_x_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_mvarId_1451_, v_x_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
return v_res_1465_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1(lean_object* v_00_u03b1_1466_, lean_object* v_mvarId_1467_, lean_object* v_x_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_mvarId_1467_, v_x_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
return v___x_1481_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1467_ = stack[1].m_obj;
lean_object* v_x_1468_ = stack[2].m_obj;
lean_object* v___y_1469_ = stack[3].m_obj;
lean_object* v___y_1470_ = stack[4].m_obj;
lean_object* v___y_1471_ = stack[5].m_obj;
lean_object* v___y_1472_ = stack[6].m_obj;
lean_object* v___y_1473_ = stack[7].m_obj;
lean_object* v___y_1474_ = stack[8].m_obj;
lean_object* v___y_1475_ = stack[9].m_obj;
lean_object* v___y_1476_ = stack[10].m_obj;
lean_object* v___y_1477_ = stack[11].m_obj;
lean_object* v___y_1478_ = stack[12].m_obj;
lean_object* v___y_1479_ = stack[13].m_obj;
lean_object* v_res_1482_;
v_res_1482_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1(lean_box(0), v_mvarId_1467_, v_x_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
stack->m_obj
 = v_res_1482_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___boxed(lean_object* v_00_u03b1_1483_, lean_object* v_mvarId_1484_, lean_object* v_x_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1(v_00_u03b1_1483_, v_mvarId_1484_, v_x_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
return v_res_1498_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(lean_object* v_as_1499_, size_t v_sz_1500_, size_t v_i_1501_, lean_object* v_b_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
uint8_t v___x_1507_; 
v___x_1507_ = lean_usize_dec_lt(v_i_1501_, v_sz_1500_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v_b_1502_);
return v___x_1508_;
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1510_; 
v_a_1509_ = lean_array_uget_borrowed(v_as_1499_, v_i_1501_);
lean_inc(v_a_1509_);
v___x_1510_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_a_1509_, v___y_1503_, v___y_1504_, v___y_1505_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1512_; size_t v___x_1513_; size_t v___x_1514_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1510_, 1);
v___x_1512_ = lean_array_push(v_b_1502_, v_a_1511_);
v___x_1513_ = ((size_t)1ULL);
v___x_1514_ = lean_usize_add(v_i_1501_, v___x_1513_);
v_i_1501_ = v___x_1514_;
v_b_1502_ = v___x_1512_;
goto _start;
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_dec_ref(v_b_1502_);
v_a_1516_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1510_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1510_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1499_ = stack[0].m_obj;
size_t v_sz_1500_ = stack[1].m_num;
size_t v_i_1501_ = stack[2].m_num;
lean_object* v_b_1502_ = stack[3].m_obj;
lean_object* v___y_1503_ = stack[4].m_obj;
lean_object* v___y_1504_ = stack[5].m_obj;
lean_object* v___y_1505_ = stack[6].m_obj;
lean_object* v_res_1524_;
v_res_1524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(v_as_1499_, v_sz_1500_, v_i_1501_, v_b_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
stack->m_obj
 = v_res_1524_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg___boxed(lean_object* v_as_1525_, lean_object* v_sz_1526_, lean_object* v_i_1527_, lean_object* v_b_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
size_t v_sz_boxed_1533_; size_t v_i_boxed_1534_; lean_object* v_res_1535_; 
v_sz_boxed_1533_ = lean_unbox_usize(v_sz_1526_);
lean_dec(v_sz_1526_);
v_i_boxed_1534_ = lean_unbox_usize(v_i_1527_);
lean_dec(v_i_1527_);
v_res_1535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(v_as_1525_, v_sz_boxed_1533_, v_i_boxed_1534_, v_b_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec_ref(v_as_1525_);
return v_res_1535_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0(lean_object* v_goal_1538_, lean_object* v_n_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1552_; 
lean_inc(v_goal_1538_);
v___x_1552_ = l_Lean_MVarId_getType(v_goal_1538_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1599_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1599_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1599_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v_names_1558_; lean_object* v_binderNames_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
v___x_1557_ = lean_unsigned_to_nat(0u);
v_names_1558_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___closed__0));
v_binderNames_1559_ = l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_introsHygienicN_collectBinders(v_n_1539_, v_a_1553_, v_names_1558_);
v___x_1560_ = lean_array_get_size(v_binderNames_1559_);
v___x_1561_ = lean_nat_dec_eq(v___x_1560_, v___x_1557_);
if (v___x_1561_ == 0)
{
uint8_t v___x_1562_; size_t v_sz_1563_; size_t v___x_1564_; lean_object* v___x_1565_; 
lean_del_object(v___x_1555_);
v___x_1562_ = 1;
v_sz_1563_ = lean_array_size(v_binderNames_1559_);
v___x_1564_ = ((size_t)0ULL);
v___x_1565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(v_binderNames_1559_, v_sz_1563_, v___x_1564_, v_names_1558_, v___y_1547_, v___y_1549_, v___y_1550_);
lean_dec_ref(v_binderNames_1559_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1567_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
lean_inc(v_goal_1538_);
v___x_1567_ = l_Lean_Meta_Sym_intros(v_goal_1538_, v_a_1566_, v___x_1562_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1579_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1579_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1579_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
if (lean_obj_tag(v_a_1568_) == 1)
{
lean_object* v_mvarId_1572_; lean_object* v___x_1574_; 
lean_dec(v_goal_1538_);
v_mvarId_1572_ = lean_ctor_get(v_a_1568_, 1);
lean_inc(v_mvarId_1572_);
lean_dec_ref_known(v_a_1568_, 2);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v_mvarId_1572_);
v___x_1574_ = v___x_1570_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_mvarId_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
else
{
lean_object* v___x_1577_; 
lean_dec(v_a_1568_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v_goal_1538_);
v___x_1577_ = v___x_1570_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_goal_1538_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v_goal_1538_);
v_a_1580_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1567_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1567_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec(v_goal_1538_);
v_a_1588_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1565_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1565_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_object* v___x_1597_; 
lean_dec_ref(v_binderNames_1559_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v_goal_1538_);
v___x_1597_ = v___x_1555_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_goal_1538_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v_n_1539_);
lean_dec(v_goal_1538_);
v_a_1600_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1552_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1552_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1538_ = stack[0].m_obj;
lean_object* v_n_1539_ = stack[1].m_obj;
lean_object* v___y_1540_ = stack[2].m_obj;
lean_object* v___y_1541_ = stack[3].m_obj;
lean_object* v___y_1542_ = stack[4].m_obj;
lean_object* v___y_1543_ = stack[5].m_obj;
lean_object* v___y_1544_ = stack[6].m_obj;
lean_object* v___y_1545_ = stack[7].m_obj;
lean_object* v___y_1546_ = stack[8].m_obj;
lean_object* v___y_1547_ = stack[9].m_obj;
lean_object* v___y_1548_ = stack[10].m_obj;
lean_object* v___y_1549_ = stack[11].m_obj;
lean_object* v___y_1550_ = stack[12].m_obj;
lean_object* v_res_1608_;
v_res_1608_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0(v_goal_1538_, v_n_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
stack->m_obj
 = v_res_1608_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___boxed(lean_object* v_goal_1609_, lean_object* v_n_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0(v_goal_1609_, v_n_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
return v_res_1623_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN(lean_object* v_goal_1624_, lean_object* v_n_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v___f_1638_; lean_object* v___x_1639_; 
lean_inc(v_goal_1624_);
v___f_1638_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___boxed), 14, 2);
lean_closure_set(v___f_1638_, 0, v_goal_1624_);
lean_closure_set(v___f_1638_, 1, v_n_1625_);
v___x_1639_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_goal_1624_, v___f_1638_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_);
return v___x_1639_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_introsHygienicN_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1624_ = stack[0].m_obj;
lean_object* v_n_1625_ = stack[1].m_obj;
lean_object* v_a_1626_ = stack[2].m_obj;
lean_object* v_a_1627_ = stack[3].m_obj;
lean_object* v_a_1628_ = stack[4].m_obj;
lean_object* v_a_1629_ = stack[5].m_obj;
lean_object* v_a_1630_ = stack[6].m_obj;
lean_object* v_a_1631_ = stack[7].m_obj;
lean_object* v_a_1632_ = stack[8].m_obj;
lean_object* v_a_1633_ = stack[9].m_obj;
lean_object* v_a_1634_ = stack[10].m_obj;
lean_object* v_a_1635_ = stack[11].m_obj;
lean_object* v_a_1636_ = stack[12].m_obj;
lean_object* v_res_1640_;
v_res_1640_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN(v_goal_1624_, v_n_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_);
stack->m_obj
 = v_res_1640_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN___boxed(lean_object* v_goal_1641_, lean_object* v_n_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN(v_goal_1641_, v_n_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
return v_res_1655_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0(lean_object* v_as_1656_, size_t v_sz_1657_, size_t v_i_1658_, lean_object* v_b_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___redArg(v_as_1656_, v_sz_1657_, v_i_1658_, v_b_1659_, v___y_1667_, v___y_1669_, v___y_1670_);
return v___x_1672_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1656_ = stack[0].m_obj;
size_t v_sz_1657_ = stack[1].m_num;
size_t v_i_1658_ = stack[2].m_num;
lean_object* v_b_1659_ = stack[3].m_obj;
lean_object* v___y_1660_ = stack[4].m_obj;
lean_object* v___y_1661_ = stack[5].m_obj;
lean_object* v___y_1662_ = stack[6].m_obj;
lean_object* v___y_1663_ = stack[7].m_obj;
lean_object* v___y_1664_ = stack[8].m_obj;
lean_object* v___y_1665_ = stack[9].m_obj;
lean_object* v___y_1666_ = stack[10].m_obj;
lean_object* v___y_1667_ = stack[11].m_obj;
lean_object* v___y_1668_ = stack[12].m_obj;
lean_object* v___y_1669_ = stack[13].m_obj;
lean_object* v___y_1670_ = stack[14].m_obj;
lean_object* v_res_1673_;
v_res_1673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0(v_as_1656_, v_sz_1657_, v_i_1658_, v_b_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
stack->m_obj
 = v_res_1673_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0___boxed(lean_object* v_as_1674_, lean_object* v_sz_1675_, lean_object* v_i_1676_, lean_object* v_b_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
size_t v_sz_boxed_1690_; size_t v_i_boxed_1691_; lean_object* v_res_1692_; 
v_sz_boxed_1690_ = lean_unbox_usize(v_sz_1675_);
lean_dec(v_sz_1675_);
v_i_boxed_1691_ = lean_unbox_usize(v_i_1676_);
lean_dec(v_i_1676_);
v_res_1692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__0(v_as_1674_, v_sz_boxed_1690_, v_i_boxed_1691_, v_b_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec_ref(v_as_1674_);
return v_res_1692_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic(lean_object* v_goal_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v___x_1706_; 
lean_inc(v_goal_1693_);
v___x_1706_ = l_Lean_MVarId_getType(v_goal_1693_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1706_, 1);
v___x_1708_ = l_Lean_Elab_Tactic_VCGen_numBindersToIntro(v_a_1707_);
lean_dec(v_a_1707_);
v___x_1709_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN(v_goal_1693_, v___x_1708_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_1709_;
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec(v_goal_1693_);
v_a_1710_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1706_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1706_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_introsHygienic_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1693_ = stack[0].m_obj;
lean_object* v_a_1694_ = stack[1].m_obj;
lean_object* v_a_1695_ = stack[2].m_obj;
lean_object* v_a_1696_ = stack[3].m_obj;
lean_object* v_a_1697_ = stack[4].m_obj;
lean_object* v_a_1698_ = stack[5].m_obj;
lean_object* v_a_1699_ = stack[6].m_obj;
lean_object* v_a_1700_ = stack[7].m_obj;
lean_object* v_a_1701_ = stack[8].m_obj;
lean_object* v_a_1702_ = stack[9].m_obj;
lean_object* v_a_1703_ = stack[10].m_obj;
lean_object* v_a_1704_ = stack[11].m_obj;
lean_object* v_res_1718_;
v_res_1718_ = l_Lean_Elab_Tactic_VCGen_introsHygienic(v_goal_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
stack->m_obj
 = v_res_1718_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic___boxed(lean_object* v_goal_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_Elab_Tactic_VCGen_introsHygienic(v_goal_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
return v_res_1732_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(lean_object* v_goal_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_hypSimpMethods_1747_; 
v_hypSimpMethods_1747_ = lean_ctor_get(v_a_1738_, 2);
if (lean_obj_tag(v_hypSimpMethods_1747_) == 1)
{
lean_object* v_val_1748_; lean_object* v_post_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v_val_1748_ = lean_ctor_get(v_hypSimpMethods_1747_, 0);
v_post_1749_ = lean_ctor_get(v_val_1748_, 1);
v___x_1750_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__0));
lean_inc_ref(v_post_1749_);
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
lean_ctor_set(v___x_1751_, 1, v_post_1749_);
lean_inc(v_goal_1737_);
v___x_1752_ = l_Lean_MVarId_getType(v_goal_1737_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; lean_object* v_simpState_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v___x_1754_ = lean_st_ref_get(v_a_1739_);
v_simpState_1755_ = lean_ctor_get(v___x_1754_, 7);
lean_inc_ref(v_simpState_1755_);
lean_dec(v___x_1754_);
v___x_1756_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_1756_, 0, v_a_1753_);
v___x_1757_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__1));
v___x_1758_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_1756_, v___x_1751_, v___x_1757_, v_simpState_1755_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v_fst_1760_; lean_object* v_snd_1761_; lean_object* v___x_1762_; lean_object* v_specBackwardRuleCache_1763_; lean_object* v_splitBackwardRuleCache_1764_; lean_object* v_latticeBackwardRuleCache_1765_; lean_object* v_frameBackwardRuleCache_1766_; lean_object* v_frameDB_1767_; lean_object* v_invariants_1768_; lean_object* v_vcs_1769_; lean_object* v_fuel_1770_; lean_object* v_inlineHandledInvariants_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1780_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v_fst_1760_ = lean_ctor_get(v_a_1759_, 0);
lean_inc(v_fst_1760_);
v_snd_1761_ = lean_ctor_get(v_a_1759_, 1);
lean_inc(v_snd_1761_);
lean_dec(v_a_1759_);
v___x_1762_ = lean_st_ref_take(v_a_1739_);
v_specBackwardRuleCache_1763_ = lean_ctor_get(v___x_1762_, 0);
v_splitBackwardRuleCache_1764_ = lean_ctor_get(v___x_1762_, 1);
v_latticeBackwardRuleCache_1765_ = lean_ctor_get(v___x_1762_, 2);
v_frameBackwardRuleCache_1766_ = lean_ctor_get(v___x_1762_, 3);
v_frameDB_1767_ = lean_ctor_get(v___x_1762_, 4);
v_invariants_1768_ = lean_ctor_get(v___x_1762_, 5);
v_vcs_1769_ = lean_ctor_get(v___x_1762_, 6);
v_fuel_1770_ = lean_ctor_get(v___x_1762_, 8);
v_inlineHandledInvariants_1771_ = lean_ctor_get(v___x_1762_, 9);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; 
v_unused_1781_ = lean_ctor_get(v___x_1762_, 7);
lean_dec(v_unused_1781_);
v___x_1773_ = v___x_1762_;
v_isShared_1774_ = v_isSharedCheck_1780_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_inlineHandledInvariants_1771_);
lean_inc(v_fuel_1770_);
lean_inc(v_vcs_1769_);
lean_inc(v_invariants_1768_);
lean_inc(v_frameDB_1767_);
lean_inc(v_frameBackwardRuleCache_1766_);
lean_inc(v_latticeBackwardRuleCache_1765_);
lean_inc(v_splitBackwardRuleCache_1764_);
lean_inc(v_specBackwardRuleCache_1763_);
lean_dec(v___x_1762_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1780_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 7, v_snd_1761_);
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_specBackwardRuleCache_1763_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_splitBackwardRuleCache_1764_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v_latticeBackwardRuleCache_1765_);
lean_ctor_set(v_reuseFailAlloc_1779_, 3, v_frameBackwardRuleCache_1766_);
lean_ctor_set(v_reuseFailAlloc_1779_, 4, v_frameDB_1767_);
lean_ctor_set(v_reuseFailAlloc_1779_, 5, v_invariants_1768_);
lean_ctor_set(v_reuseFailAlloc_1779_, 6, v_vcs_1769_);
lean_ctor_set(v_reuseFailAlloc_1779_, 7, v_snd_1761_);
lean_ctor_set(v_reuseFailAlloc_1779_, 8, v_fuel_1770_);
lean_ctor_set(v_reuseFailAlloc_1779_, 9, v_inlineHandledInvariants_1771_);
v___x_1776_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_st_ref_put(v_a_1739_, v___x_1776_);
v___x_1778_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_fst_1760_, v_goal_1737_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
return v___x_1778_;
}
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec(v_goal_1737_);
v_a_1782_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1758_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1758_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
lean_dec_ref_known(v___x_1751_, 2);
lean_dec(v_goal_1737_);
v_a_1790_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1752_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1752_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_dec(v_goal_1737_);
v___x_1798_ = lean_box(0);
v___x_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
return v___x_1799_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1737_ = stack[0].m_obj;
lean_object* v_a_1738_ = stack[1].m_obj;
lean_object* v_a_1739_ = stack[2].m_obj;
lean_object* v_a_1740_ = stack[3].m_obj;
lean_object* v_a_1741_ = stack[4].m_obj;
lean_object* v_a_1742_ = stack[5].m_obj;
lean_object* v_a_1743_ = stack[6].m_obj;
lean_object* v_a_1744_ = stack[7].m_obj;
lean_object* v_a_1745_ = stack[8].m_obj;
lean_object* v_res_1800_;
v_res_1800_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(v_goal_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
stack->m_obj
 = v_res_1800_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___boxed(lean_object* v_goal_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(v_goal_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_a_1805_);
lean_dec_ref(v_a_1804_);
lean_dec(v_a_1803_);
lean_dec_ref(v_a_1802_);
return v_res_1811_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope(lean_object* v_goal_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(v_goal_1812_, v_a_1813_, v_a_1814_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
return v___x_1825_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_simpGoalTelescope_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1812_ = stack[0].m_obj;
lean_object* v_a_1813_ = stack[1].m_obj;
lean_object* v_a_1814_ = stack[2].m_obj;
lean_object* v_a_1815_ = stack[3].m_obj;
lean_object* v_a_1816_ = stack[4].m_obj;
lean_object* v_a_1817_ = stack[5].m_obj;
lean_object* v_a_1818_ = stack[6].m_obj;
lean_object* v_a_1819_ = stack[7].m_obj;
lean_object* v_a_1820_ = stack[8].m_obj;
lean_object* v_a_1821_ = stack[9].m_obj;
lean_object* v_a_1822_ = stack[10].m_obj;
lean_object* v_a_1823_ = stack[11].m_obj;
lean_object* v_res_1826_;
v_res_1826_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope(v_goal_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
stack->m_obj
 = v_res_1826_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___boxed(lean_object* v_goal_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope(v_goal_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec(v_a_1829_);
lean_dec_ref(v_a_1828_);
return v_res_1840_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__8));
v___x_1843_ = l_Lean_stringToMessageData(v___x_1842_);
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6(void){
_start:
{
uint8_t v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1851_ = 0;
v___x_1852_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__5));
v___x_1853_ = l_Lean_MessageData_ofConstName(v___x_1852_, v___x_1851_);
return v___x_1853_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__0));
v___x_1856_ = l_Lean_stringToMessageData(v___x_1855_);
return v___x_1856_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6);
v___x_1858_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1);
v___x_1859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v___x_1857_);
return v___x_1859_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9);
v___x_1861_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7);
v___x_1862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
lean_ctor_set(v___x_1862_, 1, v___x_1860_);
return v___x_1862_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0(lean_object* v_goal_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1886_; 
lean_inc(v_goal_1870_);
v___x_1886_ = l_Lean_MVarId_getType(v_goal_1870_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1960_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1960_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1960_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___x_1900_; uint8_t v___x_1901_; 
lean_inc(v_a_1887_);
v___x_1900_ = l_Lean_Expr_cleanupAnnotations(v_a_1887_);
v___x_1901_ = l_Lean_Expr_isApp(v___x_1900_);
if (v___x_1901_ == 0)
{
lean_dec_ref(v___x_1900_);
lean_del_object(v___x_1889_);
lean_dec(v_a_1887_);
lean_dec(v_goal_1870_);
goto v___jp_1883_;
}
else
{
lean_object* v___x_1902_; uint8_t v___x_1903_; 
v___x_1902_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1900_);
v___x_1903_ = l_Lean_Expr_isApp(v___x_1902_);
if (v___x_1903_ == 0)
{
lean_dec_ref(v___x_1902_);
lean_del_object(v___x_1889_);
lean_dec(v_a_1887_);
lean_dec(v_goal_1870_);
goto v___jp_1883_;
}
else
{
lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1904_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1902_);
v___x_1905_ = l_Lean_Expr_isApp(v___x_1904_);
if (v___x_1905_ == 0)
{
lean_dec_ref(v___x_1904_);
lean_del_object(v___x_1889_);
lean_dec(v_a_1887_);
lean_dec(v_goal_1870_);
goto v___jp_1883_;
}
else
{
lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1906_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1904_);
v___x_1907_ = l_Lean_Expr_isApp(v___x_1906_);
if (v___x_1907_ == 0)
{
lean_dec_ref(v___x_1906_);
lean_del_object(v___x_1889_);
lean_dec(v_a_1887_);
lean_dec(v_goal_1870_);
goto v___jp_1883_;
}
else
{
lean_object* v_arg_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v_arg_1908_ = lean_ctor_get(v___x_1906_, 1);
lean_inc_ref(v_arg_1908_);
v___x_1909_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1906_);
v___x_1910_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13));
v___x_1911_ = l_Lean_Expr_isConstOf(v___x_1909_, v___x_1910_);
lean_dec_ref(v___x_1909_);
if (v___x_1911_ == 0)
{
lean_dec_ref(v_arg_1908_);
lean_del_object(v___x_1889_);
lean_dec(v_a_1887_);
lean_dec(v_goal_1870_);
goto v___jp_1883_;
}
else
{
uint8_t v___x_1912_; 
v___x_1912_ = l_Lean_Expr_isForall(v_arg_1908_);
lean_dec_ref(v_arg_1908_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
lean_dec(v_a_1887_);
lean_dec(v_goal_1870_);
v___x_1913_ = lean_box(0);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1913_);
v___x_1915_ = v___x_1889_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
else
{
lean_object* v_backwardRules_1917_; lean_object* v_stateArgIntro_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_del_object(v___x_1889_);
v_backwardRules_1917_ = lean_ctor_get(v___y_1871_, 0);
v_stateArgIntro_1918_ = lean_ctor_get(v_backwardRules_1917_, 1);
v___x_1919_ = lean_box(0);
lean_inc_ref(v_stateArgIntro_1918_);
v___x_1920_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_stateArgIntro_1918_, v_goal_1870_, v___x_1919_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
if (lean_obj_tag(v_a_1921_) == 1)
{
lean_object* v_mvarIds_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1951_; 
v_mvarIds_1922_ = lean_ctor_get(v_a_1921_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_a_1921_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1924_ = v_a_1921_;
v_isShared_1925_ = v_isSharedCheck_1951_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_mvarIds_1922_);
lean_dec(v_a_1921_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1951_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
if (lean_obj_tag(v_mvarIds_1922_) == 1)
{
lean_object* v_tail_1926_; 
v_tail_1926_ = lean_ctor_get(v_mvarIds_1922_, 1);
if (lean_obj_tag(v_tail_1926_) == 0)
{
lean_object* v_head_1927_; lean_object* v___x_1928_; 
lean_dec(v_a_1887_);
v_head_1927_ = lean_ctor_get(v_mvarIds_1922_, 0);
lean_inc(v_head_1927_);
lean_dec_ref_known(v_mvarIds_1922_, 2);
v___x_1928_ = l_Lean_Elab_Tactic_VCGen_introsHygienic(v_head_1927_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc_n(v_a_1929_, 2);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1930_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs(v_a_1929_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
if (lean_obj_tag(v_a_1931_) == 0)
{
lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1941_; 
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; 
v_unused_1942_ = lean_ctor_get(v___x_1930_, 0);
lean_dec(v_unused_1942_);
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1941_;
goto v_resetjp_1932_;
}
else
{
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1941_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v_a_1929_);
v___x_1936_ = v___x_1924_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1929_);
v___x_1936_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1938_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1936_);
v___x_1938_ = v___x_1933_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
else
{
lean_dec(v_a_1929_);
lean_del_object(v___x_1924_);
return v___x_1930_;
}
}
else
{
lean_dec(v_a_1929_);
lean_del_object(v___x_1924_);
return v___x_1930_;
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_del_object(v___x_1924_);
v_a_1943_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1928_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1928_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_1922_, 2);
lean_del_object(v___x_1924_);
v___y_1892_ = v___y_1878_;
v___y_1893_ = v___y_1879_;
v___y_1894_ = v___y_1880_;
v___y_1895_ = v___y_1881_;
goto v___jp_1891_;
}
}
else
{
lean_del_object(v___x_1924_);
lean_dec(v_mvarIds_1922_);
v___y_1892_ = v___y_1878_;
v___y_1893_ = v___y_1879_;
v___y_1894_ = v___y_1880_;
v___y_1895_ = v___y_1881_;
goto v___jp_1891_;
}
}
}
else
{
lean_dec(v_a_1921_);
v___y_1892_ = v___y_1878_;
v___y_1893_ = v___y_1879_;
v___y_1894_ = v___y_1880_;
v___y_1895_ = v___y_1881_;
goto v___jp_1891_;
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec(v_a_1887_);
v_a_1952_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1920_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1920_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
}
}
}
}
v___jp_1891_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1896_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10);
v___x_1897_ = l_Lean_indentExpr(v_a_1887_);
v___x_1898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1896_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_1898_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
return v___x_1899_;
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec(v_goal_1870_);
v_a_1961_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1886_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1886_);
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
v___jp_1883_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_box(0);
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
return v___x_1885_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1870_ = stack[0].m_obj;
lean_object* v___y_1871_ = stack[1].m_obj;
lean_object* v___y_1872_ = stack[2].m_obj;
lean_object* v___y_1873_ = stack[3].m_obj;
lean_object* v___y_1874_ = stack[4].m_obj;
lean_object* v___y_1875_ = stack[5].m_obj;
lean_object* v___y_1876_ = stack[6].m_obj;
lean_object* v___y_1877_ = stack[7].m_obj;
lean_object* v___y_1878_ = stack[8].m_obj;
lean_object* v___y_1879_ = stack[9].m_obj;
lean_object* v___y_1880_ = stack[10].m_obj;
lean_object* v___y_1881_ = stack[11].m_obj;
lean_object* v_res_1969_;
v_res_1969_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0(v_goal_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
stack->m_obj
 = v_res_1969_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___boxed(lean_object* v_goal_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0(v_goal_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
return v_res_1983_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs(lean_object* v_goal_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v___f_1997_; lean_object* v___x_1998_; 
lean_inc(v_goal_1984_);
v___f_1997_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___boxed), 13, 1);
lean_closure_set(v___f_1997_, 0, v_goal_1984_);
v___x_1998_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_goal_1984_, v___f_1997_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
return v___x_1998_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_introsExcessArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1984_ = stack[0].m_obj;
lean_object* v_a_1985_ = stack[1].m_obj;
lean_object* v_a_1986_ = stack[2].m_obj;
lean_object* v_a_1987_ = stack[3].m_obj;
lean_object* v_a_1988_ = stack[4].m_obj;
lean_object* v_a_1989_ = stack[5].m_obj;
lean_object* v_a_1990_ = stack[6].m_obj;
lean_object* v_a_1991_ = stack[7].m_obj;
lean_object* v_a_1992_ = stack[8].m_obj;
lean_object* v_a_1993_ = stack[9].m_obj;
lean_object* v_a_1994_ = stack[10].m_obj;
lean_object* v_a_1995_ = stack[11].m_obj;
lean_object* v_res_1999_;
v_res_1999_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs(v_goal_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
stack->m_obj
 = v_res_1999_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___boxed(lean_object* v_goal_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs(v_goal_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
lean_dec(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
return v_res_2013_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg(lean_object* v_e_2014_, lean_object* v___y_2015_){
_start:
{
uint8_t v___x_2017_; 
v___x_2017_ = l_Lean_Expr_hasMVar(v_e_2014_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v_e_2014_);
return v___x_2018_;
}
else
{
lean_object* v___x_2019_; lean_object* v_mctx_2020_; lean_object* v___x_2021_; lean_object* v_fst_2022_; lean_object* v_snd_2023_; lean_object* v___x_2024_; lean_object* v_cache_2025_; lean_object* v_zetaDeltaFVarIds_2026_; lean_object* v_postponed_2027_; lean_object* v_diag_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2037_; 
v___x_2019_ = lean_st_ref_get(v___y_2015_);
v_mctx_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc_ref(v_mctx_2020_);
lean_dec(v___x_2019_);
v___x_2021_ = l_Lean_instantiateMVarsCore(v_mctx_2020_, v_e_2014_);
v_fst_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_fst_2022_);
v_snd_2023_ = lean_ctor_get(v___x_2021_, 1);
lean_inc(v_snd_2023_);
lean_dec_ref(v___x_2021_);
v___x_2024_ = lean_st_ref_take(v___y_2015_);
v_cache_2025_ = lean_ctor_get(v___x_2024_, 1);
v_zetaDeltaFVarIds_2026_ = lean_ctor_get(v___x_2024_, 2);
v_postponed_2027_ = lean_ctor_get(v___x_2024_, 3);
v_diag_2028_ = lean_ctor_get(v___x_2024_, 4);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; 
v_unused_2038_ = lean_ctor_get(v___x_2024_, 0);
lean_dec(v_unused_2038_);
v___x_2030_ = v___x_2024_;
v_isShared_2031_ = v_isSharedCheck_2037_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_diag_2028_);
lean_inc(v_postponed_2027_);
lean_inc(v_zetaDeltaFVarIds_2026_);
lean_inc(v_cache_2025_);
lean_dec(v___x_2024_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2037_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v_snd_2023_);
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_snd_2023_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_cache_2025_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v_zetaDeltaFVarIds_2026_);
lean_ctor_set(v_reuseFailAlloc_2036_, 3, v_postponed_2027_);
lean_ctor_set(v_reuseFailAlloc_2036_, 4, v_diag_2028_);
v___x_2033_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_st_ref_put(v___y_2015_, v___x_2033_);
v___x_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2035_, 0, v_fst_2022_);
return v___x_2035_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2014_ = stack[0].m_obj;
lean_object* v___y_2015_ = stack[1].m_obj;
lean_object* v_res_2039_;
v_res_2039_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg(v_e_2014_, v___y_2015_);
stack->m_obj
 = v_res_2039_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg___boxed(lean_object* v_e_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg(v_e_2040_, v___y_2041_);
lean_dec(v___y_2041_);
return v_res_2043_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1(lean_object* v_e_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg(v_e_2044_, v___y_2053_);
return v___x_2057_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2044_ = stack[0].m_obj;
lean_object* v___y_2045_ = stack[1].m_obj;
lean_object* v___y_2046_ = stack[2].m_obj;
lean_object* v___y_2047_ = stack[3].m_obj;
lean_object* v___y_2048_ = stack[4].m_obj;
lean_object* v___y_2049_ = stack[5].m_obj;
lean_object* v___y_2050_ = stack[6].m_obj;
lean_object* v___y_2051_ = stack[7].m_obj;
lean_object* v___y_2052_ = stack[8].m_obj;
lean_object* v___y_2053_ = stack[9].m_obj;
lean_object* v___y_2054_ = stack[10].m_obj;
lean_object* v___y_2055_ = stack[11].m_obj;
lean_object* v_res_2058_;
v_res_2058_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1(v_e_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
stack->m_obj
 = v_res_2058_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___boxed(lean_object* v_e_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1(v_e_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
return v_res_2072_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(lean_object* v_mvarId_2073_, lean_object* v_val_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; lean_object* v_mctx_2078_; lean_object* v_cache_2079_; lean_object* v_zetaDeltaFVarIds_2080_; lean_object* v_postponed_2081_; lean_object* v_diag_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2112_; 
v___x_2077_ = lean_st_ref_take(v___y_2075_);
v_mctx_2078_ = lean_ctor_get(v___x_2077_, 0);
v_cache_2079_ = lean_ctor_get(v___x_2077_, 1);
v_zetaDeltaFVarIds_2080_ = lean_ctor_get(v___x_2077_, 2);
v_postponed_2081_ = lean_ctor_get(v___x_2077_, 3);
v_diag_2082_ = lean_ctor_get(v___x_2077_, 4);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2084_ = v___x_2077_;
v_isShared_2085_ = v_isSharedCheck_2112_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_diag_2082_);
lean_inc(v_postponed_2081_);
lean_inc(v_zetaDeltaFVarIds_2080_);
lean_inc(v_cache_2079_);
lean_inc(v_mctx_2078_);
lean_dec(v___x_2077_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2112_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v_depth_2086_; lean_object* v_levelAssignDepth_2087_; lean_object* v_lmvarCounter_2088_; lean_object* v_mvarCounter_2089_; lean_object* v_lDecls_2090_; lean_object* v_decls_2091_; lean_object* v_userNames_2092_; lean_object* v_lAssignment_2093_; lean_object* v_eAssignment_2094_; lean_object* v_dAssignment_2095_; lean_object* v_instanceTypedMVars_2096_; lean_object* v_synthNormMemo_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2111_; 
v_depth_2086_ = lean_ctor_get(v_mctx_2078_, 0);
v_levelAssignDepth_2087_ = lean_ctor_get(v_mctx_2078_, 1);
v_lmvarCounter_2088_ = lean_ctor_get(v_mctx_2078_, 2);
v_mvarCounter_2089_ = lean_ctor_get(v_mctx_2078_, 3);
v_lDecls_2090_ = lean_ctor_get(v_mctx_2078_, 4);
v_decls_2091_ = lean_ctor_get(v_mctx_2078_, 5);
v_userNames_2092_ = lean_ctor_get(v_mctx_2078_, 6);
v_lAssignment_2093_ = lean_ctor_get(v_mctx_2078_, 7);
v_eAssignment_2094_ = lean_ctor_get(v_mctx_2078_, 8);
v_dAssignment_2095_ = lean_ctor_get(v_mctx_2078_, 9);
v_instanceTypedMVars_2096_ = lean_ctor_get(v_mctx_2078_, 10);
v_synthNormMemo_2097_ = lean_ctor_get(v_mctx_2078_, 11);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_mctx_2078_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2099_ = v_mctx_2078_;
v_isShared_2100_ = v_isSharedCheck_2111_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_synthNormMemo_2097_);
lean_inc(v_instanceTypedMVars_2096_);
lean_inc(v_dAssignment_2095_);
lean_inc(v_eAssignment_2094_);
lean_inc(v_lAssignment_2093_);
lean_inc(v_userNames_2092_);
lean_inc(v_decls_2091_);
lean_inc(v_lDecls_2090_);
lean_inc(v_mvarCounter_2089_);
lean_inc(v_lmvarCounter_2088_);
lean_inc(v_levelAssignDepth_2087_);
lean_inc(v_depth_2086_);
lean_dec(v_mctx_2078_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2111_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2104_; 
v___x_2101_ = lean_box(0);
v___x_2102_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(v_eAssignment_2094_, v_mvarId_2073_, v_val_2074_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 8, v___x_2102_);
v___x_2104_ = v___x_2099_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_depth_2086_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_levelAssignDepth_2087_);
lean_ctor_set(v_reuseFailAlloc_2110_, 2, v_lmvarCounter_2088_);
lean_ctor_set(v_reuseFailAlloc_2110_, 3, v_mvarCounter_2089_);
lean_ctor_set(v_reuseFailAlloc_2110_, 4, v_lDecls_2090_);
lean_ctor_set(v_reuseFailAlloc_2110_, 5, v_decls_2091_);
lean_ctor_set(v_reuseFailAlloc_2110_, 6, v_userNames_2092_);
lean_ctor_set(v_reuseFailAlloc_2110_, 7, v_lAssignment_2093_);
lean_ctor_set(v_reuseFailAlloc_2110_, 8, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2110_, 9, v_dAssignment_2095_);
lean_ctor_set(v_reuseFailAlloc_2110_, 10, v_instanceTypedMVars_2096_);
lean_ctor_set(v_reuseFailAlloc_2110_, 11, v_synthNormMemo_2097_);
v___x_2104_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2106_; 
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2104_);
v___x_2106_ = v___x_2084_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_cache_2079_);
lean_ctor_set(v_reuseFailAlloc_2109_, 2, v_zetaDeltaFVarIds_2080_);
lean_ctor_set(v_reuseFailAlloc_2109_, 3, v_postponed_2081_);
lean_ctor_set(v_reuseFailAlloc_2109_, 4, v_diag_2082_);
v___x_2106_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = lean_st_ref_put(v___y_2075_, v___x_2106_);
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2101_);
return v___x_2108_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2073_ = stack[0].m_obj;
lean_object* v_val_2074_ = stack[1].m_obj;
lean_object* v___y_2075_ = stack[2].m_obj;
lean_object* v_res_2113_;
v_res_2113_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_mvarId_2073_, v_val_2074_, v___y_2075_);
stack->m_obj
 = v_res_2113_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg___boxed(lean_object* v_mvarId_2114_, lean_object* v_val_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_mvarId_2114_, v_val_2115_, v___y_2116_);
lean_dec(v___y_2116_);
return v_res_2118_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__0));
v___x_2121_ = l_Lean_stringToMessageData(v___x_2120_);
return v___x_2121_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__3));
v___x_2125_ = l_Lean_stringToMessageData(v___x_2124_);
return v___x_2125_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13(void){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2139_ = lean_box(0);
v___x_2140_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__8));
v___x_2141_ = l_Lean_mkConst(v___x_2140_, v___x_2139_);
return v___x_2141_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = lean_box(0);
v___x_2147_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__15));
v___x_2148_ = l_Lean_mkConst(v___x_2147_, v___x_2146_);
return v___x_2148_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2153_ = lean_box(0);
v___x_2154_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__18));
v___x_2155_ = l_Lean_mkConst(v___x_2154_, v___x_2153_);
return v___x_2155_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = lean_box(0);
v___x_2160_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__20));
v___x_2161_ = l_Lean_mkConst(v___x_2160_, v___x_2159_);
return v___x_2161_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0(lean_object* v_goal_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v___y_2176_; lean_object* v___y_2177_; uint8_t v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v_g_2194_; lean_object* v_fst_2198_; lean_object* v_snd_2199_; lean_object* v___x_2428_; 
lean_inc(v_goal_2162_);
v___x_2428_ = l_Lean_MVarId_getType(v_goal_2162_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v___x_2430_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2429_);
lean_dec_ref_known(v___x_2428_, 1);
v___x_2430_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__1___redArg(v_a_2429_, v___y_2171_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2432_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc_n(v_a_2431_, 2);
lean_dec_ref_known(v___x_2430_, 1);
v___x_2432_ = l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(v_a_2431_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref_known(v___x_2432_, 1);
if (lean_obj_tag(v_a_2433_) == 0)
{
v_fst_2198_ = v_goal_2162_;
v_snd_2199_ = v_a_2431_;
goto v___jp_2197_;
}
else
{
lean_object* v_val_2434_; lean_object* v___x_2435_; 
lean_dec(v_a_2431_);
v_val_2434_ = lean_ctor_get(v_a_2433_, 0);
lean_inc_n(v_val_2434_, 2);
lean_dec_ref_known(v_a_2433_, 1);
v___x_2435_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_2162_, v_val_2434_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v_fst_2198_ = v_a_2436_;
v_snd_2199_ = v_val_2434_;
goto v___jp_2197_;
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec(v_val_2434_);
v_a_2437_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2435_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2435_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec(v_a_2431_);
lean_dec(v_goal_2162_);
v_a_2445_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2432_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2432_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec(v_goal_2162_);
v_a_2453_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2430_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2430_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec(v_goal_2162_);
v_a_2461_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2428_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2428_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
v___jp_2175_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2183_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__1);
v___x_2184_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__2));
lean_inc_ref(v___y_2176_);
v___x_2185_ = l_Lean_Name_mkStr2(v___y_2176_, v___x_2184_);
v___x_2186_ = l_Lean_MessageData_ofConstName(v___x_2185_, v___y_2178_);
v___x_2187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2183_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
v___x_2188_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__4);
v___x_2189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2187_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = l_Lean_indentExpr(v___y_2177_);
v___x_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_2191_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
return v___x_2192_;
}
v___jp_2193_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2195_, 0, v_g_2194_);
v___x_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
return v___x_2196_;
}
v___jp_2197_:
{
lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2200_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__6));
v___x_2201_ = l_Lean_Expr_isAppOf(v_snd_2199_, v___x_2200_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2202_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__7));
v___x_2203_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__8));
v___x_2204_ = l_Lean_Expr_isAppOf(v_snd_2199_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2205_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__10));
v___x_2206_ = lean_unsigned_to_nat(3u);
v___x_2207_ = l_Lean_Expr_isAppOfArity(v_snd_2199_, v___x_2205_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec_ref(v_snd_2199_);
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v_fst_2198_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
return v___x_2209_;
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2210_ = l_Lean_Expr_appFn_x21(v_snd_2199_);
v___x_2211_ = l_Lean_Expr_appFn_x21(v___x_2210_);
v___x_2212_ = l_Lean_Expr_appArg_x21(v___x_2211_);
lean_dec_ref(v___x_2211_);
v___x_2213_ = l_Lean_Expr_appArg_x21(v___x_2210_);
lean_dec_ref(v___x_2210_);
v___x_2214_ = l_Lean_Expr_appArg_x21(v_snd_2199_);
lean_dec_ref(v_snd_2199_);
v___x_2215_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v___x_2213_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2217_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v___x_2217_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v___x_2214_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2219_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
lean_inc_ref(v___x_2212_);
v___x_2219_ = l_Lean_Meta_getLevel(v___x_2212_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
lean_dec_ref_known(v___x_2219_, 1);
v___x_2221_ = lean_box(0);
v___x_2222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2222_, 0, v_a_2220_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = l_Lean_mkConst(v___x_2205_, v___x_2222_);
lean_inc(v_a_2218_);
lean_inc(v_a_2216_);
lean_inc_ref(v___x_2212_);
v___x_2224_ = l_Lean_mkApp3(v___x_2223_, v___x_2212_, v_a_2216_, v_a_2218_);
v___x_2225_ = l_Lean_MVarId_replaceTargetDefEqFast(v_fst_2198_, v___x_2224_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_a_2226_);
lean_dec_ref_known(v___x_2225_, 1);
v___x_2227_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsHygienicN___lam__0___closed__0));
lean_inc(v_a_2216_);
v___x_2228_ = l_Lean_Meta_Sym_isDefEqS(v_a_2216_, v_a_2218_, v___x_2207_, v___x_2207_, v___x_2227_, v___x_2227_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2270_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2270_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2270_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
uint8_t v___x_2233_; 
v___x_2233_ = lean_unbox(v_a_2229_);
lean_dec(v_a_2229_);
if (v___x_2233_ == 0)
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
lean_dec(v_a_2216_);
lean_dec_ref(v___x_2212_);
v___x_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2234_, 0, v_a_2226_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v___x_2234_);
v___x_2236_ = v___x_2231_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
else
{
lean_object* v___x_2238_; 
lean_del_object(v___x_2231_);
lean_inc_ref(v___x_2212_);
v___x_2238_ = l_Lean_Meta_getLevel(v___x_2212_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
v___x_2240_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__12));
v___x_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2241_, 0, v_a_2239_);
lean_ctor_set(v___x_2241_, 1, v___x_2221_);
v___x_2242_ = l_Lean_mkConst(v___x_2240_, v___x_2241_);
v___x_2243_ = l_Lean_mkAppB(v___x_2242_, v___x_2212_, v_a_2216_);
v___x_2244_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_a_2226_, v___x_2243_, v___y_2171_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2252_; 
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2252_ == 0)
{
lean_object* v_unused_2253_; 
v_unused_2253_ = lean_ctor_get(v___x_2244_, 0);
lean_dec(v_unused_2253_);
v___x_2246_ = v___x_2244_;
v_isShared_2247_ = v_isSharedCheck_2252_;
goto v_resetjp_2245_;
}
else
{
lean_dec(v___x_2244_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2252_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2248_ = lean_box(0);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v___x_2248_);
v___x_2250_ = v___x_2246_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
v_a_2254_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2244_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2244_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec(v_a_2226_);
lean_dec(v_a_2216_);
lean_dec_ref(v___x_2212_);
v_a_2262_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2238_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2238_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec(v_a_2226_);
lean_dec(v_a_2216_);
lean_dec_ref(v___x_2212_);
v_a_2271_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2228_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2228_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec(v_a_2218_);
lean_dec(v_a_2216_);
lean_dec_ref(v___x_2212_);
v_a_2279_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2225_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2225_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec(v_a_2218_);
lean_dec(v_a_2216_);
lean_dec_ref(v___x_2212_);
lean_dec(v_fst_2198_);
v_a_2287_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2219_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2219_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec(v_a_2216_);
lean_dec_ref(v___x_2212_);
lean_dec(v_fst_2198_);
v_a_2295_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2217_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2217_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec_ref(v___x_2214_);
lean_dec_ref(v___x_2212_);
lean_dec(v_fst_2198_);
v_a_2303_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2215_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2215_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
else
{
lean_object* v_backwardRules_2311_; lean_object* v_andIntro_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_backwardRules_2311_ = lean_ctor_get(v___y_2163_, 0);
v_andIntro_2312_ = lean_ctor_get(v_backwardRules_2311_, 8);
v___x_2313_ = lean_box(0);
lean_inc_ref(v_andIntro_2312_);
v___x_2314_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_andIntro_2312_, v_fst_2198_, v___x_2313_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2314_, 1);
if (lean_obj_tag(v_a_2315_) == 1)
{
lean_object* v_mvarIds_2316_; 
v_mvarIds_2316_ = lean_ctor_get(v_a_2315_, 0);
lean_inc(v_mvarIds_2316_);
lean_dec_ref_known(v_a_2315_, 1);
if (lean_obj_tag(v_mvarIds_2316_) == 1)
{
lean_object* v_tail_2317_; 
v_tail_2317_ = lean_ctor_get(v_mvarIds_2316_, 1);
lean_inc(v_tail_2317_);
if (lean_obj_tag(v_tail_2317_) == 1)
{
lean_object* v_tail_2318_; 
v_tail_2318_ = lean_ctor_get(v_tail_2317_, 1);
if (lean_obj_tag(v_tail_2318_) == 0)
{
lean_object* v_head_2319_; lean_object* v_head_2320_; lean_object* v___x_2321_; 
lean_dec_ref(v_snd_2199_);
v_head_2319_ = lean_ctor_get(v_mvarIds_2316_, 0);
lean_inc(v_head_2319_);
lean_dec_ref_known(v_mvarIds_2316_, 2);
v_head_2320_ = lean_ctor_get(v_tail_2317_, 0);
lean_inc(v_head_2320_);
lean_dec_ref_known(v_tail_2317_, 2);
v___x_2321_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_head_2319_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2323_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2323_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_head_2320_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2323_) == 0)
{
if (lean_obj_tag(v_a_2322_) == 0)
{
lean_object* v_a_2324_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
if (lean_obj_tag(v_a_2324_) == 0)
{
return v___x_2323_;
}
else
{
lean_object* v_val_2325_; 
lean_inc_ref(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v_val_2325_ = lean_ctor_get(v_a_2324_, 0);
lean_inc(v_val_2325_);
lean_dec_ref_known(v_a_2324_, 1);
v_g_2194_ = v_val_2325_;
goto v___jp_2193_;
}
}
else
{
lean_object* v_a_2326_; 
v_a_2326_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2323_, 1);
if (lean_obj_tag(v_a_2326_) == 0)
{
lean_object* v_val_2327_; 
v_val_2327_ = lean_ctor_get(v_a_2322_, 0);
lean_inc(v_val_2327_);
lean_dec_ref_known(v_a_2322_, 1);
v_g_2194_ = v_val_2327_;
goto v___jp_2193_;
}
else
{
lean_object* v_val_2328_; lean_object* v_val_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2400_; 
v_val_2328_ = lean_ctor_get(v_a_2322_, 0);
lean_inc(v_val_2328_);
lean_dec_ref_known(v_a_2322_, 1);
v_val_2329_ = lean_ctor_get(v_a_2326_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v_a_2326_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2331_ = v_a_2326_;
v_isShared_2332_ = v_isSharedCheck_2400_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_val_2329_);
lean_dec(v_a_2326_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2400_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; 
lean_inc(v_val_2328_);
v___x_2333_ = l_Lean_MVarId_getType(v_val_2328_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2335_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref_known(v___x_2333_, 1);
lean_inc(v_val_2329_);
v___x_2335_ = l_Lean_MVarId_getType(v_val_2329_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc_n(v_a_2336_, 2);
lean_dec_ref_known(v___x_2335_, 1);
v___x_2337_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__13);
lean_inc(v_a_2334_);
v___x_2338_ = l_Lean_mkAppB(v___x_2337_, v_a_2334_, v_a_2336_);
v___x_2339_ = lean_box(0);
v___x_2340_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2338_, v___x_2339_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc_n(v_a_2341_, 2);
lean_dec_ref_known(v___x_2340_, 1);
v___x_2342_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__16);
lean_inc(v_a_2336_);
lean_inc(v_a_2334_);
v___x_2343_ = l_Lean_mkApp3(v___x_2342_, v_a_2334_, v_a_2336_, v_a_2341_);
v___x_2344_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_val_2328_, v___x_2343_, v___y_2171_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
lean_dec_ref_known(v___x_2344_, 1);
v___x_2345_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__19);
lean_inc(v_a_2341_);
v___x_2346_ = l_Lean_mkApp3(v___x_2345_, v_a_2334_, v_a_2336_, v_a_2341_);
v___x_2347_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_val_2329_, v___x_2346_, v___y_2171_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2358_; 
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2358_ == 0)
{
lean_object* v_unused_2359_; 
v_unused_2359_ = lean_ctor_get(v___x_2347_, 0);
lean_dec(v_unused_2359_);
v___x_2349_ = v___x_2347_;
v_isShared_2350_ = v_isSharedCheck_2358_;
goto v_resetjp_2348_;
}
else
{
lean_dec(v___x_2347_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2358_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2351_ = l_Lean_Expr_mvarId_x21(v_a_2341_);
lean_dec(v_a_2341_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 0, v___x_2351_);
v___x_2353_ = v___x_2331_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2355_; 
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___x_2353_);
v___x_2355_ = v___x_2349_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_a_2341_);
lean_del_object(v___x_2331_);
v_a_2360_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2347_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2347_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_a_2341_);
lean_dec(v_a_2336_);
lean_dec(v_a_2334_);
lean_del_object(v___x_2331_);
lean_dec(v_val_2329_);
v_a_2368_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2344_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2344_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec(v_a_2336_);
lean_dec(v_a_2334_);
lean_del_object(v___x_2331_);
lean_dec(v_val_2329_);
lean_dec(v_val_2328_);
v_a_2376_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2340_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2340_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_dec(v_a_2334_);
lean_del_object(v___x_2331_);
lean_dec(v_val_2329_);
lean_dec(v_val_2328_);
v_a_2384_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2335_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2335_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_del_object(v___x_2331_);
lean_dec(v_val_2329_);
lean_dec(v_val_2328_);
v_a_2392_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2333_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2333_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2322_);
return v___x_2323_;
}
}
else
{
lean_dec(v_head_2320_);
return v___x_2321_;
}
}
else
{
lean_dec_ref_known(v_tail_2317_, 2);
lean_dec_ref_known(v_mvarIds_2316_, 2);
v___y_2176_ = v___x_2202_;
v___y_2177_ = v_snd_2199_;
v___y_2178_ = v___x_2201_;
v___y_2179_ = v___y_2170_;
v___y_2180_ = v___y_2171_;
v___y_2181_ = v___y_2172_;
v___y_2182_ = v___y_2173_;
goto v___jp_2175_;
}
}
else
{
lean_dec(v_tail_2317_);
lean_dec_ref_known(v_mvarIds_2316_, 2);
v___y_2176_ = v___x_2202_;
v___y_2177_ = v_snd_2199_;
v___y_2178_ = v___x_2201_;
v___y_2179_ = v___y_2170_;
v___y_2180_ = v___y_2171_;
v___y_2181_ = v___y_2172_;
v___y_2182_ = v___y_2173_;
goto v___jp_2175_;
}
}
else
{
lean_dec(v_mvarIds_2316_);
v___y_2176_ = v___x_2202_;
v___y_2177_ = v_snd_2199_;
v___y_2178_ = v___x_2201_;
v___y_2179_ = v___y_2170_;
v___y_2180_ = v___y_2171_;
v___y_2181_ = v___y_2172_;
v___y_2182_ = v___y_2173_;
goto v___jp_2175_;
}
}
else
{
lean_dec(v_a_2315_);
v___y_2176_ = v___x_2202_;
v___y_2177_ = v_snd_2199_;
v___y_2178_ = v___x_2201_;
v___y_2179_ = v___y_2170_;
v___y_2180_ = v___y_2171_;
v___y_2181_ = v___y_2172_;
v___y_2182_ = v___y_2173_;
goto v___jp_2175_;
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_dec_ref(v_snd_2199_);
v_a_2401_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2314_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2314_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
}
else
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_dec_ref(v_snd_2199_);
v___x_2409_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21, &l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21_once, _init_l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___closed__21);
v___x_2410_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_fst_2198_, v___x_2409_, v___y_2171_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2418_; 
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2418_ == 0)
{
lean_object* v_unused_2419_; 
v_unused_2419_ = lean_ctor_get(v___x_2410_, 0);
lean_dec(v_unused_2419_);
v___x_2412_ = v___x_2410_;
v_isShared_2413_ = v_isSharedCheck_2418_;
goto v_resetjp_2411_;
}
else
{
lean_dec(v___x_2410_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2418_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2414_ = lean_box(0);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2414_);
v___x_2416_ = v___x_2412_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
v_a_2420_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2410_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2410_);
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
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2162_ = stack[0].m_obj;
lean_object* v___y_2163_ = stack[1].m_obj;
lean_object* v___y_2164_ = stack[2].m_obj;
lean_object* v___y_2165_ = stack[3].m_obj;
lean_object* v___y_2166_ = stack[4].m_obj;
lean_object* v___y_2167_ = stack[5].m_obj;
lean_object* v___y_2168_ = stack[6].m_obj;
lean_object* v___y_2169_ = stack[7].m_obj;
lean_object* v___y_2170_ = stack[8].m_obj;
lean_object* v___y_2171_ = stack[9].m_obj;
lean_object* v___y_2172_ = stack[10].m_obj;
lean_object* v___y_2173_ = stack[11].m_obj;
lean_object* v_res_2469_;
v_res_2469_ = l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0(v_goal_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
stack->m_obj
 = v_res_2469_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___boxed(lean_object* v_goal_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0(v_goal_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
return v_res_2483_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC(lean_object* v_goal_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v___f_2497_; lean_object* v___x_2498_; 
lean_inc(v_goal_2484_);
v___f_2497_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_cleanupVC___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2497_, 0, v_goal_2484_);
v___x_2498_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienicN_spec__1___redArg(v_goal_2484_, v___f_2497_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
return v___x_2498_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_cleanupVC_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2484_ = stack[0].m_obj;
lean_object* v_a_2485_ = stack[1].m_obj;
lean_object* v_a_2486_ = stack[2].m_obj;
lean_object* v_a_2487_ = stack[3].m_obj;
lean_object* v_a_2488_ = stack[4].m_obj;
lean_object* v_a_2489_ = stack[5].m_obj;
lean_object* v_a_2490_ = stack[6].m_obj;
lean_object* v_a_2491_ = stack[7].m_obj;
lean_object* v_a_2492_ = stack[8].m_obj;
lean_object* v_a_2493_ = stack[9].m_obj;
lean_object* v_a_2494_ = stack[10].m_obj;
lean_object* v_a_2495_ = stack[11].m_obj;
lean_object* v_res_2499_;
v_res_2499_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_goal_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
stack->m_obj
 = v_res_2499_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC___boxed(lean_object* v_goal_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_goal_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
lean_dec(v_a_2511_);
lean_dec_ref(v_a_2510_);
lean_dec(v_a_2509_);
lean_dec_ref(v_a_2508_);
lean_dec(v_a_2507_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
return v_res_2513_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0(lean_object* v_mvarId_2514_, lean_object* v_val_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___redArg(v_mvarId_2514_, v_val_2515_, v___y_2524_);
return v___x_2528_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2514_ = stack[0].m_obj;
lean_object* v_val_2515_ = stack[1].m_obj;
lean_object* v___y_2516_ = stack[2].m_obj;
lean_object* v___y_2517_ = stack[3].m_obj;
lean_object* v___y_2518_ = stack[4].m_obj;
lean_object* v___y_2519_ = stack[5].m_obj;
lean_object* v___y_2520_ = stack[6].m_obj;
lean_object* v___y_2521_ = stack[7].m_obj;
lean_object* v___y_2522_ = stack[8].m_obj;
lean_object* v___y_2523_ = stack[9].m_obj;
lean_object* v___y_2524_ = stack[10].m_obj;
lean_object* v___y_2525_ = stack[11].m_obj;
lean_object* v___y_2526_ = stack[12].m_obj;
lean_object* v_res_2529_;
v_res_2529_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0(v_mvarId_2514_, v_val_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
stack->m_obj
 = v_res_2529_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0___boxed(lean_object* v_mvarId_2530_, lean_object* v_val_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_cleanupVC_spec__0(v_mvarId_2530_, v_val_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
return v_res_2544_;
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
