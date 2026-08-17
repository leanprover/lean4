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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Pattern_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_processHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Sym_isDefEqS(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_intros(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 78, 141, 85, 50, 255, 216, 83)}};
static const lean_object* l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "<rule constructed from expression>"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_introsHygienic_collectBinders(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_VCGen_introsHygienic___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsHygienic___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__0___boxed(lean_object**);
static const lean_closure_object l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simpTelescope___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " to goal"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__12;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "le_of_forall_le"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(101, 62, 242, 60, 214, 49, 44, 186)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "failed to apply "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "solveTrivialConjuncts: failed to apply "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(58, 46, 244, 208, 18, 71, 77, 162)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " to"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__13;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__14;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "left"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(12, 252, 227, 83, 88, 185, 40, 148)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__16_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__17;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "right"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(18, 204, 165, 192, 253, 41, 237, 145)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__19_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__20;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__22;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(lean_object* v_mvarId_1_, lean_object* v_x_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1_, v_x_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v_a_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_a_9_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v___x_8_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_a_9_);
lean_dec(v___x_8_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_a_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
else
{
lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_24_; 
v_a_17_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_24_ == 0)
{
v___x_19_ = v___x_8_;
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_a_17_);
lean_dec(v___x_8_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_22_; 
if (v_isShared_20_ == 0)
{
v___x_22_ = v___x_19_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_a_17_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg___boxed(lean_object* v_mvarId_25_, lean_object* v_x_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(v_mvarId_25_, v_x_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1(lean_object* v_00_u03b1_33_, lean_object* v_mvarId_34_, lean_object* v_x_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(v_mvarId_34_, v_x_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___boxed(lean_object* v_00_u03b1_42_, lean_object* v_mvarId_43_, lean_object* v_x_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1(v_00_u03b1_42_, v_mvarId_43_, v_x_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_51_, lean_object* v_x_52_, lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
lean_object* v_ks_55_; lean_object* v_vs_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_80_; 
v_ks_55_ = lean_ctor_get(v_x_51_, 0);
v_vs_56_ = lean_ctor_get(v_x_51_, 1);
v_isSharedCheck_80_ = !lean_is_exclusive(v_x_51_);
if (v_isSharedCheck_80_ == 0)
{
v___x_58_ = v_x_51_;
v_isShared_59_ = v_isSharedCheck_80_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_vs_56_);
lean_inc(v_ks_55_);
lean_dec(v_x_51_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_80_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = lean_array_get_size(v_ks_55_);
v___x_61_ = lean_nat_dec_lt(v_x_52_, v___x_60_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
lean_dec(v_x_52_);
v___x_62_ = lean_array_push(v_ks_55_, v_x_53_);
v___x_63_ = lean_array_push(v_vs_56_, v_x_54_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_63_);
lean_ctor_set(v___x_58_, 0, v___x_62_);
v___x_65_ = v___x_58_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
else
{
lean_object* v_k_x27_67_; uint8_t v___x_68_; 
v_k_x27_67_ = lean_array_fget_borrowed(v_ks_55_, v_x_52_);
v___x_68_ = l_Lean_instBEqMVarId_beq(v_x_53_, v_k_x27_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_70_; 
if (v_isShared_59_ == 0)
{
v___x_70_ = v___x_58_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_ks_55_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_vs_56_);
v___x_70_ = v_reuseFailAlloc_74_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(1u);
v___x_72_ = lean_nat_add(v_x_52_, v___x_71_);
lean_dec(v_x_52_);
v_x_51_ = v___x_70_;
v_x_52_ = v___x_72_;
goto _start;
}
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_75_ = lean_array_fset(v_ks_55_, v_x_52_, v_x_53_);
v___x_76_ = lean_array_fset(v_vs_56_, v_x_52_, v_x_54_);
lean_dec(v_x_52_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_76_);
lean_ctor_set(v___x_58_, 0, v___x_75_);
v___x_78_ = v___x_58_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_75_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_81_, lean_object* v_k_82_, lean_object* v_v_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_81_, v___x_84_, v_k_82_, v_v_83_);
return v___x_85_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(lean_object* v_x_87_, size_t v_x_88_, size_t v_x_89_, lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v_es_92_; size_t v___x_93_; size_t v___x_94_; lean_object* v_j_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_es_92_ = lean_ctor_get(v_x_87_, 0);
v___x_93_ = ((size_t)31ULL);
v___x_94_ = lean_usize_land(v_x_88_, v___x_93_);
v_j_95_ = lean_usize_to_nat(v___x_94_);
v___x_96_ = lean_array_get_size(v_es_92_);
v___x_97_ = lean_nat_dec_lt(v_j_95_, v___x_96_);
if (v___x_97_ == 0)
{
lean_dec(v_j_95_);
lean_dec(v_x_91_);
lean_dec(v_x_90_);
return v_x_87_;
}
else
{
lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_136_; 
lean_inc_ref(v_es_92_);
v_isSharedCheck_136_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v_x_87_, 0);
lean_dec(v_unused_137_);
v___x_99_ = v_x_87_;
v_isShared_100_ = v_isSharedCheck_136_;
goto v_resetjp_98_;
}
else
{
lean_dec(v_x_87_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_136_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v_v_101_; lean_object* v___x_102_; lean_object* v_xs_x27_103_; lean_object* v___y_105_; 
v_v_101_ = lean_array_fget(v_es_92_, v_j_95_);
v___x_102_ = lean_box(0);
v_xs_x27_103_ = lean_array_fset(v_es_92_, v_j_95_, v___x_102_);
switch(lean_obj_tag(v_v_101_))
{
case 0:
{
lean_object* v_key_110_; lean_object* v_val_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_121_; 
v_key_110_ = lean_ctor_get(v_v_101_, 0);
v_val_111_ = lean_ctor_get(v_v_101_, 1);
v_isSharedCheck_121_ = !lean_is_exclusive(v_v_101_);
if (v_isSharedCheck_121_ == 0)
{
v___x_113_ = v_v_101_;
v_isShared_114_ = v_isSharedCheck_121_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_val_111_);
lean_inc(v_key_110_);
lean_dec(v_v_101_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_121_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
uint8_t v___x_115_; 
v___x_115_ = l_Lean_instBEqMVarId_beq(v_x_90_, v_key_110_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_del_object(v___x_113_);
v___x_116_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_110_, v_val_111_, v_x_90_, v_x_91_);
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
v___y_105_ = v___x_117_;
goto v___jp_104_;
}
else
{
lean_object* v___x_119_; 
lean_dec(v_val_111_);
lean_dec(v_key_110_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v_x_91_);
lean_ctor_set(v___x_113_, 0, v_x_90_);
v___x_119_ = v___x_113_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_x_90_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_x_91_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
v___y_105_ = v___x_119_;
goto v___jp_104_;
}
}
}
}
case 1:
{
lean_object* v_node_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_134_; 
v_node_122_ = lean_ctor_get(v_v_101_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v_v_101_);
if (v_isSharedCheck_134_ == 0)
{
v___x_124_ = v_v_101_;
v_isShared_125_ = v_isSharedCheck_134_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_node_122_);
lean_dec(v_v_101_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_134_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_126_ = ((size_t)5ULL);
v___x_127_ = lean_usize_shift_right(v_x_88_, v___x_126_);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_add(v_x_89_, v___x_128_);
v___x_130_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_node_122_, v___x_127_, v___x_129_, v_x_90_, v_x_91_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_130_);
v___x_132_ = v___x_124_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
v___y_105_ = v___x_132_;
goto v___jp_104_;
}
}
}
default: 
{
lean_object* v___x_135_; 
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v_x_90_);
lean_ctor_set(v___x_135_, 1, v_x_91_);
v___y_105_ = v___x_135_;
goto v___jp_104_;
}
}
v___jp_104_:
{
lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_106_ = lean_array_fset(v_xs_x27_103_, v_j_95_, v___y_105_);
lean_dec(v_j_95_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_106_);
v___x_108_ = v___x_99_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
}
else
{
lean_object* v_ks_138_; lean_object* v_vs_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_159_; 
v_ks_138_ = lean_ctor_get(v_x_87_, 0);
v_vs_139_ = lean_ctor_get(v_x_87_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_159_ == 0)
{
v___x_141_ = v_x_87_;
v_isShared_142_ = v_isSharedCheck_159_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_vs_139_);
lean_inc(v_ks_138_);
lean_dec(v_x_87_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_159_;
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
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_ks_138_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_vs_139_);
v___x_144_ = v_reuseFailAlloc_158_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v_newNode_145_; uint8_t v___y_147_; size_t v___x_153_; uint8_t v___x_154_; 
v_newNode_145_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3___redArg(v___x_144_, v_x_90_, v_x_91_);
v___x_153_ = ((size_t)7ULL);
v___x_154_ = lean_usize_dec_le(v___x_153_, v_x_89_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_155_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_145_);
v___x_156_ = lean_unsigned_to_nat(4u);
v___x_157_ = lean_nat_dec_lt(v___x_155_, v___x_156_);
lean_dec(v___x_155_);
v___y_147_ = v___x_157_;
goto v___jp_146_;
}
else
{
v___y_147_ = v___x_154_;
goto v___jp_146_;
}
v___jp_146_:
{
if (v___y_147_ == 0)
{
lean_object* v_ks_148_; lean_object* v_vs_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_ks_148_ = lean_ctor_get(v_newNode_145_, 0);
lean_inc_ref(v_ks_148_);
v_vs_149_ = lean_ctor_get(v_newNode_145_, 1);
lean_inc_ref(v_vs_149_);
lean_dec_ref(v_newNode_145_);
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_152_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(v_x_89_, v_ks_148_, v_vs_149_, v___x_150_, v___x_151_);
lean_dec_ref(v_vs_149_);
lean_dec_ref(v_ks_148_);
return v___x_152_;
}
else
{
return v_newNode_145_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_160_, lean_object* v_keys_161_, lean_object* v_vals_162_, lean_object* v_i_163_, lean_object* v_entries_164_){
_start:
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = lean_array_get_size(v_keys_161_);
v___x_166_ = lean_nat_dec_lt(v_i_163_, v___x_165_);
if (v___x_166_ == 0)
{
lean_dec(v_i_163_);
return v_entries_164_;
}
else
{
lean_object* v_k_167_; lean_object* v_v_168_; uint64_t v___x_169_; size_t v_h_170_; size_t v___x_171_; lean_object* v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v_h_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_k_167_ = lean_array_fget_borrowed(v_keys_161_, v_i_163_);
v_v_168_ = lean_array_fget_borrowed(v_vals_162_, v_i_163_);
v___x_169_ = l_Lean_instHashableMVarId_hash(v_k_167_);
v_h_170_ = lean_uint64_to_usize(v___x_169_);
v___x_171_ = ((size_t)5ULL);
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = ((size_t)1ULL);
v___x_174_ = lean_usize_sub(v_depth_160_, v___x_173_);
v___x_175_ = lean_usize_mul(v___x_171_, v___x_174_);
v_h_176_ = lean_usize_shift_right(v_h_170_, v___x_175_);
v___x_177_ = lean_nat_add(v_i_163_, v___x_172_);
lean_dec(v_i_163_);
lean_inc(v_v_168_);
lean_inc(v_k_167_);
v___x_178_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_entries_164_, v_h_176_, v_depth_160_, v_k_167_, v_v_168_);
v_i_163_ = v___x_177_;
v_entries_164_ = v___x_178_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_180_, lean_object* v_keys_181_, lean_object* v_vals_182_, lean_object* v_i_183_, lean_object* v_entries_184_){
_start:
{
size_t v_depth_boxed_185_; lean_object* v_res_186_; 
v_depth_boxed_185_ = lean_unbox_usize(v_depth_180_);
lean_dec(v_depth_180_);
v_res_186_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_185_, v_keys_181_, v_vals_182_, v_i_183_, v_entries_184_);
lean_dec_ref(v_vals_182_);
lean_dec_ref(v_keys_181_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
size_t v_x_1251__boxed_192_; size_t v_x_1252__boxed_193_; lean_object* v_res_194_; 
v_x_1251__boxed_192_ = lean_unbox_usize(v_x_188_);
lean_dec(v_x_188_);
v_x_1252__boxed_193_ = lean_unbox_usize(v_x_189_);
lean_dec(v_x_189_);
v_res_194_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_x_187_, v_x_1251__boxed_192_, v_x_1252__boxed_193_, v_x_190_, v_x_191_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
uint64_t v___x_198_; size_t v___x_199_; size_t v___x_200_; lean_object* v___x_201_; 
v___x_198_ = l_Lean_instHashableMVarId_hash(v_x_196_);
v___x_199_ = lean_uint64_to_usize(v___x_198_);
v___x_200_ = ((size_t)1ULL);
v___x_201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_x_195_, v___x_199_, v___x_200_, v_x_196_, v_x_197_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(lean_object* v_mvarId_202_, lean_object* v_val_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; lean_object* v_mctx_207_; lean_object* v_cache_208_; lean_object* v_zetaDeltaFVarIds_209_; lean_object* v_postponed_210_; lean_object* v_diag_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_240_; 
v___x_206_ = lean_st_ref_take(v___y_204_);
v_mctx_207_ = lean_ctor_get(v___x_206_, 0);
v_cache_208_ = lean_ctor_get(v___x_206_, 1);
v_zetaDeltaFVarIds_209_ = lean_ctor_get(v___x_206_, 2);
v_postponed_210_ = lean_ctor_get(v___x_206_, 3);
v_diag_211_ = lean_ctor_get(v___x_206_, 4);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_240_ == 0)
{
v___x_213_ = v___x_206_;
v_isShared_214_ = v_isSharedCheck_240_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_diag_211_);
lean_inc(v_postponed_210_);
lean_inc(v_zetaDeltaFVarIds_209_);
lean_inc(v_cache_208_);
lean_inc(v_mctx_207_);
lean_dec(v___x_206_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_240_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v_depth_215_; lean_object* v_levelAssignDepth_216_; lean_object* v_lmvarCounter_217_; lean_object* v_mvarCounter_218_; lean_object* v_lDecls_219_; lean_object* v_decls_220_; lean_object* v_userNames_221_; lean_object* v_lAssignment_222_; lean_object* v_eAssignment_223_; lean_object* v_dAssignment_224_; lean_object* v_instanceTypedMVars_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_239_; 
v_depth_215_ = lean_ctor_get(v_mctx_207_, 0);
v_levelAssignDepth_216_ = lean_ctor_get(v_mctx_207_, 1);
v_lmvarCounter_217_ = lean_ctor_get(v_mctx_207_, 2);
v_mvarCounter_218_ = lean_ctor_get(v_mctx_207_, 3);
v_lDecls_219_ = lean_ctor_get(v_mctx_207_, 4);
v_decls_220_ = lean_ctor_get(v_mctx_207_, 5);
v_userNames_221_ = lean_ctor_get(v_mctx_207_, 6);
v_lAssignment_222_ = lean_ctor_get(v_mctx_207_, 7);
v_eAssignment_223_ = lean_ctor_get(v_mctx_207_, 8);
v_dAssignment_224_ = lean_ctor_get(v_mctx_207_, 9);
v_instanceTypedMVars_225_ = lean_ctor_get(v_mctx_207_, 10);
v_isSharedCheck_239_ = !lean_is_exclusive(v_mctx_207_);
if (v_isSharedCheck_239_ == 0)
{
v___x_227_ = v_mctx_207_;
v_isShared_228_ = v_isSharedCheck_239_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_instanceTypedMVars_225_);
lean_inc(v_dAssignment_224_);
lean_inc(v_eAssignment_223_);
lean_inc(v_lAssignment_222_);
lean_inc(v_userNames_221_);
lean_inc(v_decls_220_);
lean_inc(v_lDecls_219_);
lean_inc(v_mvarCounter_218_);
lean_inc(v_lmvarCounter_217_);
lean_inc(v_levelAssignDepth_216_);
lean_inc(v_depth_215_);
lean_dec(v_mctx_207_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_239_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(v_eAssignment_223_, v_mvarId_202_, v_val_203_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 8, v___x_229_);
v___x_231_ = v___x_227_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_depth_215_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_levelAssignDepth_216_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_lmvarCounter_217_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v_mvarCounter_218_);
lean_ctor_set(v_reuseFailAlloc_238_, 4, v_lDecls_219_);
lean_ctor_set(v_reuseFailAlloc_238_, 5, v_decls_220_);
lean_ctor_set(v_reuseFailAlloc_238_, 6, v_userNames_221_);
lean_ctor_set(v_reuseFailAlloc_238_, 7, v_lAssignment_222_);
lean_ctor_set(v_reuseFailAlloc_238_, 8, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_238_, 9, v_dAssignment_224_);
lean_ctor_set(v_reuseFailAlloc_238_, 10, v_instanceTypedMVars_225_);
v___x_231_ = v_reuseFailAlloc_238_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_233_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_231_);
v___x_233_ = v___x_213_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_cache_208_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_zetaDeltaFVarIds_209_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v_postponed_210_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v_diag_211_);
v___x_233_ = v_reuseFailAlloc_237_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = lean_st_ref_put(v___y_204_, v___x_233_);
v___x_235_ = lean_box(0);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg___boxed(lean_object* v_mvarId_241_, lean_object* v_val_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(v_mvarId_241_, v_val_242_, v___y_243_);
lean_dec(v___y_243_);
return v_res_245_;
}
}
static lean_object* _init_l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__3(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = ((lean_object*)(l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__2));
v___x_253_ = ((lean_object*)(l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__1));
v___x_254_ = l_Lean_mkConst(v___x_253_, v___x_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast___lam__0(lean_object* v_goal_255_, lean_object* v_targetNew_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___x_262_; 
lean_inc(v_goal_255_);
v___x_262_ = l_Lean_MVarId_getTag(v_goal_255_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_264_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v___x_262_, 1);
v___x_264_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_256_, v_a_263_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_266_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref_known(v___x_264_, 1);
lean_inc(v_goal_255_);
v___x_266_ = l_Lean_MVarId_getType(v_goal_255_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_278_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_267_);
lean_dec_ref_known(v___x_266_, 1);
v___x_268_ = lean_obj_once(&l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__3, &l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__3_once, _init_l_Lean_MVarId_replaceTargetDefEqFast___lam__0___closed__3);
lean_inc(v_a_265_);
v___x_269_ = l_Lean_mkAppB(v___x_268_, v_a_267_, v_a_265_);
v___x_270_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(v_goal_255_, v___x_269_, v___y_258_);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v___x_270_, 0);
lean_dec(v_unused_279_);
v___x_272_ = v___x_270_;
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
else
{
lean_dec(v___x_270_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_274_ = l_Lean_Expr_mvarId_x21(v_a_265_);
lean_dec(v_a_265_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_274_);
v___x_276_ = v___x_272_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_dec(v_a_265_);
lean_dec(v_goal_255_);
v_a_280_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_266_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_266_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec(v_goal_255_);
v_a_288_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_264_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_264_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec_ref(v_targetNew_256_);
lean_dec(v_goal_255_);
v_a_296_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_262_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_262_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast___lam__0___boxed(lean_object* v_goal_304_, lean_object* v_targetNew_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_MVarId_replaceTargetDefEqFast___lam__0(v_goal_304_, v_targetNew_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast(lean_object* v_goal_312_, lean_object* v_targetNew_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___f_319_; lean_object* v___x_320_; 
lean_inc(v_goal_312_);
v___f_319_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetDefEqFast___lam__0___boxed), 7, 2);
lean_closure_set(v___f_319_, 0, v_goal_312_);
lean_closure_set(v___f_319_, 1, v_targetNew_313_);
v___x_320_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetDefEqFast_spec__1___redArg(v_goal_312_, v___f_319_, v_a_314_, v_a_315_, v_a_316_, v_a_317_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEqFast___boxed(lean_object* v_goal_321_, lean_object* v_targetNew_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_321_, v_targetNew_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0(lean_object* v_mvarId_329_, lean_object* v_val_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___redArg(v_mvarId_329_, v_val_330_, v___y_332_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0___boxed(lean_object* v_mvarId_337_, lean_object* v_val_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0(v_mvarId_337_, v_val_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0(lean_object* v_00_u03b2_345_, lean_object* v_x_346_, lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(v_x_346_, v_x_347_, v_x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_350_, lean_object* v_x_351_, size_t v_x_352_, size_t v_x_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___redArg(v_x_351_, v_x_352_, v_x_353_, v_x_354_, v_x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_357_, lean_object* v_x_358_, lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
size_t v_x_1625__boxed_363_; size_t v_x_1626__boxed_364_; lean_object* v_res_365_; 
v_x_1625__boxed_363_ = lean_unbox_usize(v_x_359_);
lean_dec(v_x_359_);
v_x_1626__boxed_364_ = lean_unbox_usize(v_x_360_);
lean_dec(v_x_360_);
v_res_365_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2(v_00_u03b2_357_, v_x_358_, v_x_1625__boxed_363_, v_x_1626__boxed_364_, v_x_361_, v_x_362_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_366_, lean_object* v_n_367_, lean_object* v_k_368_, lean_object* v_v_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3___redArg(v_n_367_, v_k_368_, v_v_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_371_, size_t v_depth_372_, lean_object* v_keys_373_, lean_object* v_vals_374_, lean_object* v_heq_375_, lean_object* v_i_376_, lean_object* v_entries_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_372_, v_keys_373_, v_vals_374_, v_i_376_, v_entries_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_379_, lean_object* v_depth_380_, lean_object* v_keys_381_, lean_object* v_vals_382_, lean_object* v_heq_383_, lean_object* v_i_384_, lean_object* v_entries_385_){
_start:
{
size_t v_depth_boxed_386_; lean_object* v_res_387_; 
v_depth_boxed_386_ = lean_unbox_usize(v_depth_380_);
lean_dec(v_depth_380_);
v_res_387_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_379_, v_depth_boxed_386_, v_keys_381_, v_vals_382_, v_heq_383_, v_i_384_, v_entries_385_);
lean_dec_ref(v_vals_382_);
lean_dec_ref(v_keys_381_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_388_, lean_object* v_x_389_, lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v_x_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_389_, v_x_390_, v_x_391_, v_x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon(lean_object* v_rule_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_expr_402_; lean_object* v_pattern_403_; lean_object* v_resultPos_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_428_; 
v_expr_402_ = lean_ctor_get(v_rule_394_, 0);
v_pattern_403_ = lean_ctor_get(v_rule_394_, 1);
v_resultPos_404_ = lean_ctor_get(v_rule_394_, 2);
v_isSharedCheck_428_ = !lean_is_exclusive(v_rule_394_);
if (v_isSharedCheck_428_ == 0)
{
v___x_406_ = v_rule_394_;
v_isShared_407_ = v_isSharedCheck_428_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_resultPos_404_);
lean_inc(v_pattern_403_);
lean_inc(v_expr_402_);
lean_dec(v_rule_394_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_428_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Meta_Sym_Pattern_shareCommon(v_pattern_403_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_419_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_419_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_419_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_419_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v_a_409_);
v___x_414_ = v___x_406_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_expr_402_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_a_409_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_resultPos_404_);
v___x_414_ = v_reuseFailAlloc_418_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_416_; 
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_414_);
v___x_416_ = v___x_411_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_del_object(v___x_406_);
lean_dec(v_resultPos_404_);
lean_dec_ref(v_expr_402_);
v_a_420_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_408_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_408_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon___boxed(lean_object* v_rule_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_rule_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(lean_object* v___y_438_, lean_object* v_mctx_439_, lean_object* v_cache_440_, lean_object* v_a_x3f_441_){
_start:
{
lean_object* v___x_443_; lean_object* v_zetaDeltaFVarIds_444_; lean_object* v_postponed_445_; lean_object* v_diag_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_456_; 
v___x_443_ = lean_st_ref_take(v___y_438_);
v_zetaDeltaFVarIds_444_ = lean_ctor_get(v___x_443_, 2);
v_postponed_445_ = lean_ctor_get(v___x_443_, 3);
v_diag_446_ = lean_ctor_get(v___x_443_, 4);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; lean_object* v_unused_458_; 
v_unused_457_ = lean_ctor_get(v___x_443_, 1);
lean_dec(v_unused_457_);
v_unused_458_ = lean_ctor_get(v___x_443_, 0);
lean_dec(v_unused_458_);
v___x_448_ = v___x_443_;
v_isShared_449_ = v_isSharedCheck_456_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_diag_446_);
lean_inc(v_postponed_445_);
lean_inc(v_zetaDeltaFVarIds_444_);
lean_dec(v___x_443_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_456_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 1, v_cache_440_);
lean_ctor_set(v___x_448_, 0, v_mctx_439_);
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_mctx_439_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_cache_440_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_zetaDeltaFVarIds_444_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_postponed_445_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v_diag_446_);
v___x_451_ = v_reuseFailAlloc_455_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_st_ref_put(v___y_438_, v___x_451_);
v___x_453_ = lean_box(0);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
return v___x_454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0___boxed(lean_object* v___y_459_, lean_object* v_mctx_460_, lean_object* v_cache_461_, lean_object* v_a_x3f_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_459_, v_mctx_460_, v_cache_461_, v_a_x3f_462_);
lean_dec(v_a_x3f_462_);
lean_dec(v___y_459_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(lean_object* v_x_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v_mctx_480_; lean_object* v_cache_481_; lean_object* v___x_482_; 
v___x_478_ = lean_st_ref_get(v___y_474_);
v___x_479_ = lean_st_ref_get(v___y_474_);
v_mctx_480_ = lean_ctor_get(v___x_478_, 0);
lean_inc_ref(v_mctx_480_);
lean_dec(v___x_478_);
v_cache_481_ = lean_ctor_get(v___x_479_, 1);
lean_inc_ref(v_cache_481_);
lean_dec(v___x_479_);
lean_inc(v___y_476_);
lean_inc_ref(v___y_475_);
lean_inc(v___y_474_);
lean_inc_ref(v___y_473_);
lean_inc(v___y_472_);
lean_inc_ref(v___y_471_);
lean_inc(v___y_470_);
lean_inc_ref(v___y_469_);
lean_inc(v___y_468_);
lean_inc(v___y_467_);
lean_inc_ref(v___y_466_);
v___x_482_ = lean_apply_12(v_x_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, lean_box(0));
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_499_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_499_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_499_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_499_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
lean_inc(v_a_483_);
if (v_isShared_486_ == 0)
{
lean_ctor_set_tag(v___x_485_, 1);
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_498_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
v___x_489_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_474_, v_mctx_480_, v_cache_481_, v___x_488_);
lean_dec_ref(v___x_488_);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; 
v_unused_497_ = lean_ctor_get(v___x_489_, 0);
lean_dec(v_unused_497_);
v___x_491_ = v___x_489_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_dec(v___x_489_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v_a_483_);
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_483_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
v_a_500_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_482_, 1);
v___x_501_ = lean_box(0);
v___x_502_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_474_, v_mctx_480_, v_cache_481_, v___x_501_);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; 
v_unused_510_ = lean_ctor_get(v___x_502_, 0);
lean_dec(v_unused_510_);
v___x_504_ = v___x_502_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_dec(v___x_502_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set_tag(v___x_504_, 1);
lean_ctor_set(v___x_504_, 0, v_a_500_);
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_500_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___boxed(lean_object* v_x_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(lean_object* v_00_u03b1_525_, lean_object* v_x_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___boxed(lean_object* v_00_u03b1_540_, lean_object* v_x_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(v_00_u03b1_540_, v_x_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(lean_object* v_a_555_, lean_object* v___x_556_, lean_object* v_rule_557_, uint8_t v___x_558_, uint8_t v_debug_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_555_, v___x_556_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v___x_574_ = l_Lean_Expr_mvarId_x21(v_a_573_);
lean_dec(v_a_573_);
v___x_575_ = l_Lean_Meta_Sym_BackwardRule_apply(v___x_574_, v_rule_557_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_588_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_588_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_588_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_588_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
if (lean_obj_tag(v_a_576_) == 0)
{
lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_580_ = lean_box(v___x_558_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_580_);
v___x_582_ = v___x_578_;
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
else
{
lean_object* v___x_584_; lean_object* v___x_586_; 
lean_dec_ref_known(v_a_576_, 1);
v___x_584_ = lean_box(v_debug_559_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_584_);
v___x_586_ = v___x_578_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
v_a_589_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_575_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_575_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec_ref(v_rule_557_);
v_a_597_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_572_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_572_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed(lean_object** _args){
lean_object* v_a_605_ = _args[0];
lean_object* v___x_606_ = _args[1];
lean_object* v_rule_607_ = _args[2];
lean_object* v___x_608_ = _args[3];
lean_object* v_debug_609_ = _args[4];
lean_object* v___y_610_ = _args[5];
lean_object* v___y_611_ = _args[6];
lean_object* v___y_612_ = _args[7];
lean_object* v___y_613_ = _args[8];
lean_object* v___y_614_ = _args[9];
lean_object* v___y_615_ = _args[10];
lean_object* v___y_616_ = _args[11];
lean_object* v___y_617_ = _args[12];
lean_object* v___y_618_ = _args[13];
lean_object* v___y_619_ = _args[14];
lean_object* v___y_620_ = _args[15];
lean_object* v___y_621_ = _args[16];
_start:
{
uint8_t v___x_43892__boxed_622_; uint8_t v_debug_boxed_623_; lean_object* v_res_624_; 
v___x_43892__boxed_622_ = lean_unbox(v___x_608_);
v_debug_boxed_623_ = lean_unbox(v_debug_609_);
v_res_624_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(v_a_605_, v___x_606_, v_rule_607_, v___x_43892__boxed_622_, v_debug_boxed_623_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(lean_object* v_msgData_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; lean_object* v_env_632_; lean_object* v___x_633_; lean_object* v_mctx_634_; lean_object* v_lctx_635_; lean_object* v_options_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_631_ = lean_st_ref_get(v___y_629_);
v_env_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc_ref(v_env_632_);
lean_dec(v___x_631_);
v___x_633_ = lean_st_ref_get(v___y_627_);
v_mctx_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc_ref(v_mctx_634_);
lean_dec(v___x_633_);
v_lctx_635_ = lean_ctor_get(v___y_626_, 2);
v_options_636_ = lean_ctor_get(v___y_628_, 2);
lean_inc_ref(v_options_636_);
lean_inc_ref(v_lctx_635_);
v___x_637_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_637_, 0, v_env_632_);
lean_ctor_set(v___x_637_, 1, v_mctx_634_);
lean_ctor_set(v___x_637_, 2, v_lctx_635_);
lean_ctor_set(v___x_637_, 3, v_options_636_);
v___x_638_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v_msgData_625_);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1___boxed(lean_object* v_msgData_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(v_msgData_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(lean_object* v_msg_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_ref_653_; lean_object* v___x_654_; lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_663_; 
v_ref_653_ = lean_ctor_get(v___y_650_, 5);
v___x_654_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(v_msg_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_663_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
lean_inc(v_ref_653_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v_ref_653_);
lean_ctor_set(v___x_659_, 1, v_a_655_);
if (v_isShared_658_ == 0)
{
lean_ctor_set_tag(v___x_657_, 1);
lean_ctor_set(v___x_657_, 0, v___x_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg___boxed(lean_object* v_msg_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_670_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0));
v___x_673_ = l_Lean_stringToMessageData(v___x_672_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2));
v___x_676_ = l_Lean_stringToMessageData(v___x_675_);
return v___x_676_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4));
v___x_679_ = l_Lean_stringToMessageData(v___x_678_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6));
v___x_682_ = l_Lean_stringToMessageData(v___x_681_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8));
v___x_685_ = l_Lean_stringToMessageData(v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10));
v___x_688_ = l_Lean_stringToMessageData(v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object* v_rule_689_, lean_object* v_goal_690_, lean_object* v_ruleDesc_x3f_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v___x_704_; 
lean_inc_ref(v_rule_689_);
lean_inc(v_goal_690_);
v___x_704_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_690_, v_rule_689_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
if (lean_obj_tag(v_a_705_) == 0)
{
uint8_t v_debug_706_; 
v_debug_706_ = lean_ctor_get_uint8(v_a_692_, sizeof(void*)*5 + 3);
if (v_debug_706_ == 0)
{
lean_dec(v_ruleDesc_x3f_691_);
lean_dec(v_goal_690_);
lean_dec_ref(v_rule_689_);
return v___x_704_;
}
else
{
lean_object* v___x_707_; 
lean_dec_ref_known(v___x_704_, 1);
v___x_707_ = l_Lean_MVarId_getType(v_goal_690_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_709_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc_n(v_a_708_, 2);
lean_dec_ref_known(v___x_707_, 1);
v___x_709_ = l_Lean_Meta_Sym_unfoldReducible(v_a_708_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_772_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_772_ == 0)
{
v___x_712_ = v___x_709_;
v_isShared_713_ = v_isSharedCheck_772_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_772_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
uint8_t v___x_714_; 
v___x_714_ = lean_expr_eqv(v_a_710_, v_a_708_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___f_718_; lean_object* v___x_719_; 
lean_del_object(v___x_712_);
v___x_715_ = lean_box(0);
v___x_716_ = lean_box(v___x_714_);
v___x_717_ = lean_box(v_debug_706_);
lean_inc_ref(v_rule_689_);
lean_inc(v_a_710_);
v___f_718_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed), 17, 5);
lean_closure_set(v___f_718_, 0, v_a_710_);
lean_closure_set(v___f_718_, 1, v___x_715_);
lean_closure_set(v___f_718_, 2, v_rule_689_);
lean_closure_set(v___f_718_, 3, v___x_716_);
lean_closure_set(v___f_718_, 4, v___x_717_);
v___x_719_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v___f_718_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_760_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_760_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_760_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_760_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___y_725_; uint8_t v___x_747_; 
v___x_747_ = lean_unbox(v_a_720_);
lean_dec(v_a_720_);
if (v___x_747_ == 0)
{
lean_object* v___x_749_; 
lean_dec(v_a_710_);
lean_dec(v_a_708_);
lean_dec(v_ruleDesc_x3f_691_);
lean_dec_ref(v_rule_689_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v_a_705_);
v___x_749_ = v___x_722_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_705_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
else
{
lean_del_object(v___x_722_);
if (lean_obj_tag(v_ruleDesc_x3f_691_) == 0)
{
lean_object* v_expr_751_; lean_object* v___x_752_; 
v_expr_751_ = lean_ctor_get(v_rule_689_, 0);
lean_inc_ref(v_expr_751_);
lean_dec_ref(v_rule_689_);
v___x_752_ = l_Lean_Expr_getAppFn(v_expr_751_);
lean_dec_ref(v_expr_751_);
if (lean_obj_tag(v___x_752_) == 4)
{
lean_object* v_declName_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_declName_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_declName_753_);
lean_dec_ref_known(v___x_752_, 2);
v___x_754_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9);
v___x_755_ = l_Lean_MessageData_ofConstName(v_declName_753_, v___x_714_);
v___x_756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
lean_ctor_set(v___x_757_, 1, v___x_754_);
v___y_725_ = v___x_757_;
goto v___jp_724_;
}
else
{
lean_object* v___x_758_; 
lean_dec_ref(v___x_752_);
v___x_758_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11);
v___y_725_ = v___x_758_;
goto v___jp_724_;
}
}
else
{
lean_object* v_val_759_; 
lean_dec_ref(v_rule_689_);
v_val_759_ = lean_ctor_get(v_ruleDesc_x3f_691_, 0);
lean_inc(v_val_759_);
lean_dec_ref_known(v_ruleDesc_x3f_691_, 1);
v___y_725_ = v_val_759_;
goto v___jp_724_;
}
}
v___jp_724_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
v___x_726_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1);
v___x_727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___y_725_);
v___x_728_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3);
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = l_Lean_indentExpr(v_a_708_);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = l_Lean_indentExpr(v_a_710_);
v___x_735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7, &l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7);
v___x_737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_737_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
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
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec(v_a_710_);
lean_dec(v_a_708_);
lean_dec(v_ruleDesc_x3f_691_);
lean_dec_ref(v_rule_689_);
v_a_761_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_719_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_719_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
else
{
lean_object* v___x_770_; 
lean_dec(v_a_710_);
lean_dec(v_a_708_);
lean_dec(v_ruleDesc_x3f_691_);
lean_dec_ref(v_rule_689_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v_a_705_);
v___x_770_ = v___x_712_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_705_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec(v_a_708_);
lean_dec(v_ruleDesc_x3f_691_);
lean_dec_ref(v_rule_689_);
v_a_773_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_709_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_709_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
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
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec(v_ruleDesc_x3f_691_);
lean_dec_ref(v_rule_689_);
v_a_781_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_707_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_707_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_a_705_, 1);
lean_dec(v_ruleDesc_x3f_691_);
lean_dec(v_goal_690_);
lean_dec_ref(v_rule_689_);
return v___x_704_;
}
}
else
{
lean_dec(v_ruleDesc_x3f_691_);
lean_dec(v_goal_690_);
lean_dec_ref(v_rule_689_);
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked___boxed(lean_object* v_rule_789_, lean_object* v_goal_790_, lean_object* v_ruleDesc_x3f_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_789_, v_goal_790_, v_ruleDesc_x3f_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(lean_object* v_00_u03b1_805_, lean_object* v_msg_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_806_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___boxed(lean_object* v_00_u03b1_820_, lean_object* v_msg_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(v_00_u03b1_820_, v_msg_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(lean_object* v_goal_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
uint8_t v_internalize_847_; 
v_internalize_847_ = lean_ctor_get_uint8(v_a_836_, sizeof(void*)*5 + 4);
if (v_internalize_847_ == 0)
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v_goal_835_);
return v___x_848_;
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_box(0);
v___x_850_ = l_Lean_Meta_Grind_processHypotheses(v_goal_835_, v___x_849_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg___boxed(lean_object* v_goal_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses(lean_object* v_goal_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_864_, v_a_865_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___boxed(lean_object* v_goal_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Elab_Tactic_VCGen_processHypotheses(v_goal_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_introsHygienic_collectBinders(lean_object* v_type_892_, lean_object* v_acc_893_){
_start:
{
switch(lean_obj_tag(v_type_892_))
{
case 7:
{
lean_object* v_binderName_894_; lean_object* v_body_895_; lean_object* v___x_896_; 
v_binderName_894_ = lean_ctor_get(v_type_892_, 0);
lean_inc(v_binderName_894_);
v_body_895_ = lean_ctor_get(v_type_892_, 2);
lean_inc_ref(v_body_895_);
lean_dec_ref_known(v_type_892_, 3);
v___x_896_ = lean_array_push(v_acc_893_, v_binderName_894_);
v_type_892_ = v_body_895_;
v_acc_893_ = v___x_896_;
goto _start;
}
case 8:
{
lean_object* v_declName_898_; lean_object* v_body_899_; lean_object* v___x_900_; 
v_declName_898_ = lean_ctor_get(v_type_892_, 0);
lean_inc(v_declName_898_);
v_body_899_ = lean_ctor_get(v_type_892_, 3);
lean_inc_ref(v_body_899_);
lean_dec_ref_known(v_type_892_, 4);
v___x_900_ = lean_array_push(v_acc_893_, v_declName_898_);
v_type_892_ = v_body_899_;
v_acc_893_ = v___x_900_;
goto _start;
}
default: 
{
lean_dec_ref(v_type_892_);
return v_acc_893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1___redArg___lam__0(lean_object* v_x_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v___x_915_; 
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
lean_inc(v___y_905_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
v___x_915_ = lean_apply_12(v_x_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, lean_box(0));
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1___redArg___lam__0___boxed(lean_object* v_x_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1___redArg___lam__0(v_x_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1___redArg(lean_object* v_mvarId_930_, lean_object* v_x_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___f_944_; lean_object* v___x_945_; 
lean_inc(v___y_938_);
lean_inc_ref(v___y_937_);
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
lean_inc(v___y_934_);
lean_inc(v___y_933_);
lean_inc_ref(v___y_932_);
v___f_944_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_944_, 0, v_x_931_);
lean_closure_set(v___f_944_, 1, v___y_932_);
lean_closure_set(v___f_944_, 2, v___y_933_);
lean_closure_set(v___f_944_, 3, v___y_934_);
lean_closure_set(v___f_944_, 4, v___y_935_);
lean_closure_set(v___f_944_, 5, v___y_936_);
lean_closure_set(v___f_944_, 6, v___y_937_);
lean_closure_set(v___f_944_, 7, v___y_938_);
v___x_945_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_930_, v___f_944_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_945_) == 0)
{
return v___x_945_;
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1___redArg___boxed(lean_object* v_mvarId_954_, lean_object* v_x_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1___redArg(v_mvarId_954_, v_x_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1(lean_object* v_00_u03b1_969_, lean_object* v_mvarId_970_, lean_object* v_x_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1___redArg(v_mvarId_970_, v_x_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1___boxed(lean_object* v_00_u03b1_985_, lean_object* v_mvarId_986_, lean_object* v_x_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1(v_00_u03b1_985_, v_mvarId_986_, v_x_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__0___redArg(lean_object* v_upperBound_1001_, lean_object* v_overrides_1002_, lean_object* v_binderNames_1003_, lean_object* v_a_1004_, lean_object* v_b_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___y_1011_; uint8_t v___x_1026_; 
v___x_1026_ = lean_nat_dec_lt(v_a_1004_, v_upperBound_1001_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; 
lean_dec(v_a_1004_);
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v_b_1005_);
return v___x_1027_;
}
else
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_array_get_size(v_overrides_1002_);
v___x_1029_ = lean_nat_dec_lt(v_a_1004_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_array_fget_borrowed(v_binderNames_1003_, v_a_1004_);
lean_inc(v___x_1030_);
v___y_1011_ = v___x_1030_;
goto v___jp_1010_;
}
else
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_array_fget_borrowed(v_overrides_1002_, v_a_1004_);
lean_inc(v___x_1031_);
v___y_1011_ = v___x_1031_;
goto v___jp_1010_;
}
}
v___jp_1010_:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v___y_1011_, v___y_1006_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
v___x_1014_ = lean_array_push(v_b_1005_, v_a_1013_);
v___x_1015_ = lean_unsigned_to_nat(1u);
v___x_1016_ = lean_nat_add(v_a_1004_, v___x_1015_);
lean_dec(v_a_1004_);
v_a_1004_ = v___x_1016_;
v_b_1005_ = v___x_1014_;
goto _start;
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v_b_1005_);
lean_dec(v_a_1004_);
v_a_1018_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1012_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1012_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__0___redArg___boxed(lean_object* v_upperBound_1032_, lean_object* v_overrides_1033_, lean_object* v_binderNames_1034_, lean_object* v_a_1035_, lean_object* v_b_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__0___redArg(v_upperBound_1032_, v_overrides_1033_, v_binderNames_1034_, v_a_1035_, v_b_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec_ref(v_binderNames_1034_);
lean_dec_ref(v_overrides_1033_);
lean_dec(v_upperBound_1032_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic___lam__0(lean_object* v_goal_1044_, lean_object* v_overrides_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v___x_1058_; 
lean_inc(v_goal_1044_);
v___x_1058_ = l_Lean_MVarId_getType(v_goal_1044_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1103_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1103_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1103_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v_names_1064_; lean_object* v_binderNames_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1063_ = lean_unsigned_to_nat(0u);
v_names_1064_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsHygienic___lam__0___closed__0));
v_binderNames_1065_ = l___private_Lean_Elab_Tactic_VCGen_Util_0__Lean_Elab_Tactic_VCGen_introsHygienic_collectBinders(v_a_1059_, v_names_1064_);
v___x_1066_ = lean_array_get_size(v_binderNames_1065_);
v___x_1067_ = lean_nat_dec_eq(v___x_1066_, v___x_1063_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
lean_del_object(v___x_1061_);
v___x_1068_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__0___redArg(v___x_1066_, v_overrides_1045_, v_binderNames_1065_, v___x_1063_, v_names_1064_, v___y_1053_, v___y_1055_, v___y_1056_);
lean_dec_ref(v_binderNames_1065_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; uint8_t v___x_1070_; lean_object* v___x_1071_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = 1;
lean_inc(v_goal_1044_);
v___x_1071_ = l_Lean_Meta_Sym_intros(v_goal_1044_, v_a_1069_, v___x_1070_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1083_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1083_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1083_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
if (lean_obj_tag(v_a_1072_) == 1)
{
lean_object* v_mvarId_1076_; lean_object* v___x_1078_; 
lean_dec(v_goal_1044_);
v_mvarId_1076_ = lean_ctor_get(v_a_1072_, 1);
lean_inc(v_mvarId_1076_);
lean_dec_ref_known(v_a_1072_, 2);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v_mvarId_1076_);
v___x_1078_ = v___x_1074_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_mvarId_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
else
{
lean_object* v___x_1081_; 
lean_dec(v_a_1072_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v_goal_1044_);
v___x_1081_ = v___x_1074_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_goal_1044_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec(v_goal_1044_);
v_a_1084_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1071_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1071_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec(v_goal_1044_);
v_a_1092_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1068_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1068_);
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
else
{
lean_object* v___x_1101_; 
lean_dec_ref(v_binderNames_1065_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v_goal_1044_);
v___x_1101_ = v___x_1061_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_goal_1044_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec(v_goal_1044_);
v_a_1104_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1058_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1058_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic___lam__0___boxed(lean_object* v_goal_1112_, lean_object* v_overrides_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_Elab_Tactic_VCGen_introsHygienic___lam__0(v_goal_1112_, v_overrides_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec_ref(v_overrides_1113_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic(lean_object* v_goal_1127_, lean_object* v_overrides_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v___f_1141_; lean_object* v___x_1142_; 
lean_inc(v_goal_1127_);
v___f_1141_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_introsHygienic___lam__0___boxed), 14, 2);
lean_closure_set(v___f_1141_, 0, v_goal_1127_);
lean_closure_set(v___f_1141_, 1, v_overrides_1128_);
v___x_1142_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1___redArg(v_goal_1127_, v___f_1141_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic___boxed(lean_object* v_goal_1143_, lean_object* v_overrides_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Elab_Tactic_VCGen_introsHygienic(v_goal_1143_, v_overrides_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__0(lean_object* v_upperBound_1158_, lean_object* v_overrides_1159_, lean_object* v_binderNames_1160_, lean_object* v_inst_1161_, lean_object* v_R_1162_, lean_object* v_a_1163_, lean_object* v_b_1164_, lean_object* v_c_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__0___redArg(v_upperBound_1158_, v_overrides_1159_, v_binderNames_1160_, v_a_1163_, v_b_1164_, v___y_1173_, v___y_1175_, v___y_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_1179_ = _args[0];
lean_object* v_overrides_1180_ = _args[1];
lean_object* v_binderNames_1181_ = _args[2];
lean_object* v_inst_1182_ = _args[3];
lean_object* v_R_1183_ = _args[4];
lean_object* v_a_1184_ = _args[5];
lean_object* v_b_1185_ = _args[6];
lean_object* v_c_1186_ = _args[7];
lean_object* v___y_1187_ = _args[8];
lean_object* v___y_1188_ = _args[9];
lean_object* v___y_1189_ = _args[10];
lean_object* v___y_1190_ = _args[11];
lean_object* v___y_1191_ = _args[12];
lean_object* v___y_1192_ = _args[13];
lean_object* v___y_1193_ = _args[14];
lean_object* v___y_1194_ = _args[15];
lean_object* v___y_1195_ = _args[16];
lean_object* v___y_1196_ = _args[17];
lean_object* v___y_1197_ = _args[18];
lean_object* v___y_1198_ = _args[19];
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__0(v_upperBound_1179_, v_overrides_1180_, v_binderNames_1181_, v_inst_1182_, v_R_1183_, v_a_1184_, v_b_1185_, v_c_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v_binderNames_1181_);
lean_dec_ref(v_overrides_1180_);
lean_dec(v_upperBound_1179_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(lean_object* v_goal_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_hypSimpMethods_1214_; 
v_hypSimpMethods_1214_ = lean_ctor_get(v_a_1205_, 2);
if (lean_obj_tag(v_hypSimpMethods_1214_) == 1)
{
lean_object* v_val_1215_; lean_object* v___x_1216_; 
v_val_1215_ = lean_ctor_get(v_hypSimpMethods_1214_, 0);
lean_inc(v_goal_1204_);
v___x_1216_ = l_Lean_MVarId_getType(v_goal_1204_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1218_; lean_object* v_post_1219_; lean_object* v_simpState_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
v___x_1218_ = lean_st_ref_get(v_a_1206_);
v_post_1219_ = lean_ctor_get(v_val_1215_, 1);
v_simpState_1220_ = lean_ctor_get(v___x_1218_, 7);
lean_inc_ref(v_simpState_1220_);
lean_dec(v___x_1218_);
v___x_1221_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__0));
lean_inc_ref(v_post_1219_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v_post_1219_);
v___x_1223_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_1223_, 0, v_a_1217_);
v___x_1224_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___closed__1));
v___x_1225_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_1223_, v___x_1222_, v___x_1224_, v_simpState_1220_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v_fst_1227_; lean_object* v_snd_1228_; lean_object* v___x_1229_; lean_object* v_specBackwardRuleCache_1230_; lean_object* v_splitBackwardRuleCache_1231_; lean_object* v_latticeBackwardRuleCache_1232_; lean_object* v_frameBackwardRuleCache_1233_; lean_object* v_frameDB_1234_; lean_object* v_invariants_1235_; lean_object* v_vcs_1236_; lean_object* v_fuel_1237_; lean_object* v_inlineHandledInvariants_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1247_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v_fst_1227_ = lean_ctor_get(v_a_1226_, 0);
lean_inc(v_fst_1227_);
v_snd_1228_ = lean_ctor_get(v_a_1226_, 1);
lean_inc(v_snd_1228_);
lean_dec(v_a_1226_);
v___x_1229_ = lean_st_ref_take(v_a_1206_);
v_specBackwardRuleCache_1230_ = lean_ctor_get(v___x_1229_, 0);
v_splitBackwardRuleCache_1231_ = lean_ctor_get(v___x_1229_, 1);
v_latticeBackwardRuleCache_1232_ = lean_ctor_get(v___x_1229_, 2);
v_frameBackwardRuleCache_1233_ = lean_ctor_get(v___x_1229_, 3);
v_frameDB_1234_ = lean_ctor_get(v___x_1229_, 4);
v_invariants_1235_ = lean_ctor_get(v___x_1229_, 5);
v_vcs_1236_ = lean_ctor_get(v___x_1229_, 6);
v_fuel_1237_ = lean_ctor_get(v___x_1229_, 8);
v_inlineHandledInvariants_1238_ = lean_ctor_get(v___x_1229_, 9);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; 
v_unused_1248_ = lean_ctor_get(v___x_1229_, 7);
lean_dec(v_unused_1248_);
v___x_1240_ = v___x_1229_;
v_isShared_1241_ = v_isSharedCheck_1247_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_inlineHandledInvariants_1238_);
lean_inc(v_fuel_1237_);
lean_inc(v_vcs_1236_);
lean_inc(v_invariants_1235_);
lean_inc(v_frameDB_1234_);
lean_inc(v_frameBackwardRuleCache_1233_);
lean_inc(v_latticeBackwardRuleCache_1232_);
lean_inc(v_splitBackwardRuleCache_1231_);
lean_inc(v_specBackwardRuleCache_1230_);
lean_dec(v___x_1229_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1247_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 7, v_snd_1228_);
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_specBackwardRuleCache_1230_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_splitBackwardRuleCache_1231_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_latticeBackwardRuleCache_1232_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v_frameBackwardRuleCache_1233_);
lean_ctor_set(v_reuseFailAlloc_1246_, 4, v_frameDB_1234_);
lean_ctor_set(v_reuseFailAlloc_1246_, 5, v_invariants_1235_);
lean_ctor_set(v_reuseFailAlloc_1246_, 6, v_vcs_1236_);
lean_ctor_set(v_reuseFailAlloc_1246_, 7, v_snd_1228_);
lean_ctor_set(v_reuseFailAlloc_1246_, 8, v_fuel_1237_);
lean_ctor_set(v_reuseFailAlloc_1246_, 9, v_inlineHandledInvariants_1238_);
v___x_1243_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_st_ref_put(v_a_1206_, v___x_1243_);
v___x_1245_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_fst_1227_, v_goal_1204_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
return v___x_1245_;
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v_goal_1204_);
v_a_1249_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1225_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1225_);
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
lean_dec(v_goal_1204_);
v_a_1257_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1216_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1216_);
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
lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec(v_goal_1204_);
v___x_1265_ = lean_box(0);
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
return v___x_1266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg___boxed(lean_object* v_goal_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(v_goal_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope(lean_object* v_goal_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(v_goal_1278_, v_a_1279_, v_a_1280_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___boxed(lean_object* v_goal_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope(v_goal_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
return v_res_1305_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__11));
v___x_1317_ = l_Lean_stringToMessageData(v___x_1316_);
return v___x_1317_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9(void){
_start:
{
uint8_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = 0;
v___x_1324_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__8));
v___x_1325_ = l_Lean_MessageData_ofConstName(v___x_1324_, v___x_1323_);
return v___x_1325_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__5));
v___x_1328_ = l_Lean_stringToMessageData(v___x_1327_);
return v___x_1328_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__9);
v___x_1330_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__6);
v___x_1331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
lean_ctor_set(v___x_1331_, 1, v___x_1329_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1332_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__12, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__12);
v___x_1333_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__10);
v___x_1334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v___x_1332_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0(lean_object* v_goal_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___x_1348_; 
lean_inc(v_goal_1335_);
v___x_1348_ = l_Lean_MVarId_getType(v_goal_1335_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1426_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1426_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1426_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1358_; uint8_t v___x_1359_; 
lean_inc(v_a_1349_);
v___x_1358_ = l_Lean_Expr_cleanupAnnotations(v_a_1349_);
v___x_1359_ = l_Lean_Expr_isApp(v___x_1358_);
if (v___x_1359_ == 0)
{
lean_dec_ref(v___x_1358_);
lean_dec(v_a_1349_);
lean_dec(v_goal_1335_);
goto v___jp_1353_;
}
else
{
lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1360_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1358_);
v___x_1361_ = l_Lean_Expr_isApp(v___x_1360_);
if (v___x_1361_ == 0)
{
lean_dec_ref(v___x_1360_);
lean_dec(v_a_1349_);
lean_dec(v_goal_1335_);
goto v___jp_1353_;
}
else
{
lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1362_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1360_);
v___x_1363_ = l_Lean_Expr_isApp(v___x_1362_);
if (v___x_1363_ == 0)
{
lean_dec_ref(v___x_1362_);
lean_dec(v_a_1349_);
lean_dec(v_goal_1335_);
goto v___jp_1353_;
}
else
{
lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1364_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1362_);
v___x_1365_ = l_Lean_Expr_isApp(v___x_1364_);
if (v___x_1365_ == 0)
{
lean_dec_ref(v___x_1364_);
lean_dec(v_a_1349_);
lean_dec(v_goal_1335_);
goto v___jp_1353_;
}
else
{
lean_object* v_arg_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v_arg_1366_ = lean_ctor_get(v___x_1364_, 1);
lean_inc_ref(v_arg_1366_);
v___x_1367_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1364_);
v___x_1368_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__4));
v___x_1369_ = l_Lean_Expr_isConstOf(v___x_1367_, v___x_1368_);
lean_dec_ref(v___x_1367_);
if (v___x_1369_ == 0)
{
lean_dec_ref(v_arg_1366_);
lean_dec(v_a_1349_);
lean_dec(v_goal_1335_);
goto v___jp_1353_;
}
else
{
uint8_t v___x_1370_; 
lean_del_object(v___x_1351_);
v___x_1370_ = l_Lean_Expr_isForall(v_arg_1366_);
lean_dec_ref(v_arg_1366_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec(v_a_1349_);
lean_dec(v_goal_1335_);
v___x_1371_ = lean_box(0);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
return v___x_1372_;
}
else
{
lean_object* v_backwardRules_1373_; lean_object* v_stateArgIntro_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v_backwardRules_1373_ = lean_ctor_get(v___y_1336_, 0);
v_stateArgIntro_1374_ = lean_ctor_get(v_backwardRules_1373_, 1);
v___x_1375_ = lean_box(0);
lean_inc_ref(v_stateArgIntro_1374_);
v___x_1376_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_stateArgIntro_1374_, v_goal_1335_, v___x_1375_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
if (lean_obj_tag(v_a_1377_) == 1)
{
lean_object* v_mvarIds_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1417_; 
v_mvarIds_1387_ = lean_ctor_get(v_a_1377_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_a_1377_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1389_ = v_a_1377_;
v_isShared_1390_ = v_isSharedCheck_1417_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_mvarIds_1387_);
lean_dec(v_a_1377_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1417_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
if (lean_obj_tag(v_mvarIds_1387_) == 1)
{
lean_object* v_tail_1391_; 
v_tail_1391_ = lean_ctor_get(v_mvarIds_1387_, 1);
if (lean_obj_tag(v_tail_1391_) == 0)
{
lean_object* v_head_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_dec(v_a_1349_);
v_head_1392_ = lean_ctor_get(v_mvarIds_1387_, 0);
lean_inc(v_head_1392_);
lean_dec_ref_known(v_mvarIds_1387_, 2);
v___x_1393_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsHygienic___lam__0___closed__0));
v___x_1394_ = l_Lean_Elab_Tactic_VCGen_introsHygienic(v_head_1392_, v___x_1393_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1396_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc_n(v_a_1395_, 2);
lean_dec_ref_known(v___x_1394_, 1);
v___x_1396_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs(v_a_1395_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
if (lean_obj_tag(v_a_1397_) == 0)
{
lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1407_; 
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; 
v_unused_1408_ = lean_ctor_get(v___x_1396_, 0);
lean_dec(v_unused_1408_);
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1407_;
goto v_resetjp_1398_;
}
else
{
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1407_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v_a_1395_);
v___x_1402_ = v___x_1389_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1395_);
v___x_1402_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1404_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1402_);
v___x_1404_ = v___x_1399_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_1397_, 1);
lean_dec(v_a_1395_);
lean_del_object(v___x_1389_);
return v___x_1396_;
}
}
else
{
lean_dec(v_a_1395_);
lean_del_object(v___x_1389_);
return v___x_1396_;
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_del_object(v___x_1389_);
v_a_1409_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1394_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1394_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_1387_, 2);
lean_del_object(v___x_1389_);
v___y_1379_ = v___y_1343_;
v___y_1380_ = v___y_1344_;
v___y_1381_ = v___y_1345_;
v___y_1382_ = v___y_1346_;
goto v___jp_1378_;
}
}
else
{
lean_del_object(v___x_1389_);
lean_dec(v_mvarIds_1387_);
v___y_1379_ = v___y_1343_;
v___y_1380_ = v___y_1344_;
v___y_1381_ = v___y_1345_;
v___y_1382_ = v___y_1346_;
goto v___jp_1378_;
}
}
}
else
{
lean_dec(v_a_1377_);
v___y_1379_ = v___y_1343_;
v___y_1380_ = v___y_1344_;
v___y_1381_ = v___y_1345_;
v___y_1382_ = v___y_1346_;
goto v___jp_1378_;
}
v___jp_1378_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1383_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13, &l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13_once, _init_l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___closed__13);
v___x_1384_ = l_Lean_indentExpr(v_a_1349_);
v___x_1385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1383_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
v___x_1386_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_1385_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
return v___x_1386_;
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v_a_1349_);
v_a_1418_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1376_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1376_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
}
}
}
v___jp_1353_:
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1354_ = lean_box(0);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1354_);
v___x_1356_ = v___x_1351_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec(v_goal_1335_);
v_a_1427_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1348_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1348_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___boxed(lean_object* v_goal_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0(v_goal_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs(lean_object* v_goal_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v___f_1462_; lean_object* v___x_1463_; 
lean_inc(v_goal_1449_);
v___f_1462_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_introsExcessArgs___lam__0___boxed), 13, 1);
lean_closure_set(v___f_1462_, 0, v_goal_1449_);
v___x_1463_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1___redArg(v_goal_1449_, v___f_1462_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs___boxed(lean_object* v_goal_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs(v_goal_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__0___redArg(lean_object* v_e_1478_, lean_object* v___y_1479_){
_start:
{
uint8_t v___x_1481_; 
v___x_1481_ = l_Lean_Expr_hasMVar(v_e_1478_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v_e_1478_);
return v___x_1482_;
}
else
{
lean_object* v___x_1483_; lean_object* v_mctx_1484_; lean_object* v___x_1485_; lean_object* v_fst_1486_; lean_object* v_snd_1487_; lean_object* v___x_1488_; lean_object* v_cache_1489_; lean_object* v_zetaDeltaFVarIds_1490_; lean_object* v_postponed_1491_; lean_object* v_diag_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1501_; 
v___x_1483_ = lean_st_ref_get(v___y_1479_);
v_mctx_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc_ref(v_mctx_1484_);
lean_dec(v___x_1483_);
v___x_1485_ = l_Lean_instantiateMVarsCore(v_mctx_1484_, v_e_1478_);
v_fst_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_fst_1486_);
v_snd_1487_ = lean_ctor_get(v___x_1485_, 1);
lean_inc(v_snd_1487_);
lean_dec_ref(v___x_1485_);
v___x_1488_ = lean_st_ref_take(v___y_1479_);
v_cache_1489_ = lean_ctor_get(v___x_1488_, 1);
v_zetaDeltaFVarIds_1490_ = lean_ctor_get(v___x_1488_, 2);
v_postponed_1491_ = lean_ctor_get(v___x_1488_, 3);
v_diag_1492_ = lean_ctor_get(v___x_1488_, 4);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v___x_1488_, 0);
lean_dec(v_unused_1502_);
v___x_1494_ = v___x_1488_;
v_isShared_1495_ = v_isSharedCheck_1501_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_diag_1492_);
lean_inc(v_postponed_1491_);
lean_inc(v_zetaDeltaFVarIds_1490_);
lean_inc(v_cache_1489_);
lean_dec(v___x_1488_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1501_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v_snd_1487_);
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_snd_1487_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_cache_1489_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_zetaDeltaFVarIds_1490_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_postponed_1491_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_diag_1492_);
v___x_1497_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = lean_st_ref_put(v___y_1479_, v___x_1497_);
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v_fst_1486_);
return v___x_1499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__0___redArg___boxed(lean_object* v_e_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__0___redArg(v_e_1503_, v___y_1504_);
lean_dec(v___y_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__0(lean_object* v_e_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__0___redArg(v_e_1507_, v___y_1516_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__0___boxed(lean_object* v_e_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__0(v_e_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__1___redArg(lean_object* v_mvarId_1535_, lean_object* v_val_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; lean_object* v_mctx_1540_; lean_object* v_cache_1541_; lean_object* v_zetaDeltaFVarIds_1542_; lean_object* v_postponed_1543_; lean_object* v_diag_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1573_; 
v___x_1539_ = lean_st_ref_take(v___y_1537_);
v_mctx_1540_ = lean_ctor_get(v___x_1539_, 0);
v_cache_1541_ = lean_ctor_get(v___x_1539_, 1);
v_zetaDeltaFVarIds_1542_ = lean_ctor_get(v___x_1539_, 2);
v_postponed_1543_ = lean_ctor_get(v___x_1539_, 3);
v_diag_1544_ = lean_ctor_get(v___x_1539_, 4);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1546_ = v___x_1539_;
v_isShared_1547_ = v_isSharedCheck_1573_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_diag_1544_);
lean_inc(v_postponed_1543_);
lean_inc(v_zetaDeltaFVarIds_1542_);
lean_inc(v_cache_1541_);
lean_inc(v_mctx_1540_);
lean_dec(v___x_1539_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1573_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v_depth_1548_; lean_object* v_levelAssignDepth_1549_; lean_object* v_lmvarCounter_1550_; lean_object* v_mvarCounter_1551_; lean_object* v_lDecls_1552_; lean_object* v_decls_1553_; lean_object* v_userNames_1554_; lean_object* v_lAssignment_1555_; lean_object* v_eAssignment_1556_; lean_object* v_dAssignment_1557_; lean_object* v_instanceTypedMVars_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1572_; 
v_depth_1548_ = lean_ctor_get(v_mctx_1540_, 0);
v_levelAssignDepth_1549_ = lean_ctor_get(v_mctx_1540_, 1);
v_lmvarCounter_1550_ = lean_ctor_get(v_mctx_1540_, 2);
v_mvarCounter_1551_ = lean_ctor_get(v_mctx_1540_, 3);
v_lDecls_1552_ = lean_ctor_get(v_mctx_1540_, 4);
v_decls_1553_ = lean_ctor_get(v_mctx_1540_, 5);
v_userNames_1554_ = lean_ctor_get(v_mctx_1540_, 6);
v_lAssignment_1555_ = lean_ctor_get(v_mctx_1540_, 7);
v_eAssignment_1556_ = lean_ctor_get(v_mctx_1540_, 8);
v_dAssignment_1557_ = lean_ctor_get(v_mctx_1540_, 9);
v_instanceTypedMVars_1558_ = lean_ctor_get(v_mctx_1540_, 10);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_mctx_1540_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1560_ = v_mctx_1540_;
v_isShared_1561_ = v_isSharedCheck_1572_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_instanceTypedMVars_1558_);
lean_inc(v_dAssignment_1557_);
lean_inc(v_eAssignment_1556_);
lean_inc(v_lAssignment_1555_);
lean_inc(v_userNames_1554_);
lean_inc(v_decls_1553_);
lean_inc(v_lDecls_1552_);
lean_inc(v_mvarCounter_1551_);
lean_inc(v_lmvarCounter_1550_);
lean_inc(v_levelAssignDepth_1549_);
lean_inc(v_depth_1548_);
lean_dec(v_mctx_1540_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1572_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1562_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetDefEqFast_spec__0_spec__0___redArg(v_eAssignment_1556_, v_mvarId_1535_, v_val_1536_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 8, v___x_1562_);
v___x_1564_ = v___x_1560_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_depth_1548_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_levelAssignDepth_1549_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_lmvarCounter_1550_);
lean_ctor_set(v_reuseFailAlloc_1571_, 3, v_mvarCounter_1551_);
lean_ctor_set(v_reuseFailAlloc_1571_, 4, v_lDecls_1552_);
lean_ctor_set(v_reuseFailAlloc_1571_, 5, v_decls_1553_);
lean_ctor_set(v_reuseFailAlloc_1571_, 6, v_userNames_1554_);
lean_ctor_set(v_reuseFailAlloc_1571_, 7, v_lAssignment_1555_);
lean_ctor_set(v_reuseFailAlloc_1571_, 8, v___x_1562_);
lean_ctor_set(v_reuseFailAlloc_1571_, 9, v_dAssignment_1557_);
lean_ctor_set(v_reuseFailAlloc_1571_, 10, v_instanceTypedMVars_1558_);
v___x_1564_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1566_; 
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1564_);
v___x_1566_ = v___x_1546_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_cache_1541_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_zetaDeltaFVarIds_1542_);
lean_ctor_set(v_reuseFailAlloc_1570_, 3, v_postponed_1543_);
lean_ctor_set(v_reuseFailAlloc_1570_, 4, v_diag_1544_);
v___x_1566_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = lean_st_ref_put(v___y_1537_, v___x_1566_);
v___x_1568_ = lean_box(0);
v___x_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
return v___x_1569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__1___redArg___boxed(lean_object* v_mvarId_1574_, lean_object* v_val_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__1___redArg(v_mvarId_1574_, v_val_1575_, v___y_1576_);
lean_dec(v___y_1576_);
return v_res_1578_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__8));
v___x_1594_ = l_Lean_stringToMessageData(v___x_1593_);
return v___x_1594_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__12));
v___x_1601_ = l_Lean_stringToMessageData(v___x_1600_);
return v___x_1601_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__14(void){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1602_ = lean_box(0);
v___x_1603_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__3));
v___x_1604_ = l_Lean_mkConst(v___x_1603_, v___x_1602_);
return v___x_1604_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__17(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1609_ = lean_box(0);
v___x_1610_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__16));
v___x_1611_ = l_Lean_mkConst(v___x_1610_, v___x_1609_);
return v___x_1611_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__20(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = lean_box(0);
v___x_1617_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__19));
v___x_1618_ = l_Lean_mkConst(v___x_1617_, v___x_1616_);
return v___x_1618_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__22(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1622_ = lean_box(0);
v___x_1623_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__21));
v___x_1624_ = l_Lean_mkConst(v___x_1623_, v___x_1622_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0(lean_object* v_goal_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; 
lean_inc(v_goal_1625_);
v___x_1638_ = l_Lean_MVarId_getType(v_goal_1625_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1640_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1640_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__0___redArg(v_a_1639_, v___y_1634_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1903_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1903_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1903_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__1));
v___x_1646_ = l_Lean_Expr_isAppOf(v_a_1641_, v___x_1645_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1647_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__3));
v___x_1648_ = l_Lean_Expr_isAppOf(v_a_1641_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1649_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__5));
v___x_1650_ = lean_unsigned_to_nat(3u);
v___x_1651_ = l_Lean_Expr_isAppOfArity(v_a_1641_, v___x_1649_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
lean_dec(v_a_1641_);
v___x_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1652_, 0, v_goal_1625_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1652_);
v___x_1654_ = v___x_1643_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
else
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
lean_del_object(v___x_1643_);
v___x_1656_ = l_Lean_Expr_appFn_x21(v_a_1641_);
v___x_1657_ = l_Lean_Expr_appArg_x21(v___x_1656_);
v___x_1658_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v___x_1657_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
v___x_1660_ = l_Lean_Expr_appArg_x21(v_a_1641_);
lean_dec(v_a_1641_);
v___x_1661_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v___x_1660_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
v___x_1663_ = l_Lean_Expr_appFn_x21(v___x_1656_);
lean_dec_ref(v___x_1656_);
v___x_1664_ = l_Lean_Expr_appArg_x21(v___x_1663_);
lean_dec_ref(v___x_1663_);
lean_inc_ref(v___x_1664_);
v___x_1665_ = l_Lean_Meta_getLevel(v___x_1664_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
v___x_1667_ = lean_box(0);
v___x_1668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1668_, 0, v_a_1666_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = l_Lean_mkConst(v___x_1649_, v___x_1668_);
lean_inc(v_a_1662_);
lean_inc(v_a_1659_);
lean_inc_ref(v___x_1664_);
v___x_1670_ = l_Lean_mkApp3(v___x_1669_, v___x_1664_, v_a_1659_, v_a_1662_);
v___x_1671_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_1625_, v___x_1670_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref_known(v___x_1671_, 1);
v___x_1673_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introsHygienic___lam__0___closed__0));
lean_inc(v_a_1659_);
v___x_1674_ = l_Lean_Meta_Sym_isDefEqS(v_a_1659_, v_a_1662_, v___x_1651_, v___x_1651_, v___x_1673_, v___x_1673_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1716_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1677_ = v___x_1674_;
v_isShared_1678_ = v_isSharedCheck_1716_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1674_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1716_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
uint8_t v___x_1679_; 
v___x_1679_ = lean_unbox(v_a_1675_);
lean_dec(v_a_1675_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1682_; 
lean_dec_ref(v___x_1664_);
lean_dec(v_a_1659_);
v___x_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1680_, 0, v_a_1672_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1680_);
v___x_1682_ = v___x_1677_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
else
{
lean_object* v___x_1684_; 
lean_del_object(v___x_1677_);
lean_inc_ref(v___x_1664_);
v___x_1684_ = l_Lean_Meta_getLevel(v___x_1664_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_a_1685_);
lean_dec_ref_known(v___x_1684_, 1);
v___x_1686_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__7));
v___x_1687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1687_, 0, v_a_1685_);
lean_ctor_set(v___x_1687_, 1, v___x_1667_);
v___x_1688_ = l_Lean_mkConst(v___x_1686_, v___x_1687_);
v___x_1689_ = l_Lean_mkAppB(v___x_1688_, v___x_1664_, v_a_1659_);
v___x_1690_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__1___redArg(v_a_1672_, v___x_1689_, v___y_1634_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1698_; 
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1698_ == 0)
{
lean_object* v_unused_1699_; 
v_unused_1699_ = lean_ctor_get(v___x_1690_, 0);
lean_dec(v_unused_1699_);
v___x_1692_ = v___x_1690_;
v_isShared_1693_ = v_isSharedCheck_1698_;
goto v_resetjp_1691_;
}
else
{
lean_dec(v___x_1690_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1698_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1694_ = lean_box(0);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1694_);
v___x_1696_ = v___x_1692_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
v_a_1700_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1690_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1690_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
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
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec(v_a_1672_);
lean_dec_ref(v___x_1664_);
lean_dec(v_a_1659_);
v_a_1708_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1684_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1684_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec(v_a_1672_);
lean_dec_ref(v___x_1664_);
lean_dec(v_a_1659_);
v_a_1717_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1674_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1674_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec_ref(v___x_1664_);
lean_dec(v_a_1662_);
lean_dec(v_a_1659_);
v_a_1725_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1671_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1671_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec_ref(v___x_1664_);
lean_dec(v_a_1662_);
lean_dec(v_a_1659_);
lean_dec(v_goal_1625_);
v_a_1733_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1665_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1665_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec(v_a_1659_);
lean_dec_ref(v___x_1656_);
lean_dec(v_goal_1625_);
v_a_1741_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1661_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1661_);
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
lean_dec_ref(v___x_1656_);
lean_dec(v_a_1641_);
lean_dec(v_goal_1625_);
v_a_1749_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1658_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1658_);
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
}
else
{
lean_object* v_backwardRules_1757_; lean_object* v_andIntro_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_del_object(v___x_1643_);
v_backwardRules_1757_ = lean_ctor_get(v___y_1626_, 0);
v_andIntro_1758_ = lean_ctor_get(v_backwardRules_1757_, 8);
v___x_1759_ = lean_box(0);
lean_inc_ref(v_andIntro_1758_);
v___x_1760_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_andIntro_1758_, v_goal_1625_, v___x_1759_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1760_, 1);
if (lean_obj_tag(v_a_1761_) == 1)
{
lean_object* v_mvarIds_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1875_; 
v_mvarIds_1776_ = lean_ctor_get(v_a_1761_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_a_1761_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1778_ = v_a_1761_;
v_isShared_1779_ = v_isSharedCheck_1875_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_mvarIds_1776_);
lean_dec(v_a_1761_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1875_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
if (lean_obj_tag(v_mvarIds_1776_) == 1)
{
lean_object* v_tail_1780_; 
v_tail_1780_ = lean_ctor_get(v_mvarIds_1776_, 1);
lean_inc(v_tail_1780_);
if (lean_obj_tag(v_tail_1780_) == 1)
{
lean_object* v_tail_1781_; 
v_tail_1781_ = lean_ctor_get(v_tail_1780_, 1);
if (lean_obj_tag(v_tail_1781_) == 0)
{
lean_object* v_head_1782_; lean_object* v_head_1783_; lean_object* v___x_1784_; 
lean_dec(v_a_1641_);
v_head_1782_ = lean_ctor_get(v_mvarIds_1776_, 0);
lean_inc(v_head_1782_);
lean_dec_ref_known(v_mvarIds_1776_, 2);
v_head_1783_ = lean_ctor_get(v_tail_1780_, 0);
lean_inc(v_head_1783_);
lean_dec_ref_known(v_tail_1780_, 2);
v___x_1784_ = l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts(v_head_1782_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1874_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1874_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1874_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts(v_head_1783_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v_g_1792_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
if (lean_obj_tag(v_a_1785_) == 0)
{
if (lean_obj_tag(v_a_1790_) == 0)
{
lean_del_object(v___x_1787_);
lean_del_object(v___x_1778_);
return v___x_1789_;
}
else
{
lean_object* v_val_1799_; 
lean_dec_ref_known(v___x_1789_, 1);
v_val_1799_ = lean_ctor_get(v_a_1790_, 0);
lean_inc(v_val_1799_);
lean_dec_ref_known(v_a_1790_, 1);
v_g_1792_ = v_val_1799_;
goto v___jp_1791_;
}
}
else
{
lean_dec_ref_known(v___x_1789_, 1);
if (lean_obj_tag(v_a_1790_) == 0)
{
lean_object* v_val_1800_; 
v_val_1800_ = lean_ctor_get(v_a_1785_, 0);
lean_inc(v_val_1800_);
lean_dec_ref_known(v_a_1785_, 1);
v_g_1792_ = v_val_1800_;
goto v___jp_1791_;
}
else
{
lean_object* v_val_1801_; lean_object* v_val_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1873_; 
lean_del_object(v___x_1787_);
lean_del_object(v___x_1778_);
v_val_1801_ = lean_ctor_get(v_a_1785_, 0);
lean_inc(v_val_1801_);
lean_dec_ref_known(v_a_1785_, 1);
v_val_1802_ = lean_ctor_get(v_a_1790_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_a_1790_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1804_ = v_a_1790_;
v_isShared_1805_ = v_isSharedCheck_1873_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_val_1802_);
lean_dec(v_a_1790_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1873_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; 
lean_inc(v_val_1801_);
v___x_1806_ = l_Lean_MVarId_getType(v_val_1801_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1808_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_a_1807_);
lean_dec_ref_known(v___x_1806_, 1);
lean_inc(v_val_1802_);
v___x_1808_ = l_Lean_MVarId_getType(v_val_1802_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc_n(v_a_1809_, 2);
lean_dec_ref_known(v___x_1808_, 1);
v___x_1810_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__14, &l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__14_once, _init_l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__14);
lean_inc(v_a_1807_);
v___x_1811_ = l_Lean_mkAppB(v___x_1810_, v_a_1807_, v_a_1809_);
v___x_1812_ = lean_box(0);
v___x_1813_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1811_, v___x_1812_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc_n(v_a_1814_, 2);
lean_dec_ref_known(v___x_1813_, 1);
v___x_1815_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__17, &l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__17);
lean_inc(v_a_1809_);
lean_inc(v_a_1807_);
v___x_1816_ = l_Lean_mkApp3(v___x_1815_, v_a_1807_, v_a_1809_, v_a_1814_);
v___x_1817_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__1___redArg(v_val_1801_, v___x_1816_, v___y_1634_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_dec_ref_known(v___x_1817_, 1);
v___x_1818_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__20, &l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__20_once, _init_l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__20);
lean_inc(v_a_1814_);
v___x_1819_ = l_Lean_mkApp3(v___x_1818_, v_a_1807_, v_a_1809_, v_a_1814_);
v___x_1820_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__1___redArg(v_val_1802_, v___x_1819_, v___y_1634_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1831_; 
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1831_ == 0)
{
lean_object* v_unused_1832_; 
v_unused_1832_ = lean_ctor_get(v___x_1820_, 0);
lean_dec(v_unused_1832_);
v___x_1822_ = v___x_1820_;
v_isShared_1823_ = v_isSharedCheck_1831_;
goto v_resetjp_1821_;
}
else
{
lean_dec(v___x_1820_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1831_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = l_Lean_Expr_mvarId_x21(v_a_1814_);
lean_dec(v_a_1814_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1824_);
v___x_1826_ = v___x_1804_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1828_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v___x_1826_);
v___x_1828_ = v___x_1822_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec(v_a_1814_);
lean_del_object(v___x_1804_);
v_a_1833_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1820_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1820_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
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
lean_dec(v_a_1814_);
lean_dec(v_a_1809_);
lean_dec(v_a_1807_);
lean_del_object(v___x_1804_);
lean_dec(v_val_1802_);
v_a_1841_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1817_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1817_);
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
lean_dec(v_a_1809_);
lean_dec(v_a_1807_);
lean_del_object(v___x_1804_);
lean_dec(v_val_1802_);
lean_dec(v_val_1801_);
v_a_1849_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1813_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1813_);
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
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v_a_1807_);
lean_del_object(v___x_1804_);
lean_dec(v_val_1802_);
lean_dec(v_val_1801_);
v_a_1857_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1808_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1808_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_del_object(v___x_1804_);
lean_dec(v_val_1802_);
lean_dec(v_val_1801_);
v_a_1865_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1806_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1806_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
}
}
v___jp_1791_:
{
lean_object* v___x_1794_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v_g_1792_);
v___x_1794_ = v___x_1778_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_g_1792_);
v___x_1794_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1796_; 
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1794_);
v___x_1796_ = v___x_1787_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
else
{
lean_del_object(v___x_1787_);
lean_dec(v_a_1785_);
lean_del_object(v___x_1778_);
return v___x_1789_;
}
}
}
else
{
lean_dec(v_head_1783_);
lean_del_object(v___x_1778_);
return v___x_1784_;
}
}
else
{
lean_dec_ref_known(v_tail_1780_, 2);
lean_dec_ref_known(v_mvarIds_1776_, 2);
lean_del_object(v___x_1778_);
v___y_1763_ = v___y_1633_;
v___y_1764_ = v___y_1634_;
v___y_1765_ = v___y_1635_;
v___y_1766_ = v___y_1636_;
goto v___jp_1762_;
}
}
else
{
lean_dec(v_tail_1780_);
lean_dec_ref_known(v_mvarIds_1776_, 2);
lean_del_object(v___x_1778_);
v___y_1763_ = v___y_1633_;
v___y_1764_ = v___y_1634_;
v___y_1765_ = v___y_1635_;
v___y_1766_ = v___y_1636_;
goto v___jp_1762_;
}
}
else
{
lean_del_object(v___x_1778_);
lean_dec(v_mvarIds_1776_);
v___y_1763_ = v___y_1633_;
v___y_1764_ = v___y_1634_;
v___y_1765_ = v___y_1635_;
v___y_1766_ = v___y_1636_;
goto v___jp_1762_;
}
}
}
else
{
lean_dec(v_a_1761_);
v___y_1763_ = v___y_1633_;
v___y_1764_ = v___y_1634_;
v___y_1765_ = v___y_1635_;
v___y_1766_ = v___y_1636_;
goto v___jp_1762_;
}
v___jp_1762_:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1767_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__9, &l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__9);
v___x_1768_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__11));
v___x_1769_ = l_Lean_MessageData_ofConstName(v___x_1768_, v___x_1646_);
v___x_1770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1767_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__13, &l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__13_once, _init_l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__13);
v___x_1772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1770_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = l_Lean_indentExpr(v_a_1641_);
v___x_1774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_1774_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
return v___x_1775_;
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec(v_a_1641_);
v_a_1876_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1760_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1760_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_del_object(v___x_1643_);
lean_dec(v_a_1641_);
v___x_1884_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__22, &l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___closed__22);
v___x_1885_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__1___redArg(v_goal_1625_, v___x_1884_, v___y_1634_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1893_; 
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; 
v_unused_1894_ = lean_ctor_get(v___x_1885_, 0);
lean_dec(v_unused_1894_);
v___x_1887_ = v___x_1885_;
v_isShared_1888_ = v_isSharedCheck_1893_;
goto v_resetjp_1886_;
}
else
{
lean_dec(v___x_1885_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1893_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1889_ = lean_box(0);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v___x_1889_);
v___x_1891_ = v___x_1887_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
v_a_1895_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1885_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1885_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v_goal_1625_);
v_a_1904_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1640_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1640_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec(v_goal_1625_);
v_a_1912_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1638_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1638_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___boxed(lean_object* v_goal_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0(v_goal_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts(lean_object* v_goal_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v___f_1947_; lean_object* v___x_1948_; 
lean_inc(v_goal_1934_);
v___f_1947_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___lam__0___boxed), 13, 1);
lean_closure_set(v___f_1947_, 0, v_goal_1934_);
v___x_1948_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introsHygienic_spec__1___redArg(v_goal_1934_, v___f_1947_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts___boxed(lean_object* v_goal_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts(v_goal_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__1(lean_object* v_mvarId_1963_, lean_object* v_val_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__1___redArg(v_mvarId_1963_, v_val_1964_, v___y_1973_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__1___boxed(lean_object* v_mvarId_1978_, lean_object* v_val_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_solveTrivialConjuncts_spec__1(v_mvarId_1978_, v_val_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
return v_res_1992_;
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
